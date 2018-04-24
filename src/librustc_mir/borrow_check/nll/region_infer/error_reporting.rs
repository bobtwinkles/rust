// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::nll::region_infer::values::RegionElement;
use rustc::hir::def_id::DefId;
use rustc::infer::InferCtxt;
use rustc::infer::RegionVariableOrigin;
use rustc::infer::error_reporting::nice_region_error::NiceRegionError;
use rustc::mir::Mir;
use rustc::ty::{self, RegionVid, Region};
use rustc::util::common::ErrorReported;
use super::RegionInferenceContext;
use syntax_pos::{Span, Mark};
use syntax_pos::symbol::InternedString;

/// Represents a description of a region
#[derive(Clone,Debug)]
enum RegionDescription {
    /// A universal region with a name
    NamedUniversalRegion(InternedString),
    /// A universal region with no user-provided name. The span should point to the place
    /// where the universal region is created, probably a function argument. The Name
    /// is what we consider to be the "important part" of the pattern binding of the argument,
    /// as created by rustc::hir::Pat::simple_name
    AnonymousUniversalRegion(Option<InternedString>, Span),
    /// An anonymous existential region. The span should point to the expression
    /// that created the region.
    AnonymousExistentialRegion(Span),
    /// This is a static region
    Static,
}

impl RegionDescription {
    fn name(&self) -> String {
        use self::RegionDescription::*;
        match *self {
            NamedUniversalRegion(name) =>
                format!("region `{}`", name),
            Static =>
                format!("region `'static`"),
            AnonymousUniversalRegion(Some(name), _) =>
                format!("region for the argument `{}`", name),
            AnonymousUniversalRegion(None, _) |
            AnonymousExistentialRegion(_) =>
                format!("anonymous region"),
        }
    }

    fn span(&self) -> Option<Span> {
        use self::RegionDescription::*;
        match *self {
            Static |
            NamedUniversalRegion(_) => None,
            AnonymousUniversalRegion(_, span) |
            AnonymousExistentialRegion(span) => Some(span),
        }
    }
}

impl<'tcx> RegionInferenceContext<'tcx> {
    /// Report an error because the universal region `fr` was required to outlive
    /// `outlived_fr` but it is not known to do so. For example:
    ///
    /// ```
    /// fn foo<'a, 'b>(x: &'a u32) -> &'b u32 { x }
    /// ```
    ///
    /// Here we would be invoked with `fr = 'a` and `outlived_fr = `'b`.
    /// If `fr` is not a universal region, we abort
    pub(super) fn report_not_outlived_error(
        &self,
        infcx: &InferCtxt<'_, '_, 'tcx>,
        mir: &Mir<'tcx>,
        mir_def_id: DefId,
        fr: RegionVid,
        outlived_fr: RegionVid,
        blame_span: Span,
    ) {
        let free_region = self.to_error_region(fr);
        let outlived_region = self.to_error_region(outlived_fr);

        debug!("report_not_outlived_error({:?}: {:?}, {:?}: {:?})",
               fr,
               free_region,
               outlived_fr,
               outlived_region);

        if let (Some(f), Some(o)) = (free_region, outlived_region) {
            // The easy case for us: both regions came from somewhere we already have AST regions
            // for so report that bad dataflow has happened
            let tables = infcx.tcx.typeck_tables_of(mir_def_id);
            let nice = NiceRegionError::new_from_span(infcx.tcx, blame_span, o, f, Some(tables));
            if let Some(ErrorReported) = nice.try_report() {
                return;
            }
        }

        // Attempt to figure out where regions start
        let fr_desc = self.compute_name_and_span(mir, mir_def_id, infcx, fr);
        let or_desc = self.compute_name_and_span(mir, mir_def_id, infcx, outlived_fr);

        let mut diag = struct_span_err!(
            infcx.tcx.sess,
            blame_span,
            E0999,
            "The {} does not outlive the {}. Required due to this expression:",
            fr_desc.name(),
            or_desc.name()
        );
        if let Some(sp) = fr_desc.span() {
            diag.span_note(sp, "the too-short region is created here");
        }
        if let Some(sp) = or_desc.span() {
            diag.span_note(sp, "the region to be outlived is created here");
        }

        diag.emit();
    }

    fn compute_name_and_span(&self,
                             mir: &Mir<'tcx>,
                             mir_def_id: DefId,
                             infcx: &InferCtxt<'_, '_, 'tcx>,
                             region_vid: RegionVid) -> RegionDescription {
        use borrow_check::nll::universal_regions::RegionClassification;
        let region = self.to_error_region(region_vid);
        debug!("compute_name_and_span({:?})", region);
        debug!("is_universal_region({:?}) -> {:?}",
               region_vid,
               self.universal_regions.is_universal_region(region_vid));
        match self.universal_regions.region_classification(region_vid) {
            // The only "global" region is 'static
            Some(RegionClassification::Global) => RegionDescription::Static,
            Some(RegionClassification::External) => {
                // External regions arise when checking closures.
                region.and_then(|r| {
                    self.try_describe_universal_region(mir_def_id, infcx, r)
                }).expect(&format!("Couldn't derive a description for an external universal \
                                    region {:?}| {:?} ({:?})",
                                   region_vid,
                                   self.definitions[region_vid],
                                   region))
            }
            // Local regions here should only come from incoming lifetime parameters.
            Some(RegionClassification::Local) => {
                let region = region.expect("unable to convert Local region to an error region");
                self.try_describe_universal_region(mir_def_id, infcx, region)
                    .expect(&format!("Couldn't derive a description for a local universal \
                                     region {:?}| {:?} ({:?})",
                                     region_vid,
                                     self.definitions[region_vid],
                                     region))
            },
            None =>
                self.try_describe_existential_region(mir, region_vid)
                    .expect(&format!("Couldn't derive a description for an existential region: \
                                      {:?} {:?}",
                                     region_vid,
                                     self.definitions[region_vid]))

        }
    }

    /// Converts a region inference variable into a `ty::Region` that
    /// we can use for error reporting. If `r` is universally bound,
    /// then we use the name that we have on record for it. If `r` is
    /// existentially bound, then we check its inferred value and try
    /// to find a good name from that. Returns `None` if we can't find
    /// one (e.g., this is just some random part of the CFG).
    pub fn to_error_region(&self, r: RegionVid) -> Option<ty::Region<'tcx>> {
        if self.universal_regions.is_universal_region(r) {
            return self.definitions[r].external_name;
        } else {
            let inferred_values = self.inferred_values
                .as_ref()
                .expect("region values not yet inferred");
            let upper_bound = self.universal_upper_bound(r);
            if inferred_values.contains(r, upper_bound) {
                self.to_error_region(upper_bound)
            } else {
                None
            }
        }
    }

    /// Attempts to find the argument that created the provided universal region
    /// Returns None if none can be found
    fn try_describe_universal_region(&self,
                                     mir_def_id: DefId,
                                     infcx: &InferCtxt<'_, '_, 'tcx>,
                                     anon_region: Region<'tcx>) -> Option<RegionDescription> {
        debug!("try_describe_universal_region({:?})", anon_region);
        // Mostly copied from
        // librustc/infer/error_reporting/nice_region_error/util.rs:find_arg_with_region
        let id = match *anon_region {
            ty::ReStatic => {
                // If the region is static, we already know where this is going
                return Some(RegionDescription::Static)
            },
            ty::ReFree(ref free_region) => free_region.scope,
            ty::ReEarlyBound(ref ebr) => {
                // If we have an explicit name for the region, just return that
                if ebr.name.len() > 0 {
                    return Some(RegionDescription::NamedUniversalRegion(ebr.name));
                }

                // Otherwise, try to track down the argument this region came from
                infcx.tcx.parent_def_id(ebr.def_id).unwrap()
            },
            _ => return None, // Not a free region
        };

        let hir = &infcx.tcx.hir;
        let node_id = hir.as_local_node_id(id)?;
        let body_id = hir.maybe_body_owned_by(node_id)?;
        let body = hir.body(body_id);
        let tables = infcx.tcx.typeck_tables_of(mir_def_id);
        body.arguments
            .iter()
            .enumerate()
            .filter_map(|(_index, arg)| {
                // May return None; sometimes the tables are not yet populated.
                let ty = tables.node_id_to_type_opt(arg.hir_id)?;
                let mut found_anon_region = false;
                let _ = infcx.tcx.fold_regions(&ty, &mut false, |r, _| {
                    if *r == *anon_region {
                        found_anon_region = true;
                    }
                    r
                });
                if found_anon_region {
                    let arg_name = arg.pat.simple_name().map(|x| { x.as_str() });
                    Some(RegionDescription::AnonymousUniversalRegion(arg_name, arg.pat.span))
                } else {
                    None
                }
            })
            .next()
    }

    /// Estimates the span covered by the provided region
    /// If the variable originates outside of NLL inference, we just use that span
    /// Returns a pair of spans representing our best guess as to the start and end of the region
    fn try_describe_existential_region(&self,
                                       mir: &Mir<'tcx>,
                                       region: RegionVid)
                                       -> Option<RegionDescription> {
        use self::RegionVariableOrigin::*;
        let rdata = &self.definitions[region];
        let orig = rdata.origin;

        let span_from_element = |e| {
            match e {
                RegionElement::Location(l) => {
                    Some(mir.source_info(l).span)
                },
                RegionElement::UniversalRegion(r) => {
                    debug!("encountered universal region {:?} ({:?}) that didn't \
                            have an external name",
                         r,
                         self.to_error_region(r));
                    None
                }
            }
        };

        if let NLL(_) = orig {
            // Attempt to figure out where this region is lexically.
            // Our general strategy is to start with a span from the first region element,
            // and then just keep growing that span until it encompasses the region.
            let mut iter = self.liveness_constraints.elements_contained_in(region);
            if let Some(init) = iter.next() {
                // Compute a reasonable lexical start location for the region to return to the user
                let region_start = span_from_element(init);
                let region_start = iter.fold(region_start, |lhs, el| {
                    let mut lhs = lhs?;
                    let mut rhs = span_from_element(el)?;
                    if rhs.ctxt() != lhs.ctxt() {
                        let lub = Mark::lub(rhs.ctxt().outer(), lhs.ctxt().outer());
                        while rhs.ctxt().outer() != lub {
                            rhs = rhs.parent().unwrap();
                        }
                        while lhs.ctxt().outer() != lub {
                            lhs = lhs.parent().unwrap();
                        }
                    }
                    // Now that they're in the same syntax context, we can just do a simple
                    // comparison
                    if rhs.lo() < lhs.lo() {
                        Some(rhs)
                    } else {
                        Some(lhs)
                    }
                })?;
                Some(RegionDescription::AnonymousExistentialRegion(region_start))
            } else {
                // We can't estimate a reasonable span for the region.
                // This would mean that we're trying to report an error
                // on a region with no constraints at all, which doesn't
                // make a whole lot of sense
                bug!("Failed to estimate span for region {:?}", region)
            }
        } else {
            bug!("A non-nll region {:?} has ended up inside the NLL definitions map!", orig)
        }
    }
}
