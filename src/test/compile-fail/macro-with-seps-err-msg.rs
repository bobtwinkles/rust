// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// gate-test-use_extern_macros

macro_rules! m {
    ($p1: path) => {
        #[derive($p1)] struct U;
    }
}

fn main() {
    globnar::brotz!(); //~ ERROR non-ident macro paths are experimental
    #[derive(foo::Bar)] struct T; //~ ERROR non-ident macro paths are experimental
    ::foo!(); //~ ERROR non-ident macro paths are experimental

    foo::<T>!();
    //~^ ERROR generic arguments in macro path
    //~| ERROR generic arguments in macro path
    //~| ERROR generic arguments in macro path
    foo::<>!();
    //~^ ERROR generic arguments in macro path
    //~| ERROR generic arguments in macro path
    //~| ERROR generic arguments in macro path
    m!(MyTrait<>);
    //~^ ERROR generic arguments in macro path
    //~| ERROR generic arguments in macro path
    //~| ERROR generic arguments in macro path
    //~| ERROR generic arguments in macro path
}
