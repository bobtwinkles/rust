// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// This test is explicitly about the quality of error message emitted, not
// detecting a class of error not covered by other tests

#![feature(nll)]
#![feature(in_band_lifetimes)]

struct CookieJar<'data> {
    vec: Vec<String>,
    data: &'data (),
}

impl CookieJar<'data> {
    fn cookie_me(&self, _: &i32) -> Cookie<'data> {
        let next = 22;
        me_want_cookie(next, self)
    }
}

struct Cookie<'jar> {
    jar: &'jar CookieJar<'jar>
}

fn me_want_cookie(next: usize, jar: &'jar CookieJar<'jar>) -> Cookie<'jar> {
    Cookie { jar }
}

fn main() {
    let jar = CookieJar { vec: vec![], data: &() };
    me_want_cookie(0, &jar);
}
