// Copyright 2016 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![crate_name="rustcxx_plugin"]
#![feature(plugin_registrar, rustc_private)]

extern crate syntax;
extern crate rustc;
extern crate rustc_plugin;
extern crate rustcxx_common;

use rustcxx_common::{parse_rust_macro, Function, Cxx, Rust};

use rustc_plugin::Registry;

use syntax::abi::Abi;
use syntax::ast;
use syntax::codemap::Span;
use syntax::ext::base::{DummyResult, ExtCtxt, MacEager, MacResult};
use syntax::ext::build::AstBuilder;
use syntax::parse::token;
use syntax::tokenstream::TokenTree;
use syntax::util::small_vector::SmallVector;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_macro("cxx", cxx_macro);
    reg.register_macro("cxx_inline", cxx_inline_macro);
}

// Expand a cxx! macro into a foreign function declaration and a call to it.
// ie :
// ```
// let x = cxx![(a: u32 = self.a) -> i32) {
//     2 * a
// }];
// ```
//
// expands to :
// ```
// let x = {
//     extern "C" {
//         fn rustcxx_XXXXXXXX(a: u32) -> u32;
//     }
//
//     rustcxx_XXXXXXXX(self.a)
// };
// ```
//
// where XXXXXXXX is some unique identifier.
fn cxx_macro<'cx>(ecx: &'cx mut ExtCtxt,
                  span: Span,
                  token_tree: &[TokenTree]) -> Box<MacResult + 'cx> {

    let function = match Function::<Cxx>::parse(ecx, span, token_tree) {
        Ok(function) => function,
        Err(mut err) => {
            err.emit();
            return DummyResult::expr(span);
        }
    };

    let foreign_fn = function.foreign_item(ecx);
    let foreign_mod = ast::ItemKind::ForeignMod(ast::ForeignMod {
        abi: Abi::C,
        items: vec![foreign_fn],
    });

    let item = ecx.item(span,
                        token::keywords::Invalid.ident(),
                        Vec::new(),
                        foreign_mod);

    let call_expr = match function.call_expr(ecx) {
        Ok(expr) => expr,
        Err(mut err) => {
            err.emit();
            return DummyResult::expr(span);
        }
    };

    let block = ecx.block(span,
                          vec![ecx.stmt_item(span, item),
                               ecx.stmt_expr(call_expr)]);

    MacEager::expr(ecx.expr_block(block))
}

// cxx_inline! may contain uses of rust!.
// We create a new rust function for each of these uses.
fn cxx_inline_macro<'cx>(ecx: &'cx mut ExtCtxt,
                         _span: Span,
                         token_tree: &[TokenTree]) -> Box<MacResult + 'cx> {

    let mut items = Vec::new();

    parse_rust_macro(token_tree, &mut |span, tts| {
        let func = match Function::<Rust>::parse(ecx, span, tts) {
            Ok(func) => func,
            Err(mut err) => {
                err.emit();
                return vec![];
            }
        };

        items.push(func.item(ecx));

        // It doesn't matter what the macro gets replaced by.
        // The plugin doesn't use it.
        vec![]
    });

    MacEager::items(SmallVector::many(items))
}
