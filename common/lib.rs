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

#![crate_name="rustcxx_common"]
#![feature(rustc_private, slice_patterns)]

extern crate syntax;
extern crate rustc;

mod types;

use std::borrow::Cow;
use std::hash::{SipHasher, Hash, Hasher};
use std::iter;

use syntax::abi::Abi;
use syntax::ast::{self, DUMMY_NODE_ID};
use syntax::codemap::{Span, Spanned, dummy_spanned, respan, spanned, DUMMY_SP};
use syntax::errors::Handler;
use syntax::ext::base::ExtCtxt;
use syntax::ext::build::AstBuilder;
use syntax::ext::quote::rt::ToTokens;
use syntax::parse::{token, PResult};
use syntax::parse::common::SeqSep;
use syntax::parse::parser::Parser;
use syntax::print::pprust::{token_to_string, tts_to_string};
use syntax::ptr::P;
use syntax::tokenstream::TokenTree;

/// Language specific parsing.
///
/// The two macros, `cxx!` and `rust!`, share a similar syntax.
/// This trait differentiates the two, such that the rest of the parsing code can be reused.
pub trait Lang {
    type Body: ToTokens;
    type ArgValue;

    fn parse_body<'a>(parser: &mut Parser<'a>) -> PResult<'a, Self::Body>;
    fn parse_arg_value<'a>(ecx: &ExtCtxt,
                           parser: &mut Parser<'a>,
                           ident: ast::SpannedIdent) -> PResult<'a, Self::ArgValue>;
}

pub enum Rust {}
pub enum Cxx {}

impl Lang for Rust {
    type Body = P<ast::Block>;
    type ArgValue = Vec<Spanned<String>>;

    fn parse_body<'a>(parser: &mut Parser<'a>) -> PResult<'a, Self::Body> {
        parser.parse_block()
    }

    fn parse_arg_value<'a>(_ecx: &ExtCtxt,
                           parser: &mut Parser<'a>,
                           ident: ast::SpannedIdent) -> PResult<'a, Self::ArgValue> {
        if parser.eat(&token::Eq) {
            let mut tokens = Vec::new();
            while !parser.check(&token::Comma) &&
                  !parser.check(&token::CloseDelim(token::Paren)) {
                tokens.push(try!(parser.parse_token_tree()));
            }
            Ok(flatten_tts(&tokens))
        } else {
            Ok(vec![respan(ident.span, ident.node.to_string())])
        }
    }
}

impl Lang for Cxx {
    type Body = Vec<TokenTree>;
    type ArgValue = P<ast::Expr>;

    fn parse_body<'a>(parser: &mut Parser<'a>) -> PResult<'a, Self::Body> {
        try!(parser.expect(&token::OpenDelim(token::Brace)));

        parser.parse_seq_to_end(
            &token::CloseDelim(token::Brace),
            SeqSep::none(),
            |parser| parser.parse_token_tree())
    }

    fn parse_arg_value<'a>(ecx: &ExtCtxt,
                           parser: &mut Parser<'a>,
                           ident: ast::SpannedIdent) -> PResult<'a, Self::ArgValue> {
        if parser.eat(&token::Eq) {
            parser.parse_expr()
        } else {
            Ok(ecx.expr_ident(ident.span, ident.node))
        }
    }
}

pub struct Function<L: Lang> {
    pub span: Span,
    pub name: ast::Ident,
    pub ret_ty: Option<P<ast::Ty>>,
    pub args: Vec<ArgSpec<L>>,
    pub body: L::Body,
}

impl <L: Lang> Function<L> {
    pub fn parse<'a>(ecx: &ExtCtxt<'a>,
                     span: Span,
                     tts: &[TokenTree]) -> PResult<'a, Function<L>> {
        let mut parser = ecx.new_parser_from_tts(tts);

        let args = if parser.check(&token::OpenDelim(token::Paren)) {
            Some(try!(Self::parse_args(ecx, &mut parser)))
        } else {
            None
        };

        let ret_ty = if args.is_some() && parser.check(&token::RArrow) {
            Some(try!(Self::parse_ret_ty(&mut parser)))
        } else {
            None
        };

        let body = try!(L::parse_body(&mut parser));

        let hash = {
            let mut hasher = SipHasher::new();
            tts_to_string(tts).hash(&mut hasher);
            hasher.finish()
        };

        let name = ecx.ident_of(&format!("rustcxx_{:016x}", hash));

        Ok(Function {
            span: span,
            name: name,
            ret_ty: ret_ty,
            args: args.unwrap_or_else(|| Vec::new()),
            body: body,
        })
    }

    fn parse_args<'a>(ecx: &ExtCtxt,
                      parser: &mut Parser<'a>) -> PResult<'a, Vec<ArgSpec<L>>> {
        parser.parse_unspanned_seq(
            &token::OpenDelim(token::Paren),
            &token::CloseDelim(token::Paren),
            SeqSep::trailing_allowed(token::Comma),
            |parser| ArgSpec::parse(ecx, parser))
    }

    fn parse_ret_ty<'a>(parser: &mut Parser<'a>) -> PResult<'a, P<ast::Ty>> {
        try!(parser.expect(&token::RArrow));
        parser.parse_ty()
    }

    pub fn fn_decl(&self, ecx: &ExtCtxt) -> P<ast::FnDecl> {
        let args = self.args.iter().map(|arg| {
            ecx.arg(arg.ident.span, arg.ident.node, arg.ty.clone())
        }).collect();

        let ret_ty = self.ret_ty.clone()
                                .map(ast::FunctionRetTy::Ty)
                                .unwrap_or(ast::FunctionRetTy::Default(DUMMY_SP));

        P(ast::FnDecl {
            inputs: args,
            output: ret_ty,
            variadic: false
        })
    }

    pub fn foreign_item(&self, ecx: &ExtCtxt) -> ast::ForeignItem {
        let fn_decl = self.fn_decl(ecx);

        ast::ForeignItem {
            id: DUMMY_NODE_ID,
            ident: self.name,
            attrs: Vec::new(),
            node: ast::ForeignItemKind::Fn(fn_decl, ast::Generics::default()),
            vis: ast::Visibility::Inherited,
            span: self.span,
        }
    }

    pub fn cxx_args<'a>(&self, ecx: &'a ExtCtxt) -> PResult<'a, String> {
        let args = try!(self.args.iter().map(|arg| {
            let ty = try!(arg.cxx_type(&ecx.parse_sess.span_diagnostic));
            Ok(format!("{} const {}", ty, arg.ident.node))
        }).collect::<PResult<Vec<String>>>());

        Ok(args.join(", "))
    }

    pub fn cxx_ret_ty<'a>(&self, ecx: &'a ExtCtxt) -> PResult<'a, Cow<'static, str>> {
        self.ret_ty.as_ref().map(|ty| {
            types::convert_ty_to_cxx(&ecx.parse_sess.span_diagnostic, &ty)
        }).unwrap_or(Ok(Cow::from("void")))
    }
}

#[derive(Debug)]
pub struct ArgSpec<L: Lang> {
    pub ident: ast::SpannedIdent,
    pub ty: P<ast::Ty>,
    pub value: L::ArgValue,
}

impl <L: Lang> ArgSpec<L> {
    pub fn parse<'a>(ecx: &ExtCtxt,
                     parser: &mut Parser<'a>) -> PResult<'a, ArgSpec<L>> {
        let ident = {
            let lo = parser.span.lo;
            let ident = try!(parser.parse_ident());
            let hi = parser.span.lo;
            spanned(lo, hi, ident)
        };

        try!(parser.expect(&token::Colon));
        let ty = try!(parser.parse_ty());

        let value = try!(L::parse_arg_value(ecx, parser, ident));

        Ok(ArgSpec {
            ident: ident,
            ty: ty,
            value: value,
        })
    }

    pub fn cxx_type<'a>(&self, handler: &'a Handler)
                        -> PResult<'a, Cow<'static, str>> {

        types::convert_ty_to_cxx(handler, &self.ty)
    }
}


impl Function<Cxx> {
    pub fn call_expr<'a>(&self, ecx: &'a ExtCtxt) -> PResult<'a, P<ast::Expr>> {
        let name = self.name.clone();
        let args = self.args.iter().map(|arg| arg.value.clone()).collect();

        Ok(ecx.expr_call_ident(self.span, name, args))
    }

    pub fn cxx_code<'a>(&self, ecx: &'a ExtCtxt) -> PResult<'a, String> {
        let ret_ty = try!(self.cxx_ret_ty(ecx));
        let args = try!(self.cxx_args(ecx));

        let signature = format!(
            "{span}\nextern \"C\" {ret_ty} {name}({args})",
            span = span_to_cpp_directive(ecx, self.span),
            ret_ty = ret_ty,
            name = self.name,
            args = args);

        let mut body = tokens_to_cpp(ecx, &flatten_tts(&self.body));
        if self.ret_ty.is_some() {
            body = format!("return ({{\n{};\n}});", body);
        }

        Ok(format!("{} {{\n{}\n}}\n", signature, body))
    }
}

// Calling rust from C++ is a bit trickier.
// We must declare the function before it can be used.
// However C++ requires the function to be declared outside the current function, but then we may
// miss type definitions which are in scope due to being in a namespace, or some includes.
//
// For example :
// ```c++
// #include <stdint.h>
// #include <stdio.h>
//
// void foo() {
//     uint32_t a = 3;
//     uint32_t double = rust![(a: uint32_t) -> uint32_t {
//         a * 2
//     }];
//     printf("double: ", a);
// }
// ```
//
// Declaring the extern function before the includes would not work, as uint32_t is not defined at
// this point. Finding the right place to declare it would be complicated and would almost require
// a full C++ parser.
//
// Instead we use an alternative approach. The function's symbol is declared with an opaque type at
// the top of the file. This does not require argument types to be in scope.
// When invoking the function, the symbol is first casted into a function pointer of the correct type.
// This way, the same typing context as in the original source is used.
//
// The example above would be translated into the following :
//
// ```c++
// struct rustcxx_XXXXXXXX;
// extern "C" rustcxx_XXXXXXXX rustcxx_XXXXXXXX;
//
// #include <stdint.h>
// #include <stdio.h>
//
// void foo() {
//     uint32_t a = 3;
//     uint32_t double = ((uint32_t (*)(uint32_t a)) &rustcxx_XXXXXXXX)(a);
//     printf("double: ", a);
// }
// ```
impl Function<Rust> {
    pub fn cxx_decl<'a>(&self, _ecx: &'a ExtCtxt) -> PResult<'a, String> {
        Ok(format!("struct {}; extern \"C\" {} {};", self.name, self.name, self.name))
    }

    pub fn cxx_call<'a>(&self, ecx: &'a ExtCtxt) -> PResult<'a, String> {
        let ret_ty = try!(self.cxx_ret_ty(ecx));
        let args_sig = try!(self.cxx_args(ecx));

        let arg_separator = respan(DUMMY_SP, String::from(","));
        let args_value = self.args.iter().map(|arg| {
            arg.value.clone()
        }).collect::<Vec<_>>().join(&arg_separator);

        let cast_ty = format!("{} (*) ({})", ret_ty, args_sig);
        let fn_ptr = format!("( ({}) &{} )", cast_ty, self.name);
        let call = format!("{} ({})", fn_ptr, tokens_to_cpp(ecx, &args_value));
        Ok(call)
    }

    pub fn item<'a>(&self, ecx: &'a ExtCtxt) -> P<ast::Item> {
        let decl = self.fn_decl(ecx);

        // Function has to be no_mangle, otherwise it can't be called from C++
        let no_mangle = ecx.meta_word(self.span, token::intern("no_mangle").as_str());

        // The function has to be exported or it would be optimized out by the compiler.
        // The compiler already prints an error, but it is easy to miss, so make it a hard error.
        let deny = ecx.meta_list(
            self.span,
            token::intern("deny").as_str(),
            vec![ecx.meta_list_item_word(self.span, token::intern("private_no_mangle_fns").as_str())]);

        let attrs = vec![
            ecx.attribute(self.span, no_mangle),
            ecx.attribute(self.span, deny),
        ];

        let fn_item = ast::ItemKind::Fn(
            decl, ast::Unsafety::Unsafe, dummy_spanned(ast::Constness::NotConst),
            Abi::C, ast::Generics::default(), self.body.clone());

        P(ast::Item {
            ident: self.name,
            attrs: attrs,
            id: ast::DUMMY_NODE_ID,
            node: fn_item,
            vis: ast::Visibility::Public,
            span: self.span,
        })
    }
}

/// Find and replace uses of rust![ .. ] in a token tree stream.
///
/// The callback is invoked for every use of the rust! macro and it's result is used to replace it.
pub fn parse_rust_macro<F>(tts: &[TokenTree], f: &mut F) -> Vec<Spanned<String>>
        where F: FnMut(Span, &[TokenTree]) -> Vec<Spanned<String>> {
    let mut result = Vec::new();

    // Iterate over the tokens with 3 tokens of lookahead.
    let mut i = 0;
    loop {
        match (tts.get(i), tts.get(i+1), tts.get(i+2)) {
            (Some(&TokenTree::Token(_, token::Ident(ident))),
             Some(&TokenTree::Token(_, token::Not)),
             Some(&TokenTree::Delimited(span, ref contents)))
                    if ident.name.to_string() == "rust" => {
                i += 2;
                result.extend(f(span, &contents.tts));
            }

            (Some(&TokenTree::Delimited(_, ref contents)), _, _) => {
                // Recursively look into the token tree
                result.push(respan(contents.open_span, token_to_string(&contents.open_token())));
                result.extend(parse_rust_macro(&contents.tts, f));
                result.push(respan(contents.close_span, token_to_string(&contents.close_token())));
            }

            (Some(&TokenTree::Token(span, ref tok)), _, _) => {
                result.push(respan(span, token_to_string(tok)));
            }

            (Some(&TokenTree::Sequence(..)), _, _) => unimplemented!(),

            (None, _, _) => break,
        }

        i += 1;
    }

    result
}

/// Flatten a token tree stream.
///
/// Each token is stringified and paired with it's span.
pub fn flatten_tts(tts: &[TokenTree]) -> Vec<Spanned<String>> {
    tts.iter().flat_map(|tt| {
        match tt {
            &TokenTree::Token(span, ref tok) => {
                vec![respan(span, token_to_string(tok))]
            }
            &TokenTree::Delimited(_, ref delimited) => {
                let open = respan(delimited.open_span, token_to_string(&delimited.open_token()));
                let close = respan(delimited.close_span, token_to_string(&delimited.close_token()));

                iter::once(open)
                    .chain(flatten_tts(&delimited.tts))
                    .chain(iter::once(close))
                    .collect()
            }
            &TokenTree::Sequence(..) => unimplemented!()
        }
    }).collect()
}

/// Join tokens, using `#line` C preprocessor directives to maintain span
/// information.
pub fn tokens_to_cpp(ecx: &ExtCtxt, tokens: &[Spanned<String>]) -> String {
    let codemap = ecx.parse_sess.codemap();

    let mut last_pos = codemap.lookup_char_pos(DUMMY_SP.lo);
    let mut column = 0;
    let mut contents = String::new();

    for token in tokens {
        if token.span != DUMMY_SP {
            let pos = codemap.lookup_char_pos(token.span.lo);

            if pos.file.name == pos.file.name && pos.line == last_pos.line + 1 {
                contents.push('\n');
                column = 0;
            } else if pos.file.name != pos.file.name || pos.line != last_pos.line {
                contents.push('\n');
                contents.push_str(&span_to_cpp_directive(ecx, token.span));
                contents.push('\n');
                column = 0;
            }

            // Pad the code such that the token remains on the same column
            while column < pos.col.0 {
                contents.push(' ');
                column += 1;
            }
            last_pos = pos;
        }

        column += token.node.len();
        contents.push_str(&token.node);
    }

    return contents;
}

pub fn span_to_cpp_directive(ecx: &ExtCtxt, span: Span) -> String {
    let codemap = ecx.parse_sess.codemap();
    let pos = codemap.lookup_char_pos(span.lo);
    format!("#line {} {:?}", pos.line, pos.file.name)
}
