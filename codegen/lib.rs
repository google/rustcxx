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

#![crate_name="rustcxx_codegen"]
#![feature(rustc_private)]

extern crate syntax;
extern crate rustc;
extern crate rustc_driver;
extern crate rustcxx_common;

#[cfg(feature="gcc")]
extern crate gcc;

use rustcxx_common::{Cxx, Rust, Function, parse_rust_macro, tokens_to_cpp};

use syntax::parse;
use syntax::ast;
use syntax::codemap::respan;
use syntax::ext::base::{DummyResolver, ExtCtxt};
use syntax::ext::expand;
use syntax::visit;

use std::fs::File;
use std::io::{self, Write};
use std::sync::{Arc, Mutex};

pub struct Codegen {
    code: String,
    deps: Vec<String>,
}

impl Codegen {
    /// Parse a rust file, and generate the corresponding C++ code
    pub fn generate(src: &std::path::Path) -> Codegen {
        let result : Arc<Mutex<Option<Codegen>>> = Arc::new(Mutex::new(None));
        let result_ = result.clone();

        let src = src.to_owned();
        rustc_driver::monitor(move || {
            let sess = parse::ParseSess::new();

            let krate = match parse::parse_crate_from_file(&src, Vec::new(), &sess) {
                Ok(krate) => krate,
                Err(mut err) => {
                    err.emit();
                    sess.span_diagnostic.abort_if_errors();
                    unreachable!();
                }
            };

            let cfg = expand::ExpansionConfig::default("foo".to_string());

            let mut resolver = DummyResolver;
            let ecx = ExtCtxt::new(&sess, Vec::new(), cfg, &mut resolver);

            let mut visitor = CodegenVisitor::new(&ecx);
            visit::walk_crate(&mut visitor, &krate);
            let code = visitor.code();

            let deps = sess.codemap().files.borrow().iter()
                .filter(|fmap| fmap.is_real_file())
                .filter(|fmap| !fmap.is_imported())
                .map(|fmap| fmap.name.clone())
                .collect();

            *result.lock().expect("lock poisoned") = Some(Codegen {
                code: code,
                deps: deps,
            });

            sess.span_diagnostic.abort_if_errors();
        });

        let value = result_.lock().expect("lock poisoned")
                           .take().expect("missing result");
        value
    }

    pub fn write_code<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        writer.write_all(self.code.as_bytes())
    }

    pub fn write_depfile<W: Write>(&self,
                                   writer: &mut W,
                                   out_path: &str) -> io::Result<()> {
        try!(writeln!(writer, "{}: {}", out_path, self.deps.join(" ")));

        // Include an empty rule for every source file.
        // Keeps make happy even if a file is deleted
        for dep in self.deps.iter() {
            try!(writeln!(writer, "{}:", dep));
        }

        Ok(())
    }

    pub fn write_code_to_path<P>(&self, path: P) -> io::Result<()>
        where P: AsRef<std::path::Path>{

        let mut file = try!(File::create(path));
        try!(self.write_code(&mut file));

        Ok(())
    }

    pub fn write_depfile_to_path<P>(&self, path: P, out_path: &str) -> io::Result<()>
        where P: AsRef<std::path::Path> {

        let mut file = try!(File::create(path));
        try!(self.write_depfile(&mut file, out_path));

        Ok(())
    }
}

/// Visitor which walks a crate looking for cxx! and cxx_inline! macros, and generates
/// the corresponding code.
struct CodegenVisitor<'a, 'b: 'a> {
    code: Vec<String>,
    ecx: &'a ExtCtxt<'b>,
}

impl <'a, 'b> CodegenVisitor<'a, 'b> {
    fn new(ecx: &'a ExtCtxt<'b>) -> CodegenVisitor<'a, 'b> {
        CodegenVisitor {
            code: Vec::new(),
            ecx: ecx,
        }
    }

    fn code(&self) -> String {
        self.code.join("\n")
    }
}

impl <'a, 'b> visit::Visitor for CodegenVisitor<'a, 'b> {
    fn visit_mac(&mut self, mac: &ast::Mac) {
        match mac.node.path.to_string().as_ref() {
            "cxx" => {
                let func = Function::<Cxx>::parse(
                    self.ecx, mac.span, &mac.node.tts
                ).and_then(|func| func.cxx_code(self.ecx));

                match func {
                    Ok(func) => self.code.push(func),
                    Err(mut err) => err.emit(),
                }
            }

            "cxx_inline" => {
                let tokens = parse_rust_macro(&mac.node.tts, &mut |span, tts| {
                    let func = Function::<Rust>::parse(self.ecx, span, tts).and_then(|func| {
                        let decl = try!(func.cxx_decl(self.ecx));
                        let call = try!(func.cxx_call(self.ecx));
                        Ok((decl, call))
                    });

                    match func {
                        Ok((decl, call)) => {
                            self.code.push(decl);
                            vec![respan(span, call)]
                        },
                        Err(mut err) => {
                            err.emit();
                            vec![]
                        }
                    }
                });

                let content = tokens_to_cpp(self.ecx, &tokens);
                self.code.push(content);
            }

            _ => {}
        }
    }
}

#[cfg(feature="gcc")]
pub fn build<P>(path: P) where P: AsRef<std::path::Path> {
    build_with_config(path, |_| {})
}

#[cfg(feature="gcc")]
pub fn build_with_config<P, F>(path: P, f: F)
        where P: AsRef<std::path::Path>,
              F: FnOnce(&mut gcc::Config) {
    let out = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("rustcxx_generated.cpp");
    Codegen::generate(path.as_ref()).write_code_to_path(&out).expect("Could not write generated source");

    let mut config = gcc::Config::new();
    config.cpp(true).file(&out);
    f(&mut config);
    config.compile("librustcxx_generated.a");
}
