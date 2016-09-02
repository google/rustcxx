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

#![feature(rustc_private)]

extern crate getopts;
extern crate rustcxx_codegen;

use std::io::{stdout, stderr, Write};
use std::path::PathBuf;
use std::process::exit;

use rustcxx_codegen::Codegen;

fn main() {
    let args : Vec<String> = std::env::args().collect();

    match run(args) {
        Ok(()) => (),
        Err(msg) => {
            writeln!(stderr(), "error: {}", msg).expect("writing to stderr failed");
            exit(1);
        }
    }
}

fn run(args: Vec<String>) -> Result<(), String> {
    let args = Arguments::parse(&args[0], &args[1..]);

    let codegen = Codegen::generate(&args.input);

    try!(codegen.write_code_to_path(&args.output).map_err(|err| {
        format!("could not write output to {}: {}", args.output.display(), err)
    }));

    if let Some(ref depfile) = args.depfile {
        try!(codegen.write_depfile_to_path(&depfile,
                                           &args.output.to_string_lossy()).map_err(|err| {
            format!("could not write depfile to {}: {}", args.output.display(), err)
        }));
    }

    Ok(())
}

struct Arguments {
    input: PathBuf,
    output: PathBuf,
    depfile: Option<PathBuf>,
}

fn print_usage_and_quit(name: &str,
                        opts: &[getopts::OptGroup],
                        header: Option<&str>,
                        error: bool) -> ! {

    let brief = format!("Usage: {} [options] INPUT", name);
    let usage = getopts::usage(&brief, opts);

    let message = if let Some(header) = header {
        format!("{}: {}\n{}", name, header, usage)
    } else {
        usage
    };

    if error {
        stderr().write_all(message.as_bytes()).expect("writing to stderr failed");
        exit(1);
    } else {
        stdout().write_all(message.as_bytes()).expect("writing to stdout failed");
        exit(0);
    }
}

impl Arguments {
    fn parse(name: &str, args: &[String]) -> Arguments {
        let opts = &[
            getopts::optopt("o", "output", "output file", "OUTPUT"),
            getopts::optopt("", "dep-file", "generate dependency file", "DEPFILE"),
            getopts::optflag("h", "help", "display this help menu"),
        ];

        let matches = match getopts::getopts(&args, opts) {
            Ok(matches) => matches,
            Err(failure) => {
                print_usage_and_quit(name, opts, Some(&failure.to_string()), true);
            }
        };

        if matches.opt_present("help") {
            print_usage_and_quit(name, opts, None, false);
        }

        let input = match matches.free.split_first() {
            None => {
                print_usage_and_quit(name, opts, Some("no input filename given"), true);
            }

            Some((_, rest)) if !rest.is_empty() => {
                print_usage_and_quit(name, opts, Some("multiple input filenames provided"), true)
            }

            Some((path, _)) => PathBuf::from(path),
        };

        let output = matches.opt_str("output").map(PathBuf::from).unwrap_or_else(|| {
            let mut path = input.clone();
            path.set_extension("cpp");
            path
        });

        let depfile = matches.opt_str("dep-file").map(PathBuf::from);

        Arguments {
            input: input,
            output: output,
            depfile: depfile,
        }
    }
}
