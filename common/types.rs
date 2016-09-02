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

use std::borrow::Cow;
use syntax::ast;
use syntax::errors::Handler;
use syntax::parse::PResult;
use syntax::print::pprust::ty_to_string;

/// Get the C++ representation of a Rust type.
///
/// Integer types (`u8`, `u16`, ...) and `libc` types (`libc::c_char`, `libc::c_float`, ...)
/// are translated into their C++ equivalents. Unknown type names are used as is.
///
/// Rust raw pointers are converted to the corresponding C++ pointer.
///
/// Everything else (tuple, reference, ...) causes an error.
pub fn convert_ty_to_cxx<'a>(handler: &'a Handler, ty: &ast::Ty)
                             -> PResult<'a, Cow<'static, str>> {

    use syntax::ast::TyKind::*;
    match ty.node {
        Ptr(ref mut_ty) => convert_ptr(handler, mut_ty),
        Path(None, ref path) => convert_path(handler, path),
        _ => {
            let msg = format!("Unsupported type `{}` in cxx! macro", ty_to_string(&ty));
            Err(handler.struct_span_err(ty.span, &msg))
        }
    }
}

fn convert_ptr<'a>(handler: &'a Handler, mut_ty: &ast::MutTy)
                   -> PResult<'a, Cow<'static, str>> {

    use syntax::ast::Mutability::*;

    let inner_ty = try!(convert_ty_to_cxx(handler, &mut_ty.ty));
    let qualifier = match mut_ty.mutbl {
        Mutable => "",
        Immutable => " const",
    };

    Ok(Cow::from(format!("{}{} *", inner_ty, qualifier)))
}

fn convert_path<'a>(handler: &'a Handler, path: &ast::Path)
                    -> PResult<'a, Cow<'static, str>> {

    match path.segments.split_first() {
        None => unreachable!("path must have at least one segment"),
        Some((segment, &[])) => {
            let name : &str = &segment.identifier.name.as_str();
            Ok(match name {
                "u64"   => Cow::from("uint64_t"),
                "u32"   => Cow::from("uint32_t"),
                "u16"   => Cow::from("uint16_t"),
                "u8"    => Cow::from("uint8_t"),
                "i64"   => Cow::from("int64_t"),
                "i32"   => Cow::from("int32_t"),
                "i16"   => Cow::from("int16_t"),
                "i8"    => Cow::from("int8_t"),
                "usize" => Cow::from("size_t"),
                "isize" => Cow::from("ssize_t"),
                _ => Cow::from(name.to_owned()),
            })
        }

        Some((module, rest)) if module.identifier.name.as_str() == "libc" && rest.len() == 1 => {
            let name : &str = &rest[0].identifier.name.as_str();
            Ok(match name {
                "c_void"      => Cow::from("void"),
                "c_char"      => Cow::from("char"),
                "c_double"    => Cow::from("double"),
                "c_float"     => Cow::from("float"),
                "c_int"       => Cow::from("int"),
                "c_long"      => Cow::from("long"),
                "c_longlong"  => Cow::from("long long"),
                "c_schar"     => Cow::from("signed char"),
                "c_short"     => Cow::from("short"),
                "c_uchar"     => Cow::from("unsigned char"),
                "c_uint"      => Cow::from("unsigned int"),
                "c_ulong"     => Cow::from("unsigned long"),
                "c_ulonglong" => Cow::from("unsigned long long"),
                "c_ushort"    => Cow::from("unsigned short"),
                _ => Cow::from(name.to_owned()),
            })
        }

        _ => {
            let msg = format!("Unsupported path `{}` in cxx! macro", path);
            Err(handler.struct_span_err(path.span, &msg))
        }
    }
}
