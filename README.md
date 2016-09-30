# rustcxx: Using C++ from Rust made easy
rustcxx is a tool allowing C++ to be used from a Rust project easily.
It works by allowing snippets of C++ to be included within a Rust function,
and vice-versa.

## Example
```rust
#![plugin(rustcxx_plugin)]

cxx_inline! {
    #include <stdint.h>
    uint32_t square_it(uint32_t x) {
        return rust![(x: u32) -> u32 {
            println!("Rust: Squaring {}", x);
            x * x
        }];
    }
}

let x: u32 = 5;
let square = unsafe { cxx![(x: u32) -> u32 {
    std::cout << "C++: Squaring " << x << std::endl;
    square_it(x)
}] };
```

See [the provided example](example/main.rs) for more details.

## Usage
rustcxx requires a nightly version of the Rust compiler.

Add to your `Cargo.toml`:
```toml
[package]
build = "build.rs"

[dependencies.rustcxx_plugin]
git = "https://github.com/google/rustcxx"
branch = "unstable"

[build-dependencies.rustcxx_codegen]
git = "https://github.com/google/rustcxx"
branch = "unstable"
```

and create a `build.rs` file containing the following:

```rust
extern crate rustcxx_codegen;

fn main() {
    rustcxx_codegen::build("src/main.rs");
}
```

## Authors

The main author is Paul Liétar.

## Contributions

We gladly accept contributions via GitHub pull requests, as long as the author
has signed the Google Contributor License. Please see
[CONTRIBUTING.md](CONTRIBUTING.md) for more details.

### Disclaimer

This is not an official Google product (experimental or otherwise), it
is just code that happens to be owned by Google.
