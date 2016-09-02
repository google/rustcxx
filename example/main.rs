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

// Sample program using rustcxx to mix Rust and C++

#![feature(plugin, libc)]
#![plugin(rustcxx_plugin)]

extern crate libc;

// The contents of cxx_inline! are copied into the C++ source.
cxx_inline! {
    #include <stdint.h>
    #include <iostream>

    class Adder {
        public:
            uint32_t add(uint32_t x, uint32_t y);
    };
}

// Opaque type used to manipulate an Adder from rust
// Can only be used through a pointer.
enum Adder {}

pub fn main() {
    unsafe {
        // cxx! is used to include C++ in a rust function.
        // The C++ snippet is wrapped in a function and compiled seperately.
        // The macro is replaced by a call to the function.
        cxx![{
            std::cout << "Hello !" << std::endl;
        }];

        // cxx! can be used where an expression is expected.
        let x = cxx![() -> u32 {
            int value;
            std::cout << "Pick a number" << std::endl << "> ";
            std::cin >> value;
            value
        }];

        // cxx! can also capture variables from the Rust context.
        cxx![(x: u32) {
            std::cout << "You chose " << x << std::endl;
        }];

        // Pointers work in the expected fashion
        let mut y = 0u32;
        cxx![(y: *mut u32 = &mut y) {
            std::cout << "Pick a second one " << std::endl << "> ";
            std::cin >> *y;
        }];

        // Can use cxx! to allocate a C++ object.
        let adder = cxx![() -> *mut Adder { new Adder }];

        // And invoke methods on it.
        let sum = cxx![(adder: *mut Adder, x: u32, y: u32) -> u32 {
            adder->add(x, y)
        }];

        // Finally, we use cxx! again to clean up.
        cxx![(adder: *mut Adder) {
            delete adder;
        }];

        println!("{} + {} = {}", x, y, sum);
    }
}

cxx_inline! {
    uint32_t Adder::add(uint32_t x, uint32_t y) {
        // cxx_inline! can use rust! to call back to rust
        return rust![(x: u32, y: u32) -> u32 {
            println!("Adding {} and {}", x, y);
            x + y
        }];
    }
}
