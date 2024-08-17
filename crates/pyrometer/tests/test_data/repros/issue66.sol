// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.19;

contract Foo {
    struct Struct {
        uint32 a;
    }

    function foo() public pure {
        Struct memory data;
        assembly {
            let x := eq(data, 0xFF)
        }
    }
}
