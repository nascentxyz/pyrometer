// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

interface B {
    function foo(uint bar) external pure returns (uint8);

    function baz() external returns (uint);
}

contract A {
    B public b;

    constructor(B _b) {
        b = _b;
    }

    function _setB(B _b) internal {
        b.baz();
        b = _b;
    }
}
