// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract StruktTester {
    struct A {
        uint256 b;
        uint256 c;
    }

    function constructStruct() public pure {
        A memory b = A({b: 100, c: 100});
        require(b.b == 100);
        require(b.c == 100);
    }

    function namedCallPub() public pure {
        namedCall({x: 100});
    }

    function namedCall(uint256 x) internal pure {
        require(x == 100);
    }
}
