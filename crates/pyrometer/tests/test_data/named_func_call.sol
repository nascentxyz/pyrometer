// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract B {
    constructor(uint c) payable {
        require(msg.value == 1);
        require(c == 2);
    }

    function t(uint a, uint b) public payable {
        require(msg.value == 2);
        require(a == 5);
        require(b == 4);
    }
}

contract StruktTester {
    struct A {
        uint256 b;
        uint256 c;
    }

    uint x;

    function constructB() public {
        require(x == 0);
        new B{value: ++x}({c: ++x});
    }

    function t() public {
        require(x == 0);
        B(address(uint160(++x))).t{value: ++x, gas: ++x}({a: ++x, b: ++x});
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
