// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract PlusPlus {
    mapping(uint => uint) map;
    uint public index;
    uint public a;

    function foo() public {
        require(index == 0);
        //   2              3                0                1
        //   v              v                v                v
        (map[++index], map[++index]) = (bar(++index), bar(++index));
        uint x = map[3];
        uint y = map[4];
        "pyro::variable::x::range::[1, 1]";
        "pyro::variable::y::range::[2, 2]";
    }

    function bar(uint x) public pure returns (uint) {
        return x;
    }
}
