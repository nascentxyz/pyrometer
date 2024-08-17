// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract PlusPlus {
    mapping(uint => uint) map;
    uint public index;
    uint public a;

    function foo() public {
        require(index == 0);
        "pyro::variable::index::range::[0, 0]";
        //   2              3                0                1
        //   v              v                v                v
        (map[++index], map[++index]) = (bar(++index), bar(++index));
        "pyro::variable::index::range::[4, 4]";
        uint x = map[3];
        uint y = map[4];
        x;
        y;
        "pyro::variable::x::range::[1, 1]";
        "pyro::variable::y::range::[2, 2]";
    }

    function bar(uint x) public pure returns (uint) {
        return x;
    }
}
