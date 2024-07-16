// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract PlusPlus {
    mapping(uint => uint) map;
    uint public index;
    uint public a;

    function foo() public returns (uint, uint, uint, uint, uint) {
        require(index == 0);
        (a, map[++index]) = (index, bar(++index));
        return (a, index, map[0], map[1], map[2]);
    }

    function bar(uint x) public pure returns (uint) {
        return x;
    }
}
