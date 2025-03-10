pragma solidity ^0.8.0;

contract CondOp {

    function if_both_possible(uint x) public returns (uint) {
        if (x > 100) {
            return 1;
        } else {
            return 2;
        }
    }

    function if_first_possible() public returns (uint) {
        uint x = 101;
        if (x > 100) {
            return 1;
        } else {
            return 2;
        }
    }

    function if_second_possible() public returns (uint) {
        uint x = 99;
        if (x > 100) {
            return 1;
        } else {
            return 2;
        }
    }

    function if_neither_possible(uint x) public returns (uint) {
        if (x > 100) {
            require(x < 100); // not possible
            return 1;
        } else {
            require(x > 100); // not possible
            return 2;
        }
        return 0;
    }


    function ternaryParam(uint x) public returns (uint) {
        uint y = x > 2 ? 1 : 2;
        return y;
    }

    function ternaryLiteral() public returns (uint) {
        uint y = 1 > 2 ? 1 : 2;
        "pyro::variable::y::range::[2,2]";
        return y;
    }
}