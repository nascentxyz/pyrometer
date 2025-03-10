// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

function x(uint256 x1) pure returns (uint256) {
    return x1 + 20;
}

library MyLib {
    function y(uint256 x4) internal pure returns (uint256) {
        return x4 + 10;
    }
}

library MyOtherLib {
    function z(uint256 x3) internal pure returns (uint256) {
        return x3 + 15;
    }
}

contract C {
    struct B {
        uint256 c;
    }

    function a() public pure returns (uint256) {
        return 100;
    }
}

library MyOtherOtherLib {
    function w(uint256 x2) internal pure returns (uint256) {
        return x2 + 30;
    }

    struct A {
        uint256 b;
    }
}

using MyLib for uint256;

contract UsingMyLib {
    function libStruct() public pure {
        MyOtherOtherLib.A memory s;
        s.b = 100;
    }

    function conStruct() public pure {
        uint256 val = C(address(1)).a();
        require(val == 100);
        C.B memory s;
        s.c = 100;
    }

    using MyOtherLib for uint256;

    using {x, MyOtherOtherLib.w} for uint256;

    function a(uint256 y) public pure returns (uint256) {
        return y.z();
    }

    function a_conc() public pure returns (uint256) {
        uint256 y = 100;
        uint256 ret = y.z();
        require(ret == 115);
        return ret;
    }

    function b(uint256 y) public pure returns (uint256) {
        return y.y();
    }

    function b_conc() public pure returns (uint256) {
        uint256 y = 100;
        uint256 ret = y.y();
        require(ret == 110);
        return ret;
    }

    function c(uint256 y) public pure returns (uint256) {
        return y.w();
    }

    function c_conc() public pure returns (uint256) {
        uint256 y = 100;
        uint256 ret = y.w();
        require(ret == 130);
        return ret;
    }
}

library lib {
    function foo(address a) internal {}
}

contract More {
    using lib for address;

    function bar(address a) public {
        a.foo();
    }
}
