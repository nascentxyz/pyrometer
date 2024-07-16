// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;
enum MyEnum {
    A,
    B,
    C
}

contract Logical {
    function enumCmp() public pure returns (bool) {
        return MyEnum.A > MyEnum.B;
    }

    function yulCmp() internal pure {
        uint x;
        uint y;
        assembly {
            x := gt(2, 3)
            y := eq(2, 3)
        }
    }

    function yulComplicatedCmp(address a) internal {
        bool success;
        /// @solidity memory-safe-assembly
        assembly {
            success := and(eq(a, 0), call(gas(), a, 4, 5, 6, 7, 8)) //error
        }
        require(success);
    }

    function or(address a) internal virtual {
        assembly {
            {
                if iszero(or(a, 0x0)) {

                }
            }
        }
    }

    function eq(address a) public pure {
        assembly {
            if eq(0x0, a) {

            }
        }
    }

    function not() public pure {
        uint256 a = 100;
        bool s = a < 100;
        require(!s);
    }

    function cond_not(uint256 a) public pure {
        bool s = a < 100;
        if (!s) {
            require(!s);
        } else {
            require(s);
        }
    }

    function cond_and(bool a, bool b) public pure {
        if (a && b) {
            require(a);
            require(b);
            bool f = a && b;
            require(f);
        } else {
            require(!a || !b);
        }
    }

    function cond_if(uint256 a) public pure {
        bool s = a < 100;
        if (s) {
            require(s);
        } else {
            require(!s);
        }
    }

    function and() public pure {
        uint256 a = 100;
        uint256 b = 1000;
        bool s = a > 99;
        bool t = b > 999;
        require(s && t);
    }

    function or_basic() public pure {
        uint256 a = 100;
        uint256 b = 1000;
        bool s = a > 99;
        bool t = b < 1000;
        require(s || t);
    }

    function or() public pure {
        uint256 a = 100;
        uint256 b = 1000;
        bool s = a > 99 || b < 1000;
        require(s);
    }

    function or_inline() public pure {
        uint256 a = 100;
        uint256 b = 1000;
        require(a > 99 || b < 1000);
    }
}
