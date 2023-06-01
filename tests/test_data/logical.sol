enum MyEnum {
    A,
    B,
    C
}

contract Logical {
    function enumCmp() public returns (bool) {
        return MyEnum.A > MyEnum.B;
    }


    function yulCmp() internal {
        uint x;
        uint y;
        assembly {
            x := gt(2,3)
            y := eq(2,3)
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
                if iszero(or(a, 0x0)) {}
            }
        }
    }

    function eq(address a) public {
        assembly {
            if eq(0x0, a) {}
        }
    }

    
    function not() public {
        uint256 a = 100;
        bool s = a < 100;
        require(!s);
    }

    function cond_not(uint256 a) public {
        bool s = a < 100;
        if (!s) {
            require(!s);
        } else {
            require(s);    
        }
    }

    function cond_and(bool a, bool b) public {
        if (a && b) {
            require(a);
            require(b);
            bool f = a && b;
            require(f);
        } else {
            require(!a || !b);
        }
    }

    function cond_if(uint256 a) public {
        bool s = a < 100;
        if (s) {
            require(s);
        } else {
            require(!s);    
        }
    }

    function and() public {
        uint256 a = 100;
        uint256 b = 1000;
        bool s = a > 99;
        bool t = b > 999;
        require(s && t);
    }

    function or_basic() public {
        uint256 a = 100;
        uint256 b = 1000;
        bool s = a > 99;
        bool t = b < 1000;
        require(s || t);
    }

    function or() public {
        uint256 a = 100;
        uint256 b = 1000;
        bool s = a > 99 || b < 1000;
        require(s);
    }

    function or_inline() public {
        uint256 a = 100;
        uint256 b = 1000;
        require(a > 99 || b < 1000);
    }
}
