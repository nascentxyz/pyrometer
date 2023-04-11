contract Logical {
    function not() public {
        uint256 a = 100;
        bool s = a < 100;
        require(!s);
    }

    function cond_not(uint256 a) public {
        bool s = a < 100;
        if (!s) {
            require(s);
        }
        require(s);
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
