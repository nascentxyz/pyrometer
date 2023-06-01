contract InternalFuncCalls {
    address _owner;

    function transferOwnership(address newOwner) public virtual {
        innerRequire(newOwner);
        _transferOwnership(newOwner);
    }

    function innerRequire(address newOwner) public virtual {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
    }

    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
    }
}

contract B {
    uint256 public a;

    function addToA(uint256 x) public {
        a += x;
    }

    constructor(uint256 x) {
        a = x;
    }
}

contract ExternalFuncCalls {
    function externalCall(uint256 x) public {
        B(address(100)).addToA(x);
    }

    function externalCall_conc() public {
        B(address(100)).addToA(100);

        uint256 ba = B(address(100)).a();
    }

    function multiReturn() public returns (uint256, uint256, uint256, uint256) {
        return (1, 2, 3, 4);
    }

    function partialReturn() public {
        (uint256 w, , uint256 y, ) = multiReturn();
        require(w == 1);
        require(y == 3);
        (uint256 w1, uint256 x1, uint256 y1, ) = multiReturn();
        require(w1 == 1);
        require(y1 == 3);
        (, uint256 x2, , uint256 z) = multiReturn();
        require(x2 == 2);
        require(z == 4);
        (, uint256 x3, uint256 y2, uint256 z2) = multiReturn();
        require(x3 == 2);
        require(y2 == 3);
        require(z2 == 4);
    }
}

contract K {
    struct L {
        uint b;
        uint c;
    }

    function foo() internal {
        L memory l = L(2, 3);
        require(l.b == 2);
        require(l.c == 3);
    }
}


contract Disambiguation {
    function foo(address from, address to, uint256 id) public {
        foo(from, to, id, 0);
    }

    function foo(address from, address to, uint256 id, uint num) internal {}

    function foo(address by, address from, address to, uint256 id) internal {}
}
