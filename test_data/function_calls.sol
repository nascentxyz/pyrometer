contract InternalFuncCalls {
	address _owner;

	// modifier onlyOwner {
	// 	require(msg.sender == _owner);
	// 	_;
	// }

	function transferOwnership(address newOwner) public virtual  {
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
}

contract ExternalFuncCalls {
	function externalCall(uint256 x) public {
		B(address(100)).addToA(x);
	}

	function externalCall_conc() public {
		B(address(100)).addToA(100);

		uint256 ba = B(address(100)).a();
	}
}
