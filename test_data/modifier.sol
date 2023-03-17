contract Modifier {
	uint256 a;
	modifier Noop() {
		_;
	}

	modifier RequireBefore() {
		require(a == 0);
		_;
	}

	modifier RequireAfter() {
		_;
		require(a == 1);
	}

	modifier Input(uint256 c) {
		require(c == 100);
		a += 1;
		_;
		
	}

	function noop() public Noop {
		a = 100;
	}

	function requireBefore() public RequireBefore {
		a += 1;
	}

	function requireAfter() public RequireAfter {
		a += 1;
	}

	function input(uint256 b) public Input(b) {
		uint256 a = b;
	}

	function input(uint256 b, uint256 c) public Input(b) Input(c) {
		uint256 k = b;
	}

	function internalMod(uint256 b) internal Input(b) {
		uint256 k = b;
	}

	function internalModPub(uint256 b) public {
		internalMod(b);
	}

    function addOne(uint256 x) internal returns (uint256) {
        return x + 1;
    }

    function inputFunc(uint256 x) Input(addOne(x)) internal returns (uint256) {
        return x;
    }

    function inputFuncConst(uint256 x) Input(addOne(99)) internal returns (uint256){
        require(a == 1);
        return x;
    }

    function inputFunc_conc() internal returns (uint256) {
        uint256 y = inputFunc(99);
        require(a == 1);
        return y;
    }
}