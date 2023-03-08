contract Math {
	function div(uint256 x, uint256 y) public returns (uint256) {
		return x / y;
	}

	function mul(uint256 x, uint256 y) public returns (uint256) {
		return x * y;
	}

	function add(uint256 x, uint256 y) public returns (uint256) {
		return x + y;
	}

	function sub(uint256 x, uint256 y) public returns (uint256) {
		return x - y;
	}

	function rmod(uint256 x, uint256 y) public returns (uint256) {
		return x % y;
	}

	function rexp(uint256 x, uint256 y) public returns (uint256) {
		return x ** y;
	}

	function int_div(int256 x, int256 y) public returns (int256) {
		return x / y;
	}

	function int_mul(int256 x, int256 y) public returns (int256) {
		return x * y;
	}

	function int_add(int256 x, int256 y) public returns (int256) {
		return x + y;
	}

	function int_sub(int256 x, int256 y) public returns (int256) {
		return x - y;
	}

	function int_rmod(int256 x, int256 y) public returns (int256) {
		return x % y;
	}

	function int_rexp(int256 x, int256 y) public returns (int256) {
		return x ** y;
	}
}