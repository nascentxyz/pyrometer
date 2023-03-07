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
}