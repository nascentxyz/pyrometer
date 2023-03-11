contract Bitwise {
	function shl(uint256 x, uint256 y) public returns (uint256) {
		return x << y;
	}

	function int_shl(int256 x, uint256 y) public returns (int256) {
		return x << y;
	}

	function shr(uint256 x, uint256 y) public returns (uint256) {
		return x >> y;
	}

	function int_shr(int256 x, uint256 y) public returns (int256) {
		return x >> y;
	}

	function int_shr(int256 x, uint256 y, uint256 z) public returns (int256) {
		return x >> y;
	}

	function shl_conc() public returns (uint256) {
		return shl(100, 1);
	}

	function int_shl_conc() public returns (int256) {
		return int_shl(-100, 1);
	}

	function shr_conc() public returns (uint256) {
		return shr(100, 1);
	}

	function int_shr_conc() public returns (int256) {
		return int_shr(-100, 1);
	}
}