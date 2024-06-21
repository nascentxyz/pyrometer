contract T {
	function a(uint256 x) public returns (uint256, uint256) {
		uint256 y = x;
		require(x != 0);
		// `y` should have the bounds `[2, 2**256 - 2]` after this statement if this challenge is solved
		y += 1;
		return (x, y);
	}
}