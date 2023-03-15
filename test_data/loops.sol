contract For {
	function const_loop() public {
		uint256 x;
		for (uint256 i; i < 10; i++) {
			x += 1;
		}

		require(x == 10);
		return x;
	}

	function while_loop(uint256 x) public {
		while (x > 10) {
			x -= 1;
		}

		require(x == 10);
		return x;
	}
}