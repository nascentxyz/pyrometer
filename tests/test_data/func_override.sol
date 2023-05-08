contract B {
	function a(uint256 x) internal virtual returns (uint256) {
		return 200;
	}
}


contract A is B {
	function a(uint256 x) internal override returns (uint256) {
		return 100;
	}

	function b() public {
		a(5);
	}
}