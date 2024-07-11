contract C {}

contract B is C {
	function a(uint256 x) internal virtual returns (uint256) {
		return 200;
	}
}


contract A is B, C {
	function a(uint256 x) internal override returns (uint256) {
		return x + 5;
	}

	function b() public returns (uint256) {
		uint256 ret = a(5);
		require(ret == 10);
		ret = super.a(5);
		require(ret == 200);
		return ret;
	}
}
