contract A {
	uint256 storageVariable;
	// uint256 public publicStorageVariable;
	// uint256 constant const;

	function funcA() public returns (uint256 ret) {
		ret = funcB(storageVariable);
	}

	function funcB(uint256 innerInput0) internal returns (uint256 ret) {
		ret = innerInput0 + 10;
	}
}