

library MyLib {
	function y(uint256 x) internal returns (uint256) {
		return x + 10;
	}
}

library MyOtherLib {
	function z(uint256 x) internal returns (uint256) {
		return x + 10;
	}
}


contract UsingMyLib {
	using {MyLib, MyOtherLib} for uint256;

	function b(uint256 y) public returns (uint256) {
		return y.y();
	}

	function conc() public returns (uint256) {
		uint256 y = 100;
		return y.y();
	}
}