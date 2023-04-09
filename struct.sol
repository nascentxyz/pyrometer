contract StruktTester {
	struct A {
		uint256 b;
		uint256 c;
	}

	function constructStruct() public {
		A({b: 100, c: 100});
	}

	function namedCallPub() public {
		namedCall({x: 100});
	}

	function namedCall(uint256 x) internal {
		
	}
}