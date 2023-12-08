contract StruktTester {
	struct A {
		uint256 b;
		uint256 c;
	}

	function constructStruct() public {
		A memory b = A({b: 100, c: 100});
		require(b.b == 100);
		require(b.c == 100);
	}

	function namedCallPub() public {
		namedCall({x: 100});
	}

	function namedCall(uint256 x) internal {
		require(x == 100);
	}
}