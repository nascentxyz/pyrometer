
contract StruktTester  {
    struct A {
		uint256 b;
		uint256 c;
	}

    function constructStruct() public {
		A memory b = A({b: 100, c: 100});
		require(b.b == 100);
		require(b.c == 100);
	}

}