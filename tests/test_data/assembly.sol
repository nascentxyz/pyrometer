

contract Assembly {
	uint256 a;
	// modifier Q {
	// 	a();
	// 	_;
	// 	b();
	// }
	function a() public {
		if (a < 100) {
		// 	if (a > 5) {
				b();
		// 	} else {
		// 		c();
		// 	}
		} else {
			c();
		}
	}
	function b() public {
		// if (a < 200) {
		// 	if (a > 5) {
		// 		d();
		// 	} else {
		// 		c();
		// 	}
		// } else {
			d();
		// }
	}
	function c() public {
		d();
	}
	function d() public {
		a += 100;
	}

	// function e() public Q {
	// 	uint256 x = 1;
	// }
	// function multiDisplay(uint256 x, uint256 y) public returns (uint256, uint256) {
	// 	require(x > 1);
	// 	return a(x, y);
	// }
	// function a(uint256 x, uint256 y) public returns (uint256, uint256) {
	// 	require(x > 5);
	// 	(uint256 f, uint256 g) = c(x + 1, y + 1);
	// 	(f, g) = b(x, y);
	// 	return c(x, y);
	// }
	// function b(uint256 x, uint256 y) public returns (uint256, uint256) {
	// 	// require(x > 100);
	// 	require(y < 100);
	// 	(uint256 f, uint256 g) = c(x + 1, y + 1);
	// 	return (x, y);
	// }
	// function c(uint256 q, uint256 z) public returns (uint256, uint256) {
	// 	require(q > 100);
	// 	require(q > z);
	// 	return (q + 1, z + 1);
	// }
	// uint256[] b;
	// function hasInline(uint256 a, uint256 b) public returns (uint256, uint256){
	// 	assembly {
	// 		a := add(100, a)
	// 		a := sub(a, 10)
	// 		a := div(a, 2)
	// 		a := mul(a, 2)
	// 		if lt(b, 200) {
	// 			b := 100
	// 		}

	// 		// let c := 0x200
	// 		// let d := true
	// 	}

	// 	if (b < 200) {
	// 		require(b == 100);
	// 	}
	// 	return (a, b);
	// }

	// function varDecl(uint256 a) public {
	// 	assembly {
	// 		function multiReturn() -> first, second {
	// 			return 100, 200
	// 		}

	// 		let b := 200
	// 		let c := 0x200
	// 		let d := true
	// 		let e, f := multiReturn()
	// 	}
	// }
}