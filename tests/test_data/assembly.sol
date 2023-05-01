

contract Assembly {
	function multiDisplay(uint256 x, uint256 y) public returns (uint256, uint256) {
		require(x > 1);
		return a(x, y);
	}
	function a(uint256 x, uint256 y) public returns (uint256, uint256) {
		require(x > 5);
		(uint256 f, uint256 g) = c(x, y);
		(f, g) = b(x, y);
		return c(x, y);
	}
	function b(uint256 x, uint256 y) public returns (uint256, uint256) {
		require(x > 100);
		require(y < 100);
		(x, y) = c(x + 1, y + 1);
		return (x, y);
	}
	function c(uint256 x, uint256 y) public returns (uint256, uint256) {
		require(x > 10);
		require(x > y);
		return (x + 1, y + 1);
	}
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