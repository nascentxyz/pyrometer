

contract Assembly {
	uint256[] b;
	function hasInline(uint256 a, uint256 b) public returns (uint256, uint256){
		assembly {
			a := add(100, a)
			a := sub(a, 10)
			a := div(a, 2)
			a := mul(a, 2)
			if lt(b, 200) {
				b := 100
			}

			// let c := 0x200
			// let d := true
		}

		if (b < 200) {
			require(b == 100);
		}
		return (a, b);
	}

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