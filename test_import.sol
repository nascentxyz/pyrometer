import { Storage, S } from "../test.sol";

contract A is Storage, S {
	function c() public returns (uint256[] memory) {
		uint256[] memory x = new uint256[](10);
		// x[0] = 1;
		// x[1] = 2;
		// x[2] = 3;
		// x[3] = 4;
		// x[4] = 5;
		// x[5] = 6;
		// x[6] = 7;
		// x[7] = 8;
		// x[8] = 9;
		// x[9] = 10;
		return b6(x);
	}
}