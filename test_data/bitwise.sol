contract Bitwise {
	function shl(uint256 x, uint256 y) public returns (uint256) {
		return x << y;
	}

	function int_shl(int256 x, uint256 y) public returns (int256) {
		return x << y;
	}

	function shr(uint256 x, uint256 y) public returns (uint256) {
		return x >> y;
	}

	function int_shr(int256 x, uint256 y) public returns (int256) {
		return x >> y;
	}

	function int_shr(int256 x, uint256 y, uint256 z) public returns (int256) {
		return x >> y;
	}

	function shl_conc() public returns (uint256) {
		uint256 a1 = shl(100, 1);
		require(a1 == 200);
		uint256 a2 = shl(100, 2);
		require(a2 == 400);
		uint256 a3 = shl(100, 4);
		require(a3 == 1600);
		uint256 a4 = shl(100, 8);
		require(a4 == 25600);
		uint256 a5 = shl(1000000000, 8);
		require(a5 == 256000000000);
		uint256 a6 = shl(1000000000, 16);
		require(a6 == 65536000000000);
		uint256 a7 = shl(10000000000, 32);
		require(a7 == 42949672960000000000);
		uint256 a8 = shl(100000000000000000000, 64);
		require(a8 == 1844674407370955161600000000000000000000);
		uint256 a9 = shl(100000000000000000000000000000000000, 128);
		require(a9 == 34028236692093846346337460743176821145600000000000000000000000000000000000);
		uint256 a10 = shl(1, 255);
		require(a10 == 57896044618658097711785492504343953926634992332820282019728792003956564819968);
	}

	function int_shl_conc() public returns (int256) {
		int256 a1 = int_shl(100, 1);
		require(a1 == 200);
		int256 a2 = int_shl(100, 2);
		require(a2 == 400);
		int256 a3 = int_shl(100, 4);
		require(a3 == 1600);
		int256 a4 = int_shl(100, 8);
		require(a4 == 25600);
		int256 a5 = int_shl(1000000000, 8);
		require(a5 == 256000000000);
		int256 a6 = int_shl(1000000000, 16);
		require(a6 == 65536000000000);
		int256 a7 = int_shl(10000000000, 32);
		require(a7 == 42949672960000000000);
		int256 a8 = int_shl(100000000000000000000, 64);
		require(a8 == 1844674407370955161600000000000000000000);
		int256 a9 = int_shl(100000000000000000000000000000000000, 128);
		require(a9 == 34028236692093846346337460743176821145600000000000000000000000000000000000);
		int256 a10 = int_shl(1, 255);
		require(a10 == 57896044618658097711785492504343953926634992332820282019728792003956564819968);

		int256 a11 = int_shl(-100, 1);
		require(a11 == -200);
		int256 a12 = int_shl(-100, 2);
		require(a12 == -400);
		int256 a13 = int_shl(-100, 4);
		require(a13 == -1600);
		int256 a14 = int_shl(-100, 8);
		require(a14 == -25600);
		int256 a15 = int_shl(-1000000000, 8);
		require(a15 == -256000000000);
		int256 a16 = int_shl(-1000000000, 16);
		require(a16 == -65536000000000);
		int256 a17 = int_shl(-10000000000, 32);
		require(a17 == -42949672960000000000);
		int256 a18 = int_shl(-100000000000000000000, 64);
		require(a18 == -1844674407370955161600000000000000000000);
		int256 a19 = int_shl(-100000000000000000000000000000000000, 128);
		require(a19 == -34028236692093846346337460743176821145600000000000000000000000000000000000);
		int256 a20 = int_shl(-1, 255);
		require(a20 == -57896044618658097711785492504343953926634992332820282019728792003956564819968);
		int256 a21 = int_shl(-1, 256);
		require(a21 == 0);
	}

	function shr_conc() public {
		uint256 a1 = shr(100, 1);
		require(a1 == 50);
		uint256 a2 = shr(100, 2);
		require(a2 == 25);
		uint256 a3 = shr(100, 4);
		require(a3 == 6);
		uint256 a4 = shr(100, 8);
		require(a4 == 0);
		uint256 a5 = shr(1000000000, 8);
		require(a5 == 3906250);
		uint256 a6 = shr(1000000000, 16);
		require(a6 == 15258);
		uint256 a7 = shr(10000000000, 32);
		require(a7 == 2);
		uint256 a8 = shr(100000000000000000000, 64);
		require(a8 == 5);
		uint256 a9 = shr(1000000000000000000000000000000000000000, 128);
		require(a9 == 2);
		uint256 a10 = shr(1000000000000000000000000000000000000000000000000000000000000000000000000000, 248);
		require(a10 == 2);
	}

	function int_shr_conc() public returns (int256) {
		int256 a1 = int_shr(100, 1);
		require(a1 == 50);
		int256 a2 = int_shr(100, 2);
		require(a2 == 25);
		int256 a3 = int_shr(100, 4);
		require(a3 == 6);
		int256 a4 = int_shr(100, 8);
		require(a4 == 0);
		int256 a5 = int_shr(1000000000, 8);
		require(a5 == 3906250);
		int256 a6 = int_shr(1000000000, 16);
		require(a6 == 15258);
		int256 a7 = int_shr(10000000000, 32);
		require(a7 == 2);
		int256 a8 = int_shr(100000000000000000000, 64);
		require(a8 == 5);
		int256 a9 = int_shr(1000000000000000000000000000000000000000, 128);
		require(a9 == 2);
		int256 a10 = int_shr(1000000000000000000000000000000000000000000000000000000000000000000000000000, 248);
		require(a10 == 2);

		int256 a11 = int_shr(-100, 1);
		require(a11 == -50);
		int256 a12 = int_shr(-100, 2);
		require(a12 == -25);
		int256 a13 = int_shr(-100, 4);
		require(a13 == -6);
		int256 a14 = int_shr(-100, 8);
		require(a14 == -1);
		int256 a15 = int_shr(-1000000000, 8);
		require(a15 == -3906250);
		int256 a16 = int_shr(-1000000000, 16);
		require(a16 == -15258);
		int256 a17 = int_shr(-10000000000, 32);
		require(a17 == -2);
		int256 a18 = int_shr(-100000000000000000000, 64);
		require(a18 == -5);
		int256 a19 = int_shr(-1000000000000000000000000000000000000000, 128);
		require(a19 == -2);
		int256 a20 = int_shr(-1000000000000000000000000000000000000000000000000000000000000000000000000000, 248);
		require(a20 == -2);
	}
}