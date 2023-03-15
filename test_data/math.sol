contract Div {
	function div(uint256 x, uint256 y) public returns (uint256) {
		return x / y;
	}

	function int_div(int256 x, int256 y) public returns (int256) {
		return x / y;
	}

	function div_conc() public returns (uint256) {
		uint256 a1 = div(100, 1);
		require(a1 == 100);
		uint256 a2 = div(100, 2);
		require(a2 == 50);
		uint256 a3 = div(100, 4);
		require(a3 == 25);
		uint256 a4 = div(100, 8);
		require(a4 == 12);
		uint256 a5 = div(1000000000, 8);
		require(a5 == 125000000);
		uint256 a6 = div(1000000000, 16);
		require(a6 == 62500000);
		uint256 a7 = div(10000000000, 32);
		require(a7 == 312500000);
		uint256 a8 = div(100000000000000000000, 64);
		require(a8 == 1562500000000000000);
		uint256 a9 = div(100000000000000000000000000000000000, 128);
		require(a9 == 781250000000000000000000000000000);
		uint256 a10 = div(1, 255);
		require(a10 == 0);
	}

	function int_div_conc() public {
		int256 a1 = int_div(100, 1);
		require(a1 == 100);
		int256 a2 = int_div(100, 2);
		require(a2 == 50);
		int256 a3 = int_div(100, 4);
		require(a3 == 25);
		int256 a4 = int_div(100, 8);
		require(a4 == 12);
		int256 a5 = int_div(1000000000, 8);
		require(a5 == 125000000);
		int256 a6 = int_div(1000000000, 16);
		require(a6 == 62500000);
		int256 a7 = int_div(10000000000, 32);
		require(a7 == 312500000);
		int256 a8 = int_div(100000000000000000000, 64);
		require(a8 == 1562500000000000000);
		int256 a9 = int_div(100000000000000000000000000000000000, 128);
		require(a9 == 781250000000000000000000000000000);
		int256 a10 = int_div(1, 255);
		require(a10 == 0);

		int256 a11 = int_div(-100, 1);
		require(a11 == -100);
		int256 a12 = int_div(-100, 2);
		require(a12 == -50);
		int256 a13 = int_div(-100, 4);
		require(a13 == -25);
		int256 a14 = int_div(-100, 8);
		require(a14 == -12);
		int256 a15 = int_div(-1000000000, 8);
		require(a15 == -125000000);
		int256 a16 = int_div(-1000000000, 16);
		require(a16 == -62500000);
		int256 a17 = int_div(-10000000000, 32);
		require(a17 == -312500000);
		int256 a18 = int_div(-100000000000000000000, 64);
		require(a18 == -1562500000000000000);
		int256 a19 = int_div(-100000000000000000000000000000000000, 128);
		require(a19 == -781250000000000000000000000000000);
		int256 a20 = int_div(-1, 255);
		require(a20 == 0);

		int256 a21 = int_div(-100, -1);
		require(a21 == 100);
		int256 a22 = int_div(-100, -2);
		require(a22 == 50);
		int256 a23 = int_div(-100, -4);
		require(a23 == 25);
		int256 a24 = int_div(-100, -8);
		require(a24 == 12);
		int256 a25 = int_div(-1000000000, -8);
		require(a25 == 125000000);
		int256 a26 = int_div(-1000000000, -16);
		require(a26 == 62500000);
		int256 a27 = int_div(-10000000000, -32);
		require(a27 == 312500000);
		int256 a28 = int_div(-100000000000000000000, -64);
		require(a28 == 1562500000000000000);
		int256 a29 = int_div(-100000000000000000000000000000000000, -128);
		require(a29 == 781250000000000000000000000000000);
		int256 a30 = int_div(-1, -255);
		require(a30 == 0);

		int256 a31 = int_div(100, -1);
		require(a31 == -100);
		int256 a32 = int_div(100, -2);
		require(a32 == -50);
		int256 a33 = int_div(100, -4);
		require(a33 == -25);
		int256 a34 = int_div(100, -8);
		require(a34 == -12);
		int256 a35 = int_div(1000000000, -8);
		require(a35 == -125000000);
		int256 a36 = int_div(1000000000, -16);
		require(a36 == -62500000);
		int256 a37 = int_div(10000000000, -32);
		require(a37 == -312500000);
		int256 a38 = int_div(100000000000000000000, -64);
		require(a38 == -1562500000000000000);
		int256 a39 = int_div(100000000000000000000000000000000000, -128);
		require(a39 == -781250000000000000000000000000000);
		int256 a40 = int_div(1, -255);
		require(a40 == 0);
	}
}

contract Mul {
	function mul(uint256 x, uint256 y) public returns (uint256) {
		return x * y;
	}

	function int_mul(int256 x, int256 y) public returns (int256) {
		return x * y;
	}

	function mul_conc() public returns (uint256) {
		uint256 a1 = mul(100, 1);
		require(a1 == 100);
		uint256 a2 = mul(100, 2);
		require(a2 == 200);
		uint256 a3 = mul(100, 4);
		require(a3 == 400);
		uint256 a4 = mul(100, 8);
		require(a4 == 800);
		uint256 a5 = mul(1000000000, 8);
		require(a5 == 8000000000);
		uint256 a6 = mul(1000000000, 16);
		require(a6 == 16000000000);
		uint256 a7 = mul(10000000000, 32);
		require(a7 == 320000000000);
		uint256 a8 = mul(100000000000000000000, 64);
		require(a8 == 6400000000000000000000);
		uint256 a9 = mul(100000000000000000000000000000000000, 128);
		require(a9 == 12800000000000000000000000000000000000);
		uint256 a10 = mul(1, 255);
		require(a10 == 255);
	}

	function int_mul_conc() public {
		int256 a1 = int_mul(100, 1);
		require(a1 == 100);
		int256 a2 = int_mul(100, 2);
		require(a2 == 200);
		int256 a3 = int_mul(100, 4);
		require(a3 == 400);
		int256 a4 = int_mul(100, 8);
		require(a4 == 800);
		int256 a5 = int_mul(1000000000, 8);
		require(a5 == 8000000000);
		int256 a6 = int_mul(1000000000, 16);
		require(a6 == 16000000000);
		int256 a7 = int_mul(10000000000, 32);
		require(a7 == 320000000000);
		int256 a8 = int_mul(100000000000000000000, 64);
		require(a8 == 6400000000000000000000);
		int256 a9 = int_mul(100000000000000000000000000000000000, 128);
		require(a9 == 12800000000000000000000000000000000000);
		int256 a10 = int_mul(1, 255);
		require(a10 == 255);

		int256 a11 = int_mul(-100, 1);
		require(a11 == -100);
		int256 a12 = int_mul(-100, 2);
		require(a12 == -200);
		int256 a13 = int_mul(-100, 4);
		require(a13 == -400);
		int256 a14 = int_mul(-100, 8);
		require(a14 == -800);
		int256 a15 = int_mul(-1000000000, 8);
		require(a15 == -8000000000);
		int256 a16 = int_mul(-1000000000, 16);
		require(a16 == -16000000000);
		int256 a17 = int_mul(-10000000000, 32);
		require(a17 == -320000000000);
		int256 a18 = int_mul(-100000000000000000000, 64);
		require(a18 == -6400000000000000000000);
		int256 a19 = int_mul(-100000000000000000000000000000000000, 128);
		require(a19 == -12800000000000000000000000000000000000);
		int256 a20 = int_mul(-1, 255);
		require(a20 == -255);

		int256 a21 = int_mul(-100, -1);
		require(a21 == 100);
		int256 a22 = int_mul(-100, -2);
		require(a22 == 200);
		int256 a23 = int_mul(-100, -4);
		require(a23 == 400);
		int256 a24 = int_mul(-100, -8);
		require(a24 == 800);
		int256 a25 = int_mul(-1000000000, -8);
		require(a25 == 8000000000);
		int256 a26 = int_mul(-1000000000, -16);
		require(a26 == 16000000000);
		int256 a27 = int_mul(-10000000000, -32);
		require(a27 == 320000000000);
		int256 a28 = int_mul(-100000000000000000000, -64);
		require(a28 == 6400000000000000000000);
		int256 a29 = int_mul(-100000000000000000000000000000000000, -128);
		require(a29 == 12800000000000000000000000000000000000);
		int256 a30 = int_mul(-1, -255);
		require(a30 == 255);

		int256 a31 = int_mul(100, -1);
		require(a31 == -100);
		int256 a32 = int_mul(100, -2);
		require(a32 == -200);
		int256 a33 = int_mul(100, -4);
		require(a33 == -400);
		int256 a34 = int_mul(100, -8);
		require(a34 == -800);
		int256 a35 = int_mul(1000000000, -8);
		require(a35 == -8000000000);
		int256 a36 = int_mul(1000000000, -16);
		require(a36 == -16000000000);
		int256 a37 = int_mul(10000000000, -32);
		require(a37 == -320000000000);
		int256 a38 = int_mul(100000000000000000000, -64);
		require(a38 == -6400000000000000000000);
		int256 a39 = int_mul(100000000000000000000000000000000000, -128);
		require(a39 == -12800000000000000000000000000000000000);
		int256 a40 = int_mul(1, -255);
		require(a40 == -255);
	}
}

contract Add {
	function add(uint256 x, uint256 y) public returns (uint256) {
		return x + y;
	}

	function int_add(int256 x, int256 y) public returns (int256) {
		return x + y;
	}

	function add_conc() public returns (uint256) {
		uint256 a1 = add(100, 1);
		require(a1 == 101);
		uint256 a2 = add(100, 2);
		require(a2 == 102);
		uint256 a3 = add(100, 4);
		require(a3 == 104);
		uint256 a4 = add(100, 8);
		require(a4 == 108);
		uint256 a5 = add(1000000000, 8);
		require(a5 == 1000000008);
		uint256 a6 = add(1000000000, 16);
		require(a6 == 1000000016);
		uint256 a7 = add(10000000000, 32);
		require(a7 == 10000000032);
		uint256 a8 = add(100000000000000000000, 64);
		require(a8 == 100000000000000000064);
		uint256 a9 = add(100000000000000000000000000000000000, 128);
		require(a9 == 100000000000000000000000000000000128);
		uint256 a10 = add(1, 255);
		require(a10 == 256);
	}

	function int_add_conc() public {
		int256 a1 = int_add(100, 1);
		require(a1 == 101);
		int256 a2 = int_add(100, 2);
		require(a2 == 102);
		int256 a3 = int_add(100, 4);
		require(a3 == 104);
		int256 a4 = int_add(100, 8);
		require(a4 == 108);
		int256 a5 = int_add(1000000000, 8);
		require(a5 == 1000000008);
		int256 a6 = int_add(1000000000, 16);
		require(a6 == 1000000016);
		int256 a7 = int_add(10000000000, 32);
		require(a7 == 10000000032);
		int256 a8 = int_add(100000000000000000000, 64);
		require(a8 == 100000000000000000064);
		int256 a9 = int_add(100000000000000000000000000000000000, 128);
		require(a9 == 100000000000000000000000000000000128);
		int256 a10 = int_add(1, 255);
		require(a10 == 256);

		int256 a11 = int_add(-100, 1);
		require(a11 == -99);
		int256 a12 = int_add(-100, 2);
		require(a12 == -98);
		int256 a13 = int_add(-100, 4);
		require(a13 == -96);
		int256 a14 = int_add(-100, 8);
		require(a14 == -92);
		int256 a15 = int_add(-1000000000, 8);
		require(a15 == -999999992);
		int256 a16 = int_add(-1000000000, 16);
		require(a16 == -999999984);
		int256 a17 = int_add(-10000000000, 32);
		require(a17 == -9999999968);
		int256 a18 = int_add(-100000000000000000000, 64);
		require(a18 == -99999999999999999936);
		int256 a19 = int_add(-100000000000000000000000000000000000, 128);
		require(a19 == -99999999999999999999999999999999872);
		int256 a20 = int_add(-1, 255);
		require(a20 == 254);

		int256 a21 = int_add(-100, -1);
		require(a21 == -101);
		int256 a22 = int_add(-100, -2);
		require(a22 == -102);
		int256 a23 = int_add(-100, -4);
		require(a23 == -104);
		int256 a24 = int_add(-100, -8);
		require(a24 == -108);
		int256 a25 = int_add(-1000000000, -8);
		require(a25 == -1000000008);
		int256 a26 = int_add(-1000000000, -16);
		require(a26 == -1000000016);
		int256 a27 = int_add(-10000000000, -32);
		require(a27 == -10000000032);
		int256 a28 = int_add(-100000000000000000000, -64);
		require(a28 == -100000000000000000064);
		int256 a29 = int_add(-100000000000000000000000000000000000, -128);
		require(a29 == -100000000000000000000000000000000128);
		int256 a30 = int_add(-1, -255);
		require(a30 == -256);

		int256 a31 = int_add(100, -1);
		require(a31 == 99);
		int256 a32 = int_add(100, -2);
		require(a32 == 98);
		int256 a33 = int_add(100, -4);
		require(a33 == 96);
		int256 a34 = int_add(100, -8);
		require(a34 == 92);
		int256 a35 = int_add(1000000000, -8);
		require(a35 == 999999992);
		int256 a36 = int_add(1000000000, -16);
		require(a36 == 999999984);
		int256 a37 = int_add(10000000000, -32);
		require(a37 == 9999999968);
		int256 a38 = int_add(100000000000000000000, -64);
		require(a38 == 99999999999999999936);
		int256 a39 = int_add(100000000000000000000000000000000000, -128);
		require(a39 == 99999999999999999999999999999999872);
		int256 a40 = int_add(1, -255);
		require(a40 == -254);
	}
}

contract Sub {
	function sub(uint256 x, uint256 y) public returns (uint256) {
		return x - y;
	}

	function int_sub(int256 x, int256 y) public returns (int256) {
		return x - y;
	}

	function sub_conc() public returns (uint256) {
		uint256 a1 = sub(100, 1);
		require(a1 == 99);
		uint256 a2 = sub(100, 2);
		require(a2 == 98);
		uint256 a3 = sub(100, 4);
		require(a3 == 96);
		uint256 a4 = sub(100, 8);
		require(a4 == 92);
		uint256 a5 = sub(1000000000, 8);
		require(a5 == 999999992);
		uint256 a6 = sub(1000000000, 16);
		require(a6 == 999999984);
		uint256 a7 = sub(10000000000, 32);
		require(a7 == 9999999968);
		uint256 a8 = sub(100000000000000000000, 64);
		require(a8 == 99999999999999999936);
		uint256 a9 = sub(100000000000000000000000000000000000, 128);
		require(a9 == 99999999999999999999999999999999872);
	}

	function int_sub_conc() public {
		int256 a1 = int_sub(100, 1);
		require(a1 == 99);
		int256 a2 = int_sub(100, 2);
		require(a2 == 98);
		int256 a3 = int_sub(100, 4);
		require(a3 == 96);
		int256 a4 = int_sub(100, 8);
		require(a4 == 92);
		int256 a5 = int_sub(1000000000, 8);
		require(a5 == 999999992);
		int256 a6 = int_sub(1000000000, 16);
		require(a6 == 999999984);
		int256 a7 = int_sub(10000000000, 32);
		require(a7 == 9999999968);
		int256 a8 = int_sub(100000000000000000000, 64);
		require(a8 == 99999999999999999936);
		int256 a9 = int_sub(100000000000000000000000000000000000, 128);
		require(a9 == 99999999999999999999999999999999872);
		int256 a10 = int_sub(1, 255);
		require(a10 == -254);

		int256 a11 = int_sub(-100, 1);
		require(a11 == -101);
		int256 a12 = int_sub(-100, 2);
		require(a12 == -102);
		int256 a13 = int_sub(-100, 4);
		require(a13 == -104);
		int256 a14 = int_sub(-100, 8);
		require(a14 == -108);
		int256 a15 = int_sub(-1000000000, 8);
		require(a15 == -1000000008);
		int256 a16 = int_sub(-1000000000, 16);
		require(a16 == -1000000016);
		int256 a17 = int_sub(-10000000000, 32);
		require(a17 == -10000000032);
		int256 a18 = int_sub(-100000000000000000000, 64);
		require(a18 == -100000000000000000064);
		int256 a19 = int_sub(-100000000000000000000000000000000000, 128);
		require(a19 == -100000000000000000000000000000000128);
		int256 a20 = int_sub(-1, 255);
		require(a20 == -256);

		int256 a21 = int_sub(-100, -1);
		require(a21 == -99);
		int256 a22 = int_sub(-100, -2);
		require(a22 == -98);
		int256 a23 = int_sub(-100, -4);
		require(a23 == -96);
		int256 a24 = int_sub(-100, -8);
		require(a24 == -92);
		int256 a25 = int_sub(-1000000000, -8);
		require(a25 == -999999992);
		int256 a26 = int_sub(-1000000000, -16);
		require(a26 == -999999984);
		int256 a27 = int_sub(-10000000000, -32);
		require(a27 == -9999999968);
		int256 a28 = int_sub(-100000000000000000000, -64);
		require(a28 == -99999999999999999936);
		int256 a29 = int_sub(-100000000000000000000000000000000000, -128);
		require(a29 == -99999999999999999999999999999999872);
		int256 a30 = int_sub(-1, -255);
		require(a30 == 254);

		int256 a31 = int_sub(100, -1);
		require(a31 == 101);
		int256 a32 = int_sub(100, -2);
		require(a32 == 102);
		int256 a33 = int_sub(100, -4);
		require(a33 == 104);
		int256 a34 = int_sub(100, -8);
		require(a34 == 108);
		int256 a35 = int_sub(1000000000, -8);
		require(a35 == 1000000008);
		int256 a36 = int_sub(1000000000, -16);
		require(a36 == 1000000016);
		int256 a37 = int_sub(10000000000, -32);
		require(a37 == 10000000032);
		int256 a38 = int_sub(100000000000000000000, -64);
		require(a38 == 100000000000000000064);
		int256 a39 = int_sub(100000000000000000000000000000000000, -128);
		require(a39 == 100000000000000000000000000000000128);
		int256 a40 = int_sub(1, -255);
		require(a40 == 256);
	}
}

contract AssignMath {
	function assignAdd(uint256 x) public {
		x += 10;
	}

	function assignSub(uint256 x) public {
		x -= 10;
	}

	function assignDiv(uint256 x) public {
		x /= 10;
	}

	function assignMul(uint256 x) public {
		x *= 10;
	}

	function preincrement(uint256 x) public returns (uint256, uint256) {
		uint256 y = ++x;
		return (y, x);
	}

	function postincrement(uint256 x) public returns (uint256, uint256) {
		uint256 y = x++;
		return (y, x);
	}

	function pre_conc() public {
		(uint256 y, uint256 x) = preincrement(100);
		require(y == 101);
		require(x == 101);
	}

	function post_conc() public {
		(uint256 y, uint256 x) = postincrement(100);
		require(y == 100);
		require(x == 101);
	}
}

contract Math {
	function rmod(uint256 x, uint256 y) public returns (uint256) {
		return x % y;
	}

	function rexp(uint256 x, uint256 y) public returns (uint256) {
		return x ** y;
	}

	function int_rmod(int256 x, int256 y) public returns (int256) {
		return x % y;
	}

	function int_rexp(int256 x, uint256 y) public returns (int256) {
		return x ** y;
	}
}