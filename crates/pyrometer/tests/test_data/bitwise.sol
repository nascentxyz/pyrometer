// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract BitAnd {
    function bit_and(bytes32 x, bytes32 y) public pure returns (bytes32) {
        return x & y;
    }

    function bit_and_conc1() public pure {
        require(uint(bytes32(type(uint256).max) & bytes32(uint(100))) == 100);
        require(uint(bytes32(0) & bytes32(uint(100))) == 0);
        require(uint(bytes32(uint(101)) & bytes32(uint(105))) == 97);
        require(
            uint(bytes32(uint(type(uint24).max)) & bytes32(uint(1225))) == 1225
        );
        require(uint(bit_and(bytes32(uint(50)), bytes32(uint(500)))) == 48);
    }

    function bit_and(uint256 x, uint256 y) public pure returns (uint256) {
        return x & y;
    }

    function bit_and_conc() public pure {
        require(type(uint256).max & 100 == 100);
        require(0 & uint(100) == 0);
        require(101 & 105 == 97);
        require(type(uint24).max & 1225 == 1225);
        require(bit_and(50, 500) == 48);
    }

    function int_bit_and(int256 x, int256 y) public pure returns (int256) {
        return x & y;
    }

    function int_bit_and_conc() public pure {
        require(type(int256).max & int(100) == 100);
        require(0 & int(100) == 0);
        require(101 & 105 == 97);
        require(type(int24).max & -5 == 8388603);
        require(int_bit_and(50, 500) == 48);
    }
}

contract BitOr {
    function bit_or(bytes32 x, bytes32 y) public pure returns (bytes32) {
        return x | y;
    }

    function bit_or_conc1() public pure {
        require(
            bytes32(type(uint256).max) | bytes32(uint(100)) ==
                bytes32(type(uint256).max)
        );
        require(bytes32(0) | bytes32(uint(100)) == bytes32(uint(100)));
        require(bytes32(uint(101)) | bytes32(uint(105)) == bytes32(uint(109)));
        require(
            bytes32(uint(type(uint24).max)) | bytes32(uint(5)) ==
                bytes32(uint(type(uint24).max))
        );
        require(uint(bit_or(bytes32(uint(50)), bytes32(uint(500)))) == 502);
    }

    function bit_or(uint256 x, uint256 y) public pure returns (uint256) {
        return x | y;
    }

    function bit_or_conc() public pure {
        require(type(uint256).max | uint(100) == type(uint256).max);
        require(0 | uint(100) == 100);
        require(101 | 105 == 109);
        require(type(uint24).max | 5 == type(uint24).max);
        require(bit_or(50, 500) == 502);
    }

    function int_bit_or(int256 x, int256 y) public pure returns (int256) {
        return x | y;
    }

    function int_bit_or_conc() public pure {
        require(type(int256).max | int(100) == type(int256).max);
        require(0 | int(100) == 100);
        require(101 | 105 == 109);
        require(type(int24).max | -5 == -1);
        require(int_bit_or(50, 500) == 502);
    }
}

contract BitXor {
    function bit_xor(uint256 x, uint256 y) public pure returns (uint256) {
        return x ^ y;
    }

    function bit_xor_conc() public pure {
        require(
            type(uint256).max ^ uint(100) ==
                115792089237316195423570985008687907853269984665640564039457584007913129639835
        );
        require(0 ^ uint(100) == 100);
        require(101 ^ 105 == 12);
        require(type(uint24).max ^ 5 == 16777210);
        require(bit_xor(50, 500) == 454);
    }

    function int_bit_xor(int256 x, int256 y) public pure returns (int256) {
        return x ^ y;
    }

    function int_bit_xor_conc() public pure {
        require(
            type(int256).max ^ int(100) ==
                57896044618658097711785492504343953926634992332820282019728792003956564819867
        );
        require(0 ^ int(100) == 100);
        require(101 ^ 105 == 12);
        require(type(int24).max ^ -5 == -8388604);
        require(type(int24).min ^ -5 == 8388603);
        require(type(int24).min ^ 5 == -8388603);
        require(int_bit_xor(50, 500) == 454);
    }
}

contract BitNot {
    function yul_bit_not() public pure {
        uint256 x;
        assembly {
            x := not(100)
        }
        require(
            x ==
                115792089237316195423570985008687907853269984665640564039457584007913129639835
        );
    }

    function bit_not() public pure returns (bytes32) {
        bytes32 x = hex"1111";
        require(
            ~x ==
                bytes32(
                    0xeeeeffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                )
        );
        bytes16 x16 = hex"1111";
        require(
            ~x16 ==
                bytes32(
                    0xeeeeffffffffffffffffffffffffffff00000000000000000000000000000000
                )
        );
        bytes8 x8 = hex"1111";
        require(
            ~x8 ==
                bytes32(
                    0xeeeeffffffffffff000000000000000000000000000000000000000000000000
                )
        );
        return ~x;
    }

    function bit_not(uint256 x) public pure returns (uint256) {
        return ~x;
    }

    function bit_not_conc() public pure {
        require(~type(uint256).max == 0);
        require(
            ~uint(100) ==
                115792089237316195423570985008687907853269984665640564039457584007913129639835
        );
        require(
            ~uint(101) ==
                115792089237316195423570985008687907853269984665640564039457584007913129639834
        );
        require(
            ~uint(105) ==
                115792089237316195423570985008687907853269984665640564039457584007913129639830
        );
        require(~type(uint24).max == 0);
        require(
            bit_not(50) ==
                115792089237316195423570985008687907853269984665640564039457584007913129639885
        );
    }

    function int_bit_not(int256 x) public pure returns (int256) {
        return ~x;
    }

    function int_bit_not_conc() public pure {
        require(~type(int256).max == type(int256).min);
        require(~type(int256).min == type(int256).max);
        require(~int256(100) == -101);
        require(~int256(105) == -106);
        require(~type(int24).max == type(int24).min);
        require(~type(int24).min == type(int24).max);
        require(int_bit_not(50) == -51);
    }
}

contract BitShl {
    function yulShl(uint256 x, uint256 y) public pure returns (uint256) {
        uint256 ret;
        assembly {
            ret := shl(y, x)
        }
        return ret;
    }

    function yulShl_conc() public pure {
        uint256 ret = yulShl(10, 1);
        uint256 other_ret = 10 << 1;
        require(ret == other_ret);
    }

    function yulShr(uint256 x, uint256 y) public pure returns (uint256) {
        uint256 ret;
        assembly {
            ret := shr(x, y)
        }
        return ret;
    }

    function shl(uint256 x, uint256 y) public pure returns (uint256) {
        return x << y;
    }

    function int_shl(int256 x, uint256 y) public pure returns (int256) {
        return x << y;
    }

    function shl_conc() public pure {
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
        require(
            a9 ==
                34028236692093846346337460743176821145600000000000000000000000000000000000
        );
        uint256 a10 = shl(1, 255);
        require(
            a10 ==
                57896044618658097711785492504343953926634992332820282019728792003956564819968
        );
    }

    function int_shl_conc() public pure {
        int256 a1 = int_shl(100, 1);
        "pyro:variable:a1:range:[200,200]";
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
        require(
            a9 ==
                34028236692093846346337460743176821145600000000000000000000000000000000000
        );
        int256 a10 = int_shl(1, 255);
        require(
            a10 ==
                -57896044618658097711785492504343953926634992332820282019728792003956564819968
        );

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
        require(
            a19 ==
                -34028236692093846346337460743176821145600000000000000000000000000000000000
        );
        int256 a20 = int_shl(-1, 255);
        require(
            a20 ==
                -57896044618658097711785492504343953926634992332820282019728792003956564819968
        );
        int256 a21 = int_shl(-1, 256);
        require(a21 == 0);
    }
}

contract BitShr {
    function shr(uint256 x, uint256 y) public pure returns (uint256) {
        return x >> y;
    }

    function int_shr(int256 x, uint256 y) public pure returns (int256) {
        return x >> y;
    }

    function shr_conc() public pure {
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
        uint256 a10 = shr(
            1000000000000000000000000000000000000000000000000000000000000000000000000000,
            248
        );
        require(a10 == 2);
    }

    function int_shr_conc() public pure {
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
        int256 a10 = int_shr(
            1000000000000000000000000000000000000000000000000000000000000000000000000000,
            248
        );
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
        int256 a20 = int_shr(
            -1000000000000000000000000000000000000000000000000000000000000000000000000000,
            248
        );
        require(a20 == -2);
    }
}
