// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

// type ShortString is bytes32;
// type MyUint is uint256;
// type MyInt is int256;

contract Cast {
    function u_int(uint256 x) public pure {
        uint248 x_uint248 = uint248(x);
        uint240 x_uint240 = uint240(x);
        uint232 x_uint232 = uint232(x);
        uint224 x_uint224 = uint224(x);
        uint216 x_uint216 = uint216(x);
        uint208 x_uint208 = uint208(x);
        uint200 x_uint200 = uint200(x);
        uint192 x_uint192 = uint192(x);
        uint184 x_uint184 = uint184(x);
        uint176 x_uint176 = uint176(x);
        uint168 x_uint168 = uint168(x);
        uint160 x_uint160 = uint160(x);
        uint152 x_uint152 = uint152(x);
        uint144 x_uint144 = uint144(x);
        uint136 x_uint136 = uint136(x);
        uint128 x_uint128 = uint128(x);
        uint120 x_uint120 = uint120(x);
        uint112 x_uint112 = uint112(x);
        uint104 x_uint104 = uint104(x);
        uint96 x_uint96 = uint96(x);
        uint88 x_uint88 = uint88(x);
        uint80 x_uint80 = uint80(x);
        uint72 x_uint72 = uint72(x);
        uint64 x_uint64 = uint64(x);
        uint56 x_uint56 = uint56(x);
        uint48 x_uint48 = uint48(x);
        uint40 x_uint40 = uint40(x);
        uint32 x_uint32 = uint32(x);
        uint24 x_uint24 = uint24(x);
        uint16 x_uint16 = uint16(x);
        uint8 x_uint8 = uint8(x);
        uint256 x_uint256 = uint256(x_uint8);
        x_uint256;
        x_uint248;
        x_uint240;
        x_uint232;
        x_uint224;
        x_uint216;
        x_uint208;
        x_uint200;
        x_uint192;
        x_uint184;
        x_uint176;
        x_uint168;
        x_uint160;
        x_uint152;
        x_uint144;
        x_uint136;
        x_uint128;
        x_uint120;
        x_uint112;
        x_uint104;
        x_uint96;
        x_uint88;
        x_uint80;
        x_uint72;
        x_uint64;
        x_uint56;
        x_uint48;
        x_uint40;
        x_uint32;
        x_uint24;
        x_uint16;
    }

    function u_int_conc() public pure {
        u_int(100);
    }

    function i_nt(int256 x) public pure {
        int248 x_int248 = int248(x);
        int240 x_int240 = int240(x);
        int232 x_int232 = int232(x);
        int224 x_int224 = int224(x);
        int216 x_int216 = int216(x);
        int208 x_int208 = int208(x);
        int200 x_int200 = int200(x);
        int192 x_int192 = int192(x);
        int184 x_int184 = int184(x);
        int176 x_int176 = int176(x);
        int168 x_int168 = int168(x);
        int160 x_int160 = int160(x);
        int152 x_int152 = int152(x);
        int144 x_int144 = int144(x);
        int136 x_int136 = int136(x);
        int128 x_int128 = int128(x);
        int120 x_int120 = int120(x);
        int112 x_int112 = int112(x);
        int104 x_int104 = int104(x);
        int96 x_int96 = int96(x);
        int88 x_int88 = int88(x);
        int80 x_int80 = int80(x);
        int72 x_int72 = int72(x);
        int64 x_int64 = int64(x);
        int56 x_int56 = int56(x);
        int48 x_int48 = int48(x);
        int40 x_int40 = int40(x);
        int32 x_int32 = int32(x);
        int24 x_int24 = int24(x);
        int16 x_int16 = int16(x);
        int8 x_int8 = int8(x);
        int256 x_int256 = int256(x_int8);
        x_int256;
        x_int248;
        x_int240;
        x_int232;
        x_int224;
        x_int216;
        x_int208;
        x_int200;
        x_int192;
        x_int184;
        x_int176;
        x_int168;
        x_int160;
        x_int152;
        x_int144;
        x_int136;
        x_int128;
        x_int120;
        x_int112;
        x_int104;
        x_int96;
        x_int88;
        x_int80;
        x_int72;
        x_int64;
        x_int56;
        x_int48;
        x_int40;
        x_int32;
        x_int24;
        x_int16;
    }

    function i_nt_conc_pos() public pure {
        i_nt(100);
    }

    function i_nt_conc_neg() public pure {
        i_nt(-100);
    }

    function u_i_nt(int256 x) public pure {
        uint256 x_uint256 = uint256(x);
        int248 x_int248 = int248(x);
        uint248 x_uint248 = uint248(x_int248);
        int240 x_int240 = int240(x);
        uint240 x_uint240 = uint240(x_int240);
        int232 x_int232 = int232(x);
        uint232 x_uint232 = uint232(x_int232);
        int224 x_int224 = int224(x);
        uint224 x_uint224 = uint224(x_int224);
        int216 x_int216 = int216(x);
        uint216 x_uint216 = uint216(x_int216);
        int208 x_int208 = int208(x);
        uint208 x_uint208 = uint208(x_int208);
        int200 x_int200 = int200(x);
        uint200 x_uint200 = uint200(x_int200);
        int192 x_int192 = int192(x);
        uint192 x_uint192 = uint192(x_int192);
        int184 x_int184 = int184(x);
        uint184 x_uint184 = uint184(x_int184);
        int176 x_int176 = int176(x);
        uint176 x_uint176 = uint176(x_int176);
        int168 x_int168 = int168(x);
        uint168 x_uint168 = uint168(x_int168);
        int160 x_int160 = int160(x);
        uint160 x_uint160 = uint160(x_int160);
        int152 x_int152 = int152(x);
        uint152 x_uint152 = uint152(x_int152);
        int144 x_int144 = int144(x);
        uint144 x_uint144 = uint144(x_int144);
        int136 x_int136 = int136(x);
        uint136 x_uint136 = uint136(x_int136);
        int128 x_int128 = int128(x);
        uint128 x_uint128 = uint128(x_int128);
        int120 x_int120 = int120(x);
        uint120 x_uint120 = uint120(x_int120);
        int112 x_int112 = int112(x);
        uint112 x_uint112 = uint112(x_int112);
        int104 x_int104 = int104(x);
        uint104 x_uint104 = uint104(x_int104);
        int96 x_int96 = int96(x);
        uint96 x_uint96 = uint96(x_int96);
        int88 x_int88 = int88(x);
        uint88 x_uint88 = uint88(x_int88);
        int80 x_int80 = int80(x);
        uint80 x_uint80 = uint80(x_int80);
        int72 x_int72 = int72(x);
        uint72 x_uint72 = uint72(x_int72);
        int64 x_int64 = int64(x);
        uint64 x_uint64 = uint64(x_int64);
        int56 x_int56 = int56(x);
        uint56 x_uint56 = uint56(x_int56);
        int48 x_int48 = int48(x);
        uint48 x_uint48 = uint48(x_int48);
        int40 x_int40 = int40(x);
        uint40 x_uint40 = uint40(x_int40);
        int32 x_int32 = int32(x);
        uint32 x_uint32 = uint32(x_int32);
        int24 x_int24 = int24(x);
        uint24 x_uint24 = uint24(x_int24);
        int16 x_int16 = int16(x);
        uint16 x_uint16 = uint16(x_int16);
        int8 x_int8 = int8(x);
        uint8 x_uint8 = uint8(x_int8);
        x_uint256 = uint256(int256(x_int8));
        x_uint248;
        x_uint240;
        x_uint232;
        x_uint224;
        x_uint216;
        x_uint208;
        x_uint200;
        x_uint192;
        x_uint184;
        x_uint176;
        x_uint168;
        x_uint160;
        x_uint152;
        x_uint144;
        x_uint136;
        x_uint128;
        x_uint120;
        x_uint112;
        x_uint104;
        x_uint96;
        x_uint88;
        x_uint80;
        x_uint72;
        x_uint64;
        x_uint56;
        x_uint48;
        x_uint40;
        x_uint32;
        x_uint24;
        x_uint16;
        x_uint8;
    }

    function b_ytes(bytes32 x) public pure {
        bytes31 x_bytes31 = bytes31(x);
        bytes30 x_bytes30 = bytes30(x);
        bytes29 x_bytes29 = bytes29(x);
        bytes28 x_bytes28 = bytes28(x);
        bytes27 x_bytes27 = bytes27(x);
        bytes26 x_bytes26 = bytes26(x);
        bytes25 x_bytes25 = bytes25(x);
        bytes24 x_bytes24 = bytes24(x);
        bytes23 x_bytes23 = bytes23(x);
        bytes22 x_bytes22 = bytes22(x);
        bytes21 x_bytes21 = bytes21(x);
        bytes20 x_bytes20 = bytes20(x);
        bytes19 x_bytes19 = bytes19(x);
        bytes18 x_bytes18 = bytes18(x);
        bytes17 x_bytes17 = bytes17(x);
        bytes16 x_bytes16 = bytes16(x);
        bytes15 x_bytes15 = bytes15(x);
        bytes14 x_bytes14 = bytes14(x);
        bytes13 x_bytes13 = bytes13(x);
        bytes12 x_bytes12 = bytes12(x);
        bytes11 x_bytes11 = bytes11(x);
        bytes10 x_bytes10 = bytes10(x);
        bytes9 x_bytes9 = bytes9(x);
        bytes8 x_bytes8 = bytes8(x);
        bytes7 x_bytes7 = bytes7(x);
        bytes6 x_bytes6 = bytes6(x);
        bytes5 x_bytes5 = bytes5(x);
        bytes4 x_bytes4 = bytes4(x);
        bytes3 x_bytes3 = bytes3(x);
        bytes2 x_bytes2 = bytes2(x);
        bytes1 x_bytes1 = bytes1(x);
        bytes32 x_bytes32 = bytes32(x_bytes1);
        x_bytes31;
        x_bytes30;
        x_bytes29;
        x_bytes28;
        x_bytes27;
        x_bytes26;
        x_bytes25;
        x_bytes24;
        x_bytes23;
        x_bytes22;
        x_bytes21;
        x_bytes20;
        x_bytes19;
        x_bytes18;
        x_bytes17;
        x_bytes16;
        x_bytes15;
        x_bytes14;
        x_bytes13;
        x_bytes12;
        x_bytes11;
        x_bytes10;
        x_bytes9;
        x_bytes8;
        x_bytes7;
        x_bytes6;
        x_bytes5;
        x_bytes4;
        x_bytes3;
        x_bytes2;
        x_bytes1;
        x_bytes32;
    }

    function b_ytes_uint(bytes32 x) public pure returns (uint256) {
        uint256 x_uint256 = uint256(x);
        return x_uint256;
    }

    function u_int_bytes(uint256 x) public pure returns (bytes32) {
        bytes32 x_bytes32 = bytes32(x);
        return x_bytes32;
    }

    function u_int_addr(uint160 x) public pure returns (address) {
        return address(x);
    }

    function addr_uint(address x) public pure returns (uint160) {
        return uint160(x);
    }

    function b_ytes_uint_conc() public pure returns (bytes32) {
        bytes32 round_trip = u_int_bytes(b_ytes_uint(hex"1337"));
        require(round_trip == bytes32(hex"1337"));
        return round_trip;
    }

    function addr_uint_conc() public pure returns (address) {
        address round_trip = u_int_addr(addr_uint(address(1337)));
        require(round_trip == address(1337));
        return round_trip;
    }

    function userStr() internal pure {
        bytes32 x = bytes32("test");
        ShortString a = ShortString.wrap(x);
        bytes32 b = ShortString.unwrap(a);
        require(b == x);
    }

    function userUint() internal pure {
        uint256 x = 100;
        MyUint a = MyUint.wrap(x);
        uint256 b = MyUint.unwrap(a);
        require(b == x);
    }

    function downcast_uint_conc() public pure returns (uint64) {
        uint128 y = type(uint128).max;
        y -= type(uint32).max;
        return uint64(y);
    }

    function downcast_int_conc() public pure returns (int64) {
        int128 x = type(int128).max;
        x -= type(int32).max;
        return int64(x);
    }

    function userInt() internal pure {
        int256 x = -100;
        MyInt a = MyInt.wrap(x);
        int256 b = MyInt.unwrap(a);
        require(b == x);
    }

    function int_uint_int_conc() internal pure {
        int256 a = -100;
        uint256 b = uint(a);
        int256 c = int(b);
        require(-100 == c);
    }

    function int_uint_int(int a) internal pure {
        uint256 b = uint(a);
        int256 c = int(b);
        c;
    }
}

contract FuncCast {
    function a(bytes32 vs) public pure {
        b(vs);
    }

    function b(bytes32 vs) public pure returns (bool) {
        bytes32 s = vs &
            bytes32(
                0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
            );
        // uint8 v = uint8((uint256(vs) >> 255) + 27);
        return c(s);
    }

    function c(bytes32 s) public pure returns (bool) {
        if (
            uint256(s) >
            0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0
        ) {
            return true;
        } else {
            return false;
        }
    }

    function foo() public {
        address ad = address(0);
        (bool r, bytes memory k) = ad.call(hex"");
        (r, k) = ad.delegatecall(hex"");
        (r, k) = ad.delegatecall(msg.data);

        bytes memory data = hex"01234567";
        data;
    }
}
