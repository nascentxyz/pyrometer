// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract Require {
    function u_int256_y(uint256 x, uint256 y) public pure {
        require(x > 100);
        require(y != x);
    }

    function u_int256(uint256 x) public pure {
        require(x > 100);
        require(x == 101);
    }

    function u_int256_neq(uint256 x) public pure {
        require(x > 100);
        require(x != 101);
    }

    function u_int128(uint128 x) public pure {
        require(x > 100);
        require(x == 101);
    }

    function u_int64(uint64 x) public pure {
        require(x > 100);
        require(x == 101);
    }

    function a_ddress(address x) public pure {
        require(x == address(100));
    }

    function a_ddress_neq(address x) public pure {
        require(x != address(100));
    }

    function b_ytes32(bytes32 x) public pure {
        require(x == bytes32(hex"1337"));
    }

    function b_ytes32_neq(bytes32 x) public pure {
        require(x != bytes32(hex"1337"));
    }

    function b_ytes32_neq_2(bytes32 x) public pure {
        require(x != bytes32(hex"00"));
    }

    function b_ytes16(bytes16 x) public pure {
        require(x == bytes16(hex"1337"));
    }

    function b_ytes8(bytes8 x) public pure {
        require(x == bytes8(hex"1337"));
    }

    function b_ytes8(bytes4 x) public pure {
        require(x == bytes4(hex"1337"));
    }

    function b_ytes2(bytes2 x) public pure {
        require(x == bytes2(hex"1337"));
    }

    function b_ytes1(bytes1 x) public pure {
        require(x == bytes1(hex"13"));
    }

    function UintMoreEqual(uint8 x) public {
        require(x >= 100);
        "pyro::constraint::(x >= 100)";
        "pyro::variable::x::range::[100, 255]";
    }

    function UintLessEqual(uint8 x) public {
        require(x <= 100);
        "pyro::constraint::(x <= 100)";
        "pyro::variable::x::range::[0, 100]";
    }
}
