// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract Assign {
    function doAssignment() public pure {
        // Multi-value LHS (tuple)
        (uint w, uint y) = (uint16(1), 2);

        // Single value RHS
        uint z = 3;

        (w, y) = (z, z);
    }

    uint x;

    function array_literals(uint z) public {
        uint[][] memory ax = new uint[][](z);
        ax[0] = new uint[](3);
        ax[0][2] = 2;

        uint[][] memory bx = ax;
        bx;
        uint8[0x2][2] memory a = [[1, 2], [1, 2]];
        a[1];
        uint[2] memory b = [uint(3), x++];
        uint[2][2] memory c = [[uint(3), x++], [uint(2), uint(3)]];
        c;
        a;
        b;
    }

    function array_slices(uint[] calldata a, uint q) public pure {
        require(a.length >= 4, "Array must have at least 4 elements");
        require(a[2] == 14);
        uint[] memory b = a[2:4];
        uint[] memory c = a[1:];
        uint[] memory d = a[:2];
        uint[] memory e = a[2:4][0:1];
        uint[] memory f = a[2:q];
        b;
        c;
        d;
        e;
        f;
    }
}
