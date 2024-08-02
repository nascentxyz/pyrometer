pragma solidity ^0.8.0;

contract Assign {
    function doAssignment() public {
        // Multi-value LHS (tuple)
        (uint x, uint y) = (uint16(1), 2);

        // Single value RHS
        uint z = 3;

        (x, y) = (z, z);
    }

    uint x;

    function array_literals(uint z) public {
        uint[][] memory ax = new uint[][](z);
        ax[0] = new uint[](3);
        ax[0][2] = 2;

        uint[][] memory bx = ax;
        uint8[0x2][2] memory a = [[1, 2], [1, 2]];
        a[1];
        uint[2] memory b = [uint(3), x++];
        uint[2][2] memory c = [[uint(3), x++], [uint(2), uint(3)]];
        a;
        b;
    }

    function array_slices(
        uint[] calldata a
    ) public pure returns (uint[] memory) {
        require(a.length >= 4, "Array must have at least 4 elements");
        a[2] = 14;
        uint[] memory b = a[2:4];
        uint[] memory c = a[1:];
        uint[] memory d = a[:2];
        uint[] memory e = a[2:4][0:1];
    }
}
