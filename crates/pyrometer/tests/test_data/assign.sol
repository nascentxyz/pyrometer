pragma solidity ^0.8.0;

contract Assign {
    function doAssignment() public {
        // Multi-value LHS (tuple)
        (uint x, uint y) = (uint16(1), 2);

        // Single value RHS
        uint z = 3;

        (x, y) = (z, z);
    }
}
