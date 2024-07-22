pragma solidity ^0.8.0;

contract Assign {

    function doAssignment() public {
        // Multi-value LHS (tuple)
        (uint x, uint y) = (uint16(1), 2);

        // Single value RHS
        uint z = 3;

        (x, y) = (z, z);

        // uint[2] memory a = [uint(1), uint(2)];
        // uint[2] memory b = [uint(3), uint(4)];


        // (a, b) = (b, a);
    }
}