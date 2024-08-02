pragma solidity ^0.8.0;

contract Cmp {
    function testCmp(int x) public {
        uint a = 5;
        bool b = (5 < 6) || (5 == 6 && 0 < 1); // Correct the tuple comparison
    }
}
