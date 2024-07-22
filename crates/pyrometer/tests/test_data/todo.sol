pragma solidity ^0.8.0;

contract Todo {

    // will live in env.sol when added
    function env() public view { 
        bytes32 b = blobhash(1);
        uint d = block.blobbasefee;
    }

    // will live in assign.sol when added
    function array_literals() public pure { 
        uint[2] memory a = [uint(1), uint(2)];
        uint[2] memory b = [uint(3), uint(4)];
    }

    // will live in assign.sol when added
    function array_slices(uint[] calldata a) public pure returns (uint[] memory) { 
        require(a.length >= 4, "Array must have at least 4 elements");
        uint[] memory b = a[2:4];
        // if a is [1,2,3,4]
        // then b is [3, 4]
        return b;
    }

    // this will live in loops.sol when fixed
    function perform_break_literal() public pure {
        for (uint256 i = 0; i < 10; i++) {
            if (i == 5) {
                break; // @brock this one weirdly does not error on the break
            }
        }
    }

    // this will live in loops.sol when fixed
    function perform_break(uint[] memory a) public pure {
        for (uint256 i = 0; i < a.length; i++) {
            if (i == a[i]) {
                break;
            }
        }
    }
}