// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract Todo {
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
