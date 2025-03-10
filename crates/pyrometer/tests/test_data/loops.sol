// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract For {
    function const_loop() public pure returns (uint) {
        uint256 x;
        for (uint256 i; i < 10; i++) {
            x += 1;
        }

        x += 1;
        require(x == 10);
        return x;
    }

    function const_loop_def_iter() public pure returns (uint) {
        uint256 x;
        for (uint256 i = 1; i < 10; i++) {
            i += 1;
        }

        require(x == 10);
        return x;
    }

    function while_loop(uint256 x) public pure returns (uint) {
        while (x > 10) {
            x -= 1;
        }

        require(x == 10);
        return x;
    }

    function complicated_while_loop(
        uint256 amount
    ) public pure returns (uint256) {
        uint256 x = amount;
        amount -= x;
        return amount;
    }

    function loop_op_assign(uint256 value) internal pure {
        uint256 temp = value;
        uint256 digits;
        while (temp != 0) {
            digits++;
            temp /= 10;
        }
    }
}
