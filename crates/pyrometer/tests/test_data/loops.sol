contract For {
    function const_loop() public {
        uint256 x;
        for (uint256 i; i < 10; i++) {
            x += 1;
        }

        x += 1;
        require(x == 10);
        return x;
    }

    function const_loop_def_iter() public {
        uint256 x;
        for (uint256 i = 1; i < 10; i++) {
            i += 1;
        }

        require(x == 10);
        return x;
    }

    function while_loop(uint256 x) public {
        while (x > 10) {
            x -= 1;
        }

        require(x == 10);
        return x;
    }

    function complicated_while_loop(uint256 amount) public returns (uint256) {
        uint256 x = amount;
        amount -= x;
        return amount;
        // uint256 balance = 1;
        // uint256 amountToRedeem;
        // if (amount > balance) {
        //     amountToRedeem = balance;
        // } else {
        //     amountToRedeem = amount;
        // }
        // amount -= amountToRedeem;

        // return amount;
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



