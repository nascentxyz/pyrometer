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
}
