contract Test {
    function backdoor(uint256 x, uint256 y) external pure {
        uint256 number = 99;
        unchecked {
            uint256 z = x - 1;
            y = y - 10 + z;
            if (y == 69122131241245311234) {
                if (z == 6912213124124531) {
                    number = 0;
                } else {
                    number = 1;
                }
            } else {
                number = 1;
            }
        }
        assert(number != 0);
    }
}