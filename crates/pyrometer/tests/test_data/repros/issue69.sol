contract SymbolicTest {
    // https://github.com/foundry-rs/foundry/issues/2851
    function backdoor(uint256 x) external pure {
        uint256 number = 99;
        unchecked {
            uint256 z = x - 1;
            if (z == 6912213124124531) {
                number = 0;
            } else {
                number = 1;
            }
        }
        assert(number != 0);
    }
}