contract Test {
    function backdoor(uint256 x, uint256 y) external pure {
        uint256 number = 99;
        unchecked {
            uint256 z = x - 1;
            y = y - 10 + z;
            if (y == 69122131241245311234) {
                // "pyro::constraint::(y == 69122131241245311234)";
                // "pyro::variable::y::range::[69122131241245311234,69122131241245311234]";
                if (z == 6912213124124531) {
                    // "pyro::constraint::(z == 6912213124124531)";
                    // "pyro::variable::z::range::[6912213124124531,6912213124124531]";
                    number = 0;
                    // "pyro::variable::number::range::[0,0]";
                } else {
                    // "pyro::constraint::(z != 6912213124124531)";
                    number = 1;
                    // "pyro::variable::number::range::[1,1]";
                }
            } else {
                // "pyro::constraint::(y != 69122131241245311234)";
                number = 1;
            }
        }
        assert(number != 0);
    }
}
