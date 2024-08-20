contract Mul {
    function mul(uint x, uint y) internal pure returns (uint) {
        return x * y;
    }

    function mul_conc() public pure {
        uint256 a3 = mul(100, 4);
        "pyro::variable::a3::range::[400,400]";
    }
}
