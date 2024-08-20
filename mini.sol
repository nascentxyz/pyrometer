contract Div {
    function div(uint x, uint y) internal pure returns (uint) {
        return x / y;
    }

    function div_conc() public pure {
        uint256 a10 = div(1, 255);
        "pyro::variable::a10::range::[0,0]";
    }
}
