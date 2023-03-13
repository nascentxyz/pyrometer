contract F1A9 is IPuzzle {
    /// @inheritdoc IPuzzle
    function name() external pure returns (string memory) {
        return "0xF1A9";
    }

    /// @inheritdoc IPuzzle
    function generate(address _seed) external view returns (uint256) {
        return (uint256(uint160(_seed)) >> (((block.number >> 8) & 0x1F) << 2)) & 0xFFFF;
    }

    /// @inheritdoc IPuzzle
    function verify(address _seed, uint256 _solution) external returns (bool) {
        uint256 _start = generate(_seed);
        uint256 prefix = block.timestamp < 1678446000 ? (0xF1A9 << 16) | _start : 0;

        require((_solution >> 128) == prefix);
        // return
        //     prefix == (_solution >> 128) &&
        //     ISolve(address(uint160(_solution))).curtaPlayer() == msg.sender;
    }
}

interface ISolve {
    function curtaPlayer() external pure returns (address);
}