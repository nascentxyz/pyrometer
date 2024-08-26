contract A {
    uint256 storageVariable;
    uint256 public publicStorageVariable;

    function func(
        uint256 input0,
        bytes32 input1,
        uint256[] memory input2
    ) public returns (uint256 ret) {
        uint256 innerVar = 100;
        storageVariable = innerVar;
        ret = innerVar;
    }
}
