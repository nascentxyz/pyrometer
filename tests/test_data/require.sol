contract A {
    function b(int256) public {}
}
contract ParserError {
    // Σ
    function a() public returns (uint256) {
        A.non_existent(100);
        return 100;
    }
}