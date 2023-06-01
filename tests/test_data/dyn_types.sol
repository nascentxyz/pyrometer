contract DynTypes {
    uint256[] storeVar;

    // function bytes_dyn(bytes calldata x) public {
    //     bytes memory y = x;
    //     require(x.length < 10);
    //     y[8] = 0xff;
    //     require(y.length == 9);
    // }

    // function array_dyn(uint256[] calldata x) public {
    //     uint256[] memory y = x;
    //     require(x.length < 10);
    //     y[8] = 100;
    //     require(y.length == 9);
    // }

    // function nested_bytes_dyn(bytes[] calldata x) public {
    //     bytes memory a = hex"1337";
    //     x[0] = a;
    //     require(x[0][0] == hex"13");
    //     require(x.length == 1);
    // }

    // function array_push(uint256 x) public {
    //     require(x > 5);
    //     storeVar.push(x);
    //     // TODO: handle this better
    //     require(storeVar[0] == x);
    //     uint256 y = storeVar.pop();
    //     require(y == x);
    // }

    function indexInto() public returns (uint256) {
        return storeVar[basicFunc()];
    }

    function basicFunc() public returns (uint256) {
        return 1;
    }
}
