contract DynTypes {
    uint256[] storeVar;

    struct Strukt {
        uint256 a;
        uint256 b;
    }

    mapping(address => Strukt) public someMapping;

    function bytes_dyn(bytes calldata x) public {
        bytes memory y = x;
        require(x.length < 10);
        y[8] = 0xff;
        require(y.length == 9);
    }

    function array_dyn(uint256[] memory x) public {
        x[0] = 5;
        require(x.length < 10);
        uint256[] memory y = x;
        y[8] = 100;
        require(y.length == 9);
    }

    function nested_bytes_dyn(
        bytes[] memory x,
        uint y
    ) public returns (bytes1) {
        bytes memory a = hex"1337";
        x[0] = a;
        require(x[0][0] == hex"13");
        // return x[0][0];

        x[y] = hex"1122";
        uint256 z = y - 1;
        require(x[z + 1][0] == hex"11");
    }

    function array_push(uint256 x) public {
        // require(x > 5);
        storeVar.push(x);
        storeVar.push(x);
        storeVar.push(x);
        // TODO: handle this better
        require(storeVar[0] == x);
        storeVar.push(x);
        require(storeVar[1] == x);
        uint256 y = storeVar[storeVar.length - 1];
        storeVar.pop();
        require(y == x);
    }

    function indexInto() public returns (uint256) {
        return storeVar[basicFunc()];
    }

    function basicFunc() public returns (uint256) {
        return 1;
    }

    function indexIntoMapping(address who) public {
        // TODO: this should panic
        Strukt storage a = someMapping[who];
        a.a = 100;
        a.b = 100;
        require(someMapping[who].a == 300);
    }

    address[] t;

    function inLoop(address holder, address[] memory tokens) public {
        address[] memory h = new address[](1);
        h[0] = holder;
        inLoop(h, tokens);
    }

    function inLoop(address[] memory holders, address[] memory tokens) public {
        for (uint j = 0; j < holders.length; j++) {
            address holder = holders[j];
        }
    }
}
