// contract A {
// 	uint256 storageVariable;
// 	// uint256 public publicStorageVariable;
// 	// uint256 constant const;

// 	function funcA() public returns (uint256 ret) {
// 		ret = funcB(storageVariable);
// 	}

// 	function funcB(uint256 innerInput0) internal returns (uint256 ret) {
// 		ret = innerInput0 + 10;
// 	}
// }

contract InvariantBreaker {
    bool public flag0 = true;
    bool public flag1 = true;

    function set0(int256 val) public returns (bool) {
        if (val % 100 == 0) {
            flag0 = false;
        }
        return flag0;
    }

    function set1(int256 val) public returns (bool) {
        if (val % 10 == 0 && !flag0) {
            flag1 = false;
        }
        return flag1;
    }
}
