contract ConstVar {
    uint256 internal constant typeVar = type(uint256).max;
    uint256 internal constant funcVar = a();
    uint256 internal constant funcVarInput = aInput(100);
    bytes16 private constant bytesString = "0123456789abcdef";

    function a() public pure returns (uint256) {
        return type(uint256).max;
    }

    function aInput(uint256 b) public pure returns (uint256) {
        if (b < 100) {
            return b + 1;
        } else {
            return b + 10;
        }
    }

    function checkA() public pure {
        require(funcVar == type(uint256).max);
    }

    function checkAInput() public pure {
        require(funcVarInput == 110);
    }

    function c() public pure {
        require(typeVar == type(uint256).max);
    }

    function checkBytesString() public pure {
        bytes16 _bytesString = "0123456789abcdef";
        require(bytesString == _bytesString);
    }
}