contract ConstVar {
    uint256 internal constant typeVar = type(uint256).max;
    uint256 internal constant funcVar = a();
    uint256 internal constant funcVarInput = aInput(100);

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

    function checkA() public pure returns (uint256) {
        require(funcVar == type(uint256).max);
    }

    function checkAInput() public pure returns (uint256) {
        require(funcVarInput == 110);
    }

    function c() public pure returns (uint256) {
        require(typeVar == type(uint256).max);
    }
}