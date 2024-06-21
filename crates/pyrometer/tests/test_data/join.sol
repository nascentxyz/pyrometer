contract A {
	uint constant doubleScale = 1e36;

	struct Double {
        uint mantissa;
    }

    function mulIf_(uint a, Double memory b) pure internal returns (uint) {
    	if (b.mantissa > 10) {
    		return mul_(a, 10) / doubleScale;
		} else {
			return mul_(a, b.mantissa) / doubleScale;	
		}
        
    }

	function mul_(uint a, Double memory b) pure internal returns (uint) {
        return mul_(a, b.mantissa) / doubleScale;
    }

    function mul_(uint a, uint b) pure internal returns (uint) {
        return a * b;
    }

    function pureChildrenNoFork() pure internal {
    	Double memory d = Double({mantissa: 1e36});
    	uint256 ret = mul_(10, d);
    	require(ret == 10);
    }

    function pureChildrenFork(uint256 x) pure internal {
    	Double memory d = Double({mantissa: x});
    	mulIf_(10, d);
    }
}