pragma solidity ^0.8.0;

library Math {
    function mulDiv(uint256 x, uint256 y, uint256 denominator) internal pure returns (uint256 result) {
        unchecked {
            uint256 prod0;
            uint256 prod1;
            assembly {
                let mm := mulmod(x, y, not(0))
                prod0 := mul(x, y)
                prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            }

            require(denominator > prod1);


            uint256 twos = denominator & (~denominator + 1);
            assembly {
                twos := add(div(sub(0, twos), twos), 1)
            }

            return 0;
        }
    }
}