// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract A {
    uint constant doubleScale = 1e36;

    struct Double {
        uint mantissa;
    }

    // function mulIf_(uint a, Double memory b) internal pure returns (uint) {
    //     if (b.mantissa > 10) {
    //         return mul_(a, 10) / doubleScale;
    //     } else {
    //         return mul_(a, b.mantissa) / doubleScale;
    //     }
    // }

    function mul_(uint a, Double memory b) internal pure returns (uint) {
        return mul_(a, b.mantissa) / doubleScale;
    }

    function mul_(uint a, uint b) internal pure returns (uint) {
        return a * b;
    }

    function pureChildrenNoFork() internal pure {
        Double memory d = Double({mantissa: 1e36});
        uint256 ret = mul_(10, d);
        require(ret == 10);
    }

    // function pureChildrenFork(uint256 x) internal pure {
    //     Double memory d = Double({mantissa: x});
    //     mulIf_(10, d);
    // }
}
