// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract Assembly {
    function switchStatement(uint256 x) public pure returns (uint256) {
        uint256 y = x;
        y;
        assembly {
            switch mod(x, 10)
            case 1 {
                x := add(x, 1)
            }
            case 2 {
                x := add(x, 2)
            }
            case 3 {
                x := add(x, 3)
            }
            case 4 {
                x := add(x, 4)
            }
            default {
                x := add(x, 10)
            }
        }

        return x;
    }

    function hasInline(
        uint256 a,
        uint256 b
    ) public pure returns (uint256, uint256) {
        assembly {
            a := add(100, a)
            a := sub(a, 10)
            a := div(a, 2)
            a := mul(a, 2)
            if lt(b, 200) {
                b := 100
            }

            // let c := 0x200
            // let d := true
        }

        if (b < 200) {
            require(b == 100);
        }
        return (a, b);
    }

    function varDecl(uint256 a) public pure {
        a;
        assembly {
            let b := 200
            let c := 0x200
            let d := true
        }
    }
}
