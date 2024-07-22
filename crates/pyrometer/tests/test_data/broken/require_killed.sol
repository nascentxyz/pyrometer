// SPDX-License-Identifier: MIT or APACHE2
// Move to require_with_killed.sol when fixed
// Note: I've added broken@brock comments to the issues i know of
pragma solidity ^0.8.0;

contract RequireWithKilled {
    uint public count = 0;
    uint storeRange = 0;

    function setStoreRange(uint x) public {
        storeRange = x;
    }

    function requireLt(uint x) public {
        // set bounds for storeRange
        require(5 < storeRange && storeRange < 100);
        "pyro::variable::storeRange::range::[6, 99]"; // broken@brock this range appears as [0,99]
        // set tighter bounds for x
        require(6 < x && x < 99);
        "pyro::variable::x::range::[7, 98]"; // broken@brock this range appears as [0,98]
        // make x less than storeRange
        require(x < storeRange);
    }

    function requireLte(uint x) public {
        // set bounds for storeRange
        require(5 < storeRange && storeRange < 100);
        // set tighter bounds for x
        require(6 < x && x < 99);
        // make x less than or equal to storeRange
        require(x <= storeRange);
    }

    function requireGt(uint x) public {
        // set bounds for storeRange
        require(5 < storeRange && storeRange < 100);
        // set tighter bounds for x
        require(6 < x && x < 99);
        // make x greater than storeRange
        require(x > storeRange);
    }

    function requireGte(uint x) public {
        // set bounds for storeRange
        require(5 < storeRange && storeRange < 100);
        // set tighter bounds for x
        require(6 < x && x < 99);
        // make x greater than or equal to storeRange
        require(x >= storeRange);
    }

    function requireEq(uint x) public {
        // set bounds for storeRange
        require(5 < storeRange && storeRange < 100);
        // set tighter bounds for x
        require(6 < x && x < 99);
        // make x equal to storeRange
        require(x == storeRange);
    }

    function requireNeq(uint x) public {
        // set bounds for storeRange
        require(5 < storeRange && storeRange < 100);
        // set tighter bounds for x
        require(6 < x && x < 99);
        // make x not equal to storeRange
        require(x != storeRange);
    }

    function setCount() public {
        count = 0;
    }

    function andShortCircuit() public {
        count = 0;
        // ( bump(false) && bump(true) ) || true , this will test that the second bump is not evaluated since the `and` short circuits
        require(
            (bumpCountIfValueEq1ThenReturn(1, false) &&
                bumpCountIfValueEq1ThenReturn(1, true)) || true
        );
        "pyro::variable::count::range::[1, 1]"; // broken@brock `count` is not found in context. this goes for the other "pyro::" statements with `count` too
    }

    function andFullCircuit() public {
        count = 0;
        // ( bump(true) && bump(true) ) , this will test that the second bump is evaluated since the `and` does not short circuit
        // broken@brock `&&` has parse issues here
        require(
            (bumpCountIfValueEq1ThenReturn(1, true) &&
                bumpCountIfValueEq1ThenReturn(1, true))
        );
        "pyro::variable::count::range::[2, 2]";
    }

    function orShortCircuit() public {
        count = 0;
        // ( bump(true) || bump(true) ) , this will test that the second bump is not evaluated since the `or` short circuits
        require(
            bumpCountIfValueEq1ThenReturn(1, true) ||
                bumpCountIfValueEq1ThenReturn(1, true)
        );
        "pyro::variable::count::range::[1, 1]";
    }

    function orShortCircuitRHS() public {
        count = 0;
        // ( bump(true) || bump(true) ) , this will test that the second bump is not evaluated since the `or` short circuits
        require(
            bumpCountIfValueEq1ThenReturn(2, true) ||
                bumpCountIfValueEq1ThenReturn(1, true)
        );
        "pyro::variable::count::range::[0, 0]";

        count = 0;
        require(bumpCountIfValueEq1ThenReturn(1, true) || true);
        "pyro::variable::count::range::[1, 1]";

        count = 0;
        require(true || bumpCountIfValueEq1ThenReturn(1, true));
        "pyro::variable::count::range::[0, 0]";
    }

    function yulAndFullCircuit() public {
        count = 0;
        assembly {
            function bumpCountIfValueEq1ThenReturn(x, returnValue) -> result {
                let count_val := sload(0)
                // first if needs both x and count to be 0
                if and(eq(count_val, 0), eq(x, 0)) {
                    // add 1 to count
                    sstore(0, add(sload(0), 1))
                }
                // second if needs both values to be 1
                if and(eq(count_val, 1), eq(x, 1)) {
                    // add 1 to count
                    sstore(0, add(sload(0), 1))
                }
                result := true
            }

            // in yul: rhs is evaluated, then lhs. no short circuiting
            if or(
                bumpCountIfValueEq1ThenReturn(1, true),
                bumpCountIfValueEq1ThenReturn(0, true)
            ) {

            }
        }
        "pyro::variable::count::range::[2, 2]";
    }

    function orFullCircuit() public {
        count = 0;
        // ( bump(false) || bump(true) ) , this will test that the second bump is evaluated since the `or` does not short circuit
        require(
            bumpCountIfValueEq1ThenReturn(1, false) ||
                bumpCountIfValueEq1ThenReturn(1, true)
        );
        "pyro::variable::count::range::[2, 2]";
    }

    function bumpCountIfValueEq1ThenReturn(
        uint8 x,
        bool returnValue
    ) internal returns (bool) {
        if (x == 1) {
            count += 1;
        }
        return returnValue;
    }
}
