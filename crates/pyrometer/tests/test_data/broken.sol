pragma solidity ^0.8.0;

/////// This block of code will live in variable.sol when fixed ///////////
contract B {
    struct A {
        address a;
    }
}

contract A is B {
    A a; // contract A

    function return_struct() external returns (A memory) {
        // a is of type B.A, *not* Contract::A
        a = A(address(this));
        return a;
    }
}

//////////////////////////////////////////////////////////////

///////// This whole contract will live in require_with_killed.sol when fixed ///////////
// Note: I've added broken@brock comments to the issues i know of
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

/////////////////////////////////////////////////////////////////

////// This contract's functions will be merged into delete.sol when fixed ///////////
contract ComplexDelete {
    struct ContactInfo {
        string email;
        string phone;
    }

    struct Address {
        string street;
        string city;
        string country;
        uint256 postalCode;
    }

    struct Employment {
        string company;
        string position;
        uint256 startDate;
        uint256 endDate;
    }

    struct Education {
        string institution;
        string degree;
        uint256 graduationYear;
    }

    struct User {
        uint256 id;
        string name;
        ContactInfo contactInfo;
        Address[] addresses;
        Employment[] employmentHistory;
        Education[] educationHistory;
        mapping(string => bool) preferences;
    }

    mapping(uint256 => User) public users;
    uint256[] public userIds;

    function deleteUserAddress(uint256 userId, uint256 addressIndex) public {
        require(
            addressIndex < users[userId].addresses.length,
            "Address index out of bounds"
        );
        users[userId].addresses[addressIndex] = users[userId].addresses[
            users[userId].addresses.length - 1
        ];
        users[userId].addresses.pop();
    }

    function deleteEmploymentHistory(
        uint256 userId,
        uint256 employmentIndex
    ) public {
        require(
            employmentIndex < users[userId].employmentHistory.length,
            "Employment index out of bounds"
        );
        users[userId].employmentHistory[employmentIndex] = users[userId]
            .employmentHistory[users[userId].employmentHistory.length - 1];
        users[userId].employmentHistory.pop();
    }

    function deleteEducationHistory(
        uint256 userId,
        uint256 educationIndex
    ) public {
        require(
            educationIndex < users[userId].educationHistory.length,
            "Education index out of bounds"
        );
        users[userId].educationHistory[educationIndex] = users[userId]
            .educationHistory[users[userId].educationHistory.length - 1];
        users[userId].educationHistory.pop();
    }
}
/////////////////////////////////////////////////////////////////
