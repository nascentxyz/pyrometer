// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract Todo {
    // this will live in loops.sol when fixed
    function perform_break_literal() public pure {
        for (uint256 i = 0; i < 10; i++) {
            if (i == 5) {
                break; // @brock this one weirdly does not error on the break
            }
        }
    }

    // this will live in loops.sol when fixed
    function perform_break(uint[] memory a) public pure {
        for (uint256 i = 0; i < a.length; i++) {
            if (i == a[i]) {
                break;
            }
        }
    }

    function try_catch_func_require() public view returns (uint) {
        try T(address(1)).t(0, 101) returns (string memory result) {
            return 2;
        } catch Error(string memory reason) {
            return 1;
        }
    }

    function try_catch_func_assert() public view returns (uint) {
        try T(address(1)).t(0, 101) returns (string memory result) {
            return 2;
        } catch (bytes memory reason) {
            return 1;
        }
    }

    function try_catch_contract_require() public returns (uint) {
        try new T(0, 101) returns (T t) {
            return 2;
        } catch Error(string memory reason)  {
            return 1;
        }
    }

    function try_catch_contract_assert() public returns (uint) {
        try new T(100, 0) returns (T t) {
            return 2;
        } catch (bytes memory reason) {
            return 1;
        }
    }
}

contract T {
    constructor(uint x, uint y) {
        require(x == 100, "fail");
        assert(y == 101);
    }

    function t(uint x, uint y) public {
        require(x == 100, "fail");
        assert(y == 101);
    }
}
