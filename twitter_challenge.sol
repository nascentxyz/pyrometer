contract test_zero_case {
    // function good0(uint8 v, bytes32 r, bytes32 s, bytes32 hash) external pure returns (bool) {
    //     address signer = ecrecover(hash, v, r, s);
    //     require(signer != address(0), "ECDSA: invalid signature");
    //     return true;
    // }
    // function good1(uint8 v, bytes32 r, bytes32 s, bytes32 hash) external pure returns (bool) {
    //     require(ecrecover(hash, v, r, s) != address(0), "ECDSA: invalid signature");
    //     return true;
    // }
    // function good2(uint8 v, bytes32 r, bytes32 s, bytes32 hash) external pure returns (bool) {
    //     if (ecrecover(hash, v, r, s) != address(0)) {
    //         bool second_pass = good3(v, r, s, hash);
    //         return true;
    //     }


    //     revert("here");
    // }

    // function good3(uint8 v, bytes32 r, bytes32 s, bytes32 hash) external pure returns (bool) {
    //     if (ecrecover(hash, v, r, s) > address(0)) {
    //         return true;
    //     }
    //     return false;
    // }

    // function bad0(uint8 v, bytes32 r, bytes32 s, bytes32 hash) external pure returns (bool) {
    //     address signer = ecrecover(hash, v, r, s);
    //     return true;
    // }
}
