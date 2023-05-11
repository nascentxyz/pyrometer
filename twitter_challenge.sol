contract Apron {
    uint256 k;
    uint256 i;
    function entry() public returns (uint256, uint256) {
        k = 0;
        i = 0;
        bb1();
        return (i, k);
    }

    function bb1() public {
        bb1_t();
        bb1_f();
    }

    function bb1_t() public {
        if (i <= 99) {
            bb2();
        }
    }

    function bb2() public {
        i += 1;
        k += 1;
        if (i <= 99) {
            bb1();
        }
    }

    function bb1_f() public {
        require(-1 * int256(i) <= -100);
    }
}

// contract constant_fold {
//     function getSqrtRatioAtTick(uint256 y) internal pure returns (uint256[] memory) {
//         uint256[] memory x = new uint256[](1);
//         x[1] = y + 1;
//         return x;
//     }
// }

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

    // struct TokenStream {
    //     uint256 lastCumulativeRewardPerToken;
    //     uint256 virtualBalance;
    //     // tokens is amount (uint112) scaled by 10**18 (which fits in 2**64), so 112 + 64 == 176.
    //     uint224 tokens;
    //     uint32 lastUpdate;
    //     uint224 rewards;
    //     bool merkleAccess;
    // }

    // /// @dev Stream start time
    // uint32 private immutable startTime;
    // /// @dev Length of stream
    // uint32 private immutable streamDuration;

    // /// @dev End of stream
    // uint32 private immutable endStream;
    // uint256 private cumulativeRewardPerToken;
    // uint256 public totalVirtualBalance;

    // uint112 private immutable depositScale;
    // uint112 private immutable rewardScale;

    // function lastApplicableTime() internal view returns (uint32) {
    //     if (block.timestamp <= endStream) {
    //         if (block.timestamp <= startTime) {
    //             return startTime;
    //         } else {
    //             if (block.timestamp == 0) {
    //                 return 100;
    //             } else {
    //                 return uint32(block.timestamp);    
    //             }
    //         }
    //     } else {
    //         return endStream;
    //     }
    // }

    // uint32 public lastUpdate;
    // uint112 private rewardTokenAmount;

    // mapping(address => TokenStream) public tokenStreamForAccount;

    // function rewardPerToken() public view returns (uint256) {
    //     if (totalVirtualBalance == 0) {
    //         return cumulativeRewardPerToken;
    //     } else {
    //         // ∆time*rewardTokensPerSecond*oneDepositToken / totalVirtualBalance
    //         uint256 rewardsPerToken;
    //         // Safety:
    //         //  1. lastApplicableTime has the same bounds as lastUpdate for minimum, current, and max
    //         //  2. lastApplicableTime() - lastUpdate guaranteed to be <= streamDuration
    //         //  3. streamDuration*rewardTokenAmount*depositDecimalOne is guaranteed to not overflow in `fundStream`
    //         //  4. streamDuration and totalVirtualBalance guaranteed to not be 0
    //         // NOTE: this causes rounding down. This leaves a bit of dust in the contract
    //         // because when we do rewardDelta calculation for users, its basically (currUnderestimateRPT - storedUnderestimateRPT)
    //         unchecked {
    //             uint256 rewardsOverTime = (uint256(lastApplicableTime() - lastUpdate) * normalizeRewardTokenAmt(rewardTokenAmount)) / streamDuration;
    //             rewardsPerToken = rewardsOverTime / totalVirtualBalance;
    //         }
    //         return cumulativeRewardPerToken + rewardsPerToken;
    //     }
    // }

    // function normalizeRewardTokenAmt(uint256 _rewardTokens) public view returns (uint224) {
    //     // 2**112 * 2**112 always fits in a 2**224
    //     unchecked { return uint224(_rewardTokens * rewardScale); }
    // }

    // function normalizeDepositTokenAmt(uint256 _depositTokens) public view returns (uint224) {
    //     // 2**112 * 2**112 always fits in a 2**224
    //     unchecked { return uint224(_depositTokens * depositScale); }
    // }

    // function denormalizeRewardTokenAmt(uint256 _rewardTokens) public view returns (uint112) {
    //     unchecked { return uint112(_rewardTokens / rewardScale); }
    // }

    // function denormalizeDepositTokenAmt(uint256 _depositTokens) public view returns (uint112) {
    //     unchecked { return uint112(_depositTokens / depositScale); }
    // }

    // function getEarned(address who) external view returns (uint256) {
    //     TokenStream storage ts = tokenStreamForAccount[who];
    //     return earned(ts, rewardPerToken()) / 10**18;
    // }

    // function earned(TokenStream storage ts, uint256 currCumRewardPerToken) internal view returns (uint224) {
    //     uint256 rewardDelta;
    //     // Safety:
    //     //  1. currCumRewardPerToken - ts.lastCumulativeRewardPerToken: currCumRewardPerToken will always be >= ts.lastCumulativeRewardPerToken
    //     unchecked {
    //         rewardDelta = currCumRewardPerToken - ts.lastCumulativeRewardPerToken;
    //     }

    //     // TODO: Think more about the bounds on ts.virtualBalance. This mul may be able to be unchecked?
    //     // NOTE: This can cause small rounding issues that will leave dust in the contract
    //     // virtualBalance is 
    //     uint224 reward = uint224(normalizeDepositTokenAmt(ts.virtualBalance) * rewardDelta / normalizeDepositTokenAmt(1));
    //     return reward + ts.rewards;
    // }

// }
