// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

/// @notice Library for date time operations.
/// @author Solady (https://github.com/vectorized/solady/blob/main/src/utils/DateTimeLib.sol)
///
/// Conventions:
/// --------------------------------------------------------------------+
/// Unit      | Range                | Notes                            |
/// --------------------------------------------------------------------|
/// timestamp | 0..0x1e18549868c76ff | Unix timestamp.                  |
/// epochDay  | 0..0x16d3e098039     | Days since 1970-01-01.           |
/// year      | 1970..0xffffffff     | Gregorian calendar year.         |
/// month     | 1..12                | Gregorian calendar month.        |
/// day       | 1..31                | Gregorian calendar day of month. |
/// weekday   | 1..7                 | The day of the week (1-indexed). |
/// --------------------------------------------------------------------+
/// All timestamps of days are rounded down to 00:00:00 UTC.
library DateTimeLib {
    /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
    /*                         CONSTANTS                          */
    /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

    // Weekdays are 1-indexed for a traditional rustic feel.

    // "And on the seventh day God finished his work that he had done,
    // and he rested on the seventh day from all his work that he had done."
    // -- Genesis 2:2

    uint256 internal constant MON = 1;
    uint256 internal constant TUE = 2;
    uint256 internal constant WED = 3;
    uint256 internal constant THU = 4;
    uint256 internal constant FRI = 5;
    uint256 internal constant SAT = 6;
    uint256 internal constant SUN = 7;

    // Months and days of months are 1-indexed for ease of use.

    uint256 internal constant JAN = 1;
    uint256 internal constant FEB = 2;
    uint256 internal constant MAR = 3;
    uint256 internal constant APR = 4;
    uint256 internal constant MAY = 5;
    uint256 internal constant JUN = 6;
    uint256 internal constant JUL = 7;
    uint256 internal constant AUG = 8;
    uint256 internal constant SEP = 9;
    uint256 internal constant OCT = 10;
    uint256 internal constant NOV = 11;
    uint256 internal constant DEC = 12;

    // These limits are large enough for most practical purposes.
    // Inputs that exceed these limits result in undefined behavior.

    uint256 internal constant MAX_SUPPORTED_YEAR = 0xffffffff;
    uint256 internal constant MAX_SUPPORTED_EPOCH_DAY = 0x16d3e098039;
    uint256 internal constant MAX_SUPPORTED_TIMESTAMP = 0x1e18549868c76ff;

    /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
    /*                    DATE TIME OPERATIONS                    */
    /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

    /// @dev Returns the number of days since 1970-01-01 from (`year`,`month`,`day`).
    /// See: https://howardhinnant.github.io/date_algorithms.html
    /// Note: Inputs outside the supported ranges result in undefined behavior.
    /// Use {isSupportedDate} to check if the inputs are supported.
    function dateToEpochDay(uint256 year, uint256 month, uint256 day)
        internal
        pure
        returns (uint256 epochDay)
    {
        /// @solidity memory-safe-assembly
        assembly {
            year := sub(year, lt(month, 3))
            let doy := add(shr(11, add(mul(62719, mod(add(month, 9), 12)), 769)), day)
            let yoe := mod(year, 400)
            let doe := sub(add(add(mul(yoe, 365), shr(2, yoe)), doy), div(yoe, 100))
            epochDay := sub(add(mul(div(year, 400), 146097), doe), 719469)
        }
    }

    /// @dev Returns (`year`,`month`,`day`) from the number of days since 1970-01-01.
    /// Note: Inputs outside the supported ranges result in undefined behavior.
    /// Use {isSupportedDays} to check if the inputs is supported.
    function epochDayToDate(uint256 epochDay)
        internal
        pure
        returns (uint256 year, uint256 month, uint256 day)
    {
        /// @solidity memory-safe-assembly
        assembly {
            epochDay := add(epochDay, 719468)
            let doe := mod(epochDay, 146097)
            let yoe :=
                div(sub(sub(add(doe, div(doe, 36524)), div(doe, 1460)), eq(doe, 146096)), 365)
            let doy := sub(doe, sub(add(mul(365, yoe), shr(2, yoe)), div(yoe, 100)))
            let mp := div(add(mul(5, doy), 2), 153)
            day := add(sub(doy, shr(11, add(mul(mp, 62719), 769))), 1)
            month := sub(add(mp, 3), mul(gt(mp, 9), 12))
            year := add(add(yoe, mul(div(epochDay, 146097), 400)), lt(month, 3))
        }
    }

    /// @dev Returns the unix timestamp from (`year`,`month`,`day`).
    /// Note: Inputs outside the supported ranges result in undefined behavior.
    /// Use {isSupportedDate} to check if the inputs are supported.
    function dateToTimestamp(uint256 year, uint256 month, uint256 day)
        internal
        pure
        returns (uint256 result)
    {
        unchecked {
            result = dateToEpochDay(year, month, day) * 86400;
        }
    }

    /// @dev Returns (`year`,`month`,`day`) from the given unix timestamp.
    /// Note: Inputs outside the supported ranges result in undefined behavior.
    /// Use {isSupportedTimestamp} to check if the inputs are supported.
    function timestampToDate(uint256 timestamp)
        internal
        pure
        returns (uint256 year, uint256 month, uint256 day)
    {
        (year, month, day) = epochDayToDate(timestamp / 86400);
    }

    /// @dev Returns the unix timestamp from
    /// (`year`,`month`,`day`,`hour`,`minute`,`second`).
    /// Note: Inputs outside the supported ranges result in undefined behavior.
    /// Use {isSupportedDateTime} to check if the inputs are supported.
    function dateTimeToTimestamp(
        uint256 year,
        uint256 month,
        uint256 day,
        uint256 hour,
        uint256 minute,
        uint256 second
    ) internal pure returns (uint256 result) {
        unchecked {
            result = dateToEpochDay(year, month, day) * 86400 + hour * 3600 + minute * 60 + second;
        }
    }

    /// @dev Returns (`year`,`month`,`day`,`hour`,`minute`,`second`)
    /// from the given unix timestamp.
    /// Note: Inputs outside the supported ranges result in undefined behavior.
    /// Use {isSupportedTimestamp} to check if the inputs are supported.
    function timestampToDateTime(uint256 timestamp)
        internal
        pure
        returns (
            uint256 year,
            uint256 month,
            uint256 day,
            uint256 hour,
            uint256 minute,
            uint256 second
        )
    {
        unchecked {
            (year, month, day) = epochDayToDate(timestamp / 86400);
            uint256 secs = timestamp % 86400;
            hour = secs / 3600;
            secs = secs % 3600;
            minute = secs / 60;
            second = secs % 60;
        }
    }

    /// @dev Returns if the `year` is leap.
    function isLeapYear(uint256 year) internal pure returns (bool leap) {
        /// @solidity memory-safe-assembly
        assembly {
            leap := iszero(and(add(mul(iszero(mod(year, 25)), 12), 3), year))
        }
    }

    /// @dev Returns number of days in given `month` of `year`.
    function daysInMonth(uint256 year, uint256 month) internal pure returns (uint256 result) {
        bool flag = isLeapYear(year);
        /// @solidity memory-safe-assembly
        assembly {
            // `daysInMonths = [31,28,31,30,31,30,31,31,30,31,30,31]`.
            // `result = daysInMonths[month - 1] + isLeapYear(year)`.
            result :=
                add(byte(month, shl(152, 0x1F1C1F1E1F1E1F1F1E1F1E1F)), and(eq(month, 2), flag))
        }
    }

    /// @dev Returns the weekday from the unix timestamp.
    /// Monday: 1, Tuesday: 2, ....., Sunday: 7.
    function weekday(uint256 timestamp) internal pure returns (uint256 result) {
        unchecked {
            result = ((timestamp / 86400 + 3) % 7) + 1;
        }
    }

    /// @dev Returns if (`year`,`month`,`day`) is a supported date.
    /// - `1970 <= year <= MAX_SUPPORTED_YEAR`.
    /// - `1 <= month <= 12`.
    /// - `1 <= day <= daysInMonth(year, month)`.
    function isSupportedDate(uint256 year, uint256 month, uint256 day)
        internal
        pure
        returns (bool result)
    {
        uint256 md = daysInMonth(year, month);
        /// @solidity memory-safe-assembly
        assembly {
            let w := not(0)
            result :=
                and(
                    lt(sub(year, 1970), sub(MAX_SUPPORTED_YEAR, 1969)),
                    and(lt(add(month, w), 12), lt(add(day, w), md))
                )
        }
    }

    /// @dev Returns if (`year`,`month`,`day`,`hour`,`minute`,`second`) is a supported date time.
    /// - `1970 <= year <= MAX_SUPPORTED_YEAR`.
    /// - `1 <= month <= 12`.
    /// - `1 <= day <= daysInMonth(year, month)`.
    /// - `hour < 24`.
    /// - `minute < 60`.
    /// - `second < 60`.
    function isSupportedDateTime(
        uint256 year,
        uint256 month,
        uint256 day,
        uint256 hour,
        uint256 minute,
        uint256 second
    ) internal pure returns (bool result) {
        if (isSupportedDate(year, month, day)) {
            /// @solidity memory-safe-assembly
            assembly {
                result := and(lt(hour, 24), and(lt(minute, 60), lt(second, 60)))
            }
        }
    }

    /// @dev Returns if `epochDay` is a supported unix epoch day.
    function isSupportedEpochDay(uint256 epochDay) internal pure returns (bool result) {
        unchecked {
            result = epochDay < MAX_SUPPORTED_EPOCH_DAY + 1;
        }
    }

    /// @dev Returns if `timestamp` is a supported unix timestamp.
    function isSupportedTimestamp(uint256 timestamp) internal pure returns (bool result) {
        unchecked {
            result = timestamp < MAX_SUPPORTED_TIMESTAMP + 1;
        }
    }

    /// @dev Returns the unix timestamp of the given `n`th weekday `wd`, in `month` of `year`.
    /// Example: 3rd Friday of Feb 2022 is `nthWeekdayInMonthOfYearTimestamp(2022, 2, 3, 5)`
    /// Note: `n` is 1-indexed for traditional consistency.
    /// Invalid weekdays (i.e. `wd == 0 || wd > 7`) result in undefined behavior.
    function nthWeekdayInMonthOfYearTimestamp(uint256 year, uint256 month, uint256 n, uint256 wd)
        internal
        pure
        returns (uint256 result)
    {
        uint256 d = dateToEpochDay(year, month, 1);
        uint256 md = daysInMonth(year, month);
        /// @solidity memory-safe-assembly
        assembly {
            let diff := sub(wd, add(mod(add(d, 3), 7), 1))
            let date := add(mul(sub(n, 1), 7), add(mul(gt(diff, 6), 7), diff))
            result := mul(mul(86400, add(date, d)), and(lt(date, md), iszero(iszero(n))))
        }
    }

    /// @dev Returns the unix timestamp of the most recent Monday.
    function mondayTimestamp(uint256 timestamp) internal pure returns (uint256 result) {
        uint256 t = timestamp;
        /// @solidity memory-safe-assembly
        assembly {
            let day := div(t, 86400)
            result := mul(mul(sub(day, mod(add(day, 3), 7)), 86400), gt(t, 345599))
        }
    }

    /// @dev Returns whether the unix timestamp falls on a Saturday or Sunday.
    /// To check whether it is a week day, just take the negation of the result.
    function isWeekEnd(uint256 timestamp) internal pure returns (bool result) {
        result = weekday(timestamp) > FRI;
    }

    /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
    /*              DATE TIME ARITHMETIC OPERATIONS               */
    /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

    /// @dev Adds `numYears` to the unix timestamp, and returns the result.
    /// Note: The result will share the same Gregorian calendar month,
    /// but different Gregorian calendar years for non-zero `numYears`.
    /// If the Gregorian calendar month of the result has less days
    /// than the Gregorian calendar month day of the `timestamp`,
    /// the result's month day will be the maximum possible value for the month.
    /// (e.g. from 29th Feb to 28th Feb)
    function addYears(uint256 timestamp, uint256 numYears) internal pure returns (uint256 result) {
        (uint256 year, uint256 month, uint256 day) = epochDayToDate(timestamp / 86400);
        result = _offsetted(year + numYears, month, day, timestamp);
    }

    /// @dev Adds `numMonths` to the unix timestamp, and returns the result.
    /// Note: If the Gregorian calendar month of the result has less days
    /// than the Gregorian calendar month day of the `timestamp`,
    /// the result's month day will be the maximum possible value for the month.
    /// (e.g. from 29th Feb to 28th Feb)
    function addMonths(uint256 timestamp, uint256 numMonths)
        internal
        pure
        returns (uint256 result)
    {
        (uint256 year, uint256 month, uint256 day) = epochDayToDate(timestamp / 86400);
        month = _sub(month + numMonths, 1);
        result = _offsetted(year + month / 12, _add(month % 12, 1), day, timestamp);
    }

    /// @dev Adds `numDays` to the unix timestamp, and returns the result.
    function addDays(uint256 timestamp, uint256 numDays) internal pure returns (uint256 result) {
        result = timestamp + numDays * 86400;
    }

    /// @dev Adds `numHours` to the unix timestamp, and returns the result.
    function addHours(uint256 timestamp, uint256 numHours) internal pure returns (uint256 result) {
        result = timestamp + numHours * 3600;
    }

    /// @dev Adds `numMinutes` to the unix timestamp, and returns the result.
    function addMinutes(uint256 timestamp, uint256 numMinutes)
        internal
        pure
        returns (uint256 result)
    {
        result = timestamp + numMinutes * 60;
    }

    /// @dev Adds `numSeconds` to the unix timestamp, and returns the result.
    function addSeconds(uint256 timestamp, uint256 numSeconds)
        internal
        pure
        returns (uint256 result)
    {
        result = timestamp + numSeconds;
    }

    /// @dev Subtracts `numYears` from the unix timestamp, and returns the result.
    /// Note: The result will share the same Gregorian calendar month,
    /// but different Gregorian calendar years for non-zero `numYears`.
    /// If the Gregorian calendar month of the result has less days
    /// than the Gregorian calendar month day of the `timestamp`,
    /// the result's month day will be the maximum possible value for the month.
    /// (e.g. from 29th Feb to 28th Feb)
    function subYears(uint256 timestamp, uint256 numYears) internal pure returns (uint256 result) {
        (uint256 year, uint256 month, uint256 day) = epochDayToDate(timestamp / 86400);
        result = _offsetted(year - numYears, month, day, timestamp);
    }

    /// @dev Subtracts `numYears` from the unix timestamp, and returns the result.
    /// Note: If the Gregorian calendar month of the result has less days
    /// than the Gregorian calendar month day of the `timestamp`,
    /// the result's month day will be the maximum possible value for the month.
    /// (e.g. from 29th Feb to 28th Feb)
    function subMonths(uint256 timestamp, uint256 numMonths)
        internal
        pure
        returns (uint256 result)
    {
        (uint256 year, uint256 month, uint256 day) = epochDayToDate(timestamp / 86400);
        uint256 yearMonth = _totalMonths(year, month) - _add(numMonths, 1);
        result = _offsetted(yearMonth / 12, _add(yearMonth % 12, 1), day, timestamp);
    }

    /// @dev Subtracts `numDays` from the unix timestamp, and returns the result.
    function subDays(uint256 timestamp, uint256 numDays) internal pure returns (uint256 result) {
        result = timestamp - numDays * 86400;
    }

    /// @dev Subtracts `numHours` from the unix timestamp, and returns the result.
    function subHours(uint256 timestamp, uint256 numHours) internal pure returns (uint256 result) {
        result = timestamp - numHours * 3600;
    }

    /// @dev Subtracts `numMinutes` from the unix timestamp, and returns the result.
    function subMinutes(uint256 timestamp, uint256 numMinutes)
        internal
        pure
        returns (uint256 result)
    {
        result = timestamp - numMinutes * 60;
    }

    /// @dev Subtracts `numSeconds` from the unix timestamp, and returns the result.
    function subSeconds(uint256 timestamp, uint256 numSeconds)
        internal
        pure
        returns (uint256 result)
    {
        result = timestamp - numSeconds;
    }

    /// @dev Returns the difference in Gregorian calendar years
    /// between `fromTimestamp` and `toTimestamp`.
    /// Note: Even if the true time difference is less than a year,
    /// the difference can be non-zero is the timestamps are
    /// from diffrent Gregorian calendar years
    function diffYears(uint256 fromTimestamp, uint256 toTimestamp)
        internal
        pure
        returns (uint256 result)
    {
        toTimestamp - fromTimestamp;
        (uint256 fromYear,,) = epochDayToDate(fromTimestamp / 86400);
        (uint256 toYear,,) = epochDayToDate(toTimestamp / 86400);
        result = _sub(toYear, fromYear);
    }

    /// @dev Returns the difference in Gregorian calendar months
    /// between `fromTimestamp` and `toTimestamp`.
    /// Note: Even if the true time difference is less than a month,
    /// the difference can be non-zero is the timestamps are
    /// from diffrent Gregorian calendar months.
    function diffMonths(uint256 fromTimestamp, uint256 toTimestamp)
        internal
        pure
        returns (uint256 result)
    {
        toTimestamp - fromTimestamp;
        (uint256 fromYear, uint256 fromMonth,) = epochDayToDate(fromTimestamp / 86400);
        (uint256 toYear, uint256 toMonth,) = epochDayToDate(toTimestamp / 86400);
        result = _sub(_totalMonths(toYear, toMonth), _totalMonths(fromYear, fromMonth));
    }

    /// @dev Returns the difference in days between `fromTimestamp` and `toTimestamp`.
    function diffDays(uint256 fromTimestamp, uint256 toTimestamp)
        internal
        pure
        returns (uint256 result)
    {
        result = (toTimestamp - fromTimestamp) / 86400;
    }

    /// @dev Returns the difference in hours between `fromTimestamp` and `toTimestamp`.
    function diffHours(uint256 fromTimestamp, uint256 toTimestamp)
        internal
        pure
        returns (uint256 result)
    {
        result = (toTimestamp - fromTimestamp) / 3600;
    }

    /// @dev Returns the difference in minutes between `fromTimestamp` and `toTimestamp`.
    function diffMinutes(uint256 fromTimestamp, uint256 toTimestamp)
        internal
        pure
        returns (uint256 result)
    {
        result = (toTimestamp - fromTimestamp) / 60;
    }

    /// @dev Returns the difference in seconds between `fromTimestamp` and `toTimestamp`.
    function diffSeconds(uint256 fromTimestamp, uint256 toTimestamp)
        internal
        pure
        returns (uint256 result)
    {
        result = toTimestamp - fromTimestamp;
    }

    /*´:°•.°+.*•´.*:˚.°*.˚•´.°:°•.°•.*•´.*:˚.°*.˚•´.°:°•.°+.*•´.*:*/
    /*                      PRIVATE HELPERS                       */
    /*.•°:°.´+˚.*°.˚:*.´•*.+°.•°:´*.´•*.•°.•°:°.´:•˚°.*°.˚:*.´+°.•*/

    /// @dev Unchecked arithmetic for computing the total number of months.
    function _totalMonths(uint256 numYears, uint256 numMonths)
        private
        pure
        returns (uint256 total)
    {
        unchecked {
            total = numYears * 12 + numMonths;
        }
    }

    /// @dev Unchecked arithmetic for adding two numbers.
    function _add(uint256 a, uint256 b) private pure returns (uint256 c) {
        unchecked {
            c = a + b;
        }
    }

    /// @dev Unchecked arithmetic for subtracting two numbers.
    function _sub(uint256 a, uint256 b) private pure returns (uint256 c) {
        unchecked {
            c = a - b;
        }
    }

    /// @dev Returns the offsetted timestamp.
    function _offsetted(uint256 year, uint256 month, uint256 day, uint256 timestamp)
        private
        pure
        returns (uint256 result)
    {
        uint256 dm = daysInMonth(year, month);
        if (day >= dm) {
            day = dm;
        }
        result = dateToEpochDay(year, month, day) * 86400 + (timestamp % 86400);
    }
}

// contract Apron {
//     uint256 k;
//     uint256 i;
//     function entry() public returns (uint256, uint256) {
//         k = 0;
//         i = 0;
//         bb1();
//         return (i, k);
//     }

//     function bb1() public {
//         bb1_t();
//         bb1_f();
//     }

//     function bb1_t() public {
//         if (i <= 99) {
//             bb2();
//         }
//     }

//     function bb2() public {
//         i += 1;
//         k += 1;
//         if (i <= 99) {
//             bb1();
//         }
//     }

//     function bb1_f() public {
//         require(-1 * int256(i) <= -100);
//     }
// }

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
