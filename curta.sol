contract WhatAreBuckets is IPuzzle {
    uint256 public constant PRIMES = 0x20305070b0d1113171d1f25292b2f353b;
    uint256 public constant numPrimes = 17;

    /// @inheritdoc IPuzzle
    function name() external pure returns (string memory) {
        return unicode"what are buckets?";
    }

    function work(uint256 state, uint8 op) internal pure returns (uint256) {
        if (op >> 2 == 0) {
            if ((op & 2) == 2) {
                state <<= 8;
            }
            state &= 0xffffff00ff;
            if ((op & 1) == 1) {
                state |= (state >> 16) & 0xff00;
            }
            if ((op & 2) == 2) {
                state >>= 8;
            }
        } else if ((op & 5) == 4) {
            if ((op & 2) == 2) {
                state = (state & 0xff00ff00) >> 8 | (state & 0x00ff00ff) << 8;
            }
            uint256 flow0 = (state >> 8) & 0xff;
            uint256 flow1 = ((state >> 16) & 0xff) - (state & 0xff);
            uint256 flow = flow0 > flow1 ? flow1 : flow0;
            state -= flow << 8;
            state += flow;
            if ((op & 2) == 2) {
                state = (state & 0xff00ff00) >> 8 | (state & 0x00ff00ff) << 8;
            }
        }
        return state;
    }

    function workAll(uint256 state, uint256 commands) internal pure returns (uint256) {
        for (uint256 i = 0; i < 85; i++) {
            state = work(state, uint8(commands >> (i * 3)) & 7);
        }
        return state;
    }

    /// @inheritdoc IPuzzle
    function generate(address _seed) external pure returns (uint256) {
        uint256 seed = uint256(keccak256(abi.encodePacked(_seed)));
        uint256 tmp = seed;

        uint256 numPairs = numPrimes * (numPrimes - 1);
        while (tmp > 0) {
            uint256 v = tmp % numPairs;
            tmp /= numPairs;
            uint256 a = v % numPrimes;
            uint256 b = v / numPrimes;
            if (b >= a) b += 1;
            uint256 prime1 = (PRIMES >> (a << 3)) & 0xff;
            uint256 prime2 = (PRIMES >> (b << 3)) & 0xff;
            if (
                (prime1 + 1) % prime2 == 0 || (prime2 + 1) % prime1 == 0
                    || (prime1 - 1) % prime2 == 0 || (prime2 - 1) % prime1 == 0
            ) {
                continue;
            }
            return workAll((prime1 << 24) | (prime2 << 16), seed);
        }

        // It's your lucky day!
        return 1;
    }

    /// @inheritdoc IPuzzle
    function verify(uint256 _start, uint256 _solution) external pure returns (bool) {
        return
            workAll(_start, _solution ^ uint256(keccak256(abi.encodePacked(_start)))) & 0xffff == 1;
    }
}