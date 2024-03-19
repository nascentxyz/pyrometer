// Realistically this challenge requires `join` functionality to run in a normal time frame (15 seconds currently)

// uint256 constant ITERS = 20;
// int256 constant ITERS2 = int(ITERS) - 1;

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
        if (i <= 50) {
            bb2();
        }
    }

    function bb2() public {
        i += 1;
        k += 1;
        if (i <= 50) {
            bb1();
        }
    }

    function bb1_f() public {
        require(-1 * int256(i) <= -51);
    }
}