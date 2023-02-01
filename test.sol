contract Storage {
    uint256 c;

    function b5(uint128 x) public returns (uint256) {
        if (x % 2 == 0) {
            x = x / 2;
        } else {
            x = x * 3 + 1;
            require( x % 2 == 0);
        }
        c += x;
        (uint256 a, uint256 b) = x < 5 ? (1 + 2, 5) : (3 + 4, 6);
        a += 1;
        require(a < 10);
        require(b < 8);
        if (x < 7) {
            c += 1;
            c += a;
        } else {
            c += 2;
            c += b;
        }



        return c;
    }
}