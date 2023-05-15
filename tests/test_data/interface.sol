contract A {
    B b;
    constructor(B _b) {
        b = _b;
    }
}

interface B {
    function foo(uint bar) external pure returns (uint8);
}