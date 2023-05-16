abstract contract A {
    uint a;
    function foo(uint b) internal {
        if (bar() > 1) {}
        a = b;
    }

    function bar() virtual internal view returns (uint);
}