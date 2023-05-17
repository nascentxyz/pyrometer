abstract contract A {
    uint a;
    function foo(uint b) internal {
        if (bar() > 1) {}
        a = b;
    }

    function bar() virtual internal view returns (uint);
}

abstract contract YInterface {
    function foo() virtual external returns (uint);
}

contract Y is YInterface {
    function foo() virtual override public returns (uint) {
        return 1;
    }

    function bar(Y y) internal {
        y.foo();
    }
}

abstract contract Base {
    function foo() virtual public returns (uint){
        return 0;
    }
}

contract Base2 is Base {}

contract Base3 is Base2 {}

contract Test is Base3 {
    function foo() override public returns (uint){
        return super.foo();
    }
}