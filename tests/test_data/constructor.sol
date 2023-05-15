contract A {
    address a;
    constructor(address _a) {
        a = _a;
    }
}

contract B is A {
    constructor(address _a) A(_a) {}
}

contract C is B {
    constructor(address _a) B(_a) {}
}

contract X {
    address x;
    constructor(address _x) {
        x = _x;
    }
}

abstract contract Y is X {
    constructor(address _x) {} // abstract doesnt need to init bases
}

contract D is Y, C {
    constructor(address _a) Y(_a) X(_a) C(_a) {} // inheriting abstract leads to needing to explicitly init the bases here
}

abstract contract F {
    function foo() public virtual {

    }
}

contract G is F {
    function foo() public override {
        super.foo();
    }
}