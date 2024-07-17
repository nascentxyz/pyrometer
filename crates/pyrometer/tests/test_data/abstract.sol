// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

abstract contract A {
    uint a;

    function foo(uint b) internal {
        if (bar() > 1) {}
        a = b;
    }

    function bar() internal view virtual returns (uint);
}

// abstract contract YInterface {
//     function foo() external virtual returns (uint);
// }

// contract Y is YInterface {
//     function foo() public virtual override returns (uint) {
//         return 1;
//     }

//     function bar(Y y) internal {
//         y.foo();
//     }
// }

// abstract contract Base {
//     function foo() public virtual returns (uint) {
//         return 0;
//     }
// }

// contract Base2 is Base {}

// contract Base3 is Base2 {}

// contract Test is Base3 {
//     function foo() public override returns (uint) {
//         return super.foo();
//     }
// }
