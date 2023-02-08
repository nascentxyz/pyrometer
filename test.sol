pragma solidity 0.8.17;



contract Storage {

    // struct A {
    //     uint256 c;
    //     uint256 d;
    // }

    // A public a;

    uint256 a;
    address owner;
    constructor() {
        owner = msg.sender;
    }

    fallback() returns (uint256) {
        return 1;
    }

    receive() returns (uint256) {
        return 1;
    }

    function set_a(uint256 b) public {
        require(msg.sender == owner);
        a = b;
    }

    // function b5(A memory x) public returns (uint256) {
    //     require(msg.sender == owner);
    //     (a.c, a.d) = b4();
    //     x.d += 10;
    //     x.d += b3(a.c);
    //     return x.d;
    // }

    // function b6(uint256[] memory x) public returns (uint256[] memory) {
    //     require(x.length > 3);
    //     x[6] += 10;
    //     x[6] += 10;
    //     return x;
    // }

    // function b4() internal returns (uint256, uint256) {
    //     return (10, 20);
    // }

    // function b3(uint256 y) internal returns (uint256) {
    //     a.d += 10;
    //     return y + 1;
    // }
}

// contract S {
//     function run() public returns (uint256) {
//         Storage s = new Storage();
//         uint256 a = s.b5(10);
//         return a;
//     }
// }

// contract Baz {

//     bool private state1;
//     bool private state2;
//     bool private state3;
//     bool private state4;
//     bool private state5;

//     function baz(int256 a, int256 b, int256 c) public returns (int256) {
//         int256 d = b + c;

//         //minimize(d < 1 ? 1 - d : 0);
//         //minimize(d < 1 ? 0 : d);
//         if (d < 1) {
//             //minimize(b < 3 ? 3 - b : 0);
//             //minimize(b < 3 ? 0 : b - 2);
//             if (b < 3) {
//                 state1 = true;
//                 return 1;
//             }
//             //minimize(a == 42 ? 1 : 0);
//             //minimize(a == 42 ? 0 : |a - 42|);
//             if (a == 42) {
//                 state2 = true;
//                 return 2;
//             }
    
//             state3 = true;
//             return 3;
//         } else {
//             //minimize(c < 42 ? 42 - c : 0);
//             //minimize(c < 42 ? 0 : c - 41);
//             if (c < 42) {
//                 state4 = true;
//                 return 4;
//             }
//             state5 = true;
//             return 5;
//         }
//     }
// }