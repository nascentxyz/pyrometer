// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract DynTypes {
    // uint256[] storeVar;

    struct Strukt {
        uint256 a;
        uint256 b;
    }

    mapping(address => Strukt) public someMapping;

    // mapping(address => Strukt[]) public someMapping2;

    // function memory_alias(uint[] memory x) public pure {
    //     uint[] memory y = x;
    //     uint[] memory z = y;
    //     z[0] = 0x11;
    //     "pyro::variable::z[0]::range::[17,17]";
    //     "pyro::variable::y[0]::range::[17,17]";
    //     "pyro::variable::x[0]::range::[17,17]";
    // }

    // function bytes_dyn(bytes memory x) public pure {
    //     bytes memory y = x;
    //     require(x.length < 10);
    //     "pyro::variable::x.length::range::[0,9]";
    //     y[8] = 0xff;
    //     "pyro::variable::y[8]::range::[0xff,0xff]";
    //     // TODO: "pyro::variable::y.length::range::[9,9]";
    // }

    // function array_dyn(uint256[] memory x) public pure {
    //     x[0] = 5;
    //     require(x.length < 10);
    //     "pyro::variable::x.length::range::[1,9]";
    //     uint256[] memory y = x;
    //     y[8] = 100;
    //     "pyro::variable::y[8]::range::[100,100]";
    //     // TODO: "pyro::variable::y.length::range::[9,9]";
    // }

    // function nested_bytes_dyn(bytes[] memory x, uint y) public pure {
    //     bytes memory a = hex"1337";
    //     x[0] = a;
    //     x[0][0];
    //     "pyro::variable::x[0][0]::range::[0x13,0x13]";
    //     x[y] = hex"1122";
    //     uint256 z = y - 1;
    //     bytes1 tmp = x[z + 1][0];
    //     bytes1 tmp2 = x[z + 1][1];
    //     "pyro::variable::tmp::range::[0x11,0x11]";
    //     "pyro::variable::tmp2::range::[0x22,0x22]";
    // }

    // function array_push(uint256 x) public {
    //     // require(x > 5);
    //     storeVar.push(x);
    //     storeVar.push(x);
    //     storeVar.push(x);
    //     // TODO: handle this better
    //     require(storeVar[0] == x);
    //     storeVar.push(x);
    //     require(storeVar[1] == x);
    //     uint256 y = storeVar[storeVar.length - 1];
    //     storeVar.pop();
    //     require(y == x);
    // }

    // function indexInto() public view returns (uint256) {
    //     return storeVar[basicFunc()];
    // }

    // function basicFunc() public pure returns (uint256) {
    //     return 1;
    // }

    function indexIntoMapping(address who) public {
        Strukt storage a = someMapping[who];
        Strukt storage b = someMapping[who];
        a.a = 100;
        "pyro::variable::a.a::range::[100,100]";
        "pyro::variable::b.a::range::[100,100]";

        a.b = 200;
        "pyro::variable::a.b::range::[200,200]";
        "pyro::variable::b.b::range::[200,200]";

        uint tmp = someMapping[who].a;
        "pyro::variable::tmp::range::[100,100]";
        tmp = a.b;
        "pyro::variable::tmp::range::[200,200]";
        tmp = someMapping[who].b;
        "pyro::variable::tmp::range::[200,200]";

        b.a = 300;
        "pyro::variable::b.a::range::[300,300]";
        "pyro::variable::a.a::range::[300,300]";
        tmp = someMapping[who].a;
        "pyro::variable::tmp::range::[300,300]";
    }

    // address[] t;

    // function inLoop(address holder, address[] memory tokens) public pure {
    //     address[] memory h = new address[](1);
    //     h[0] = holder;
    //     inLoop(h, tokens);
    // }

    // function inLoop(address[] memory holders, address[] memory) public pure {
    //     for (uint j = 0; j < holders.length; j++) {
    //         address holder = holders[j];
    //         holder;
    //     }
    // }

    // struct DontUseMoreThanOnce {
    //     uint256 a;
    //     uint256 b;
    // }

    // function dynUserType() public pure {
    //     DontUseMoreThanOnce[] memory dont = new DontUseMoreThanOnce[](1);
    //     dont[0].a = 100;
    //     dont[0].b = 100;
    //     require(dont[0].a == 100);
    // }

    // function getReturnedUserType() public pure {
    //     // Strukt[] memory strukt = returnUserType()[0];
    //     Strukt memory strukt = returnUserType()[0];
    //     require(strukt.a == 100);
    // }

    // function returnUserType() public pure returns (Strukt[] memory) {
    //     Strukt[] memory strukt = new Strukt[](1);
    //     strukt[0].a = 100;
    //     strukt[0].b = 100;
    //     return strukt;
    // }

    // function multiDimensionalArray() public pure returns (bool z) {
    //     uint256[][] memory multiArray = new uint256[][](2);
    //     uint256[] memory indices = new uint256[](2);

    //     indices[0] = 0;
    //     indices[1] = 1;

    //     for (uint i = 0; i < multiArray.length; i++) {
    //         multiArray[i] = new uint256[](2);
    //         for (uint j = 0; j < multiArray[i].length; j++) {
    //             multiArray[i][j] = 1;
    //         }
    //     }

    //     z = true;
    // }
}
