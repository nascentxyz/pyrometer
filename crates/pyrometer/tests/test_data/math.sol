// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract Div {
    function div(uint256 x, uint256 y) public pure returns (uint256) {
        return x / y;
    }

    function int_div(int256 x, int256 y) public pure returns (int256) {
        return x / y;
    }

    function div_conc() public pure {
        uint256 a1 = div(100, 1);
        "pyro::variable::a1::range::[100,100]";
        uint256 a2 = div(100, 2);
        "pyro::variable::a2::range::[50,50]";
        uint256 a3 = div(100, 4);
        "pyro::variable::a3::range::[25,25]";
        uint256 a4 = div(100, 8);
        "pyro::variable::a4::range::[12,12]";
        uint256 a5 = div(1000000000, 8);
        "pyro::variable::a5::range::[125000000,125000000]";
        uint256 a6 = div(1000000000, 16);
        "pyro::variable::a6::range::[62500000,62500000]";
        uint256 a7 = div(10000000000, 32);
        "pyro::variable::a7::range::[312500000,312500000]";
        uint256 a8 = div(100000000000000000000, 64);
        "pyro::variable::a8::range::[1562500000000000000,1562500000000000000]";
        uint256 a9 = div(100000000000000000000000000000000000, 128);
        "pyro::variable::a9::range::[781250000000000000000000000000000,781250000000000000000000000000000]";
        uint256 a10 = div(1, 255);
        "pyro::variable::a10::range::[0,0]";
    }

    function int_div_conc() public pure {
        int256 a1 = int_div(100, 1);
        "pyro::variable::a1::range::[100,100]";
        int256 a2 = int_div(100, 2);
        "pyro::variable::a2::range::[50,50]";
        int256 a3 = int_div(100, 4);
        "pyro::variable::a3::range::[25,25]";
        int256 a4 = int_div(100, 8);
        "pyro::variable::a4::range::[12,12]";
        int256 a5 = int_div(1000000000, 8);
        "pyro::variable::a5::range::[125000000,125000000]";
        int256 a6 = int_div(1000000000, 16);
        "pyro::variable::a6::range::[62500000,62500000]";
        int256 a7 = int_div(10000000000, 32);
        "pyro::variable::a7::range::[312500000,312500000]";
        int256 a8 = int_div(100000000000000000000, 64);
        "pyro::variable::a8::range::[1562500000000000000,1562500000000000000]";
        int256 a9 = int_div(100000000000000000000000000000000000, 128);
        "pyro::variable::a9::range::[781250000000000000000000000000000,781250000000000000000000000000000]";
        int256 a10 = int_div(1, 255);
        "pyro::variable::a10::range::[0,0]";

        int256 a11 = int_div(-100, 1);
        "pyro::variable::a11::range::[-100,-100]";
        int256 a12 = int_div(-100, 2);
        "pyro::variable::a12::range::[-50,-50]";
        int256 a13 = int_div(-100, 4);
        "pyro::variable::a13::range::[-25,-25]";
        int256 a14 = int_div(-100, 8);
        "pyro::variable::a14::range::[-12,-12]";
        int256 a15 = int_div(-1000000000, 8);
        "pyro::variable::a15::range::[-125000000,-125000000]";
        int256 a16 = int_div(-1000000000, 16);
        "pyro::variable::a16::range::[-62500000,-62500000]";
        int256 a17 = int_div(-10000000000, 32);
        "pyro::variable::a17::range::[-312500000,-312500000]";
        int256 a18 = int_div(-100000000000000000000, 64);
        "pyro::variable::a18::range::[-1562500000000000000,-1562500000000000000]";
        int256 a19 = int_div(-100000000000000000000000000000000000, 128);
        "pyro::variable::a19::range::[-781250000000000000000000000000000,-781250000000000000000000000000000]";
        int256 a20 = int_div(-1, 255);
        "pyro::variable::a20::range::[0,0]";

        int256 a21 = int_div(-100, -1);
        "pyro::variable::a21::range::[100,100]";
        int256 a22 = int_div(-100, -2);
        "pyro::variable::a22::range::[50,50]";
        int256 a23 = int_div(-100, -4);
        "pyro::variable::a23::range::[25,25]";
        int256 a24 = int_div(-100, -8);
        "pyro::variable::a24::range::[12,12]";
        int256 a25 = int_div(-1000000000, -8);
        "pyro::variable::a25::range::[125000000,125000000]";
        int256 a26 = int_div(-1000000000, -16);
        "pyro::variable::a26::range::[62500000,62500000]";
        int256 a27 = int_div(-10000000000, -32);
        "pyro::variable::a27::range::[312500000,312500000]";
        int256 a28 = int_div(-100000000000000000000, -64);
        "pyro::variable::a28::range::[1562500000000000000,1562500000000000000]";
        int256 a29 = int_div(-100000000000000000000000000000000000, -128);
        "pyro::variable::a29::range::[781250000000000000000000000000000,781250000000000000000000000000000]";
        int256 a30 = int_div(-1, -255);
        "pyro::variable::a30::range::[0,0]";

        int256 a31 = int_div(100, -1);
        "pyro::variable::a31::range::[-100,-100]";
        int256 a32 = int_div(100, -2);
        "pyro::variable::a32::range::[-50,-50]";
        int256 a33 = int_div(100, -4);
        "pyro::variable::a33::range::[-25,-25]";
        int256 a34 = int_div(100, -8);
        "pyro::variable::a34::range::[-12,-12]";
        int256 a35 = int_div(1000000000, -8);
        "pyro::variable::a35::range::[-125000000,-125000000]";
        int256 a36 = int_div(1000000000, -16);
        "pyro::variable::a36::range::[-62500000,-62500000]";
        int256 a37 = int_div(10000000000, -32);
        "pyro::variable::a37::range::[-312500000,-312500000]";
        int256 a38 = int_div(100000000000000000000, -64);
        "pyro::variable::a38::range::[-1562500000000000000,-1562500000000000000]";
        int256 a39 = int_div(100000000000000000000000000000000000, -128);
        "pyro::variable::a39::range::[-781250000000000000000000000000000,-781250000000000000000000000000000]";
        int256 a40 = int_div(1, -255);
        "pyro::variable::a40::range::[0,0]";
    }
}

contract Mul {
    function mul(uint256 x, uint256 y) public pure returns (uint256) {
        return x * y;
    }

    function int_mul(int256 x, int256 y) public pure returns (int256) {
        return x * y;
    }

    function mul_conc() public pure {
        uint256 a1 = mul(100, 1);
        "pyro::variable::a1::range::[100,100]";
        uint256 a2 = mul(100, 2);
        "pyro::variable::a2::range::[200,200]";
        uint256 a3 = mul(100, 4);
        "pyro::variable::a3::range::[400,400]";
        uint256 a4 = mul(100, 8);
        "pyro::variable::a4::range::[800,800]";
        uint256 a5 = mul(1000000000, 8);
        "pyro::variable::a5::range::[8000000000,8000000000]";
        uint256 a6 = mul(1000000000, 16);
        "pyro::variable::a6::range::[16000000000,16000000000]";
        uint256 a7 = mul(10000000000, 32);
        "pyro::variable::a7::range::[320000000000,320000000000]";
        uint256 a8 = mul(100000000000000000000, 64);
        "pyro::variable::a8::range::[6400000000000000000000,6400000000000000000000]";
        uint256 a9 = mul(100000000000000000000000000000000000, 128);
        "pyro::variable::a9::range::[12800000000000000000000000000000000000,12800000000000000000000000000000000000]";
        uint256 a10 = mul(1, 255);
        "pyro::variable::a10::range::[255,255]";
    }

    function int_mul_conc() public pure {
        int256 a1 = int_mul(100, 1);
        "pyro::variable::a1::range::[100,100]";
        int256 a2 = int_mul(100, 2);
        "pyro::variable::a2::range::[200,200]";
        int256 a3 = int_mul(100, 4);
        "pyro::variable::a3::range::[400,400]";
        int256 a4 = int_mul(100, 8);
        "pyro::variable::a4::range::[800,800]";
        int256 a5 = int_mul(1000000000, 8);
        "pyro::variable::a5::range::[8000000000,8000000000]";
        int256 a6 = int_mul(1000000000, 16);
        "pyro::variable::a6::range::[16000000000,16000000000]";
        int256 a7 = int_mul(10000000000, 32);
        "pyro::variable::a7::range::[320000000000,320000000000]";
        int256 a8 = int_mul(100000000000000000000, 64);
        "pyro::variable::a8::range::[6400000000000000000000,6400000000000000000000]";
        int256 a9 = int_mul(100000000000000000000000000000000000, 128);
        "pyro::variable::a9::range::[12800000000000000000000000000000000000,12800000000000000000000000000000000000]";
        int256 a10 = int_mul(1, 255);
        "pyro::variable::a10::range::[255,255]";

        int256 a11 = int_mul(-100, 1);
        "pyro::variable::a11::range::[-100,-100]";
        int256 a12 = int_mul(-100, 2);
        "pyro::variable::a12::range::[-200,-200]";
        int256 a13 = int_mul(-100, 4);
        "pyro::variable::a13::range::[-400,-400]";
        int256 a14 = int_mul(-100, 8);
        "pyro::variable::a14::range::[-800,-800]";
        int256 a15 = int_mul(-1000000000, 8);
        "pyro::variable::a15::range::[-8000000000,-8000000000]";
        int256 a16 = int_mul(-1000000000, 16);
        "pyro::variable::a16::range::[-16000000000,-16000000000]";
        int256 a17 = int_mul(-10000000000, 32);
        "pyro::variable::a17::range::[-320000000000,-320000000000]";
        int256 a18 = int_mul(-100000000000000000000, 64);
        "pyro::variable::a18::range::[-6400000000000000000000,-6400000000000000000000]";
        int256 a19 = int_mul(-100000000000000000000000000000000000, 128);
        "pyro::variable::a19::range::[-12800000000000000000000000000000000000,-12800000000000000000000000000000000000]";
        int256 a20 = int_mul(-1, 255);
        "pyro::variable::a20::range::[-255,-255]";

        int256 a21 = int_mul(-100, -1);
        "pyro::variable::a21::range::[100,100]";
        int256 a22 = int_mul(-100, -2);
        "pyro::variable::a22::range::[200,200]";
        int256 a23 = int_mul(-100, -4);
        "pyro::variable::a23::range::[400,400]";
        int256 a24 = int_mul(-100, -8);
        "pyro::variable::a24::range::[800,800]";
        int256 a25 = int_mul(-1000000000, -8);
        "pyro::variable::a25::range::[8000000000,8000000000]";
        int256 a26 = int_mul(-1000000000, -16);
        "pyro::variable::a26::range::[16000000000,16000000000]";
        int256 a27 = int_mul(-10000000000, -32);
        "pyro::variable::a27::range::[320000000000,320000000000]";
        int256 a28 = int_mul(-100000000000000000000, -64);
        "pyro::variable::a28::range::[6400000000000000000000,6400000000000000000000]";
        int256 a29 = int_mul(-100000000000000000000000000000000000, -128);
        "pyro::variable::a29::range::[12800000000000000000000000000000000000,12800000000000000000000000000000000000]";
        int256 a30 = int_mul(-1, -255);
        "pyro::variable::a30::range::[255,255]";

        int256 a31 = int_mul(100, -1);
        "pyro::variable::a31::range::[-100,-100]";
        int256 a32 = int_mul(100, -2);
        "pyro::variable::a32::range::[-200,-200]";
        int256 a33 = int_mul(100, -4);
        "pyro::variable::a33::range::[-400,-400]";
        int256 a34 = int_mul(100, -8);
        "pyro::variable::a34::range::[-800,-800]";
        int256 a35 = int_mul(1000000000, -8);
        "pyro::variable::a35::range::[-8000000000,-8000000000]";
        int256 a36 = int_mul(1000000000, -16);
        "pyro::variable::a36::range::[-16000000000,-16000000000]";
        int256 a37 = int_mul(10000000000, -32);
        "pyro::variable::a37::range::[-320000000000,-320000000000]";
        int256 a38 = int_mul(100000000000000000000, -64);
        "pyro::variable::a38::range::[-6400000000000000000000,-6400000000000000000000]";
        int256 a39 = int_mul(100000000000000000000000000000000000, -128);
        "pyro::variable::a39::range::[-12800000000000000000000000000000000000,-12800000000000000000000000000000000000]";
        int256 a40 = int_mul(1, -255);
        "pyro::variable::a40::range::[-255,-255]";
    }
}

contract Exp {
    function exp(uint256 x, uint256 y) public pure returns (uint256) {
        return x ** y;
    }

    function int_exp(int256 x, uint256 y) public pure returns (int256) {
        return x ** y;
    }

    function exp_conc() public pure {
        uint256 a1 = exp(0, 0);
        "pyro::variable::a1::range::[1,1]";
        uint256 a2 = exp(0, 1);
        "pyro::variable::a2::range::[0,0]";
        uint256 a3 = exp(100, 4);
        "pyro::variable::a3::range::[100000000,100000000]";
        uint256 a4 = exp(100, 8);
        "pyro::variable::a4::range::[10000000000000000,10000000000000000]";
        uint256 a5 = exp(1000000000, 8);
        require(
            a5 ==
                1000000000000000000000000000000000000000000000000000000000000000000000000
        );
        uint256 a6 = exp(2, 24);
        "pyro::variable::a6::range::[16777216,16777216]";
    }

    function int_exp_conc() public pure {
        int256 a1 = int_exp(-100, 0);
        "pyro::variable::a1::range::[1,1]";
        int256 a2 = int_exp(-100, 2);
        "pyro::variable::a2::range::[10000,10000]";
        int256 a3 = int_exp(-100, 3);
        "pyro::variable::a3::range::[-1000000,-1000000]";
        int256 a4 = int_exp(-100, 8);
        "pyro::variable::a4::range::[10000000000000000,10000000000000000]";
        int256 a5 = int_exp(-2, 23);
        "pyro::variable::a5::range::[-8388608,-8388608]";
    }
}

contract Add {
    function add(uint256 x, uint256 y) public pure returns (uint256) {
        return x + y;
    }

    function int_add(int256 x, int256 y) public pure returns (int256) {
        return x + y;
    }

    function add_conc() public pure {
        uint256 a1 = add(100, 1);
        "pyro::variable::a1::range::[101,101]";
        uint256 a2 = add(100, 2);
        "pyro::variable::a2::range::[102,102]";
        uint256 a3 = add(100, 4);
        "pyro::variable::a3::range::[104,104]";
        uint256 a4 = add(100, 8);
        "pyro::variable::a4::range::[108,108]";
        uint256 a5 = add(1000000000, 8);
        "pyro::variable::a5::range::[1000000008,1000000008]";
        uint256 a6 = add(1000000000, 16);
        "pyro::variable::a6::range::[1000000016,1000000016]";
        uint256 a7 = add(10000000000, 32);
        "pyro::variable::a7::range::[10000000032,10000000032]";
        uint256 a8 = add(100000000000000000000, 64);
        "pyro::variable::a8::range::[100000000000000000064,100000000000000000064]";
        uint256 a9 = add(100000000000000000000000000000000000, 128);
        "pyro::variable::a9::range::[100000000000000000000000000000000128,100000000000000000000000000000000128]";
        uint256 a10 = add(1, 255);
        "pyro::variable::a10::range::[256,256]";
    }

    function int_add_conc() public pure {
        int256 a1 = int_add(100, 1);
        "pyro::variable::a1::range::[101,101]";
        int256 a2 = int_add(100, 2);
        "pyro::variable::a2::range::[102,102]";
        int256 a3 = int_add(100, 4);
        "pyro::variable::a3::range::[104,104]";
        int256 a4 = int_add(100, 8);
        "pyro::variable::a4::range::[108,108]";
        int256 a5 = int_add(1000000000, 8);
        "pyro::variable::a5::range::[1000000008,1000000008]";
        int256 a6 = int_add(1000000000, 16);
        "pyro::variable::a6::range::[1000000016,1000000016]";
        int256 a7 = int_add(10000000000, 32);
        "pyro::variable::a7::range::[10000000032,10000000032]";
        int256 a8 = int_add(100000000000000000000, 64);
        "pyro::variable::a8::range::[100000000000000000064,100000000000000000064]";
        int256 a9 = int_add(100000000000000000000000000000000000, 128);
        "pyro::variable::a9::range::[100000000000000000000000000000000128,100000000000000000000000000000000128]";
        int256 a10 = int_add(1, 255);
        "pyro::variable::a10::range::[256,256]";

        int256 a11 = int_add(-100, 1);
        "pyro::variable::a11::range::[-99,-99]";
        int256 a12 = int_add(-100, 2);
        "pyro::variable::a12::range::[-98,-98]";
        int256 a13 = int_add(-100, 4);
        "pyro::variable::a13::range::[-96,-96]";
        int256 a14 = int_add(-100, 8);
        "pyro::variable::a14::range::[-92,-92]";
        int256 a15 = int_add(-1000000000, 8);
        "pyro::variable::a15::range::[-999999992,-999999992]";
        int256 a16 = int_add(-1000000000, 16);
        "pyro::variable::a16::range::[-999999984,-999999984]";
        int256 a17 = int_add(-10000000000, 32);
        "pyro::variable::a17::range::[-9999999968,-9999999968]";
        int256 a18 = int_add(-100000000000000000000, 64);
        "pyro::variable::a18::range::[-99999999999999999936,-99999999999999999936]";
        int256 a19 = int_add(-100000000000000000000000000000000000, 128);
        "pyro::variable::a19::range::[-99999999999999999999999999999999872,-99999999999999999999999999999999872]";
        int256 a20 = int_add(-1, 255);
        "pyro::variable::a20::range::[254,254]";

        int256 a21 = int_add(-100, -1);
        "pyro::variable::a21::range::[-101,-101]";
        int256 a22 = int_add(-100, -2);
        "pyro::variable::a22::range::[-102,-102]";
        int256 a23 = int_add(-100, -4);
        "pyro::variable::a23::range::[-104,-104]";
        int256 a24 = int_add(-100, -8);
        "pyro::variable::a24::range::[-108,-108]";
        int256 a25 = int_add(-1000000000, -8);
        "pyro::variable::a25::range::[-1000000008,-1000000008]";
        int256 a26 = int_add(-1000000000, -16);
        "pyro::variable::a26::range::[-1000000016,-1000000016]";
        int256 a27 = int_add(-10000000000, -32);
        "pyro::variable::a27::range::[-10000000032,-10000000032]";
        int256 a28 = int_add(-100000000000000000000, -64);
        "pyro::variable::a28::range::[-100000000000000000064,-100000000000000000064]";
        int256 a29 = int_add(-100000000000000000000000000000000000, -128);
        "pyro::variable::a29::range::[-100000000000000000000000000000000128,-100000000000000000000000000000000128]";
        int256 a30 = int_add(-1, -255);
        "pyro::variable::a30::range::[-256,-256]";

        int256 a31 = int_add(100, -1);
        "pyro::variable::a31::range::[99,99]";
        int256 a32 = int_add(100, -2);
        "pyro::variable::a32::range::[98,98]";
        int256 a33 = int_add(100, -4);
        "pyro::variable::a33::range::[96,96]";
        int256 a34 = int_add(100, -8);
        "pyro::variable::a34::range::[92,92]";
        int256 a35 = int_add(1000000000, -8);
        "pyro::variable::a35::range::[999999992,999999992]";
        int256 a36 = int_add(1000000000, -16);
        "pyro::variable::a36::range::[999999984,999999984]";
        int256 a37 = int_add(10000000000, -32);
        "pyro::variable::a37::range::[9999999968,9999999968]";
        int256 a38 = int_add(100000000000000000000, -64);
        "pyro::variable::a38::range::[99999999999999999936,99999999999999999936]";
        int256 a39 = int_add(100000000000000000000000000000000000, -128);
        "pyro::variable::a39::range::[99999999999999999999999999999999872,99999999999999999999999999999999872]";
        int256 a40 = int_add(1, -255);
        "pyro::variable::a40::range::[-254,-254]";
    }
}

contract Sub {
    function sub(uint256 x, uint256 y) public pure returns (uint256) {
        return x - y;
    }

    function int_sub(int256 x, int256 y) public pure returns (int256) {
        return x - y;
    }

    function sub_conc() public pure {
        uint256 a1 = sub(100, 1);
        "pyro::variable::a1::range::[99,99]";
        uint256 a2 = sub(100, 2);
        "pyro::variable::a2::range::[98,98]";
        uint256 a3 = sub(100, 4);
        "pyro::variable::a3::range::[96,96]";
        uint256 a4 = sub(100, 8);
        "pyro::variable::a4::range::[92,92]";
        uint256 a5 = sub(1000000000, 8);
        "pyro::variable::a5::range::[999999992,999999992]";
        uint256 a6 = sub(1000000000, 16);
        "pyro::variable::a6::range::[999999984,999999984]";
        uint256 a7 = sub(10000000000, 32);
        "pyro::variable::a7::range::[9999999968,9999999968]";
        uint256 a8 = sub(100000000000000000000, 64);
        "pyro::variable::a8::range::[99999999999999999936,99999999999999999936]";
        uint256 a9 = sub(100000000000000000000000000000000000, 128);
        "pyro::variable::a9::range::[99999999999999999999999999999999872,99999999999999999999999999999999872]";
    }

    function int_sub_conc() public pure {
        int256 a1 = int_sub(100, 1);
        "pyro::variable::a1::range::[99,99]";
        int256 a2 = int_sub(100, 2);
        "pyro::variable::a2::range::[98,98]";
        int256 a3 = int_sub(100, 4);
        "pyro::variable::a3::range::[96,96]";
        int256 a4 = int_sub(100, 8);
        "pyro::variable::a4::range::[92,92]";
        int256 a5 = int_sub(1000000000, 8);
        "pyro::variable::a5::range::[999999992,999999992]";
        int256 a6 = int_sub(1000000000, 16);
        "pyro::variable::a6::range::[999999984,999999984]";
        int256 a7 = int_sub(10000000000, 32);
        "pyro::variable::a7::range::[9999999968,9999999968]";
        int256 a8 = int_sub(100000000000000000000, 64);
        "pyro::variable::a8::range::[99999999999999999936,99999999999999999936]";
        int256 a9 = int_sub(100000000000000000000000000000000000, 128);
        "pyro::variable::a9::range::[99999999999999999999999999999999872,99999999999999999999999999999999872]";
        int256 a10 = int_sub(1, 255);
        "pyro::variable::a10::range::[-254,-254]";

        int256 a11 = int_sub(-100, 1);
        "pyro::variable::a11::range::[-101,-101]";
        int256 a12 = int_sub(-100, 2);
        "pyro::variable::a12::range::[-102,-102]";
        int256 a13 = int_sub(-100, 4);
        "pyro::variable::a13::range::[-104,-104]";
        int256 a14 = int_sub(-100, 8);
        "pyro::variable::a14::range::[-108,-108]";
        int256 a15 = int_sub(-1000000000, 8);
        "pyro::variable::a15::range::[-1000000008,-1000000008]";
        int256 a16 = int_sub(-1000000000, 16);
        "pyro::variable::a16::range::[-1000000016,-1000000016]";
        int256 a17 = int_sub(-10000000000, 32);
        "pyro::variable::a17::range::[-10000000032,-10000000032]";
        int256 a18 = int_sub(-100000000000000000000, 64);
        "pyro::variable::a18::range::[-100000000000000000064,-100000000000000000064]";
        int256 a19 = int_sub(-100000000000000000000000000000000000, 128);
        "pyro::variable::a19::range::[-100000000000000000000000000000000128,-100000000000000000000000000000000128]";
        int256 a20 = int_sub(-1, 255);
        "pyro::variable::a20::range::[-256,-256]";

        int256 a21 = int_sub(-100, -1);
        "pyro::variable::a21::range::[-99,-99]";
        int256 a22 = int_sub(-100, -2);
        "pyro::variable::a22::range::[-98,-98]";
        int256 a23 = int_sub(-100, -4);
        "pyro::variable::a23::range::[-96,-96]";
        int256 a24 = int_sub(-100, -8);
        "pyro::variable::a24::range::[-92,-92]";
        int256 a25 = int_sub(-1000000000, -8);
        "pyro::variable::a25::range::[-999999992,-999999992]";
        int256 a26 = int_sub(-1000000000, -16);
        "pyro::variable::a26::range::[-999999984,-999999984]";
        int256 a27 = int_sub(-10000000000, -32);
        "pyro::variable::a27::range::[-9999999968,-9999999968]";
        int256 a28 = int_sub(-100000000000000000000, -64);
        "pyro::variable::a28::range::[-99999999999999999936,-99999999999999999936]";
        int256 a29 = int_sub(-100000000000000000000000000000000000, -128);
        "pyro::variable::a29::range::[-99999999999999999999999999999999872,-99999999999999999999999999999999872]";
        int256 a30 = int_sub(-1, -255);
        "pyro::variable::a30::range::[254,254]";

        int256 a31 = int_sub(100, -1);
        "pyro::variable::a31::range::[101,101]";
        int256 a32 = int_sub(100, -2);
        "pyro::variable::a32::range::[102,102]";
        int256 a33 = int_sub(100, -4);
        "pyro::variable::a33::range::[104,104]";
        int256 a34 = int_sub(100, -8);
        "pyro::variable::a34::range::[108,108]";
        int256 a35 = int_sub(1000000000, -8);
        "pyro::variable::a35::range::[1000000008,1000000008]";
        int256 a36 = int_sub(1000000000, -16);
        "pyro::variable::a36::range::[1000000016,1000000016]";
        int256 a37 = int_sub(10000000000, -32);
        "pyro::variable::a37::range::[10000000032,10000000032]";
        int256 a38 = int_sub(100000000000000000000, -64);
        "pyro::variable::a38::range::[100000000000000000064,100000000000000000064]";
        int256 a39 = int_sub(100000000000000000000000000000000000, -128);
        "pyro::variable::a39::range::[100000000000000000000000000000000128,100000000000000000000000000000000128]";
        int256 a40 = int_sub(1, -255);
        "pyro::variable::a40::range::[256,256]";
    }
}

contract AssignMath {
    function assignAdd(uint256 x) public pure {
        x += 10;
    }

    function assignSub(uint256 x) public pure {
        x -= 10;
    }

    function assignDiv(uint256 x) public pure {
        x /= 10;
    }

    function assignMul(uint256 x) public pure {
        x *= 10;
    }

    function preincrement(uint256 x) public pure returns (uint256, uint256) {
        uint256 y = ++x;
        return (y, x);
    }

    function postincrement(uint256 x) public pure returns (uint256, uint256) {
        uint256 y = x++;
        return (y, x);
    }

    function predecrement(uint256 x) public pure returns (uint256, uint256) {
        uint256 y = --x;
        return (y, x);
    }

    function postdecrement(uint256 x) public pure returns (uint256, uint256) {
        uint256 y = x--;
        return (y, x);
    }

    function pre_conc() public pure {
        (uint256 y, uint256 x) = preincrement(100);
        x;
        y;
        "pyro::variable::y::range::[101,101]";
        "pyro::variable::x::range::[101,101]";
    }

    function post_conc() public pure {
        (uint256 y, uint256 x) = postincrement(100);
        x;
        y;
        "pyro::variable::y::range::[100,100]";
        "pyro::variable::x::range::[101,101]";
    }

    function pre_deconc() public pure {
        (uint256 y, uint256 x) = predecrement(100);
        "pyro::variable::y::range::[99,99]";
        "pyro::variable::x::range::[99,99]";
    }

    function post_deconc() public pure {
        (uint256 y, uint256 x) = postdecrement(100);
        "pyro::variable::y::range::[100,100]";
        "pyro::variable::x::range::[99,99]";
    }
}

contract Mod {
    function rmod(uint256 x, uint256 y) public pure returns (uint256) {
        return x % y;
    }

    function rexp(uint256 x, uint256 y) public pure returns (uint256) {
        return x ** y;
    }

    function int_rmod(int256 x, int256 y) public pure returns (int256) {
        return x % y;
    }

    function int_rexp(int256 x, uint256 y) public pure returns (int256) {
        return x ** y;
    }
}

contract Unchecked {
    function assemblyWrappingSub(uint256 a) public pure {
        assembly {
            a := sub(0, 100)
        }
        require(
            a ==
                115792089237316195423570985008687907853269984665640564039457584007913129639836
        );

        int256 y = type(int256).min;
        assembly {
            a := sub(y, 100)
        }
        require(
            a ==
                57896044618658097711785492504343953926634992332820282019728792003956564819868
        );
    }

    function uncheckedSub(uint256 a) public pure {
        unchecked {
            uint t = 0;
            a = t - 100;
        }
        require(
            a ==
                115792089237316195423570985008687907853269984665640564039457584007913129639836
        );

        int256 y = type(int256).min;
        unchecked {
            a = uint(y) - 100;
        }
        require(
            a ==
                57896044618658097711785492504343953926634992332820282019728792003956564819868
        );
    }

    function uncheckedSymbolicSub(uint256 a) public pure {
        unchecked {
            a -= 100;
        }
    }

    function assemblyWrappingAdd(uint256 a) public pure {
        uint256 m = type(uint256).max;
        assembly {
            a := add(m, 100)
        }
        "pyro::variable::a::range::[99,99]";
        a += (type(uint256).max - 99);
        require(a == type(uint256).max);
    }

    function uncheckedAdd(uint256 a) public pure {
        unchecked {
            a = type(uint256).max + 100;
        }
        "pyro::variable::a::range::[99,99]";
        a += (type(uint256).max - 99);
        require(a == type(uint256).max);
    }

    function assemblyWrappingMul(uint256 a) public pure {
        uint256 m = type(uint128).max;
        assembly {
            a := mul(m, m)
        }
        require(
            a ==
                115792089237316195423570985008687907852589419931798687112530834793049593217025
        );
        a /= 3;
        a *= 3;
        // "pyro::variable::a::range::[115792089237316195423570985008687907852589419931798687112530834793049593217025,115792089237316195423570985008687907852589419931798687112530834793049593217025]";
    }

    function uncheckedMul(uint256 a) public pure {
        unchecked {
            a = type(uint256).max + 100;
        }
        "pyro::variable::a::range::[99,99]";
        a += (type(uint256).max - 99);
        require(a == type(uint256).max);
    }

    function symbUncheckedMul(int256 a, int b) public pure {
        unchecked {
            a = a * b;
            int c1 = (a * a) / a;
            int d1 = a * c1 * b;
            d1;
        }
        a = a * b;
        int c = (a * a) / a;
        int d = a * c * b;
        d;
    }

    function asmSymbUncheckedMul(int256 a, int b) public pure {
        assembly {
            a := mul(a, b)
        }
    }
}
