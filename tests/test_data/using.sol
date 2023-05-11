function x(uint256 x) internal returns (uint256) {
    return x + 20;
}

library MyLib {
    function y(uint256 x) internal returns (uint256) {
        return x + 10;
    }
}

library MyOtherLib {
    function z(uint256 x) internal returns (uint256) {
        return x + 15;
    }
}

library MyOtherOtherLib {
    function w(uint256 x) internal returns (uint256) {
        return x + 30;
    }
}

using MyLib for uint256;

contract UsingMyLib {
    using MyOtherLib for uint256;

    using {x, MyOtherOtherLib.w} for uint256;

    // function a(uint256 y) public returns (uint256) {
    //     return y.z();
    // }

    // function a_conc() public returns (uint256) {
    //     uint256 y = 100;
    //     uint256 ret = y.z();
    //     require(ret == 115);
    //     return ret;
    // }

    // function b(uint256 y) public returns (uint256) {
    //     return y.y();
    // }

    function b_conc() public returns (uint256) {
        uint256 y = 100;
        uint256 ret = y.y();
        require(ret == 110);
        return ret;
    }

    // function c(uint256 y) public returns (uint256) {
    //     return y.w();
    // }

    // function c_conc() public returns (uint256) {
    //     uint256 y = 100;
    //     uint256 ret = y.w();
    //     require(ret == 130);
    //     return ret;
    // }
}
