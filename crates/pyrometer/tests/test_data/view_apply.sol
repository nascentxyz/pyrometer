// contract Simple {
//     uint x;

//     function viewAdd(uint a, uint b) internal view returns (uint) {
//         return a + b + x;
//     }

//     function nestedViewAdd(uint x, uint y) internal view returns (uint) {
//         return viewAdd(x, y);
//     }

//     function concAdd() internal {
//         require(x < 100);
//         uint q = 100;
//         uint r = 100;
//         uint ret = viewAdd(q, r);
//         "pyro::variable::ret::range::[200,299]";
//         x += 1;
//         uint ret2 = nestedViewAdd(q, r);
//         "pyro::variable::ret2::range::[201,300]";
//     }
// }

contract Mapping {
    mapping(uint => uint) t;

    function viewMap(uint a, uint b) internal view returns (uint) {
        return a + b + t[a];
    }

    function nestedViewMap(uint x, uint y) internal view returns (uint) {
        return viewMap(x, y);
    }

    function concAdd() internal {
        require(t[100] < 100);
        uint q = 100;
        uint r = 100;
        uint ret = viewMap(q, r);
        "pyro::variable::ret::range::[200,299]";
        t[100] += 1;
        uint ret2 = nestedViewMap(q, r);
        "pyro::variable::ret2::range::[201,300]";
    }
}
