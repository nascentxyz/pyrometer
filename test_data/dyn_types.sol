contract DynTypes {
    function bytes_dyn(bytes calldata x) public {
        bytes memory y = x;
        require(x.length < 10);
        y[8] = 0xff;
        require(y.length == 9);
    }

	// function array_dyn(uint256[] calldata x) public {
	// 	uint256[] memory y = x;
	// 	require(x.length < 10);
	// 	y[8] = 100;
	// 	require(y.length == 9);
	// }

	// function nested_bytes_dyn(bytes[] calldata x) public {
	// 	bytes memory a = hex"1337";
	// 	require(x[0] == hex"14");
	// 	require(x.length == 1);
	// }
}

// contract StoragePush {
//     address[] internal owners;

//     constructor() {
//         owners.push(address(0x1));
//         owners.push(address(0x2));
//         owners.push(address(0x3));
//     }
// }

