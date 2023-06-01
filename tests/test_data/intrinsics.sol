contract Intrinsics {
	function strConcat() public {
		string memory a = "aa";
		string memory b = "bb";
		string memory c = string.concat(a, b);
		string memory d = string.concat(a, b, c);
	}

	function bytesConcat() public {
		bytes memory a = hex"aa";
		bytes memory b = hex"bb";
		bytes memory c = bytes.concat(a, b);
		require(c[0] == hex"aa");
		require(c[1] == hex"bb");
		bytes memory d = bytes.concat(a, b, c);
		require(d[0] == hex"aa");
		require(d[1] == hex"bb");
		require(d[2] == hex"aa");
		require(d[3] == hex"bb");

	}

	function yulIntrinsics() public {
        assembly {
            let a := timestamp()
            let b := caller()
            pop(staticcall(0, 0, 0, 0, 0, 0))
            let c := extcodesize(b)
        }
    }


	function blockData() public {
		uint256 fee = block.basefee;
		uint256 chainid = block.chainid;
		address coinbase = block.coinbase;
		uint256 difficulty = block.difficulty;
		uint256 prevrandao = block.prevrandao;
		uint256 gaslimit = block.gaslimit;
		uint256 number = block.number;
		uint256 timestamp = block.timestamp;
		bytes32 hash = blockhash(number);
	}

	function msgData() public {
		bytes memory data = msg.data;
		address sender = msg.sender;
		bytes4 sig = msg.sig;
		uint256 value = msg.value;
	}

	function txData() public {
		uint256 gasprice = tx.gasprice;
		address origin = tx.origin;
		uint256 gasleft = gasleft();
	}

	function asserting() public {
		assert(true);
	}

	function requiring() public {
		require(true, "with string");
		require(true);
	}


	// error A();
	// function revertingWithError() public {
	// 	revert A();
	// }

	// function reverting() public {
	// 	revert();
	// }

	function precompiles() public {
		bytes memory a = hex"aa";
		bytes32 hash = keccak256(a);
		bytes32 shaHash = sha256(a);
		bytes20 ripmdHash = ripemd160(a);
		address recoveredAddr = ecrecover(hash, 1, 2, 3);
		uint256 addMod = addmod(125, 100, 100);
		require(addMod == 25);
		uint256 mulMod = mulmod(125, 100, 100);
		require(mulMod == 25);
	}

	function typeAttrs() public {
		string memory name = type(Other).name;
		// require(name == "Other");

		bytes memory code = type(Other).creationCode;
		bytes memory runtimeCode = type(Other).runtimeCode;

		bytes4 id = type(IOther).interfaceId;
	}

	function uintMinMax() public {
		uint256 max256 = type(uint256).max;
		require(max256 == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
		uint248 max248 = type(uint248).max;
		require(max248 == 2**248 - 1);
		uint240 max240 = type(uint240).max;
		require(max240 == 2**240 - 1);
		uint232 max232 = type(uint232).max;
		require(max232 == 2**232 - 1);
		uint224 max224 = type(uint224).max;
		require(max224 == 2**224 - 1);
		uint216 max216 = type(uint216).max;
		require(max216 == 2**216 - 1);
		uint208 max208 = type(uint208).max;
		require(max208 == 2**208 - 1);
		uint200 max200 = type(uint200).max;
		require(max200 == 2**200 - 1);
		uint192 max192 = type(uint192).max;
		require(max192 == 2**192 - 1);
		uint184 max184 = type(uint184).max;
		require(max184 == 2**184 - 1);
		uint176 max176 = type(uint176).max;
		require(max176 == 2**176 - 1);
		uint168 max168 = type(uint168).max;
		require(max168 == 2**168 - 1);
		uint160 max160 = type(uint160).max;
		require(max160 == 2**160 - 1);
		uint152 max152 = type(uint152).max;
		require(max152 == 2**152 - 1);
		uint144 max144 = type(uint144).max;
		require(max144 == 2**144 - 1);
		uint136 max136 = type(uint136).max;
		require(max136 == 2**136 - 1);
		uint128 max128 = type(uint128).max;
		require(max128 == 2**128 - 1);
		uint120 max120 = type(uint120).max;
		require(max120 == 2**120 - 1);
		uint112 max112 = type(uint112).max;
		require(max112 == 2**112 - 1);
		uint104 max104 = type(uint104).max;
		require(max104 == 2**104 - 1);
		uint96 max96 = type(uint96).max;
		require(max96 == 2**96 - 1);
		uint88 max88 = type(uint88).max;
		require(max88 == 2**88 - 1);
		uint80 max80 = type(uint80).max;
		require(max80 == 2**80 - 1);
		uint72 max72 = type(uint72).max;
		require(max72 == 2**72 - 1);
		uint64 max64 = type(uint64).max;
		require(max64 == 2**64 - 1);
		uint56 max56 = type(uint56).max;
		require(max56 == 2**56 - 1);
		uint48 max48 = type(uint48).max;
		require(max48 == 2**48 - 1);
		uint40 max40 = type(uint40).max;
		require(max40 == 2**40 - 1);
		uint32 max32 = type(uint32).max;
		require(max32 == 2**32 - 1);
		uint24 max24 = type(uint24).max;
		require(max24 == 2**24 - 1);
		uint16 max16 = type(uint16).max;
		require(max16 == 2**16 - 1);
		uint8 max8 = type(uint8).max;
		require(max8 == 2**8 - 1);

		uint256 min256 = type(uint256).min;
		require(min256 == 0);
		uint248 min248 = type(uint248).min;
		require(min248 == 0);
		uint240 min240 = type(uint240).min;
		require(min240 == 0);
		uint232 min232 = type(uint232).min;
		require(min232 == 0);
		uint224 min224 = type(uint224).min;
		require(min224 == 0);
		uint216 min216 = type(uint216).min;
		require(min216 == 0);
		uint208 min208 = type(uint208).min;
		require(min208 == 0);
		uint200 min200 = type(uint200).min;
		require(min200 == 0);
		uint192 min192 = type(uint192).min;
		require(min192 == 0);
		uint184 min184 = type(uint184).min;
		require(min184 == 0);
		uint176 min176 = type(uint176).min;
		require(min176 == 0);
		uint168 min168 = type(uint168).min;
		require(min168 == 0);
		uint160 min160 = type(uint160).min;
		require(min160 == 0);
		uint152 min152 = type(uint152).min;
		require(min152 == 0);
		uint144 min144 = type(uint144).min;
		require(min144 == 0);
		uint136 min136 = type(uint136).min;
		require(min136 == 0);
		uint128 min128 = type(uint128).min;
		require(min128 == 0);
		uint120 min120 = type(uint120).min;
		require(min120 == 0);
		uint112 min112 = type(uint112).min;
		require(min112 == 0);
		uint104 min104 = type(uint104).min;
		require(min104 == 0);
		uint96 min96 = type(uint96).min;
		require(min96 == 0);
		uint88 min88 = type(uint88).min;
		require(min88 == 0);
		uint80 min80 = type(uint80).min;
		require(min80 == 0);
		uint72 min72 = type(uint72).min;
		require(min72 == 0);
		uint64 min64 = type(uint64).min;
		require(min64 == 0);
		uint56 min56 = type(uint56).min;
		require(min56 == 0);
		uint48 min48 = type(uint48).min;
		require(min48 == 0);
		uint40 min40 = type(uint40).min;
		require(min40 == 0);
		uint32 min32 = type(uint32).min;
		require(min32 == 0);
		uint24 min24 = type(uint24).min;
		require(min24 == 0);
		uint16 min16 = type(uint16).min;
		require(min16 == 0);
		uint8 min8 = type(uint8).min;
		require(min8 == 0);
	}

	function addressAttrs() public {
		address tester = address(100);
		uint256 bal = tester.balance;
		bytes memory code = tester.code;
		bytes32 codehash = tester.codehash;
		bool result = tester.send(1);
		tester.transfer(1);
	}
}

contract Other {
	function dummyFunc() public returns (uint256) {
		return 100;
	}
}

interface IOther {
	function dummyFunc() external returns (uint256);
}