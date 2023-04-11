contract Dummy {}

enum DummyEnum {}

contract Storage {
	mapping (address => uint256) public map;
	mapping (address => mapping ( address => uint256)) public nestedMap;
	uint256[] public arr;
	uint256[][] public nestedArr;

	function setMap(address who) public {
		map[who] = 1000;
		require(map[who] == 1000);
	}

	function setNestedMap(address who, address who2) public {
		nestedMap[who][who2] = 1000;
		require(nestedMap[who][who2] == 1000);
	}

	function setArray(uint256 idx) public {
		arr[idx] = 1000;
		require(arr[idx] == 1000);
	}

	function setNestedArray(uint256 idx, uint256 idx2) public {
		nestedArr[idx][idx2] = 1000;
		require(nestedArr[idx][idx2] == 1000);
	}
}