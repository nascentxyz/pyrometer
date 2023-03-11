contract Env {
	function msg_sender() public returns (address) {
		return msg.sender;
	}

	function msg_data() public returns (bytes memory) {
		return msg.data;
	}
}