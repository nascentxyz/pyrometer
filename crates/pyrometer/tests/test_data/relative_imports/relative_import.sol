import "../env.sol";

contract RelativeImport {
	function deploy() public {
		Env env = Env(address(100));
		env.msg_sender();
	}
}