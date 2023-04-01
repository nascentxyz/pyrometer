import "@relative/relative_import.sol";

contract RemappingImport {
	function deploy() public {
		Env env = Env(address(100));
		env.msg_sender();
	}
}