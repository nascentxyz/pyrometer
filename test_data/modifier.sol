contract Modifier {
	uint256 a;
	modifier Noop() {
		_;
	}

	modifier RequireBefore() {
		require(a == 0);
		_;
	}

	modifier RequireAfter() {
		_;
		require(a == 1);
	}

	modifier Input(uint256 c) {
		require(c == 100);
		a += 1;
		_;
		
	}

	function noop() Noop() {
		a = 100;
	}

	function requireBefore() RequireBefore {
		a += 1;
	}

	function requireAfter() RequireAfter {
		a += 1;
	}

	function input(uint256 b) Input(b) {
		uint256 a = b;
	}

	function input(uint256 b, uint256 c) Input(b) Input(c) {
		uint256 k = b;
	}
}