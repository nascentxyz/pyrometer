

contract FuncCalls {
	address _owner;

	// modifier onlyOwner {
	// 	require(msg.sender == _owner);
	// 	_;
	// }

	function transferOwnership(address newOwner) public virtual  {
        innerRequire(newOwner);
        _transferOwnership(newOwner);
    }

    function innerRequire(address newOwner) public virtual {
    	require(newOwner != address(0), "Ownable: new owner is the zero address");
    }

    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
    }
}
