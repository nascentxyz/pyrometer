

contract FuncCalls {
	address _owner;

	modifier onlyOwner {
		require(msg.sender == _owner);
		_;
	}

	function transferOwnership(address newOwner) public virtual  {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    function _transferOwnership(address newOwner) internal virtual onlyOwner {
        address oldOwner = _owner;
        _owner = newOwner;
    }
}
