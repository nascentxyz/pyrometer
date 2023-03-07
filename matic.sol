

contract MaticLike {
    function ecrecovery(bytes32 hash, bytes memory sig)
        public
        pure
        returns (address result)
    {
        bytes32 r;
        bytes32 s;
        uint8 v;
        if (sig.length != 65) {
            return address(0x0);
        }
        
        // *** Assembly not yet supported ***
        // assembly {
        //     r := mload(add(sig, 32))
        //     s := mload(add(sig, 64))
        //     v := and(mload(add(sig, 65)), 255)
        // }

        // https://github.com/ethereum/go-ethereum/issues/2053
        if (v < 27) {
            v += 27;
        }
        if (v != 27 && v != 28) {
            return address(0x0);
        }
        // get address out of hash and signature
        result = ecrecover(hash, v, r, s);
        // ecrecover returns zero on error
        require(result != address(0x0), "Error in ecrecover");
    }

    function transferWithSig(
        bytes calldata sig,
        uint256 amount,
        bytes32 data,
        uint256 expiration,
        address to
    ) external returns (address from) {
        require(amount > 0);
        require(
            expiration == 0 || block.number <= expiration,
            "Signature is expired"
        );

        
        bytes32 dataHash;
        // *** not relevant to this analysis ***
        //  = hashEIP712MessageWithAddress(
        //     hashTokenTransferOrder(msg.sender, amount, data, expiration),
        //     address(this)
        // );

        // require(disabledHashes[dataHash] == false, "Sig deactivated");
        // disabledHashes[dataHash] = true;

        from = ecrecovery(dataHash, sig);
        _transferFrom(from, address(uint160(to)), amount);
    }

    function _transferFrom(address from, address to, uint256 value)
        internal
        returns (bool)
    {
        uint256 input1;// = this.balanceOf(from);
        uint256 input2;// = this.balanceOf(to);
        // _transfer(from, to, value);
        emit LogTransfer(
            token,
            from,
            to,
            value,
            input1,
            input2,
            this.balanceOf(from),
            this.balanceOf(to)
        );
        return true;
    }
}