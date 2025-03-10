// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract Env {
    function msg_sender() public view returns (address) {
        return msg.sender;
    }

    function msg_data() public pure returns (bytes memory) {
        return msg.data;
    }

    function testBlock() public payable {
        /*
        blockhash(uint blockNumber) returns (bytes32): hash of the given block - only works for 256 most recent blocks
        blobhash(uint index) returns (bytes32): versioned hash of the index-th blob associated with the current transaction. A versioned hash consists of a single byte representing the version (currently 0x01), followed by the last 31 bytes of the SHA256 hash of the KZG commitment (EIP-4844).
        block.basefee (uint): current block’s base fee (EIP-3198 and EIP-1559)
        block.blobbasefee (uint): current block’s blob base fee (EIP-7516 and EIP-4844)
        block.chainid (uint): current chain id
        block.coinbase (address payable): current block miner’s address
        block.difficulty (uint): current block difficulty (EVM < Paris). For other EVM versions it behaves as a deprecated alias for block.prevrandao that will be removed in the next breaking release
        block.gaslimit (uint): current block gaslimit
        block.number (uint): current block number
        block.prevrandao (uint): random number provided by the beacon chain (EVM >= Paris) (see EIP-4399 )
        block.timestamp (uint): current block timestamp in seconds since Unix epoch
        gasleft() returns (uint256): remaining gas
        msg.data (bytes): complete calldata
        msg.sender (address): sender of the message (current call)
        msg.sig (bytes4): first four bytes of the calldata (i.e. function identifier)
        msg.value (uint): number of wei sent with the message
        tx.gasprice (uint): gas price of the transaction
        tx.origin (address): sender of the transaction (full call chain)
        */
        bytes32 a = blockhash(1);
        uint c = block.basefee;
        uint e = block.chainid;
        address payable f = block.coinbase;
        uint g = block.difficulty;
        uint h = block.gaslimit;
        uint i = block.number;
        uint j = block.prevrandao;
        uint k = block.timestamp;
        uint l = gasleft();
        bytes memory m = msg.data;
        address n = msg.sender;
        bytes4 o = msg.sig;
        uint p = msg.value;
        uint q = tx.gasprice;
        address r = tx.origin;
    }
}
