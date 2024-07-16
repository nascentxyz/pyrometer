// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

contract Env {
    function msg_sender() public view returns (address) {
        return msg.sender;
    }

    function msg_data() public pure returns (bytes memory) {
        return msg.data;
    }
}
