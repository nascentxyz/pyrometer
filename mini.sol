contract ExponentialNoError {
    function safe32(uint256 n, string memory errorMessage) internal pure returns (uint32) {
        require(n < 2 ** 32, errorMessage);
        return uint32(n);
    }
}

contract ComptrollerV3Storage {
    struct CompMarketState {
        // The market's last updated compBorrowIndex or compSupplyIndex
        uint224 index;
        // The block number the index was last updated at
        uint32 block;
    }

    mapping(address => CompMarketState) public compSupplyState;
    mapping(address => CompMarketState) public compBorrowState;
}

contract ComptrollerV4Storage is ComptrollerV3Storage {}

contract ComptrollerV5Storage is ComptrollerV4Storage {}

contract ComptrollerV6Storage is ComptrollerV5Storage {}

contract ComptrollerV7Storage is ComptrollerV6Storage {}

contract Comptroller is ExponentialNoError, ComptrollerV7Storage {
    uint224 public constant compInitialIndex = 1e36;

    function _initializeMarket(address cToken) internal {
        uint32 blockNumber = safe32(getBlockNumber(), "block number exceeds 32 bits");

        CompMarketState storage supplyState = compSupplyState[cToken];
        CompMarketState storage borrowState = compBorrowState[cToken];

        /*
         * Update market state indices
         */
        if (supplyState.index == 0) {
            // Initialize supply state index with default value
            supplyState.index = compInitialIndex;
        }

        if (borrowState.index == 0) {
            // Initialize borrow state index with default value
            borrowState.index = compInitialIndex;
        }

        /*
         * Update market state block numbers
         */
        supplyState.block = borrowState.block = blockNumber;
    }

    function getBlockNumber() public view virtual returns (uint256) {
        return block.number;
    }
}
