contract Comp {
    struct Checkpoint {
        uint32 fromBlock;
        uint96 votes;
    }

    mapping(address => mapping(uint32 => Checkpoint)) public checkpoints;
    mapping(address => uint32) public numCheckpoints;

    function _moveDelegates(
        address srcRep,
        address dstRep,
        uint96 amount
    ) internal {
        if (amount > 0) {
            uint32 srcRepNum = numCheckpoints[srcRep];
            uint96 srcRepOld = srcRepNum > 0
                ? checkpoints[srcRep][srcRepNum - 1].votes
                : 0;
            uint96 srcRepNew = sub96(
                srcRepOld,
                amount,
                "Comp::_moveVotes: vote amount underflows"
            );
        }
    }

    function sub96(
        uint96 a,
        uint96 b,
        string memory errorMessage
    ) internal pure returns (uint96) {
        require(b <= a, errorMessage);
        return a - b;
    }
}
