
interface IERC20 {
    function transfer(address, uint256) returns (bool);
    function transferFrom(address, address, uint256) returns (bool);
}

abstract contract Ownable {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(msg.sender);
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == msg.sender, "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}


abstract contract StakingRewardsFundingBuggy is Ownable {
    uint80 public rewardRate;
    uint40 public lastUpdate;
    uint40 public periodFinish;
    uint96 public totalRewardAdded;
    uint256 public constant periodDuration = 1 days;
    IERC20 public immutable token;

    event RewardRemoved(uint256 reward);
    event RewardAdded(uint256 reward);
    event PeriodDurationUpdated(uint256 newDuration);

    constructor(address rewardsToken) {
        token = IERC20(rewardsToken); // deployer must ensure token reverts on failed transfers
    }

    function setPeriodDuration(uint256 newDuration) external onlyOwner {
        require(block.timestamp >= periodFinish, "ONGOING_PERIOD");
        require(newDuration >= 2 ** 16 + 1, "SHORT_PERIOD_DURATION");
        require(newDuration <= type(uint32).max, "LONG_PERIOD_DURATION");
        emit PeriodDurationUpdated(periodDuration = newDuration);
    }

    function removeReward() external onlyOwner {
        uint256 tmpPeriodFinish = periodFinish;
        uint256 leftover;
        if (tmpPeriodFinish > block.timestamp) {
            unchecked {
                leftover = (tmpPeriodFinish - block.timestamp) * rewardRate;
                totalRewardAdded -= uint96(leftover);
                periodFinish = uint40(block.timestamp);
            }
        }
        token.transfer(msg.sender, leftover);
        emit RewardRemoved(leftover);
    }

    function addReward(uint256 amount) external onlyOwner {
        uint256 tmpPeriodDuration = periodDuration;
        require(amount <= type(uint96).max, "INVALID_AMOUNT");
        unchecked {
            uint256 tmpTotalRewardAdded = totalRewardAdded;
            uint256 newTotalRewardAdded = tmpTotalRewardAdded + amount;
            require(newTotalRewardAdded <= type(uint96).max, "OVERFLOW");
            totalRewardAdded = uint96(newTotalRewardAdded);
        }
        uint256 newRewardRate;
        if (lastUpdate >= periodFinish) {
            unchecked {
                newRewardRate = amount / tmpPeriodDuration;
            }
        } else {
            unchecked {
                uint256 leftover = (periodFinish - lastUpdate) * rewardRate;
                unchecked {
                    newRewardRate = ((amount + leftover) / tmpPeriodDuration);
                }
            }
        }
        require(newRewardRate != 0, "ZERO_REWARD_RATE");
        rewardRate = uint80(newRewardRate); // MIN_PERIOD_DURATION ensures no truncation
        unchecked {
            lastUpdate = uint40(block.timestamp);
            periodFinish = uint40(block.timestamp + tmpPeriodDuration);
        }
        token.transferFrom(msg.sender, address(this), amount);
        emit RewardAdded(amount);
    }

    function _claim() internal returns (uint256 reward) {
        reward = _pendingRewards();
        lastUpdate = uint40(block.timestamp);
    }

    function _pendingRewards() internal view returns (uint256 rewards) {
        uint256 tmpPeriodFinish = periodFinish;
        uint256 lastTimeRewardApplicable =
            tmpPeriodFinish < block.timestamp ? tmpPeriodFinish : block.timestamp;
        uint256 tmpLastUpdate = lastUpdate;
        if (lastTimeRewardApplicable > tmpLastUpdate) {
            unchecked { rewards = (lastTimeRewardApplicable - tmpLastUpdate) * rewardRate; }
        }
    }
}