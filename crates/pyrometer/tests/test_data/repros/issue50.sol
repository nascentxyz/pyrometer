abstract contract struct_push {
    struct NFTData {
        string[] comments;
    }

    mapping(uint256 => NFTData) nftList;

    function foo(uint index) public {
        string memory comment = "hello";
        nftList[index].comments.push() = comment;
    }
}