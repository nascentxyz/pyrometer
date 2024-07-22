contract Variable {
    aUserType a_user_type;

    struct aUserType {
        uint aUserType;
    }

    function a_user_type_memory(
        aUserType memory a_user_type
    ) public returns (uint) {
        return a_user_type.aUserType;
    }

    function a_user_type_calldata(
        aUserType calldata a_user_type
    ) public returns (uint) {
        return a_user_type.aUserType;
    }

    function a_user_type_storage() public returns (uint) {
        aUserType storage a_user_type = a_user_type;
        return a_user_type.aUserType;
    }
}

contract C {
    C c;

    function return_contract() external returns (C) {
        // c is of type Contract::C
        c = C(address(this));
        return c;
    }
}
