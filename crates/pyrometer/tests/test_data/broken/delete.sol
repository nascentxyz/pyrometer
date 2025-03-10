// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

// Merge into delete.sol when fixed
contract ComplexDelete {
    struct ContactInfo {
        string email;
        string phone;
    }

    struct Address {
        string street;
        string city;
        string country;
        uint256 postalCode;
    }

    struct Employment {
        string company;
        string position;
        uint256 startDate;
        uint256 endDate;
    }

    struct Education {
        string institution;
        string degree;
        uint256 graduationYear;
    }

    struct User {
        uint256 id;
        string name;
        ContactInfo contactInfo;
        Address[] addresses;
        Employment[] employmentHistory;
        Education[] educationHistory;
        mapping(string => bool) preferences;
    }

    mapping(uint256 => User) public users;
    uint256[] public userIds;

    function deleteUserAddress(uint256 userId, uint256 addressIndex) public {
        require(
            addressIndex < users[userId].addresses.length,
            "Address index out of bounds"
        );
        users[userId].addresses[addressIndex] = users[userId].addresses[
            users[userId].addresses.length - 1
        ];
        users[userId].addresses.pop();
    }

    function deleteEmploymentHistory(
        uint256 userId,
        uint256 employmentIndex
    ) public {
        require(
            employmentIndex < users[userId].employmentHistory.length,
            "Employment index out of bounds"
        );
        users[userId].employmentHistory[employmentIndex] = users[userId]
            .employmentHistory[users[userId].employmentHistory.length - 1];
        users[userId].employmentHistory.pop();
    }

    function deleteEducationHistory(
        uint256 userId,
        uint256 educationIndex
    ) public {
        require(
            educationIndex < users[userId].educationHistory.length,
            "Education index out of bounds"
        );
        users[userId].educationHistory[educationIndex] = users[userId]
            .educationHistory[users[userId].educationHistory.length - 1];
        users[userId].educationHistory.pop();
    }
}
