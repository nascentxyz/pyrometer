// SPDX-License-Identifier: MIT or APACHE2
pragma solidity ^0.8.0;

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

    function addUser(
        uint256 id,
        string memory name,
        string memory email,
        string memory phone
    ) public {
        require(users[id].id == 0, "User already exists");
        User storage newUser = users[id];
        newUser.id = id;
        newUser.name = name;
        newUser.contactInfo = ContactInfo(email, phone);
        userIds.push(id);
    }

    function addUserAddress(
        uint256 userId,
        string memory street,
        string memory city,
        string memory country,
        uint256 postalCode
    ) public {
        users[userId].addresses.push(
            Address(street, city, country, postalCode)
        );
    }

    function addEmploymentHistory(
        uint256 userId,
        string memory company,
        string memory position,
        uint256 startDate,
        uint256 endDate
    ) public {
        users[userId].employmentHistory.push(
            Employment(company, position, startDate, endDate)
        );
    }

    function addEducationHistory(
        uint256 userId,
        string memory institution,
        string memory degree,
        uint256 graduationYear
    ) public {
        users[userId].educationHistory.push(
            Education(institution, degree, graduationYear)
        );
    }

    function setUserPreference(
        uint256 userId,
        string memory key,
        bool value
    ) public {
        users[userId].preferences[key] = value;
    }

    function deleteUser(uint256 userId) public {
        require(users[userId].id != 0, "User does not exist");
        delete users[userId];
        for (uint256 i = 0; i < userIds.length; i++) {
            if (userIds[i] == userId) {
                userIds[i] = userIds[userIds.length - 1];
                userIds.pop();
            }
        }
    }

    function deleteUserPreference(uint256 userId, string memory key) public {
        delete users[userId].preferences[key];
    }

    function updateContactInfo(
        uint256 userId,
        string memory newEmail,
        string memory newPhone
    ) public {
        users[userId].contactInfo = ContactInfo(newEmail, newPhone);
    }

    function clearAllUserAddresses(uint256 userId) public {
        delete users[userId].addresses;
    }

    function clearAllEmploymentHistory(uint256 userId) public {
        delete users[userId].employmentHistory;
    }

    function clearAllEducationHistory(uint256 userId) public {
        delete users[userId].educationHistory;
    }

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

contract UseComplexDelete {
    ComplexDelete t;

    constructor() {
        t = new ComplexDelete();
    }

    function useIt() public {
        // Add users
        t.addUser(1, "Alice", "alice@example.com", "1234567890");
        t.addUser(2, "Bob", "bob@example.com", "0987654321");

        // Add addresses
        t.addUserAddress(1, "123 Main St", "New York", "USA", 10001);
        t.addUserAddress(1, "456 Elm St", "Los Angeles", "USA", 90001);
        t.addUserAddress(2, "789 Oak St", "Chicago", "USA", 60601);

        // Add employment history
        t.addEmploymentHistory(
            1,
            "TechCorp",
            "Developer",
            1609459200,
            1640995200
        );
        t.addEmploymentHistory(1, "WebSoft", "Senior Developer", 1641081600, 0);
        t.addEmploymentHistory(2, "DataFirm", "Analyst", 1577836800, 0);

        // Add education history
        t.addEducationHistory(
            1,
            "Tech University",
            "BSc Computer Science",
            2020
        );
        t.addEducationHistory(2, "Data College", "MSc Data Science", 2019);

        // Set preferences
        t.setUserPreference(1, "receiveNewsletter", true);
        t.setUserPreference(1, "darkMode", false);
        t.setUserPreference(2, "receiveNewsletter", false);

        // Test deletions and updates

        // Delete an address
        t.deleteUserAddress(1, 0); // TODO @brock these need uncommented when the pop is fixed and these functions are back

        // Delete employment history
        t.deleteEmploymentHistory(1, 0); // TODO @brock these need uncommented when the pop is fixed and these functions are back

        // Delete education history
        t.deleteEducationHistory(2, 0); // TODO @brock these need uncommented when the pop is fixed and these functions are back

        // Delete user preference
        t.deleteUserPreference(1, "darkMode");

        // Update contact info
        t.updateContactInfo(2, "bob.new@example.com", "1122334455");

        // Clear all addresses for a user
        t.clearAllUserAddresses(1);

        // Clear all employment history for a user
        t.clearAllEmploymentHistory(2);

        // Clear all education history for a user
        t.clearAllEducationHistory(1);

        // Delete an entire user
        t.deleteUser(1);

        // Add a new user to test after deletions
        t.addUser(3, "Charlie", "charlie@example.com", "5556667777");
        t.addUserAddress(3, "321 Pine St", "San Francisco", "USA", 94101);
    }
}
