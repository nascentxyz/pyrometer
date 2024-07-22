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
        users[userId].addresses.push(Address(street, city, country, postalCode));
    }

    function addEmploymentHistory(
        uint256 userId,
        string memory company,
        string memory position,
        uint256 startDate,
        uint256 endDate
    ) public {
        users[userId].employmentHistory.push(Employment(company, position, startDate, endDate));
    }

    function addEducationHistory(
        uint256 userId,
        string memory institution,
        string memory degree,
        uint256 graduationYear
    ) public {
        users[userId].educationHistory.push(Education(institution, degree, graduationYear));
    }

    function setUserPreference(uint256 userId, string memory key, bool value) public {
        users[userId].preferences[key] = value;
    }

    function deleteUser(uint256 userId) public {
        require(users[userId].id != 0, "User does not exist");
        delete users[userId];
        for (uint256 i = 0; i < userIds.length; i++) {
            if (userIds[i] == userId) {
                userIds[i] = userIds[userIds.length - 1];
                userIds.pop();
                break;
            }
        }
    }

    function deleteUserAddress(uint256 userId, uint256 addressIndex) public {
        require(addressIndex < users[userId].addresses.length, "Address index out of bounds");
        users[userId].addresses[addressIndex] = users[userId].addresses[users[userId].addresses.length - 1];
        users[userId].addresses.pop();
    }

    function deleteEmploymentHistory(uint256 userId, uint256 employmentIndex) public {
        require(employmentIndex < users[userId].employmentHistory.length, "Employment index out of bounds");
        users[userId].employmentHistory[employmentIndex] = users[userId].employmentHistory[users[userId].employmentHistory.length - 1];
        users[userId].employmentHistory.pop();
    }

    function deleteEducationHistory(uint256 userId, uint256 educationIndex) public {
        require(educationIndex < users[userId].educationHistory.length, "Education index out of bounds");
        users[userId].educationHistory[educationIndex] = users[userId].educationHistory[users[userId].educationHistory.length - 1];
        users[userId].educationHistory.pop();
    }

    function deleteUserPreference(uint256 userId, string memory key) public {
        delete users[userId].preferences[key];
    }

    function updateContactInfo(uint256 userId, string memory newEmail, string memory newPhone) public {
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
}