// returns 42
function freePure() pure returns (uint8) {
    return 42;
}

// takes a function and returns that same function
function freeHigherOrder(
    function() pure returns (uint8) func
) pure returns (
    function() pure returns (uint8)
) {
    return func;
}

// calls higher order which takes a function then returns it
// then that function returns 42
function freePureCaller() pure returns (uint8) {
    return freeHigherOrder(freePure)();
}

contract Funcs {
    // calls the function that calls higher order which takes
    // a function then returns it then that function returns 42
    function callInternal() external pure returns (uint8) {
        return freePureCaller();
    }

    // takes an external function and returns it
    function externalPure(
        function() external returns (uint8) func
    ) public pure returns (
        function() external returns (uint8)
    ) {
        return func;
    }

    // takes an external function, passes it to an external
    // function which returns the original external function
    // then calls it
    function callExternalPure(
        function() external pure returns (uint8) func
    ) external returns (uint8) {
        return externalPure(func)();
    }
}

contract A {
    // returns 69
    function a() external pure returns (uint8) {
        return 69;
    }
}

contract B {
    // takes an external function and returns it
    function b(
        function() external pure returns (uint8) a
    ) public pure returns (
        function() external pure returns (uint8)
    ) {
        return a;
    }
}

contract C {
    // takes an external function and an external function
    // that takes an external function and returns it
    function c(
        function() external pure returns (uint8) a,
        function(
            function() external pure returns (uint8)
        ) external pure returns (
            function() external pure returns (uint8)
        ) b
    ) external pure returns (
        function() external pure returns (uint8)
    ) {
        return b(a);
    }
}

contract D {
    // takes an external function, an external function that
    // takes an external function and returns it, and an
    // external function that takes an external function and
    // an external function that takes an external function
    // and returns it
    // then calls the original external function, returning 69
    function d(
        function() external pure returns (uint8) a,
        function(
            function() external pure returns (uint8)
        ) external pure returns (
            function() external pure returns (uint8)
        ) b,
        function(
            function() external pure returns (uint8),
            function(
                function() external pure returns (uint8)
            ) external pure returns (
                function() external pure returns (uint8)
            )
        ) external pure returns (
            function() external pure returns (uint8)
        ) c
    ) external pure returns (uint8) {
        return c(a, b)();
    }
}

contract E is D, C, B, A {
    // takes an external function, an external function that
    // takes an external function and returns it, and an
    // external function that takes an external function and
    // an external function that takes an external function
    // and returns it
    // then calls the original external function, returning 69
    function eval() external returns (uint8) {
        this.a();
        this.b(this.a);
        this.c(this.a, this.b);
        return this.d(this.a, this.b, this.c);
    }
}