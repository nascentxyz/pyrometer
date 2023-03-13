<img align="right" width="100" height="100" src="NascentLogo.png">

# Pyrometer



## TODO
- [ ] General
    - [ ] Graceful error handling
    - [ ] Trait/Lang separation cleanup
    - [ ] 
- [ ] Language
    - [ ] Storage
        - [ ] Considering constructor
        - [ ] Considering non-constructor initializer
    - [ ] Functions
        - [ ] Call modifier at start of function analysis
        - [ ] Call modifiers when calling another function from within a function
    - [ ] Considering `unchecked` math
        - [ ] Keep uncheckedness for the entire block
        - [ ] Pass uncheckedness into `bin_op`
    - [ ] Support `assembly`
    - [ ] Support `for` loop
    - [ ] Support `while`/`do while`
    - [ ] Support `++i/i++/--i/i++`
    - [ ] Support low-level call
- [ ] Analyzers
    - [ ] Bound Analyzer
        - [ ] Cleanup CLI output
        - [ ] Fix multiple calls to single function that don't show
    - [ ] Taint Analyzer
    - [ ] Gas Optimization Analyzer
        - [ ] Unchecked Recommendation Analyzer
        - [ ] Storage Variable Initialization Analyzer
    - [ ] Invariant Analyzer
    - [ ] Reentrancy Analyzer
- [ ] Queries
    - [ ] Access Control Querier
        - [ ] Cleanup output
    - [ ] Code Path Querier
- [ ] Long term
    - [ ] GUI for better exploring code execution forks
    - [ ] LSP/IDE integration
    - [ ] DSL for writing queries
    - [ ] Export bounds for SMT solvers (z3, cvc5, etc.)

