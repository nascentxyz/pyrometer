<img width="100%" src="pyro.jpg">

# 🔥🔫 Pyrometer 🔥🔫

[![Telegram Chat][tg-badge]][tg-url]

[tg-badge]: https://img.shields.io/endpoint?color=neon&logo=telegram&label=chat&style=flat-square&url=https%3A%2F%2Ftg.sumanjay.workers.dev%2Fpyrometer
[tg-url]: https://t.me/pyrometer

Pyrometer is a work-in-progress security tool currently in _BETA_. It should work on most solidity `0.8.x` contracts, but there are some limitations and language edge cases not yet covered.

Effectively, Pyrometer is a mix of symbolic execution, abstract interpretation, and static analysis - we take ideas from each and apply them with an *engineering first* mindset to create an effective tool (and avoid nerdsnipes by academic papers) aiming to help both auditors and developers.

Pyrometer may eventually be language agnostic, but for now it is targeting Solidity. The code isn't currently entirely structured for multi-language support, but it has some of the bones to be able to support other EVM-targeting languages.

Here is an example output:

<img width="100%" src="demo.png">


## Installing
First, make sure rust is installed:
```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

Then:
```bash
git clone https://github.com/nascentxyz/pyrometer
cd pyrometer/crates/cli
cargo install --path . --locked
pyrometer <PATH_TO_SOLIDITY_FILE> --help
```

If your project imports contracts via `node_modules` or uses remappings, be sure to pass the `--remappings remappings.txt` flag after running `forge remappings > remappings.txt`.

Make sure `$CARGO_HOME/bin` is in your `$PATH`.


Binaries will eventually be built and released for version upgrades.

### Configuring Pyrometer
Run `pyrometer --help` for more details.

### Quick tips
1. `pyrometer ./myContract.sol --remappings remappings.txt`: the `--remappings` flag is generally needed otherwise you will get a crash with `file does not exist`.
1. `pyrometer ./myContract.sol -vv`: `-vv` is generally the sweet spot in terms of verbosity
1. `pyrometer ./myContract.sol --funcs "myFunc"`: the `--funcs` flag can help narrow the down the output to only the function you care about. You can repeat the flag as many times as you like to match more functions
1. `pyrometer ./myContract.sol --contracts "myContract"`: the `--contracts` flag can help narrow the down the output to only the contract you care about. You can repeat the flag as many times as you like to match more functions

## What can I do with it?

There are two main uses of pyrometer as it stands *today*. 

### As a binary
The target users of the binary (i.e. the CLI application) are developers and auditors. A suggested use case is for manual verification of a function or functions. A video tutorial around getting the most out of pyrometer is in the works. 

### As a library
Pyrometer's graph intermediate representation and bound analysis can be useful for a whole host of solidity based tooling. It could be used as:
1. Backend to an LSP (although not recommend yet)
2. Contract visualization tool (we already support outputting the graph to `dot` via the `--dot` flag)
3. Improved fuzzers (work in progress, reach out if interested in helping)
4. Backend to a query language for writing analyses (analyses similar to Slither detectors)
5. Code refactoring/preprocessor tool

## Understanding the output

You will generally see a line underlined followed by the `∈` symbol followed by  `[ minimum possible value, maximum possible value ]`. `∈` indicates set membership and means "is an element of", and the brackets indicate an *interval* - so for example, if you see:

` "x" ∈ [ 0, 10 ] && ∉ { 5 }`, you can read this as "x is in the range 0 to 10, excluding 5". Each solidity type has their own default bounds. If you see `"x" == 3`, `x` must be 3 at that point in the program.

## Whats the theory behind this?
See the [Theory](./THEORY.md) page for details. 

## How is the repo structured?
See the [Architecture](./ARCHITECTURE.md) page for details. 

## Contributing
Read the [Architecture](./ARCHITECTURE.md) page first, then start hacking. Hop in the telegram (see badge above) to ask questions. 

See the [TODO](./TODO.md) for top priorities.

<br/><br/>
<p align="center">
    <img width="100" height="100" src="NascentLogo.png">
</p>
