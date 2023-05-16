<img width="100%" src="pyro.jpg">

# 🔥🔫 Pyrometer 🔥🔫

[![Telegram Chat][tg-badge]][tg-url]

[tg-badge]: https://img.shields.io/endpoint?color=neon&logo=telegram&label=chat&style=flat-square&url=https%3A%2F%2Ftg.sumanjay.workers.dev%2Fpyrometer
[tg-url]: https://t.me/pyrometer

Pyrometer is a work-in-progress security tool currently in _BETA_. We are releasing it in its current stage to find contributors and adventurous users (that don't mind when the tool breaks).

Effectively, Pyrometer is a mix of symbolic execution, abstract interpretation, and static analysis - we take ideas from each and apply them with an *engineering first* mindset to create an effective tool (and avoid nerdsnipes by academic papers) aiming to help both auditors and developers.

Pyrometer may eventually be language agnostic, but for now it is targeting Solidity. The code isn't currently entirely structured for multi-language support, but it has some of the bones to be able to support other EVM-targeting languages.

Here is an example output:

<img width="100%" src="demo.png">

## Can I use it today?
Yes\*. There are going to be issues and crashes, see the [TODO](#TODO) below before opening an issue. In general, it doesn't take too long to add a language feature, but actually listing all the features of Solidity hasn't been done to keep track. Right now, Pyrometer shines for analyzing math and access control, but is in rapid development supporting a broader set of use cases. Some of the analyzers listed below would be extremely quick to implement but better language support has been the priority thus far. 

## How can I use it?
First, make sure rust is installed:
```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

Then:
```bash
git clone https://github.com/nascentxyz/pyrometer
cd pyrometer/cli
cargo install --path . --locked
pyrometer <PATH_TO_SOLIDITY_FILE> --help
```

Make sure `$CARGO_HOME/bin` is in your `$PATH`.

Binaries will eventually be built and released for version upgrades.


### Configuring Pyrometer
Run `pyrometer --help` for more details

## How does it work?
See the [Architecture](./ARCHITECTURE.md) page for details. 

## Why does it work?
See the [Theory](./Theory.md) page for details. 

## What can I do with it?


## Understanding the output

You will generally see a line underlined followed by the `∈` symbol followed by  `[ minimum possible value, maximum possible value ]`. `∈` indicates set membership and means "is an element of", and the brackets indicate an *interval* - so for example, if you see:

` "x" ∈ [ 0, 10 ] && ∉ { 5 }`, you can read this as "x is in the range 0 to 10, excluding 5". Each solidity type has their own default bounds. If you see `"x" == 3`, `x` must be 3 at that point in the program.

## Contributing
Read the [Architecture](./ARCHITECTURE.md) page first, then start hacking. Hop in the telegram (see badge above) to ask questions. 

See the [TODO](./TODO.md) for top priorities.

<br/><br/>
<p align="center">
    <img width="100" height="100" src="NascentLogo.png">
</p>
