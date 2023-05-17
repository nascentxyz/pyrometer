# Theory

## Solidity Domain

There are four types of range elements:
1. Concrete
2. Dynamic
3. Expression
4. RangeDynamic

A range is composed of a minimum and a maximum, each being one of the range elements.

### Concrete

This is a concrete value, like `1` or `2`. For example:
```solidity
uint256 x = 2;
──────┬──────
      ╰──────── "x" == 2
```

### Dynamic
This is a relational value, like `y`. For example:
```solidity
x = y;
┬
╰── "x" == y
```

Mostly these are evaluated away into concrete range elements.

### Expression

This is a combination of other range elements. For example:
```solidity
x = y + 1;
┬
╰────── "x" == (y + 1)
```

The expression in this example consists of a `Dynamic`, `RangeOp::Add`, and a `Concrete`.

### Range Dynamic

A RangeDynamic consists of a length and a mapping of indices to values of elements. For example:
```solidity
x[1] = y + 1;
──────┬─────
      ╰─────── Memory var "x[1]" == (y + 1)
      │
      ╰─────── Memory var "x" ∈ [ {len: 0, indices: {1: (y + 1)}}, {len: 2**256 - 1, indices: {1: (y + 1)}} ]
```

Here `x[1]` can be treated as the underlying type (`uint256`), so normal solidity semantics work as expected. `x` itself is treated differently and holds a that mapping of indices to values. Range dynamic values are currently unstable and don't always work as expected.

## Solidity to an Interval Domain

### Mapping the Relational Domain to the Interval Domain

Throughout the program we generate *relational* elements - i.e. Dynamic range elements (i.e. `x = y`). While this dynamic relationship is informative, most often the actual interval domain (i.e. `"x" ∈ [ 0, 255 ]`) is more relevant to finding bugs. Using the type system in solidity we can take these relational components and reduce down into a concrete interval or value. By default solidity types have the following intervals:


| Type          | Domain ([min, max])     |
| ------------- | ----------- |
| `address`      | [`[0x00; 20]`,  `[0xff; 20]`] |
| `uint_x`      | [`0`,  `2`<sup>`x`</sup>`- 1`] |
| `int_x`      | [`-2`<sup>`(x-1)`</sup>, `2`<sup>`(x-1)`</sup>`- 1`] |
| `bytes_x`      | [`[0x00; x]`, `[0xff; x]`] |
| `string`      | [`RangeDynamic`, `RangeDynamic`] |
| `bytes `      | [`RangeDynamic`, `RangeDynamic`] |

We can then apply operations on the intervals based on solidity semantics (i.e. `unchecked` or checked math).


### Operations

Operations can be performed between most element types, assuming they are stack elements and not memory elements.

| Range Operation Variant | Operation | Symbol | Element Types Supported |
| ----------- | ----------- | ---- | ---- |
| `RangeOp::Add` | Addition | + | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Mul` | Multiplication | * | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Sub` | Subtraction | - | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Div` | Division | / | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Mod` | Modulos | % | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Min` | Minimum | `min` | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Max` | Maximum | `max` | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Lt` | Less than | < | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Lte` | Less than or equal | <= | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Gt` | Geater than | > | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Gte` | Greater than or equal | >= | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Eq` | Equal | == | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Neq` | Not Equal | != | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Not` | Logical Not | ! | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Shl` | Bitwise shift left | << | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Shr` | Bitwise shift right | >> | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::And` | Logical AND | && | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Or` | Logical OR | \|\| | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Cast` | Cast | `cast` | [`Concrete`, `Dynamic`, `Expression`, `RangeDynamic`] |
| `RangeOp::BitAnd` | Bitwise AND | & | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::BitOr` | Bitwise OR | \| | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::BitXor` | Bitwise XOR | \^ | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::BitNot` | Bitwise NOT | \~ | [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Exp` | Exponentiation | \*\*| [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Concat` | Concatenation | `concat` | [`RangeDynamic`] |

Note that equality operations are within the algebra here and we can use this to generate constraints on variables.

### Constraints

Constraints are added as code is analyzed. They are derived from `require`, `if`, and `assert` statements. Constraints are represented as an expression, like:
```solidity
function a(uint256 x) public {
      if (x < 100) {
            return 100;
      } else {
            return 200;
      }
}
```

results in:
```solidity
constraint: (x < 100) == true

function a(uint256 x) public {
   if (x < 100) {
       ───┬───
          ╰───── "x" ∈ [ 0, 99 ]
     return 100;
     ─────┬────
          ╰────── returns: "100" == 100

}
```

and (the `else` block negates the operation):
```solidity
constraint: (x >= 100) == true

function a(uint256 x) public {
   if (x < 100) {
       ───┬───
          ╰───── "x" ∈ [ 100, 2**256 - 1 ]

     return x;
     ────┬───
         ╰───── returns: "x" ∈ [ 100, 2**256 - 1 ]

}
```

These constraints build up based on the path taken in the code, and can later be used to determine valid inputs to reach a particular path of exeuction.

## Programs as Relational Representations

Fundamentally all programs can be represented as a modification of input variables into output variables. In the EVM, we also have state variables, which from a relational representation standpoint, can just be considered input variables. This has some interesting applications, for example in fuzzing and faster/more percise analysis.


#### Fuzzing
One direction that is being explored is using pyrometer to improve [Foundry's](https://github.com/foundry/foundry-rs) fuzzer. Currently, the fuzzer makes some informed guesses as interesting values by reading the bytecode of your contract, but it has not conception of relations, so a code branch from a statement like `if (x < 1000 - y) { .. }`, may never been reached because the fuzzer lacks sophistication. The current approach being explored leverages the constraints generated by running the tool on a contract. These constraints are then used to generate values which are fed into the fuzzer as function inputs. This should enable significantly improved code coverage.

#### Faster and More Precise Analysis

The tool as it stands today is very fast and precise if the contract it is analyzing has limited recursion, branches, and no looping. Recursion and branching causes the state needed to represent the program to expand exponentially, which slows the program to a halt.  Loops require some complicated logic to analyze correctly, so the tool currently just sets values referenced in the loop to their max interval, which keeps the analysis sound, but loses precision and thus decreases the usefulness of the tool.

Future work will leverage the fact that we can represent loop bodies, function calls, etc., as a transformation of the input. This speed up most aspects of the program, decrease the effect of state exposion (it is still present, but much less memory is needed), and improve precision. For recursive calls and for loops, the tool will "join" the two contexts (the caller context, and the callee context), effectively applying the transformation over the input variables. This will cut down on a significant amount of overhead associated with spinning up a new context and reevaluating the function body with the new inputs, as is currently done.

Since all variables are just constructions of input variables, storage variables, or constants, a "join" is just a number of swap operations and execution of the mathematical representation. For example:
```solidity
function someFunc(uint256 y) public pure returns (uint256) {
      return y + 10;
}
```

This function has a simple representation of its return value of:
```
RangeExpr { lhs: "y", op: RangeOp::Add, rhs: 10}
```

where `y` is a dynamic/relational value referencing the input variable. Now consider this caller function:
```solidity
function someCaller(uint256 first, uint256 second) public pure returns (uint256, uint256) {
      return (someFunc(first), someFunc(second));
}
```
To join these, the tool clones the return expression above, and swaps out the `y` with `first` and another clone with `second` instead of `y`. This operation doesn't have to create a new context, or evaluate `someFunc`'s function body. This can further chain upwards (i.e. `parentFunc <- someCaller <- SomeFunc`. For for loops and recursions, depending on the operations performed as well as branches inside loops, the tool may be able to abstract the expressions, pull out constants, etc to improve precision.

Another future trick that the tool can employ is estimating how much gas a function will consume, and using that to place a limit on the number of loops/recursion possible. This will be slightly unsound due to a mismatch in actual gas/estimated gas, but assuming less gas used than what is reasonably possible, should be sound in most instances (`gasleft()` would remain unaffected by gas estimates most likely).