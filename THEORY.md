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

Here `x[1]` can be treated as the underlying type (`uint256`), so normal solidity semantics work as expected. `x` itself is treated differently and holds a that mapping of indices to values 

### Solidity to an Interval Domain

| Type          | Domain ([min, max])     |
| ------------- | ----------- |
| `address`      | [`[0x00; 20]`,  `[0xff; 20]`] |
| `uint_x`      | [`0`,  `2`<sup>`x`</sup>`- 1`] |
| `int_x`      | [`-2`<sup>`(x-1)`</sup>, `2`<sup>`(x-1)`</sup>`- 1`] |
| `bytes_x`      | [`[0x00; x]`, `[0xff; x]`] |
| `string`      | [`RangeDynamic`, `RangeDynamic`] |
| `bytes `      | [`RangeDynamic`, `RangeDynamic`] |



### Operations

Operations can be performed between most element types, assuming they are a stack element and not a memory element.

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
| `RangeOp::Exp` | Exponentiation | \*\*| [`Concrete`, `Dynamic`, `Expression`] |
| `RangeOp::Concat` | Concatenation | `concat` | [`RangeDynamic`] |


### Mapping the Relational Domain to the Interval Domain

Throughout the program we generate *relational* elements - i.e. Dynamic range elements (i.e. `x = y`). While this dynamic relationship is often informative, most often the actual interval domain (i.e. `"x" ∈ [ 0, 255 ]`) is more relevant. 
