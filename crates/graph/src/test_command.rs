use crate::nodes::Concrete;
use alloy_primitives::{B256, I256, U256};
use std::str::FromStr;

#[derive(Debug, Clone)]
pub enum TestCommand {
    Variable(String, VariableCommand),
    Constraint(String),
    Coverage(CoverageCommand),
}

#[derive(Debug, Clone)]
pub enum VariableCommand {
    RangeAssert { min: Concrete, max: Concrete },
}

#[derive(Debug, Clone)]
pub enum CoverageCommand {
    OnlyPath,
    Unreachable,
}

pub fn parse_test_command(s: &str) -> Option<TestCommand> {
    let split = s.split("::").collect::<Vec<_>>();
    if split.first().copied() == Some("pyro") {
        match split.get(1).copied() {
            Some("variable") => parse_variable(split),
            Some("constraint") => parse_constraint(split),
            Some("coverage") => parse_coverage(split),
            _ => None,
        }
    } else {
        None
    }
}

pub fn parse_variable(variable: Vec<&str>) -> Option<TestCommand> {
    let name = variable.get(2).copied()?;
    match variable.get(3).copied() {
        Some("range") => parse_range(name, variable),
        _ => None,
    }
}

pub fn parse_range(name: &str, range: Vec<&str>) -> Option<TestCommand> {
    let range = range
        .get(4)
        .copied()?
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect::<String>();
    let range = range
        .trim_start_matches('[')
        .trim_end_matches(']')
        .split(',')
        .collect::<Vec<_>>();
    let mut min_str = *range.first()?;
    let mut min_neg = false;
    if let Some(new_min) = min_str.strip_prefix('-') {
        min_neg = true;
        min_str = new_min;
    }

    let mut max_str = *range.get(1)?;
    let mut max_neg = false;
    if let Some(new_max) = max_str.strip_prefix('-') {
        max_neg = true;
        max_str = new_max;
    }

    let min = parse_input(min_str, min_neg)?;
    let max = parse_input(max_str, max_neg)?;

    Some(TestCommand::Variable(
        name.to_string(),
        VariableCommand::RangeAssert { min, max },
    ))
}

pub fn parse_input(input: &str, negative: bool) -> Option<Concrete> {
    if let Some(res) = input.strip_prefix("0x") {
        // hex
        let mut h = vec![];
        if let Ok(hex_val) = hex::decode(res) {
            h.extend(hex_val)
        }
        let mut target = B256::default();
        let mut max = 0;
        h.iter().enumerate().for_each(|(i, hex_byte)| {
            if *hex_byte != 0x00u8 {
                max = i as u8 + 1;
            }
            target.0[i] = *hex_byte;
        });
        return Some(Concrete::Bytes(max, target));
    }

    if let Some(res) = input.strip_prefix("uint") {
        // uint type
        let size = u16::from_str(
            &res.chars()
                .take_while(|c| c.is_ascii_digit())
                .collect::<String>(),
        )
        .unwrap_or(256);

        if res.strip_suffix("max").is_some() {
            let max = if size == 256 {
                U256::MAX
            } else {
                U256::from(2).pow(U256::from(size)) - U256::from(1)
            };
            return Some(Concrete::from(max));
        }

        if res.strip_suffix("min").is_some() {
            return Some(Concrete::from(U256::ZERO));
        }
        return None;
    }

    if let Some(res) = input.strip_prefix("int") {
        // int type
        let size = u16::from_str(
            &res.chars()
                .take_while(|c| c.is_ascii_digit())
                .collect::<String>(),
        )
        .unwrap_or(256);
        let max = if size == 256u16 {
            I256::MAX
        } else {
            I256::from_raw(U256::from(1u8) << U256::from(size - 1)) - I256::ONE
        };

        if res.strip_suffix("max").is_some() {
            return Some(Concrete::from(max));
        }

        if res.strip_suffix("min").is_some() {
            let min = max * I256::MINUS_ONE - I256::ONE;
            return Some(Concrete::from(min));
        }
        return None;
    }

    let val = U256::from_str_radix(input, 10).ok()?;
    let size: u16 = ((32 - (val.leading_zeros() / 8)) * 8).max(8) as u16;
    if negative {
        let val = if val == U256::from(2).pow(255.try_into().unwrap()) {
            // no need to set upper bit
            I256::from_raw(val)
        } else {
            let raw = I256::from_raw(val);
            if raw < I256::ZERO {
                return None;
            }
            I256::MINUS_ONE * raw
        };
        Some(Concrete::Int(size, val))
    } else {
        Some(Concrete::Uint(size, val))
    }
}

pub fn parse_constraint(constraint: Vec<&str>) -> Option<TestCommand> {
    let constraint = constraint.get(2).copied()?;
    Some(TestCommand::Constraint(constraint.to_string()))
}

pub fn parse_coverage(coverage: Vec<&str>) -> Option<TestCommand> {
    match coverage.get(2).copied() {
        Some("onlyPath") => Some(TestCommand::Coverage(CoverageCommand::OnlyPath)),
        Some("unreachable") => Some(TestCommand::Coverage(CoverageCommand::Unreachable)),
        _ => None,
    }
}
