use ethers_core::rand::Rng;
use proptest::{
    strategy::{NewTree, Strategy, ValueTree},
    test_runner::TestRunner,
};

use ethers_core::types::U256;

/// Value tree for unsigned ints (up to uint256).
/// This is very similar to [proptest::BinarySearch]
pub struct UintValueTree {
    /// Lower base
    lo: U256,
    /// Current value
    curr: U256,
    /// Higher base
    hi: U256,
    /// If true cannot be simplified or complexified
    fixed: bool,
}

impl UintValueTree {
    /// Create a new tree
    /// # Arguments
    /// * `start` - Starting value for the tree
    /// * `fixed` - If `true` the tree would only contain one element and won't be simplified.
    fn new(start: U256, fixed: bool) -> Self {
        Self { lo: 0.into(), curr: start, hi: start, fixed }
    }

    fn reposition(&mut self) -> bool {
        let interval = self.hi - self.lo;
        let new_mid = self.lo + interval / 2;

        if new_mid == self.curr {
            false
        } else {
            self.curr = new_mid;
            true
        }
    }
}

impl ValueTree for UintValueTree {
    type Value = U256;

    fn current(&self) -> Self::Value {
        self.curr
    }

    fn simplify(&mut self) -> bool {
        if self.fixed || (self.hi <= self.lo) {
            return false
        }

        self.hi = self.curr;
        self.reposition()
    }

    fn complicate(&mut self) -> bool {
        if self.fixed || (self.hi <= self.lo) {
            return false
        }

        self.lo = self.curr + 1;
        self.reposition()
    }
}

pub struct PairValueTree {
    x_tree: UintValueTree,
    y_tree: UintValueTree,
}

impl PairValueTree {
    fn new(x_start: U256, y_start: U256, fixed: bool) -> Self {
        let x_tree = UintValueTree::new(x_start, fixed);
        let y_tree = UintValueTree::new(y_start, fixed);

        Self { x_tree, y_tree }
    }
}

impl ValueTree for PairValueTree {
    type Value = (U256, U256);

    fn current(&self) -> Self::Value {
        (self.x_tree.current(), self.y_tree.current())
    }

    fn simplify(&mut self) -> bool {
        self.x_tree.simplify() || self.y_tree.simplify()
    }

    fn complicate(&mut self) -> bool {
        self.x_tree.complicate() || self.y_tree.complicate()
    }
}

#[derive(Debug)]
pub struct PairStrategy {
    uint_strategy: UintStrategy,
}

impl PairStrategy {
    pub fn new(bits: usize, fixtures: Vec<U256>) -> Self {
        Self {
            uint_strategy: UintStrategy::new(bits, fixtures),
        }
    }

    fn generate_xy(&self, runner: &mut TestRunner) -> NewTree<Self> {
        let x_tree = self.uint_strategy.new_tree(runner)?;
        let y_tree = self.uint_strategy.new_tree(runner)?;

        let x_start = x_tree.current();
        let y_start = y_tree.current();

        if x_start < y_start {
            Ok(PairValueTree::new(x_start, y_start, false))
        } else {
            let new_y_start = x_start + 1;
            Ok(PairValueTree::new(x_start, new_y_start, false))
        }
    }
}

impl Strategy for PairStrategy {
    type Tree = PairValueTree;
    type Value = (U256, U256);

    fn new_tree(&self, runner: &mut TestRunner) -> NewTree<Self> {
        self.generate_xy(runner)
    }
}
