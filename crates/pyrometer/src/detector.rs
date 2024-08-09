use crate::Analyzer;
use serde::{Deserialize, Serialize};
use solang_parser::pt::Loc;

/// Represents the severity of an issue detected in the code.
///
/// The severity levels are ordered from least to most severe:
/// Informational < Low < Medium < High
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Severity {
    /// Informational issues are not problematic but might be of interest.
    Informational,
    /// Low severity issues pose minimal risk.
    Low,
    /// Medium severity issues pose moderate risk and should be addressed.
    Medium,
    /// High severity issues pose significant risk and require attention.
    High,
}

/// Indicates the level of confidence in the accuracy of a detected issue.
///
/// The confidence levels are ordered from least to most certain:
/// Low < Medium < High < Certain
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Confidence {
    /// Low confidence suggests a high chance of false positives.
    Low,
    /// Medium confidence indicates a moderate level of certainty.
    Medium,
    /// High confidence suggests a low chance of false positives.
    High,
    /// Certain confidence indicates that the issue is definitely present.
    Certain,
}

/// Represents the result of a detector finding an issue in the code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectorResult {
    /// The name or title of the detected issue.
    pub issue_name: String,
    /// The name of the detector that found the issue.
    pub detector_name: String,
    /// The location in the source code where the issue was detected.
    pub location: Loc,
    /// A detailed description of the detected issue.
    pub message: String,
    /// A list of details about the issue.
    // pub details: Vec<DetectorDetail>,
    /// The severity level of the detected issue.
    pub severity: Severity,
    /// The confidence level in the accuracy of the detected issue.
    pub confidence: Confidence,
}


impl DetectorResult {}

pub struct DetectorDetail {
    pub loc: Loc,
    pub description: String,
}

/// Defines the interface for implementing a code pattern detector.
pub trait Detector {
    /// Returns the name of the detector.
    fn name(&self) -> &'static str;

    /// Provides a description of what the detector looks for.
    fn description(&self) -> String;

    /// Returns the severity level of issues found by this detector.
    fn severity(&self) -> Severity;

    /// Returns the confidence level of issues found by this detector.
    fn confidence(&self) -> Confidence;

    /// Executes the detector on the provided analyzer and returns a list of detected issues.
    ///
    /// # Arguments
    ///
    /// * `analyzer` - A reference to the Analyzer containing the code to be analyzed.
    ///
    /// # Returns
    ///
    /// A vector of `DetectorResult` instances, each representing a detected issue.
    fn run(&self, analyzer: &Analyzer) -> Vec<DetectorResult>;
}
