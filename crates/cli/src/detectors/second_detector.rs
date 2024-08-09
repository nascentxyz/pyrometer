// crates/cli/src/detectors/second_detector.rs
use pyrometer::detector::{Detector, DetectorResult, Severity, Confidence};
use pyrometer::Analyzer;

pub struct SecondDetector;

impl Detector for SecondDetector {
    fn name(&self) -> &'static str {
        "SecondDetector"
    }

    fn description(&self) -> String {
        "Detects a second pattern in the code".to_string()
    }

    fn severity(&self) -> Severity {
        Severity::Medium
    }

    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }

    fn run(&self, analyzer: &Analyzer) -> Vec<DetectorResult> {
        // Implement detection logic here
        vec![]
    }
}