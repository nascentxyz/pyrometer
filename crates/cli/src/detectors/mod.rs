use pyrometer::detector::{Detector, DetectorResult};
use pyrometer::Analyzer;
use pyrometer::reporter::{ReportFormat, get_reporter};

pub mod my_detector;
pub mod second_detector;

// Import other detector modules here

pub fn get_all_detectors() -> Vec<Box<dyn Detector>> {
    vec![
        Box::new(my_detector::MyDetector),
        Box::new(second_detector::SecondDetector),
        // Add more detectors here as you create them
        // Box::new(your_detector::YourDetector),
        // Box::new(his_detector::HisDetector),
    ]
}

pub fn find_detector(name: &str) -> Option<Box<dyn Detector>> {
    get_all_detectors().into_iter().find(|d| d.name() == name)
}

pub fn run_detectors(analyzer: &Analyzer, detector_names: &[String]) -> Vec<DetectorResult> {
    let mut results = Vec::new();

    for name in detector_names {
        if let Some(detector) = find_detector(name) {
            results.extend(detector.run(analyzer));
        } else {
            println!("Unknown detector: {}", name);
        }
    }

    results
}

pub fn report_results(results: &[DetectorResult], format: ReportFormat) {
    let reporter = get_reporter(format);
    reporter.report(results);
}