use crate::detector::{Confidence, DetectorResult, Severity};
use colored::*;

pub trait DetectorResultReporter {
    fn report(&self, results: &[DetectorResult]);
}

pub enum ReportFormat {
    Markdown,
    Json,
    Stdout,
}

pub struct MarkdownReporter;
pub struct JsonReporter;
pub struct StdoutReporter;

pub fn get_reporter(format: ReportFormat) -> Box<dyn DetectorResultReporter> {
    match format {
        ReportFormat::Markdown => Box::new(MarkdownReporter),
        ReportFormat::Json => Box::new(JsonReporter),
        ReportFormat::Stdout => Box::new(StdoutReporter),
    }
}

impl DetectorResultReporter for MarkdownReporter {
    fn report(&self, results: &[DetectorResult]) {
        // Implementation for Markdown output
    }
}

impl DetectorResultReporter for JsonReporter {
    fn report(&self, results: &[DetectorResult]) {
        match serde_json::to_string_pretty(results) {
            Ok(json) => println!("{}", json),
            Err(e) => eprintln!("Error serializing to JSON: {}", e),
        }
    }
}

impl DetectorResultReporter for StdoutReporter {
    fn report(&self, results: &[DetectorResult]) {
        if results.is_empty() {
            println!("{}", "No issues detected.".green());
            return;
        }

        println!("{}", "Detector Results:".bold().underline());
        println!();

        for (index, result) in results.iter().enumerate() {
            self.print_result(index + 1, result);
            println!();
        }

        self.print_summary(results);
    }
}

impl StdoutReporter {
    fn print_result(&self, index: usize, result: &DetectorResult) {
        println!(
            "{}. {} ({})",
            index,
            result.issue_name.bold(),
            result.detector_name.italic()
        );
        println!(
            "   {}: {}",
            "Severity".yellow(),
            self.format_severity(result.severity)
        );
        println!(
            "   {}: {}",
            "Confidence".yellow(),
            self.format_confidence(result.confidence)
        );
        println!(
            "   {}: {}:{}-{}",
            "Location".yellow(),
            result.location.file_no(),
            result.location.start(),
            result.location.end()
        );
        println!("   {}: {}", "Description".yellow(), result.message);
    }

    fn format_severity(&self, severity: Severity) -> ColoredString {
        match severity {
            Severity::Informational => "Informational".blue(),
            Severity::Low => "Low".green(),
            Severity::Medium => "Medium".yellow(),
            Severity::High => "High".red(),
        }
    }

    fn format_confidence(&self, confidence: Confidence) -> ColoredString {
        match confidence {
            Confidence::Low => "Low".yellow(),
            Confidence::Medium => "Medium".yellow(),
            Confidence::High => "High".green(),
            Confidence::Certain => "Certain".green().bold(),
        }
    }

    fn print_summary(&self, results: &[DetectorResult]) {
        let total = results.len();
        let (high, medium, low, info) =
            results
                .iter()
                .fold((0, 0, 0, 0), |acc, r| match r.severity {
                    // summing up the counts of each severity
                    Severity::High => (acc.0 + 1, acc.1, acc.2, acc.3),
                    Severity::Medium => (acc.0, acc.1 + 1, acc.2, acc.3),
                    Severity::Low => (acc.0, acc.1, acc.2 + 1, acc.3),
                    Severity::Informational => (acc.0, acc.1, acc.2, acc.3 + 1),
                });

        println!("{}", "Summary:".bold().underline());
        println!("Total issues: {}", total);
        println!("  High:     {}", high.to_string().red());
        println!("  Medium:   {}", medium.to_string().yellow());
        println!("  Low:      {}", low.to_string().green());
        println!("  Info:     {}", info.to_string().blue());
    }
}
