//! `ts-proof check|prove|build|coverage|explain`

use std::env;
use std::path::PathBuf;
use std::process::ExitCode;
use ts_proof_core::ErrorCode;
use ts_proof_frontend::{check_project, OutputFormat, Mode};

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    ExitCode::from(run(&args) as u8)
}

pub fn run(args: &[String]) -> i32 {
    match command(args) {
        Ok(Command::Explain(code)) => match ErrorCode::parse(&code) {
            Some(code) => {
                println!("error[{code}]: {}\n\n{}", code.title(), code.explain());
                0
            }
            None => {
                eprintln!("unknown diagnostic code `{code}`");
                eprintln!("known codes: VERIFY001 through VERIFY015");
                2
            }
        },
        Ok(Command::Help) => {
            println!(
                "ts-proof check [path] [--format text|json|sarif|junit]\n\
                 ts-proof prove [path]\n\
                 ts-proof build [path]\n\
                 ts-proof coverage [path]\n\
                 ts-proof explain VERIFY001"
            );
            0
        }
        Ok(Command::Run { mode, root, format }) => {
            let report = check_project(&root, mode);
            println!("{}", report.render(format));
            report.exit_code()
        }
        Err(message) => {
            eprintln!("{message}");
            2
        }
    }
}

enum Command {
    Run {
        mode: Mode,
        root: PathBuf,
        format: OutputFormat,
    },
    Explain(String),
    Help,
}

fn command(args: &[String]) -> Result<Command, String> {
    if args.is_empty() || args.iter().any(|arg| arg == "--help" || arg == "-h") && args.len() == 1 {
        return Ok(Command::Help);
    }
    if args.iter().any(|arg| arg == "--help" || arg == "-h") && args.first().map(String::as_str) != Some("explain") {
        return Ok(Command::Help);
    }
    let mut format = OutputFormat::Text;
    let mut positional = Vec::new();
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--format" {
            let value = args.get(i + 1).ok_or_else(|| "--format needs text, json, sarif, or junit".to_string())?;
            format = OutputFormat::parse(value).ok_or_else(|| format!("unknown format `{value}`"))?;
            i += 2;
            continue;
        }
        if let Some(value) = args[i].strip_prefix("--format=") {
            format = OutputFormat::parse(value).ok_or_else(|| format!("unknown format `{value}`"))?;
            i += 1;
            continue;
        }
        positional.push(args[i].as_str());
        i += 1;
    }
    let Some(verb) = positional.first().copied() else {
        return Ok(Command::Help);
    };
    if verb == "explain" {
        let code = positional.get(1).ok_or_else(|| "explain needs a code such as VERIFY001".to_string())?;
        return Ok(Command::Explain((*code).to_string()));
    }
    let mode = match verb {
        "check" => Mode::Check,
        "prove" => Mode::Prove,
        "build" => Mode::Build,
        "coverage" => Mode::Coverage,
        other => return Err(format!("unknown command `{other}`")),
    };
    let root = positional.get(1).map(PathBuf::from).unwrap_or_else(|| PathBuf::from("."));
    Ok(Command::Run { mode, root, format })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn explain_prints_the_fail_closed_rule() {
        let code = run(&["explain".into(), "VERIFY001".into()]);
        assert_eq!(code, 0);
        assert_eq!(run(&["explain".into(), "NOPE".into()]), 2);
    }
}
