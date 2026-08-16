use kiota::parser;
use kiota::tc;
use std::io::{BufReader, Read, Write};

const EXIT_ACCEPT: i32 = 0;
const EXIT_REJECT: i32 = 1;
const EXIT_DECLINE: i32 = 2;

/// Report the verdict and end the process. Never returns.
///
/// This is deliberately called from the worker thread rather than returned to
/// `main`. Letting the worker unwind runs its thread-local destructors, and
/// those walk the whole interned term DAG dropping one `Rc` at a time.
/// Sampling `perf/beta-ladder` put the large majority of samples in that
/// teardown rather than in checking. The process is about to end and the OS
/// reclaims the arena wholesale, so the work buys nothing.
fn finish(result: Result<(), tc::TcError>) -> ! {
    let code = match result {
        Ok(()) => EXIT_ACCEPT,
        Err(tc::TcError::Reject(msg)) => {
            eprintln!("REJECT: {msg}");
            EXIT_REJECT
        }
        Err(tc::TcError::Decline(msg)) => {
            eprintln!("DECLINE: {msg}");
            EXIT_DECLINE
        }
        Err(tc::TcError::Other(msg)) => {
            eprintln!("ERROR: {msg}");
            EXIT_REJECT
        }
    };
    let _ = std::io::stderr().flush();
    let _ = std::io::stdout().flush();
    std::process::exit(code);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut use_stdin = false;
    let mut path: Option<String> = None;
    for a in &args[1..] {
        if a == "--use-stdin" || a == "-" {
            use_stdin = true;
        } else if !a.starts_with('-') {
            path = Some(a.clone());
        }
    }

    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let outcome = std::panic::catch_unwind(|| {
                let mut p = parser::Parser::new();
                if use_stdin || path.is_none() {
                    let stdin = std::io::stdin();
                    let reader = BufReader::with_capacity(8 * 1024 * 1024, stdin.lock());
                    p.run(reader)
                } else {
                    let f = std::fs::File::open(path.unwrap()).expect("open input");
                    let reader = BufReader::with_capacity(8 * 1024 * 1024, f);
                    p.run(reader)
                }
            });
            kiota::stats::report();
            kiota::stats::report_inst();
            let result = match outcome {
                Ok(r) => r,
                Err(_) => Err(tc::TcError::Other("panic during checking".into())),
            };
            finish(result)
        })
        .expect("spawn worker thread");

    // `finish` ends the process from inside the worker, so this is reached only
    // if the thread died without getting there.
    let _ = handle.join();
    finish(Err(tc::TcError::Other("worker thread panicked".into())))
}

#[allow(dead_code)]
fn silence_unused(_: impl Read) {}
