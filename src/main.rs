use kiota::parser;
use kiota::tc;
use std::io::{BufReader, Cursor, Read};

const EXIT_ACCEPT: i32 = 0;
const EXIT_REJECT: i32 = 1;
const EXIT_DECLINE: i32 = 2;

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

    // Read all input up front so the actual checking work can run on a worker
    // thread with a much larger stack (deeply nested terms in large proofs can
    // otherwise blow the default 8MB stack).
    let mut bytes = Vec::new();
    if use_stdin || path.is_none() {
        std::io::stdin()
            .lock()
            .read_to_end(&mut bytes)
            .expect("read stdin");
    } else {
        let mut f = std::fs::File::open(path.unwrap()).expect("open input");
        f.read_to_end(&mut bytes).expect("read file");
    }

    let handle = std::thread::Builder::new()
        .stack_size(1024 * 1024 * 1024)
        .spawn(move || {
            let outcome = std::panic::catch_unwind(|| {
                let mut p = parser::Parser::new();
                let reader = BufReader::new(Cursor::new(bytes));
                p.run(reader)
            });
            match outcome {
                Ok(r) => r,
                Err(_) => Err(tc::TcError::Other("panic during checking".into())),
            }
        })
        .expect("spawn worker thread");
    let result: Result<(), tc::TcError> = handle
        .join()
        .unwrap_or_else(|_| Err(tc::TcError::Other("worker thread panicked".into())));

    match result {
        Ok(()) => std::process::exit(EXIT_ACCEPT),
        Err(tc::TcError::Reject(msg)) => {
            eprintln!("REJECT: {msg}");
            std::process::exit(EXIT_REJECT);
        }
        Err(tc::TcError::Decline(msg)) => {
            eprintln!("DECLINE: {msg}");
            std::process::exit(EXIT_DECLINE);
        }
        Err(tc::TcError::Other(msg)) => {
            eprintln!("ERROR: {msg}");
            std::process::exit(EXIT_REJECT);
        }
    }
}

#[allow(dead_code)]
fn silence_unused(_: impl Read) {}
