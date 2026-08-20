#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use kiota::parser;
use kiota::tc;
use std::io::{BufReader, Cursor, Read, Write};

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
    // `std::process::exit` still runs Apple TLS dtors, which walk the
    // interned `Rc` term DAG (`Interner` in thread-local). Full Init is
    // ~13 GB of nodes; that drop took longer than checking. The OS
    // reclaims the address space on `_exit`.
    unsafe {
        extern "C" {
            fn _exit(status: i32) -> !;
        }
        _exit(code);
    }
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
            kiota::stats::report();
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
