use std::{
    io::{BufRead, ErrorKind},
    net::{IpAddr, SocketAddr},
    process::{ChildStdout, Command, Stdio},
    sync::{atomic::AtomicBool, Arc, Condvar, Mutex},
    thread,
};

use envconfig::Envconfig;

const OUTPUT_LINES: u64 = 18825;

/// Configuration.
#[derive(Envconfig)]
pub struct Config {
    /// Address to listen on.
    #[envconfig(from = "LCF_SERVER_LISTEN", default = "0.0.0.0")]
    pub listen: IpAddr,

    /// Port to listen on.
    #[envconfig(from = "LCF_SERVER_PORT", default = "5000")]
    pub port: u16,
}

/// Check if the server is running.
fn network_check(addr: std::net::SocketAddr) -> bool {
    match std::net::TcpStream::connect(addr) {
        Ok(_) => true,
        Err(e) => match e.kind() {
            ErrorKind::ConnectionRefused => false,
            e => panic!("Failed to connect to server: {}", e),
        },
    }
}

/// Show a progress bar for the server output.
fn show_progress_bar(stdout: ChildStdout, started: Arc<AtomicBool>, addr: SocketAddr) {
    let mut reader = std::io::BufReader::new(stdout);
    let progress_bar = indicatif::ProgressBar::new(OUTPUT_LINES);
    let progress_bar = progress_bar.with_style(
        indicatif::ProgressStyle::with_template(
            "[{elapsed_precise}] {bar:40.cyan/blue} {percent_precise}%",
        )
        .unwrap()
        .progress_chars("#> "),
    );

    let mut buffer = String::new();
    loop {
        if reader.read_line(&mut buffer).is_ok() {
            progress_bar.inc(1);
            if progress_bar.position() == OUTPUT_LINES {
                break;
            }
        }
        if started.load(std::sync::atomic::Ordering::SeqCst) {
            break;
        }
    }

    progress_bar.finish();
    if !network_check(addr) {
        eprintln!("[HOL_RPC] Warning: Server stopped unexpectedly");
    }

    let _ = std::io::copy(&mut reader, &mut std::io::stdout());
}

fn main() {
    let config = Config::init_from_env().expect("Failed to load configuration");

    let bin = std::env::args().nth(1).expect("Missing server binary");
    let listen = SocketAddr::new(config.listen, config.port);

    if network_check(listen) {
        eprintln!("[HOL_RPC] Server already running at {}", listen);
        std::process::exit(0);
    }

    let mut server = Command::new(&bin)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to start server");

    let stdout = server.stdout.take().unwrap();
    let mut stderr = server.stderr.take().unwrap();

    eprintln!("[HOL_RPC] Loading HOL-Light...");

    ctrlc::set_handler({
        move || {
            eprintln!("[HOL_RPC] Stopping server...");
            server.kill().unwrap();
            std::process::exit(0);
        }
    })
    .expect("Failed to set Ctrl-C handler");

    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    thread::spawn({
        let pair = pair.clone();
        move || loop {
            if network_check(listen) {
                let (lock, cvar) = &*pair;
                let mut started = lock.lock().unwrap();
                *started = true;
                cvar.notify_one();
                break;
            }
            thread::sleep(std::time::Duration::from_millis(1000));
        }
    });

    let flag_started = Arc::new(AtomicBool::new(false));
    thread::spawn({
        let should_stop = flag_started.clone();
        move || show_progress_bar(stdout, should_stop, listen)
    });

    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();
    while !*started {
        started = cvar.wait(started).unwrap();
    }
    flag_started.store(true, std::sync::atomic::Ordering::SeqCst);

    eprintln!("[HOL_RPC] Server started at {}", listen);

    loop {
        let _ = std::io::copy(&mut stderr, &mut std::io::stderr());
    }
}
