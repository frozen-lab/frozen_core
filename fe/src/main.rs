use fe::from_err_code;
use std::env;

fn main() {
    let arg = env::args().nth(1).expect("usage: <bin> <error_code>");
    let code = arg.parse::<u32>().expect("invalid error code");

    let (module, domain, reason) = from_err_code(code);
    println!("code=0x{code:08X} module={module} domain={domain} reason={reason}",);
}
