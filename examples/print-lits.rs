//! Example to showcase `ipasir-display` feature

macro_rules! show_ipasir_var {
    ($ipasir:expr) => {{
        println!(
            "`Display` IPASIR literal {:3}: {:>16}",
            $ipasir,
            format!("{}", rustsat::ipasir_lit![$ipasir])
        );
        println!(
            "`Display` IPASIR literal {:3}: {:>16}",
            -$ipasir,
            format!("{}", rustsat::ipasir_lit![-$ipasir])
        );
        println!(
            "  `Debug` IPASIR literal {:3}: {:>2?}",
            $ipasir,
            rustsat::ipasir_lit![$ipasir]
        );
        println!(
            "  `Debug` IPASIR literal {:3}: {:>2?}",
            -$ipasir,
            rustsat::ipasir_lit![-$ipasir]
        );
    }};
}

fn main() {
    show_ipasir_var![1];
    show_ipasir_var![42];
}
