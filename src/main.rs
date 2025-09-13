use std::io::Read;
use std::path::PathBuf;
use std::{fs, io};

use anyhow::{Error, Result, anyhow};
use clap::Parser;
use ron_edit::File;

#[derive(Parser)]
struct Opts {
    #[arg(long, default_value_t = false, help = "Read from stdin")]
    stdin: bool,
    #[arg(help = "Read one or multiple files")]
    files: Option<Vec<PathBuf>>,
}

fn main() -> Result<()> {
    let opts = Opts::parse();
    let Opts { stdin, files } = opts;
    if let Some(files) = files {
        for file in &files {
            let ron = fs::read_to_string(file)?;
            let ron = File::try_from(ron.as_str())
                .map_err(|err| anyhow!("Error while reading `{}`: {err}", file.display()))?;
            fs::write(file, rondafk::format(&ron))?;
        }
    }
    if stdin {
        let mut ron = String::new();
        io::stdin().read_to_string(&mut ron)?;
        let ron = File::try_from(ron.as_str()).map_err(Error::msg)?;
        print!("{}", rondafk::format(&ron));
    }

    Ok(())
}
