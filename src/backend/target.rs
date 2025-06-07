use std::{path::Path, process::Command};

use crate::{backend::CodegenOptions, middle::lir};

mod x86_64_linux_gnu;

pub trait CodeGenerator {
    fn translate_to_asm(&self, module: &lir::Module, options: &CodegenOptions) -> String;
    fn create_assembler_command(&self, input_file: &Path, output_file: &Path) -> Command;
    fn create_linker_command(&self, input_file: &Path, output_file: &Path) -> Command;
}

#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Target {
    x86_64LinuxGnu,
}

impl Target {
    pub fn get_code_generator(self) -> impl CodeGenerator {
        match self {
            Target::x86_64LinuxGnu => x86_64_linux_gnu::CodeGeneratorX86_64LinuxGnu,
        }
    }
}
