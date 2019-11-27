# MicroTESK-for-RISC-V Binaries

This directory contains binary code samples (along with C sources and other related information).
The purpose is to demonstrate MicroTESK's disassembler and symbolic executor as well as
their application to binary code deductive verification.

## Samples

- `euclid`
- `fibonacci`
- `idiv`
- `memset`
- `strlen` (this sample is from [VerKer](https://forge.ispras.ru/projects/verker/) project)
- `sum`

## How to ...

### Prerequisites

- Install MicroTESK for RISC-V: https://forge.ispras.ru/projects/microtesk-riscv
- Install GNU toolchain for RISC-V: https://github.com/riscv/riscv-gnu-toolchain

### Command line

- Handling all samples:
```
$ make
```
- Handling `<sample>`:
```
$ cd <sample>
$ make
```
