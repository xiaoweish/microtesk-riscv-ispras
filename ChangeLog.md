# MicroTESK for RISC-V Builds

## MicroTESK for RISC-V 0.1

### 2019/12/27 - MicroTESK for RISC-V 0.1.0

* **Tool Functions:** Updated the MicroTESK core to 2.5.0
* **Binary Samples:** Added binaries samples w/ their C sources
  (see the `arch/riscv/binaries` directory)
* **Test and Debug:** Used QEMU4V 0.3.4 for running tests

## MicroTESK for RISC-V 0.0

### 2019/10/25 - MicroTESK for RISC-V 0.0.9

* **Specifications:** Added the system registers and the related modes
* **Specifications:** Added sample specifications of some vector instructions
  (consistent with `RISC-V "V" Vector Extension Version 0.7.1`)
* **Specifications:** Fixed bugs in the RV64A instructions
* **Specifications:** Fixed bugs in the RV32{F,D} instructions (`FEQ`, `FLE`, and `FLT`)
* **Test Templates:** Added sample test templates for vector instructions
* **Test Templates:** Changed the structure of directories
* **Test Templates:** Fixed the Torture-like template (`synthetics/rvxxx`)
* **Tool Functions:** Moved the branch data generators to TestBase
* **Test and Debug:** Used QEMU4V 0.3.3 for running tests

### 2019/02/06 - MicroTESK for RISC-V 0.0.8

* **Specifications:** Specified address translation for the Sv32, Sv39, and Sv48 modes
* **Test Templates:** Added test templates for address translation
* **Test and Debug:** Used QEMU4V 0.3.2 for running tests

### 2018/11/30 - MicroTESK for RISC-V 0.0.7

* **Specifications:** Added sketch specifications of the V extension

### 2018/08/21 - MicroTESK for RISC-V 0.0.6

* **Specifications:** Fixed bugs in the floating-point instructions
* **Tool Functions:** Updated the MicroTESK core

### 2018/07/25 - MicroTESK for RISC-V 0.0.5

* **Specifications:** Fixed several bugs
* **Test Templates:** Added Toture-like test templates
* **Test Templates:** Added test templates for floating-point instructions
* **Tool Functions:** Improved the floating-point support
* **Tool Functions:** Improved the register allocation mechanism
* **Tool Functions:** Supported operations with dynamic immediate values in test templates:
**  `_AND`, `_OR`, `_XOR`, `_ADD`, `_SUB`, `_PLUS`, `_MINUS`, `_NOT`, and `_SLL`
* **Test and Debug:** Improved Make scripts for running test templates
* **Test and Debug:** Specification code coverage is measured
* **Test and Debug:** Test suite uses QEMU4V 0.2.2

### 2018/06/01 - MicroTESK for RISC-V 0.0.4

* **Specifications:** Supported the RV32C and RV64C extensions
* **Test Templates:** Added the `rv32uc/rvc` and `rv64uc/rvc` compliance tests
* **Test Templates:** Split test templates into groups
* **Test and Debug:** Used QEMU4V 0.1.1 for running tests

### 2018/05/05 - MicroTESK for RISC-V 0.0.3

* **Specifications:** Added the system registers and the system instructions
* **Test Templates:** Added automatically generated test templates
* **Test Templates:** Added branch-related test templates
* **Test Templates:** Added libraries to describe initialization/finalization code
* **Test Templates:** Updated the linker settings
* **Test Templates:** Added test templates to validate user-level instructions
* **Test Templates:** Added more demo test templates
* **Tool Functions:** Supported global labels, numeric labels, and weak symbols
* **Tool Functions:** Implemented test data iteration
* **Tool Functions:** Supported automated generation of test templates, so-called Autogen
* **Test and Debug:** Used QEMU for RISC-V 0.2.1 for running tests
* **Test and Debug:** Used Spike for running tests
* **Test and Debug:** Used Trace Matcher 0.1.8 for comparing test traces

### 2017/12/06 - MicroTESK for RISC-V 0.0.2

* **Specifications:** Added new pseudo instructions for RV32I, RV32F, and RV32D
* **Test Templates:** Added 5 new test templates

### 2017/11/23 - MicroTESK for RISC-V 0.0.1

* **Specifications:** Added specifications of the following ISA subsets

| Subset | Variants        | Description |
| :----- | :-------------- | :---------- |
| I      | RV32I and RV64I | Base Integer Instruction Set |
| M      | RV32M and RV64M | Standard Extension for Integer Multiplication and Division |
| A      | RV32A and RV64A | Standard Extension for Atomic Instructions |
| F      | RV32F and RV64F | Standard Extension for Single-Precision Floating-Point |
| D      | RV32D and RV64D | Standard Extension for Double-Precision Floating-Point |

* **Test Templates:** Added 20 demo test templates
