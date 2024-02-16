### 1) Simple boundary division case (from STM32X errata sheet)
When using the signed 32-by-16-bit division
instruction, div.sd, the Overflow bit does not
always get set when an overflow occurs.
This erratum only affects operations in which at
least one of the following conditions is true:
a) Dividend and divisor differ in sign,
b) Dividend > 0x3FFFFFFF or
c) Dividend <= 0xC0000000.

### **Work Around:**
The application software must perform both the
following actions in order to handle possible
undetected overflow conditions:
a) The value of the dividend must always be
constrained to be in the following range:
0xC0000000 < Dividend < 0x3FFFFFFF.
b) If the dividend and divisor differ in sign
(e.g., dividend is negative and divisor is
positive), then after executing the div.sd
instruction or the compiler built-in function,
__builtin_divsd(), inspect the sign of
the resultant quotient.
If the quotient is found to be a positive

### Source:
https://ww1.microchip.com/downloads/en/DeviceDoc/dsPIC33EPXXXGS70X-80X-Family-Silicon-Errata-and-Data-Sheet-Clarification-DS80000722H.pdf

### 2) Odd-numbered FPU register dependency not properly checked in some double-precision FPU operations
Data dependency is not properly checked between a load singleword floating-point instruction (LDF) involving an odd-numbered floating-point register as a destination of the load and an immediately following double-precision floating-point
instruction (FADDd, FSUBd, FMULd, FDIVd or FSQRTd) that satisfies all of the following conditions:
- the odd-numbered floating-point register is used as (part of) a source operand
- the destination floating-point register is also a source operand
- in an FSUBd or FDIVd, the two source operands are different registers

In this case, the final result of the double-precision floating-point instruction will be wrong.
Other double-precision floating-point instructions (FCMPd, FCMPEd, FdTOi and FdTOs) are not affected by this issue and
will operate as expected.
The error case appears when any of the six following sequences of instructions is present (n in [0:31], x and y as
different even numbers in [0:30]):
Case 1:
```assembly
LD [%rn], %fx+1
FPOPd(1) %fx, %fy, %fx
```
Case 2:
```assembly
LD [%rn], %fx+1
FPOPd(1) %fy, %fx, %fx
```
Case 3:
```assembly
LD [%rn], %fx+1
FPOPd(1) %fx, %fy, %fy
```
Case 4:
```assembly
LD [%rn], %fx+1
FPOPd(1) %fy, %fx, %fy
```
Case 5:
```assembly
LD [%rn], %fx+1
FPOPd(2) %fx, %fx, %fx
```
Case 6:
```assembly
LD [%rn], %fx+1
SQRTd %fx, %fx
```

Notes: 1. FPOPd is one of FADDd, FSUBd, FMULd or FDIVd.
2. FPOPd is one of FADDd or FMULd (FSUBd and FDIVd operate as expected).
Workarounds
If direct control over assembly language is possible, simply insert a NOP before the double-precision floating-point
instruction (case 1 to 6):
```assembly
LD [%rn], %fx+1
NOP
FPOPd <same registers set as described above>
```
### Source:
https://www.microchip.com/content/dam/mchp/documents/OTH/ProductDocuments/Errata/at697f_errata.pdf