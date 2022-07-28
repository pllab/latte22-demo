# Program synthesis for processor control logic


There are two demos in this directory:

1. Accumulator-style processor (written in Verilog)
2. Single-cycle RISC-V processor (written in PyRTL)

To generate control logic for each run the corresponding Racket file:

1. `$ racket acc-verilog.rkt`
2. `$ racket rv-single-cycle-demo.rkt`

Rosette needs to be installed to run.

The Rosette IR, its interpreter, and synthesis procedures are defined in
`ir.rkt`.
