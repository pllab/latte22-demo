# Verilog to Rosette IR

This directory contains some very incomplete code for translating from Verilog
to the Rosette IR. The main route is through Yosys, using its RTLIL intermediate
representation. (Requires Yosys to be built with Python bindings.)

This translation works enough for the simple processor included here, but
probably not much beyond that.

To run:

```
$ python verilog-to-ir.py
```
