# LS-IDL



this is a local search solver for SMT on Integer Difference Logic, and it combines with Yices to obtain a wrapper SMT solver.

To build the solver:

```bash
cd src
./starexec_build
```

The solver is compiled and can be found in /bin folder.

To run an instances:

```bash
cd bin
./starexec_run_default {file_name.smt2} 
```

