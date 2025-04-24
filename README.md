# Linear Resources and Process Compositions

In this entry we formalise a framework for process composition based on actions that are specified by their input and output resources.
We verify their correctness by translating compositions of process into deductions of intuitionistic linear logic.
As part of the verification we derive simple conditions on the compositions which ensure well-formedness of the corresponding deduction.

We describe an earlier version of this formalisation in our article [Linear Resources in Isabelle/HOL](https://doi.org/10.1007/s10817-024-09698-2), which also includes a formalisation of manufacturing processes in the simulation game Factorio.

This is the development version of our Archive of Formal Proofs [entry](https://www.isa-afp.org/entries/ProcessComposition.html).
It contains updates, work in progress and examples.

## Structure
This formalisation consists of the following sessions:
- `ProcessComposition` is the base theory of linear resources and process compositions.
- `ProcessComposition_ILL` translates concepts from the base theory into intuitionistic linear logic to demonstrate linearity of valid process compositions.
- `ProcessComposition_Factorio` is a basic formalisation of manufacturing in the simulation game [Factorio](https://www.factorio.com/) as an example use of process compositions.
- `ProcessComposition_Marking` demonstrates resource and process refinement by formalising two views of course work marking.
- `ProcessComposition_PortGraph` constructs port graphs from process compositions, emphasising the view of them as representing connections between actions and prove a graphical variant of linearity.

## Requirements
This formalisation is tested with Isabelle 2024, but should work with most modern versions.
The base session relies only on `HOL`.
The `ProcessComposition_ILL` session relies on the base session and the `ILL` entry, which is available either on the [AFP](https://www.isa-afp.org/entries/ILL.html) or in its own [development repository](https://github.com/pilif0/isa-ILL/).
The `ProcessComposition_PortGraph` session relies on the base session and the `PortGraph` and `PortGraph_Export` sessions, which are available in their own [repository](https://github.com/pilif0/isa-PortGraph/).

## Installation
To use this formalisation, add it as a component to your Isabelle installation:
```
isabelle components -u PATH/TO/REPO
```

If you have a local copy of the AFP as a component, disable the corresponding entry to avoid a clash.
You can do this by removing it from the AFP `ROOTS` file, or by renaming either entry if you want to use both versions.
