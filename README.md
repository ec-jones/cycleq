# Getting Started

We have provided a virtual machine image containing our CycleQ tool and benchmark data.
The image is a standard Ubuntu 20.04.4 LTS minimal install, to which we added ghc-9.0.2 and cabal-3.6.2.0 (for compiling and running the artifact) and graphviz (for visualising proofs).
The virtual machine image was created using Virtual Box 6.1.32 on a Windows 10 host.

To get started log in with the user name and password "pldi22", this may be done automatically.
On the desktop you will find the CycleQ directory containing the tool and a copy of this document explaining, in the following sections, how to use and evaluate it. 

During the prepration of this artifact, we noticed a bug that we have since fixed. Consequently, the results supplied here, and in the version of the paper attached to the artifact, differ slightly from those in the version of the paper originally submitted. No other changes have been made.

# CycleQ: an efficient bassis for cyclic equational reasoning

This tool is a plugin for GHC which attempts to prove equations about program terms at compile time.
The key files and directories of the project are layed out as follows:

```
CycleQ
├── cycleq-benchmarks
├── our results
├── proofs
├── scratch
└── src
```

We will now explain the tool's usage before outlining our claims and how to evaluate them.

To integrate the plugin into a cabal compilation pipeline add `cycleq` as a dependency and `-fplugin CycleQ` as a `ghc-option` to the cabal project which you wish to verify.

To run the plugin simply compile the project, i.e. `cabal build scratch` or `cabal build cycleq-benchmarks`. Note that cabal does not recompile unless necessary and so the plugin will also not be run in this case.

The plugin extracts all top-level function definitions for a module which annotated with `CycleQ` parameters, interprets them as equations universally quantified over the functions arguments, and then attempts to prove they hold. For example, the definition:

```
{-# ANN mapId CycleQ { fuel = 4, output = "proofs/mapId.svg", lemmas = [] } #-}
mapId :: List a -> Equation
mapId xs =
  map id xs === xs
```
corresponds to the equation `∀xs. map id xs = xs`, which will be proven at compile time.

The expected terminal output during compilation is `Success!` or `Fail!`. Note that the tool is sound but not complete (for a subset of Haskell) so a success means the property holds, but failure does not necessary imply the existence of a counter-example. Note this is why failure does not interupt compilation.

Please ensure the annotated definition has the type `Equation` and is build using the `===` function *directly* The plugin does not unfold definitions before parsing so it is sensitive to syntax.

The types `Equation`, `===`, and `CycleQ` are exported by the `CycleQ` module. Currently, CycleQ is unable to view equations or definitions from other modules so we encourage user to hide the Haskell prelude with `import Prelude ()`.

## Parameters

### Fuel
The fuel corresponds to the depth of proof search. The higher the fuel the more likely a proof will be found but the longer proof search might take. Note that some proofs will always be out of scope.

### Output
In addition to the simple success or failure of a proof, the plugin can output a graphical representation of the proof, generated using the graphviz tool, as a `.svg` file. This parameter sets the target output file, which we recommend gathering in the `proofs` directory.
To not generate a graphical output, use `\0`. 

### Lemmas
Some equations require other equations used as lemmas in order to prove them. The `lemmas` parameter allows the programmer to list other top-level equations, which are assumed true, to be used in the proof of the annotated equation.

The syntax for this employs Template Haskell quoted name, which are prefixed by the prime character: ` CycleQ { lemmas = [ 'lemma1, 'lemma2 ] } `. It is, therefore, necessary to include `{-# LANGUAGE TemplateHaskellQuotes #-}` at the start of the module in order to use this feature.

### Defaults
An equation may also be annotated with default parameters `{-# ANN equation defaultParams #-}` in place of `CycleQ { fuel = 12, output = "\0", lemmas = [] }`.
Furthemore, a subset of parameters may be modified as follows: `{-# ANN equation defaultParams { fuel = 4, output = "proofs/myProof.svg" } #-}`.

## Benchmarking
If the ghc-option `-fplugin-opt CycleQ:benchmark` is added to a project, then CycleQ will run in benchmarking mode. The tools will then record the time (ms) taken to prove each equation and the time (ms/%) spent verifying cycles. The user is prompted to enter the number of runs to perform, over which an average is taken. These results are stored as a table in `benchmarks - {module name}.tex`, found in the `CycleQ` directory.

Note that in benchmarking mode the graphical output of the tool is supressed.

## Evaluation
As there are very few implementations of cyclic proof systems, an their performance with equational goals is not well understood. Our aim with this project is to show that the CycleQ system, although simple, is resonably efficient.
The evaluation, therefore, consist of a standard series of benchmark equations found in the `benchmarks/IsaPlanner.hs` file and a small number of additional benchmarks, `benchmarks/Mutual.hs`, which test the tools capcity for mutual induction - a distinguishing feature.

As a proofs of concept there are features that CycleQ lacks, such as lemma generation and conditional equations. Benchmarks from the IsaPlanner series that requires these features have been commented out.

To run the benchmarks, use the command `cabal build cycleq-benchmarks`. As outlined above you will be prompte with the number of runs you wish to perform and the results will be outputed as tables in the `CycleQ` directory.
These can be compared to our results found in the `our results` directory. For reference, these were generated as a average of 10 runs. The use of a virtual machine, and differences in hardware, may impact performance and a smaller number of runs may be appropriate.

We also have created a scratch project for you to experiment with your own equations, see the `scratch` directory.
To run CycleQ, on this project use the command `cabal build scratch`. This is not setup for benchmarking in order to demonstrate the tools graphical output feature. Note, as stated above, the CycleQ tools is a prototype is currently unable to use equations or definitions from a different module.
