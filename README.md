Introduction
------------

The goal of this article is to provide a complete overview of Kami. In
this article, we present all of the key definitions, theorems, and
tactics defined by the library.

Kami is an open source Coq library that can be used to model and reason
about digital circuits.

You can download a copy from <https://github.com/sifive/Kami>.

The Kami package includes tools that can be used to generate Verilog
models for these circuits. The Compile.v file defines code that can be
extracted to a Haskell script. The Haskell script can be executed to
generate the Verilog the code.

Loading the Kami Library
------------------------

Before you can use the Kami library, you must perform the
following steps:

0.  Create a "Projects" directory where all the repositories are going to reside
1.  Download and Compile the MIT Bedrock Bit Vectors library from
    <https://github.com/mit-plv/bbv>.
    1.  In the “Projects” directory use
        `git clone `[`https://github.com/mit-plv/bbv.git`](https://github.com/mit-plv/bbv.git)
        to clone the repo.
    2.  cd into bbv and run `make` to compile the files.
2.  Download and compile the Kami library
    1.  In the “Projects” directory use
        `git clone `[`https://github.com/sifive/Kami.git`](https://github.com/sifive/Kami.git)
        to clone the Kami repo.
    2.  cd into kami and run `make` to compile the files.
3.  Open proofgeneral or your favorite IDE for Coq.
    1.  In the Vernacular, execute `Require Import Kami.All.` to load all of the Kami library.
    2.  Write a Kami module and its specification based on what is described below and prove it!

Library Organization
--------------------

Syntax.v defines the data structures, predicates, and functions that
represent digital circuits components (modules), their behavior, and
their properties.

The Syntax.v module contains a number of definitions, functions, and
predicates prefixed with the letter “P” (for example, the file defines a
constructor named “SemLetExpr” and another named “PSemLetExpr”). The
file is roughly divided into two models. One represents the registers,
rules, and methods in a module using lists. The other equates modules
that differ only by permutations on these lists. The definitions that
begin with the “P” are those that work with permutations.

Kami Semantics Overview
-----------------------

Kami consists of 7 things:

1.  a domain specific language that defines constructs for representing
    digital circuits (i.e. kinds, expressions, actions, registers,
    methods, rules, modules, and traces)
2.  a denotational semantics that maps expressions, kinds, and actions,
    etc onto Gallina terms)
3.  an operational semantics that models the behavior of digital
    circuits represented by Kami modules.
4.  a collection of axioms and theorems asserting relations between
    constructs
5.  a collection of tactics to automate proving certain properties
6.  and a compiler that maps Kami constructs onto Verilog constructs.

In Kami, we represent digital circuits as modules. A Kami module
consists of a set of registers, rules, and methods. These elements
correspond to physical circuit elements. When compiled into Verilog,
registers become physical registers while rules and methods become
combinatorial circuits.

Kami's operational semantics model the behavior of digital circuits. The
behavior of a digital circuit is represented by the sequential execution
of a series of rules. Each rule consists of a sequence of actions.
Actions may read values stored in registers, store values in registers,
call methods, or perform arithmetic operations. In actual circuits,
actions correspond to the transmission of values across wires. Register
updates are controlled by a central clock. Each rule is executed within
a single clock cycle, and all values written to registers are stored
simultaneously at the end of each clock cycle. A Kami trace is a
sequence of rule executions, external method calls, and external method
executions that represent the externally visible behavior of a circuit
over time.

Kami's denotational semantics describes how Kami expressions are
translated into Gallina terms.

The datastructures used to represent Kami kinds, expressions, actions,
registers, methods, rules, modules, and traces are all defined in
Syntax.v. The definitions for these constructors are abstracted with
respect to a function (represented by the variable `ty`) that maps Kami
kinds onto Gallina and Verilog terms - i.e. the definitions for Kami
expressions and actions accepts a parameter function that maps Kami
kinds onto Gallina types[^1].

Syntax.v defines a mapping function named `type` that effectively maps
the Kami types according to the denotational semantics outlined in Kami:
A Platform for High-Level Parametric Hardware Specification and Its
Modular Verification[^2]. Compile.v defines an alternative mapping
function that leads to a mapping of Kami kinds into Verilog terms.

The denotational semantics defined by Syntax.v effectively duplicates
combinatorial circuit elements[^3]. The semantics defined by Compile.v
ensures that shared combinatorial circuit elements are generated once
and then linked by wires represented by Verilog variable references.
It's easier to prove theorems using the denotational semantics defined
by Syntax.v, but the circuits modeled by Compile.v are more
efficient/less redundant.

The `ty` parameter represents a function that maps Kami types onto
Gallina types. In effect, it gives the denotation for Kami Kinds - i.e.
the interpretation of various Kinds as Gallina terms. For theorem
proving we use the function `type` defined in Syntax.v. This function
essentially represents the duplication of combinatorial circuits
whenever they are referenced. This approach simplifies theorem proving,
but it would be inefficient to generate Verilog code that contained
component duplications. The compiler defined in Compile.v uses a
different function that generates combinatorial circuits, defines a
temporary identifier for these circuits represented as a list of nats,
and then generates verilog code that creates the combinatorial circuits
once and then connects code that uses them over wires - i.e. the
identifiers become Verilog component IDs and mapping generates Verilog
variable references.

The fundamental relationship within Kami is trace inclusion. Given two
modules, m and n, we say that m refines n iff every trace produced by m
can also be produced by n. A trace is a sequence of labels where a label
denotes either a rule execution, a method call, or a method execution.
Trace's summarize the externally visible behavior of a circuit.

Theorem proving in Kami is based on three fundamental theorems: the
modular substitution theorem, the inlining theorem, and the simulation
theorem (previously referred to as the decomposition theorem). These
theorems allow us to decompose complex circuits into smaller subcircuits
represented by small modules, to prove properties about these modules,
to combine these modules into larger composite modules, and to project
these properties onto composite modules.

Representing Circuits
---------------------

### Values within Digital Circuits

#### Kinds

The *types* of values that can be represented by digital circuit signals
are represented by the terms of the inductive type `Kind`, which is
defined in Syntax.v.

For example, the *type* of boolean values are represented by `Bool`.

Kami allows us to use Gallina types to describe the values within
circuits. These types cannot be translated into Verilog, but can be used
to describe specifications[^4]. To represent Types that may include Coq
types, we use the `FullKind` type defined in Syntax.v.

For example, `Check (SyntaxKind Bool).` represents the *type* of boolean
values.

#### Expressions

Kami values are represented by terms belonging to the inductive type
`Expr`. This defines multiple constructors for representing different
types of values.

For example:

-   `Const type true : Expr type (SyntaxKind Bool)` represents a boolean
    value.
-   `Const type (natToWord 32 4)` Represents the number 4 as a 32 bit
    sequence.
-   `Var type (SyntaxKind Bool) true` a variable containing a bool equal
    to true.
-   `Const type (ConstBit WO~1~0~0~0)` represents a 4 bit binary string.

These notations are defined in Syntax.v.

We can form composite values using the constructors for Syntax.Expr. For
example:

-   `UniBool Neg (Const type true)` represents the boolean negation of
    true.
-   `BinBitBool (LessThan 4) (Const type (ConstBit WO~1~0~0~0)) (Const type (ConstBit WO~0~1~1~0))`
    represents the 4 bit less than comparison between two binary
    strings.

```coq
    :   <small>Using notations:
        `Const type WO~0~1~1~0) > Const type WO~1~0~0~0`</small>.
```

Kami defines a denotational semantics that maps expressions onto Gallina
terms. Whereas the `type` function maps Kami types onto Gallina types,
the `evalExpr` function maps Kami expressions onto Gallina terms. For
example:

```coq
    Compute (evalExpr (Const type (natToWord 32 4))).
      = WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0
      : fullType type (SyntaxKind (Bit 32))
```

#### Variables

The values returned by method calls, and register reads are represented
by Kami variables[^5]. Kami expressions and actions accept a function
that maps Kami Kinds onto Gallina terms. This function parameter has
type `Kind -> Type`. This parameter plays a role in the way in which
Kami expressions are translated into Gallina and Verilog terms.

For example, read register actions can be represented as:

```coq
    ReadReg "register" (SyntaxKind (Bit 16))
      (fun result : type (Bit 16)
        => Ret Const type WO)
```

As this example illustrates, the kind (Bit 16) passed to the
continuation function has been mapped by `type : Kind -> Type`.

These values can be converted back into Kami Variable expressions using
the `#x` notation.

#### Words

Words are used to represent binary bit strings. The following is an
example two bit string: `WS false (WS true W0)`. Using notations, we may
write this as: `W0~1~0`. Note the most significant bit is to the left.

The `#w` notation can be used to convert bit strings into natural
numbers. For example: `Compute (#(WO~1~0)).` evaluates to `2:nat`.

Conversely, the `$n` notation, and the `natToWord` function, can be used
to convert numbers into bit strings. For example: `Compute ($4):word 4`
evaluates to `WO~0~1~0~0`.

`Void` represents the set of 0 length bit vectors. It contains `WO` -
i.e. the bit string of 0 length.

#### Bit Representation

The `Syntax.pack` function accepts an expression/circuit value and
returns an equivalent bit string.

For example: `Compute (pack (Const type true)).` evaluates to
`If Const type true then Const type WO~1 else Const type WO~0`. This
reflects the fact that boolean values represent bit comparisons.

This function is inverted by `unpack`.

For example:

-   `Compute (unpack Bool (Const type (ConstBit WO~0))).` evaluates to
    `Const type WO~0 == Const type WO~1` reflecting the fact that
    boolean values represent bit comparisons.
-   `Compute (unpack Bool (Const type (ConstBit WO~1))).` evaluates to
    `Const type WO~1 == Const type WO~1`.

#### Default Values

The function `getDefaultConst` accepts a Kami kind and returns the
default value for the given type.

For example:

-   `Compute (getDefaultConst (Bit 4)).` returns
    `ConstBit WO~0~0~0~0 : ConstT (Bit 4)`.
-   `Compute (getDefaultConst Bool).` returns
    `ConstBool false : ConstT Bool`.

To return these values as a Kami expression, use the following scheme:

-   `Check (Const type (getDefaultConst Bool)).`

### Actions

In actual circuits, actions correspond to the transmission of values
across wires.

Actions are represented by terms belonging to the `Action` type, which
is defined by in Syntax.v. Action wraps `ActionT` terms that represent
composed sequences of actions.

`ActionT` accepts two arguments. The first is a function that maps Kami
kinds to gallina terms. The second represents the kind returned by the
sequence of actions. For example:

-   `ActionT type Void` denotes a sequence of actions whose return type
    is Void.
-   `ActionT type (Bit 1)` denotes a sequence of actions whose return
    type is a single bit.

Actions are constructed using the terms in ActionT. For example:

-   `Check (Return (Const type (ConstBit WO))).` evaluates to
    `(Ret Const type WO)%kami_action : ActionT type Void`.
-   `Check (WriteReg `“`register`”` (Const type (ConstBit WO)) (Return (Const type (ConstBit WO~1)))).`
    evaluates to
    `(Write `“`register`”` : Void <- Const type WO; Ret Const type WO~1)%kami_action : ActionT type (Bit 1)`.
-   `Check (ReadReg `“`register`”` (SyntaxKind (Bit 16)) (fun result => Ret Const type WO)).`
    evaluates to
    `(Read _ : Bit 16 <- `“`register`”`; Ret Const type WO): ActionT type Void`.

```coq
      Check (
        MCall "example_method" (Void, Bit 1)  (* an action that calls a method named "example_method," where the method accepts a Void value and returns a single bit. *)
          (Const type (ConstBit WO))          (* the value passed to the method named "example_method." *)
          (fun result : word 1 .              (* a function that accepts the value returned by the called method and returns the action executed on the returned value. *)
            => Ret Const type WO)             (* the continuation action returns void *)
      ) : Action type Void.
```

<small>Note the simplification of `type (Bit 1)` to `word 1` in the
example given above. The reductions effected by `type` simulate the
inlining of the circuits represented by variables bound to the results
of method calls.</small>

The Kami library defines a set of notations to simplify writing actions.
These notations are contained in the scope “kami\_action”.

The “system” actions refer to debugging messages output by the Verilog
compiler/interpreter when simulating code generated by Kami.

`ActionT` represents actions in which this translation function is
given. `Syntax.Action` represents functions that accept a translation
function and return a fully specified action (i.e. and `Syntax.ActionT`
value).

For example, I've replaced `type` in the following with a function that
accepts the translation function as an argument:

```coq
      Check (
        fun translate
          => MCall "example_method" (Void, Bit 1)
               (Const translate (ConstBit WO))
               (fun result : translate (Bit 1)
                 => Ret Const translate WO)
      ) : Action Void 
```

### Rules

Rules are represented by terms belonging to the RuleT type, which is
defined in Syntax.v. RuleT is just a pair containing a label and a
sequence of actions (Action may denote a composite action).

For example:

-   `Check ((`“`example_rule`”`, fun translate_type => Ret Const translate_type WO) : RuleT).`
    evaluates to `RuleT` and represents a rule (a sequence of actions
    that are performed as frequently as possible) that simply returns a
    void value.

```coq
    Definition example_rule : RuleT
      := ("example_rule",
          fun translate_type
            => Call _ : Bit 1 <- "example_method" (Const translate_type WO : Void);
               Ret Const translate_type WO).
```

### Methods

Methods represent sequences of actions that can be executed when called.

For example:

```coq
    Check (
      (fun translate_type (input : translate_type (Bit 1)) (* Represents a method that accepts a single bit argument and returns void. *)
        => Ret Const translate_type WO)
      : MethodT (Bit 1, Void)
    ).
```

#### Method Definitions

The following is an example method definition represented by a term of
type `DefMethT`:

```coq
    Definition example_method : DefMethT
      := ("example_method",
          existT MethodT (Bit 1, Void)
            (fun translate_type (method_input : translate_type (Bit 1))
              => Ret Const translate_type WO)).
```

Note that a method definition has three components: a name, a type
signature, and an action.

Represents a method that accepts a 16 bit number, writes that number
into register 1 and returns the register's original value.

```coq
    Example method0 : DefMethT
      := ("method0",
          existT MethodT (Bit 16, Bit 16)
            (fun type (x : type (Bit 16))
              => Write "register1" : Bit 16 <- #x;
                 Read result : Bit 16 <- "register";
                 Ret #result)).
```

Note: that here, we use the `#v` syntax to represent variable
references.

### Registers

The following example represents an unitialized register that should
store void values.

-   `Definition example_register : RegInitT := (`“`example_register`”`, existT optConstFullT (SyntaxKind Void) None).`

The following example defines a register containing a single bit value.

```coq
    Definition example_register : RegInitT
      := ("example_register",                      (* specifies the name of the register. *)
          existT optConstFullT
            (SyntaxKind (Bit 1))                   (* specifies the type of value stored in the register. *)
            (Some (SyntaxConst (ConstBit WO~1)))). (* specifies the value stored in the register. *)
```

### Modules

Digital circuits are represented by Modules in Kami.

A module is a tuple that consists of four components: a name, a set of
registers, a set of rules, and a set of methods[^6]. A name is a unique
string that identifies a module. A register, is a memory location that
can be used to store values. A rule is a sequence of actions that are
executed as frequently as possible. A method is a named sequence of
actions that can be executed by other modules (and potentially external
devices).

Modules are represented by the `Mod` data type defined in Syntax.v. The
`Mod` data type defines three types of modules: `Base`, `ConcatMod`, and
`HideMeth`. `Base` modules represent “normal” modules. `ConcatMod`
represents modules/circuits that are formed by taking two or more
modules together. `HideMeth`, represents the result of taking a module
and “hiding” one of its methods.

#### Base Modules

Base modules are constructed by the `BaseModule` data type.

Base modules are represented by the `BaseModule` type defined in
Syntax.v. There are two constructors: `BaseMod` and `BaseRegFile`.
`BaseMod` represents full “normal” modules. The constructor accepts a
list of registers, a list of rules, and a list of method definitions.
When a module only consists of a collection of registers, we use the
second constructor - `BaseRegFile`[^7].

The simplest base module is:
`Definition example_module : Mod := Base (BaseMod [] [] []).`[^8] This
represents a base module that has no registers, rules, or method
definitions.

Kami defines notations to simplify the representation of base modules.
This notation is illustrated in the example below:

```coq
    Example example_module : BaseModule
      := MODULE {
        (* represents a 16 bit register *)
        Register "example_register" : Bit 16 <- getDefaultConst (Bit 16)

        (* represents a rule *)
        with Rule "example_rule" := Retv

        (* represents a method *)
        with Method "example_method" (x : Bit 8) : Void := Retv
    }.
```

##### Register Files

Register files are modules that only contain registers. These are
represented by terms of type `RegFileBase`. This inductive type defines
two constructors: `RegFile` and `SyncRegFile`. The difference between
register files constructed using `RegFile` and `SyncRegFile` is
expressed in the generated Verlog code.

`RegFile` accepts six arguments: label (“dataArray”), which gives the
name of the register file; read, the name of the read method; write, the
name of the write method; IdxNum; and init, the initial value stored in
all of the register.

The following is an example register file represents a register file
containing two 4 bit registers initialized to the value 8.:

```coq
    Example register_file0 : Mod
      := Base (BaseRegFile (RegFile
           "register_file0"
           ["read0" ; "read1"]
           "write0" 2 (Some (ConstBit WO~1~0~0~0)))).
```

Given a register file, Kami defines functions to derive the registers,
rules, and methods associated with them. Register files do not have any
rules (see `getRules`).

#### Composite Modules

Composite modules represent modules that have been lumped together. We
construct them by applying the `ConcatMod` constructor from the `Mod`
type.

For example, the following example composes two modules, `module0` and
`module1`: `ConcatMod module0 module1 : Mod`.

### Module Rules, Registers, and Methods

Kami defines a number of helper functions to get the rules, registers,
and methods belonging to modules. `Compute (getAllRegisters module).`
returns all of the registers in a module. `getAllRules` and
`getAllMethods` behave similarly.

#### Hidden Methods

Kami allows use to simplify modules by hiding methods. See the
`HideMeth` constructor.

### Well Formed Modules

Kami places several additional constraints on modules. To be a well
formed module, a module's registers, rules, and methods must satisfy
certain constraints. Well formed modules are represented by the `ModWf`
record type defined in Syntax.v. `ModWf` records consist of a module and
a proof that the module is well formed. Proofs that a module is well
formed are represented by terms of the inductive predicate `WfMod` which
is also defined in Syntax.v. Proofs that a base module is well formed
are represented by terms of the inductive type `WfBaseModule`, which is
defined in Syntax.v. Proofs that a composite module is well formed are
represented by terms of `WfMod` constructed using the `ConcatModWf`
constructor.

Additionally, the library provides a way to represent well formed base
modules. Well formed base modules are represented by instances of the
`BaseModWf` record type, which is essentially a pair containing a base
module and a proof that the base module is well formed.

#### Proving that Actions are Well Formed

To prove that an action is well formed, we must construct a term of type
`WfActionT` using structural induction on action terms.

The simplest possible example is a proof that the Return Void action is
well formed. In general, Kami places no restrictions on return actions,
and we prove that a return action is well formed by applying the
`WfReturn` constructor:

```coq
    (** Represents the return void action. *)
    Example void_action : ActionT type Void := Retv.

    (** Proves that the return void action is well formed. *)
    Definition void_action_wellformed
      :  forall module : BaseModule, WfActionT module void_action
      := fun module
           => WfReturn module (Const type WO).
```

To prove that a method call is well formed, we must simply prove that
the actions performed after it are well formed. For example:

```coq
    (**      
      Represents an action that a calls a void
      method and returns void.
    *)
    Example void_method_call : ActionT type Void
      := Call _ : Void <- "example_method" (Const type WO : Void);
         Retv.

    (**
      Proves that the void method call action is
      well formed within any module.
    *)
    Definition void_method_call_wellformed
      :  forall module : BaseModule, WfActionT module void_method_call
      := fun module : BaseModule
           => WfMCall "example_method" (Void, Void) (Const type WO)
                (fun _ : word 0 => Retv)
                (fun _ : word 0 => WfReturn module (Const type WO)).
```

Proving that other actions are well formed is performed similarly. The
only effective constraint Kami imposes on well formed actions is that
register read and write actions only reference registers defined within
the current module.

#### Proving that Base Modules are Well Formed

To prove that a base module is well formed, we must prove that every
action in every module rule is well formed; that every action in every
action in every method is well formed; that every method name is unique;
that every register name is unique; and that every rule name is unique.
These constraints are represented by the inductive `WfBaseModule`
predicate.

```coq
    (** Represents the null base module. *)
    Example null_base_module : BaseModule := BaseMod [] [] [].

    (**
      Proves that the null module is well formed.
    *)
    Definition null_base_module_wellformed : WfBaseModule null_base_module
      := conj
           (fun rule (H : In rule []) => False_ind _ H)
           (conj
             (fun method (H : In method []) => False_ind _ H)
             (conj (NoDup_nil string)
               (conj (NoDup_nil string)
                     (NoDup_nil string)))).
```

#### Proving that the Composition of Two Base Modules is Wellformed

Given an action, `action` and a module `module`,
`WfConcatActionT action module` asserts that `action` can be performed
in a rule or method added to `module`.

Given two modules, `module0` and `module1`, `WfConcat` asserts that the
rules and methods defined in `module0` can be safely added to `module1`.
It does this by asserting that every action `action` defined in
`module0` satisfies `WfConcatActionT action module1`.

`WfConcatActionT` simply requires that the action is well formed in the
sense of `WfActionT` (i.e. that all register reads and writes only
reference local registers) and that none of the method calls in
`module0` reference a method hidden in `module1`.

#### Proving that Modules are Well Formed

We assert that module is wellformed using the inductive predicate
`WfMod`.

If the module is simply a base module, we apply the constructor `BaseWf`
to a proof of `WfBaseModule`. For example, extending the proof that the
null base module is well formed:

```coq
    (** Represents the null module. *)
    Example null_module : Mod := Base null_base_module.

    (** Proves that the null module is well formed. *)
    Definition null_module_wellformed : WfMod null_module := BaseWf null_base_module_wellformed.
```

#### Tactics for Proving that Modules are Well Formed

Kami provides an automated tactic named `discharge_wf` that can
automaticall prove that modules are well formed.

For example, we can prove that the null module is well formed directly
using the following:

```
    Coq < Theorem discharge_wf_example : WfMod null_module.
    1 subgoal
      
      ============================
      WfMod null_module

    thm < discharge_wf.
    No more subgoals.
```

#### Well Formed Modules

In Kami, `ModWf` represents the set of well formed modules. `ModWf` is
essentially a sigma type. For example, the wellformed null module can be
represented as follows:

```coq
    Example well_formed_null_module : ModWf := mkWfMod null_module_wellformed.
```

We can use the `discharge_wf` tactic to automatically prove the
wellformedness property for more complicated modules. For example:

```coq
    Example module2 : BaseModule                                                                         
      := MODULE {                                                                                        
        Register "example_register" : Bit 16 <- getDefaultConst (Bit 16)                                                                                                                                      
        with Rule "example_rule" := Retv                                                                                                                                                                      
        with Method "example_method" (x : Bit 8) : Void := Retv                                          
    }.

    Example wellformed_module2 : ModWf := @mkWfMod (Base module2) ltac:(discharge_wf).
```

Modeling Behavior
-----------------

### Module States

The state of a register corresponds to the value stored within it. The
state of a module/circuit corresponds to the values stored within its
registers. The behavior of a module corresponds to a series of state
transitions - i.e. a sequence of register updates, method calls, and
method executions.

#### Register States

Kami represents the values stored within registers using terms of the
`RegT` type. The following example asserts that a register named
“example\_register” contains a 2 bit value representing the number 1:

```coq
    Example example_register_value : RegT
      := ("example_register",
          existT (fullType type) (SyntaxKind (Bit 2)) WO~0~1).
```

The set of values stored in the registers belonging to a module
constitute the module's state. Kami defines a type alias `RegsT` which
represents a list of `RegT` terms. The following example asserts that
two registers named “register0” and “register1” contain two binary
values:

```coq
    Example example_register_values : RegsT
      := [("register0", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 4));
          ("register1", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 8))].
```

#### Method Calls and Executions

Kami's denotational semantics maps Kami kinds onto Gallina types, and
Kami expressions onto Gallina terms/values. Every Kami method has a
signature that is a pair specifying the kind of value accepted and
returned by the method. Kami uses `SignT` to represent the actual
Gallina terms passed to a returned by a method. For instance:

```coq
    Check ((natToWord 8 16, natToWord 8 4) : SignT (Bit 8, Bit 8)).
```

Kami uses `MethT` to represent the value passed to and returned by a
named method. For example, the following term represents the event where
a method named “example\_method” was called with a void value and
returned an 8 bit string encoding the value 4. Note, the term also
includes the methods Kami signature:

```coq
    Check ("example_method", existT SignT (Bit 0, Bit 8) (WO, natToWord 8 4)) : MethT).
```

### Actions

Kami defines an inductive predicate named `SemAction` in Syntax.v that
accepts six arguments: k, the kind returned by the action; an action;
readRegs, a set of register states; newRegs, another set of register
states; calls, a set of method call/executions; and fret, the Gallina
term representing the value returned by the action. `SemAction` terms
represent proofs that the given actions map the register values in
readRegs to the values in newRegs and include the method
calls/executions in calls.

In a digital circuit, each action represents a signal flowing across a
wire from one circuit element to another.

Kami represents the semantics of an action by defining a predicate that
takes the state before the action, and the state following the action,
and asserts that the following state results from the action.

The simplest possible action is a void return. The following example
asserts that the void return action performs no register reads, register
writes, or method calls:

```coq
    Example void_return_effect
      :  forall initial_reg_state : RegsT,
           SemAction initial_reg_state
             Retv (* the action *)
             []   (* no register reads *)
             []   (* no register writes *)
             []   (* no method calls *)
             WO   (* returns void *)
      := fun initial_reg_state
           => SemReturn
                initial_reg_state (* the initial register state *)                                       
                (Const type WO)   (* the action's return value *)                                        
                (eq_refl WO)                                                                             
                (eq_refl [])      (* the return action does not read any registers *)                    
                (eq_refl [])      (* the return action does not update any registers *)                  
                (eq_refl []).     (* the return action does not call any registers *)
```

Method calls are add entries to the list of method calls as expected:

```coq
    Example method_call_effect                                                                    
      :  SemAction
           []                                                       (* initial register state *)
           (Call _ : Void <- "method" (Const type WO : Void); Retv) (* the action *)
           [] []                                                    (* register reads and writes *)
           [("method", existT SignT (Void, Void) (WO, WO))]         (* the method call/executions *)
           WO                                                       (* the return value *)
      := SemMCall
           (s := (Void, Void))                                        (* explicitly specifies the method signature *)
           (Const type WO)                                            (* the action's return value *)
           (fun _ : word 0 => Retv)                                   (* the continuation after this call action. *)
           (eq_refl [("method", existT SignT (Void, Void) (WO, WO))]) (* the values passed to and returned by this method call. *)
           (void_return_effect []).                                   (* proves that the continuation produces the needed effect. *)
```

Register writes add entries to the list of registers that were written
to and ensures that only one write per register occurs.

```coq
    Example write_effect
      :  SemAction
           [("register", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 5))] (* the initial register state *)
           (Write "register" : Bit 8 <- $6; Retv)                                      (* the action performed *)
           []                                                                          (* the register reads *)
           [("register", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 6))] (* the register updates *)
           []                                                                          (* the method calls/executions *)
           WO                                                                          (* the return value *)
      := SemWriteReg
           (o := [("register", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 5))])
           (Const type (natToWord 8 6))

           (* prove that the correct type of value is stored. *)
           (or_introl 
             (eq_refl ("register", SyntaxKind (Bit 8))))

           (* Prove that the register has only been written to once. *)
           (fun value (H : In ("register", value) nil) => H)

           (* Prove that the value written equals the value stored. *)
           (eq_refl [("register", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 6))])

           (* Prove that the return action has no further effect. *)
           (void_return_effect
             [("register", existT (fullType type) (SyntaxKind (Bit 8)) (natToWord 8 5))]).
```

### Labels

" It \[a label\] summarizes all externally visible interactions of the
step. ... in Kami the analogous interactions are making and receiving
method calls" Choi et. al. 2017.

>    A label ℓ is a set formed from the following elements:
>
>    Label element ω ::= • | f (a) = b | f (a) = b
>
>    The label elements denote the presence of a rule (•), a called method (f (a) = b), or its dual,
>    an executed method (f (a) = b) with method name f , argument a, and return value b.

Labels are represented by terms of the type `FullLabel` which is a
notation for a pair containing an initial register state and a list of
rules and methods. The list of rules and methods is constructed in such
a way as to ensure that only (at most) one rule is included and, if a
rule is included, the rule is the first item in the list.

The following is an example label:

-   `([], (Rle `“`example_rule`”`, [])) : FullLabel` - a label with a
    single rule named “example\_rule.”

The following label contains a single rule and a single method
call/execution.

```coq
    ([], (* register updates *)
      (Rle "example_rule",
      [("example_method", existT SignT (Bit 0, Bit 8) (WO, natToWord 8 4))])
    ) : FullLabel
```

### Substeps

“A substep defines the execution of a collection of at most one rule and
any number of methods.” (Choi et. al. 2017)

In a digital circuit, a substep represents a set of wires that are
actively carrying signals from one set of circuit elements to another
set of elements. Clearly, only certain actions can be performed
simultaneously. For example, only one register write operation can occur
at a time and only one call per method is allowed per substep.

Kami's semantics only allow one rule to be executed at a time. When
compiled, Kami generates a scheduler that attempts to execute more than
one rule at a time, but this restriction simplifies the analysis.

Labels are used to record the methods called, the methods executed, and
the rule executed within a step.

Substeps are represented by terms of the inductive predicate type
`Substeps`, which is defined in Syntax.v. This predicate accepts a base
module, a register state list, and a list of labels and returns true iff
the list denotes a valid substep. Substeps are constructed by adding
rule executions and method call/executions to an initial null substep.

The simplest possible substep is the nil substep which involves no
actions, method calls, or method executions:

```coq
    Example null_substep
      :  Substeps null_base_module [] []
      := NilSubstep null_base_module [] (eq_refl []).
```

The following illustrates a substep consisting of a single rule
execution, where the rule is a simple return statement.

```coq
    Example rule_substep
      :  Substeps
           (BaseMod [register0] [rule0] [])                                                              
           [("register0",                                                                                
             existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5))]                             
           [([], (Rle "rule0", []))]                                                                     
      := AddRule
           (m := BaseMod [register0] [rule0] [])                                                         
           (o := [("register0", existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5))])         

           (* prove that the register types in the initial register state agree with the module definitions. *)      
           (eq_refl [("register0", SyntaxKind (Bit 32))])                                                

           (* the rule body. *)                                                                          
           (fun type => Ret Const type WO)                                                               

           (* prove that the rule is defined by the module. *)                                           
           (or_introl                                                                                    
             (eq_refl ("rule0", fun type => Ret Const type WO)))                                         

           (* proves that the rule body produces the given register reads, register writes, and method calls and returns void. *)
           (void_return_effect                                                                           
             [("register0", existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5))])             

           (* proves that the types given for register reads agree with the module definitions. *)       
           (fun read (H : In read nil) => False_ind _ H)                                                 

           (* proves that the types given for register writes agree with the module definitions. *)      
           (fun write (H : In write nil) => False_ind _ H)                                               

           (* explicitly give the first label. *)                                                        
           (l := [([], (Rle "rule0", []))])                                                              

           (* explicitly give the remaining labels. *)                                                   
           (ls := [])                                                                                    

           (* prove that the first label contains an entry for this rule. *)                             
           (eq_refl [([], (Rle "rule0", []))])                                                           

           (* *)                                                                                         
           (fun label (H : In label nil) _ => False_ind _ H)                                             

           (* prove that none of the remaining labels are rule executions. *)                            
           (fun label (H : In label nil) => False_ind _ H)                                               

           (* prove that the remaining substeps are valid. *)                                            
           (NilSubstep                                                                                   
             (BaseMod [register0] [rule0] [])                                                            
             [("register0", existT (fullType type) (SyntaxKind (Bit 32)) (natToWord 32 5))]              
             (eq_refl [("register0", SyntaxKind (Bit 32))])).
```

The following example illustrates a substep consisting of a single
method call.

```coq
    (** Represents the null method. *)
    Example method1 : DefMethT
      := ("method1",
           existT MethodT (Void, Void)
             (fun type (_ : type (Void))
               => Retv)).

    (** Represents a substep that calls the null method. *)
    Example method_substep
      :  Substeps
           (BaseMod [] [] [method1])
           [] (* no initial register states. *)
           [([], (Meth ("method1", existT SignT (Void, Void) (WO, WO)), []))]
      := AddMeth
           (m := BaseMod [] [] [method1])
           (o := [])
           (* prove that the register types in the initial register state agree with the module definitions. *)
           (eq_refl [])

           (* the method body *)
           (existT MethodT (Void, Void) (fun type (_ : type (Void)) => Retv))

           (* prove that the method is defined by the module. *)
           (or_introl
             (eq_refl ("method1", existT MethodT (Void, Void) (fun type (_ : type (Void)) => Retv))))

           (* prove that the method body produces the given effects. *)
           (void_return_effect [])

           (* proves that the types given for register reads agree with the module definitions. *)
           (fun read (H : In read nil) => False_ind _ H)

           (* proves that the types given for register writes agree with the module definitions. *)
           (fun write (H : In write nil) => False_ind _ H)

           (* explicitly give the first label. *)
           (l := [([], (Meth ("method1", existT SignT (Void, Void) (WO, WO)), []))])

           (* explicitly give the remaining labels. *)
           (ls := [])

           (* prove that the first label contains an entry for this rule. *)
           (eq_refl [([], (Meth ("method1", existT SignT (Void, Void) (WO, WO)), []))])

           (* prove that this method is called only once per substep. *)
           (fun label (H : In label nil) _ => False_ind _ H)

           (* prove that the remaining substeps are valid. *)
           (NilSubstep
             (BaseMod [] [] [method1])
             []
             (eq_refl [])).
```

### Steps

“A step is a single atomic transition of a module, where all internal
communications \[method calls and executions\] are hidden.” (Choi et.
al. 2017).

In a digital circuit, a step represents the set of actions and register
updates that can occur during a single clock cycle.

Steps are represented by terms of the inductive predicate type `Step`.
Like `Substep`, this predicate accepts a module, list of register
states, and a list of labels. It allows us to define steps by
concatenating base steps (represented by `BaseStep`) to form combined
steps represented by `ConcatModStep`.

The following is a simple example of a step that executes a void return
rule named “rule0”:

```coq
    (** 
      An example step in which a single rule named
      "rule0" is executed.
                                                                                                         
      Note: this rule is simply a substep in which
      we've verified that the number of calls is less
      than the number of executions for each method.
    *)
    Example rule_step
      : Step
          (Base (BaseMod [] [rule0] []))
          []
          [([], (Rle "rule0", []))]
      := BaseStep
           rule_substep
           (* prove that the number of calls is less than or equal to the number of executions for every method. *)
           (fun method (H : In (fst method) nil)
             => ltac:(contradiction)).
```

Note that, in the example above, we've defined a substep that records
the rule execution. To derive a Kami step, we simply prove that the
number of calls is less than the number of executions for every method.

### Traces

A trace is a pair that consists of an initial register state and a list
of labels. Trace's summarize the externally visible behavior of a given
module. Kami represents traces using
`Trace : Mod -> RegsT -> list (list FullLabel) -> Prop`.

`Trace` includes two constructors. `InitTrace`

Footnotes
---------

<references/>
<Category:Note>

[^1]: “In brief, this encoding style \[Parametric Higher-Order Abstract
    Syntax\] represents terms as polymorphic functions, parameterized
    over representation types for **variables**, one per object-language
    type.” Choi et. al. 2017

[^2]: [Kami: A Platform for High-Level Parametric Hardware Specification
    and Its Modular
    Verification](http://plv.csail.mit.edu/kami/papers/icfp17.pdf)

[^3]: “the definitions of the interacting methods are semantically
    inlined at the places of their calls.” Choi et. al. 2017

[^4]: “we found it convenient to define one Kami language with embedding
    of normal Coq programs as an optional feature, by convention to be
    used only for specifications, not “real” designs.” Choi et. al. 2017

[^5]: “the return value \[from method calls\] is assumed and cannot be
    computed”, Choi et. al. 2017

[^6]: As a general convention, we avoid defining module methods. Doing
    so simplifies proofs.

[^7]: Using `BaseRegFile` allows us to apply Verilog optimizations to
    the output

[^8]: To use the list notations execute
    `Require Import List. Import ListNotations. Open Scope list_scope.`
