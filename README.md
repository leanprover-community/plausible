# Chamelean 
Chamelean is an extension of Lean's Plausible property-based testing library which automatically derives
generators, enumerators and checkers for inductive relations.

Our design is heavily inspired by [Coq/Rocq's QuickChick](https://github.com/QuickChick/QuickChick) library and the following papers:
- *Testing Theorems, Fully Automatically* (under submission, 2025)
- [*Computing Correctly with Inductive Relations* (PLDI 2022)](https://lemonidas.github.io/pdf/ComputingCorrectly.pdf)
- [*Generating Good Generators for Inductive Relations* (POPL 2018)](https://lemonidas.github.io/pdf/GeneratingGoodGenerators.pdf)

## Overview
Like QuickChick, we provide the following typeclasses:
- `Arbitrary`: unconstrained random generators for inhabitants of algebraic data types
- `ArbitrarySuchThat`: constrained generators which only produce random values that satisfy a user-supplied inductive relation
- `ArbitrarySized`, `ArbitrarySizedSuchThat`: versions of the two typeclasses above where the generator's size parameter is made explicit 
- `Enum, EnumSuchThat, EnumSized, EnumSizedSuchThat`: Like their `Arbitrary` counterparts but for deterministic enumerators instead
- `DecOpt`: Checkers (partial decision procedures that return `Option Bool`) for inductive propositions

We provide various top-level commands which automatically derive generators for Lean `inductive`s:

**1. Deriving unconstrained generators/enumerators**              
An *unconstrained* generator produces random inhabitants of an algebraic data type, while an unconstrained enumerator *enumerates* (deterministically) these inhabitants. 
          
Users can write `deriving Arbitrary` and/or `deriving Enum` after an inductive type definition, e.g..
```lean 
inductive Foo where
  ...
  deriving Arbitrary, Eunm
```
Alternatively, users can also write `deriving instance Arbitrary for T1, ..., Tn` (or `deriving instance Enum ...`) as a top-level command to derive `Arbitrary` / `Enum` instances for types `T1, ..., Tn` simultaneously.

To sample from a derived unconstrained generator, users can simply call `runArbitrary`, specify the type 
for the desired generated values and provide some `Nat` to act as the generator's size parameter (`10` in the example below):

```lean
#eval runArbitrary (α := Tree) 10
```

Similarly, to return the elements produced form a derived enumerator, users can call `runEnum` like so:
```lean
#eval runEnum (α := Tree) 10
```

If you are defining your own type it needs instances of `Repr`, `Plausible.Shrinkable` and
`Plausible.SampleableExt` (or `Plausible.Arbitrary`):

**2. Deriving constrained generators** (for inductive relations)                
A *constrained* producer only produces values that satisfy a user-specified inductive relation. 

We provide two commands for deriving constrained generators/enumerators. For example, 
support we want to derive constrained producers of `Tree`s satisfying some inductive relation `balanced n t` (height-`n` trees that are `balanced`. To do so, the user would write:

```lean
-- `#derive_generator` & `#derive_enumerator` derive constrained generators/enumerators 
-- for `Tree`s that are balanced at some height `n`,
-- where `balanced n t` is a user-defined inductive relation
#derive_generator (fun (t : Tree) => balanced n t) 
#derive_enumerator (fun (t : Tree) => balanced n t)
```
To sample from the derived producer, users invoke `runSizedGen` / `runSizedEnum` & specify the right 
instance of the `ArbitrarySizedSuchThat` / `EnumSizedSuchThat` typeclass (along with some `Nat` to act as the generator size):

```lean
-- For generators:
#eval runSizedGen (ArbitrarySizedSuchThat.arbitrarySizedST (fun t => balanced 5 t)) 10

-- For enumerators:
-- (we recommend using a smaller `Nat` as the fuel for enumerators to avoid stack overflow)
#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun t => balanced 5 t)) 3
```

Some extra details about the grammar of the lambda-abstraction that is passed to `#derive_generator` / `#derive_enumerator`:

Specifically: in the command
```lean
#derive_generator (fun (x : t) => P x1 ... x .... xn)
```
`P` must be an inductively defined relation, `x` is the value to be generated (the type annotation on `x` is required), and `x1 ... xn` are (implicitly universally quantified) variable names. Following QuickChick, we expect `x1, ..., xn` to be variable names (we don't support literals in the position of the `xi` currently). 

**3. Deriving checkers (partial decision procedures)** (for inductive relations)                                 
A checker for an inductively-defined `Prop` is a `Nat -> Option Bool` function, which 
takes a `Nat` argument as fuel and returns `none` if it can't decide whether the `Prop` holds (e.g. it runs out of fuel),
and otherwise returns `some true/some false` depending on whether the `Prop` holds.

We provide a command elaborator which elaborates the `#derive_checker` command:

```lean
-- `#derive_checker` derives a checker which determines whether `Tree`s `t` 
-- satisfy the `balanced` inductive relation mentioned above 
#derive_checker (balanced n t)
```

## Repo overview

**Building & compiling**:
- To compile, run `lake build` from the top-level repository.
- To run snapshot tests, run `lake test`.
- To run linter checks, run `lake lint`. 
  + This invokes the linter provided via the [Batteries](https://github.com/leanprover-community/batteries/tree/main) library.
  + Note that some linter warnings are suppressed in [`scripts/nolints.json`](./scripts/nolints.json).

**Typeclass definitions**:
- [`Arbitrary.lean`](./Plausible/Arbitrary.lean): The `Arbitrary` & `ArbitrarySized` typeclasses for unconstrained generators, adapted from QuickChick
- [`ArbitrarySizedSuchThat.lean`](./Plausible/Chamelean/ArbitrarySizedSuchThat.lean): The `ArbitrarySuchThat` & `ArbitrarySizedSuchThat` typeclasses for constrained generators, adapted from QuickChick
- [`DecOpt.lean`](./Plausible/Chamelean/DecOpt.lean): The `DecOpt` typeclass for partially decidable propositions, adapted from QuickChick
- [`Enumerators.lean`](./Plausible/Chamelean/Enumerators.lean): The `Enum, EnumSized, EnumSuchThat, EnumSizedSuchThat` typeclasses for constrained & unconstrained enumeration

**Combinators for generators & enumerators**:
- [`GeneratorCombinators.lean`](./Plausible/Chamelean/GeneratorCombinators.lean): Extra combinators for Plausible generators (e.g. analogs of the `sized` and `frequency` combinators from Haskell QuickCheck)
- [`OptionTGen.lean`](./Plausible/Chamelean/OptionTGen.lean): Generator combinators that work over the `OptionT Gen` monad transformer (representing generators that may fail)
- [`EnumeratorCombinators.lean`](./Plausible/Chamelean/EnumeratorCombinators.lean): Combinators over enumerators 

**Algorithm for deriving constrained producers & checkers** (adapted from the QuickChick papers):
- [`UnificationMonad.lean`](./Plausible/Chamelean/UnificationMonad.lean): The unification monad described in [*Generating Good Generators*](https://lemonidas.github.io/pdf/GeneratingGoodGenerators.pdf)
- [`Schedules.lean`](./Plausible/Chamelean/Schedules.lean): Type definitions for generator schedules, as described in *Testing Theorems*
- [`DeriveSchedules.lean`](./Plausible/Chamelean/DeriveSchedules.lean): Algorithm for deriving generator schedules, as described in *Testing Theorems* 
- [`DeriveConstrainedProducer.lean`](./Plausible/Chamelean/DeriveConstrainedProducer.lean): Algorithm for deriving constrained generators using the aforementioned unification algorithm & generator schedules
- [`MExp.lean`](./Plausible/Chamelean/MExp.lean): An intermediate representation for monadic expressions (`MExp`), used when compiling schedules to Lean code
- [`MakeConstrainedProducerInstance.lean`](./Plausible/Chamelean/MakeConstrainedProducerInstance.lean): Auxiliary functions for creating instances of typeclasses for constrained producers (`ArbitrarySuchThat`, `EnumSuchThat`)
- [`DeriveChecker.lean`](./Plausible/Chamelean/DeriveChecker.lean): Deriver for automatically deriving checkers (instances of the `DecOpt` typeclass)

**Derivers for unconstrained producers**:
- [`DeriveArbitrary.lean`](./Plausible/DeriveArbitrary.lean): Deriver for unconstrained generators (instances of the `Arbitrary` / `ArbitrarySized` typeclasses)
- [`DeriveEnum.lean`](./Plausible/Chamelean/DeriveEnum.lean): Deriver for unconstrainted enumerators 
(instances of the `Enum` / `EnumSized` typeclasses) 

**Miscellany**:
- [`TSyntaxCombinators.lean`](./Plausible/Chamelean/TSyntaxCombinators.lean): Combinators over `TSyntax` for creating monadic `do`-blocks & other Lean expressions via metaprogramming
- [`LazyList.lean`](./Plausible/Chamelean/LazyList.lean): Implementation of lazy lists (used for enumerators)
- [`Idents.lean`](./Plausible/Chamelean/Idents.lean): Utilities for dealing with identifiers / producing fresh names 
- [`Utils.lean`](./Plausible/Chamelean/Utils.lean): Other miscellaneous utils

**Tests & Examples**:
- [`ExampleInductiveRelations.lean`](./Plausible/Chamelean/Examples/ExampleInductiveRelations.lean): Some example inductive relations (BSTs, balanced trees, STLC)
- [`DeriveRegExpGenerator.lean`](./Test/DeriveArbitrary/DeriveRegExpGenerator.lean): Example generators for regular expressions

### Tests
**Overview of snapshot test corpus**:
- The [`Test`](./Test/) subdirectory contains [snapshot tests](https://www.cs.cornell.edu/~asampson/blog/turnt.html) (aka [expect tests](https://blog.janestreet.com/the-joy-of-expect-tests/)) for the `#derive_generator` & `#derive_arbitrary` command elaborators. 
- Run `lake test` to check that the derived generators in [`Test`](./Test/) typecheck, and that the code for the derived generators match the expected output.
- See [`DeriveBSTGenerator.lean`](./Test/DeriveArbitrarySuchThat/DeriveBSTGenerator.lean) & [`DeriveBalancedTreeGenerator.lean`](./Test/DeriveArbitrarySuchThat/DeriveBalancedTreeGenerator.lean) for examples of snapshot tests. Follow the template in these two files to add new snapshot test file, and remember to import the new test file in [`Test.lean`](./Test.lean) afterwards.

**Key Value Store Example**:
- [`KeyValueStore.lean`](./Test/KeyValueStoreExample/KeyValueStore.lean): Definitions for a hypothetical key-value store, in which inductive types are used to encode API calls and K/V states, and inductive relations are used to define API call semantics
- [`TestKeyValueStoreCheckerGenerators.lean`](./Test/KeyValueStoreExample/TestKeyValueStoreCheckerGenerators.lean): The derived checkers & generators for the K/V store example (in particular, the derived generator produces well-formed sequences of API calls)

**Cedar Example**:
- [`Cedar.lean`](./Test/CedarExample/Cedar.lean): Lean formalization of a subset of the [Cedar policy language (OOPSLA '24)](https://dl.acm.org/doi/10.1145/3649835), adapted from Mike Hicks's Coq formalization
- [`CedarCheckerGenerators.lean`](./Test/CedarExample/CedarCheckerGenerators.lean): Snapshot tests for derived checkers & generators for Cedar terms / types / schemas 
- [`CedarWellTypedTermGenerator.lean`](./Test/CedarExample/CedarWellTypedTermGenerator.lean): Example generator for well-typed Cedar expressions

**Tests for Unconstrained Generators (`#derive_arbitrary`)**:
- [`BitVecStructureTest.lean`](./Test/DeriveArbitrary/BitVecStructureTest.lean): Tests for structures with dependently-typed `BitVec` arguments
- [`DeriveNKIBinopGenerator.lean`](./Test/DeriveArbitrary/DeriveNKIBinopGenerator.lean): Derived generator for NKI binary operators (logical, comparison, arithmetic, bitwise)
- [`DeriveNKIValueGenerator.lean`](./Test/DeriveArbitrary/DeriveNKIValueGenerator.lean): Derived generator for NKI value types (none, bool, int, string, tensor, etc.)
- [`DeriveRegExpGenerator.lean`](./Test/DeriveArbitrary/DeriveRegExpGenerator.lean): Derived generator for regular expressions with counterexample testing
- [`DeriveSTLCTermTypeGenerators.lean`](./Test/DeriveArbitrary/DeriveSTLCTermTypeGenerators.lean): Derived generator for STLC types and terms
- [`DeriveTreeGenerator.lean`](./Test/DeriveArbitrary/DeriveTreeGenerator.lean): Derived generator for binary trees with mirror property testing
- [`MissingNonRecursiveConstructorTest.lean`](./Test/DeriveArbitrary/MissingNonRecursiveConstructorTest.lean): Error handling test for types without non-recursive constructors
- [`MutuallyRecursiveTypeTest.lean`](./Test/DeriveArbitrary/MutuallyRecursiveTypeTest.lean): Derived generator for mutually recursive inductive types
- [`ParameterizedTypeTest.lean`](./Test/DeriveArbitrary/ParameterizedTypeTest.lean): Derived generator for parameterized types (polymorphic `MyList`)
- [`StructureTest.lean`](./Test/DeriveArbitrary/StructureTest.lean): Derived generator for structures with named fields

**Tests for Constrained Generators (`#derive_generator`)**:
- [`DeriveBSTGenerator.lean`](./Test/DeriveArbitrarySuchThat/DeriveBSTGenerator.lean): Derived generator for Binary Search Trees (with a BST insertion property-based test)
- [`DeriveBalancedTreeGenerator.lean`](./Test/DeriveArbitrarySuchThat/DeriveBalancedTreeGenerator.lean): Derived generator for balanced binary trees
- [`DerivePermutationGenerator.lean`](./Test/DeriveArbitrarySuchThat/DerivePermutationGenerator.lean): Derived generator for list permutations
- [`DeriveRegExpMatchGenerator.lean`](./Test/DeriveArbitrarySuchThat/DeriveRegExpMatchGenerator.lean): Derived generator for strings matching regular expressions
- [`DeriveSTLCGenerator.lean`](./Test/DeriveArbitrarySuchThat/DeriveSTLCGenerator.lean): Derived generator for well-typed STLC terms
- [`FunctionCallsTest.lean`](./Test/DeriveArbitrarySuchThat/FunctionCallsTest.lean): Tests handling inductive relations with function calls in conclusions
- [`MutuallyRecursiveRelationsTest.lean`](./Test/DeriveArbitrarySuchThat/MutuallyRecursiveRelationsTest.lean): Tests for mutually recursive inductive relations (`Even`/`Odd`)
- [`NonLinearPatternsTest.lean`](./Test/DeriveArbitrarySuchThat/NonLinearPatternsTest.lean): Tests for relations with non-linear patterns (repeated variables)
- [`SimultaneousMatchingTests.lean`](./Test/DeriveArbitrarySuchThat/SimultaneousMatchingTests.lean): Tests for relations with simultaneous pattern matching on multiple inputs

**Tests for Checkers (`#derive_checker`)**:
- [`DeriveBSTChecker.lean`](./Test/DeriveDecOpt/DeriveBSTChecker.lean): derived checker for BSTs
- [`DeriveBalancedTreeChecker.lean`](./Test/DeriveDecOpt/DeriveBalancedTreeChecker.lean): derived checker for balanced trees
- [`DerivePermutationChecker.lean`](./Test/DeriveDecOpt/DerivePermutationChecker.lean): derived checker for list permutations
- [`DeriveRegExpMatchChecker.lean`](./Test/DeriveDecOpt/DeriveRegExpMatchChecker.lean): derived checker for strings matching regular expression patterns
- [`DeriveSTLCChecker.lean`](./Test/DeriveDecOpt/DeriveSTLCChecker.lean): derived STLC type-checker
- [`ExistentialVariablesTest.lean`](./Test/DeriveDecOpt/ExistentialVariablesTest.lean): Tests for relations with existentially quantified variables
- [`FunctionCallsTest.lean`](./Test/DeriveDecOpt/FunctionCallsTest.lean): Tests for derived checker with function calls in the conclusion of constructors 
- [`NonLinearPatternsTest.lean`](./Test/DeriveDecOpt/NonLinearPatternsTest.lean): Tests for derived checker with non-linear patterns
- [`SimultaneousMatchingTests.lean`](./Test/DeriveDecOpt/SimultaneousMatchingTests.lean): Derived checker for inductive relations which require matching on multiple inputs

**Tests for Unconstrained Enumerators (`#derive_enum`)**:
- [`BitVecStructureTest.lean`](./Test/DeriveEnum/BitVecStructureTest.lean): Derived enumerators for structures with `BitVec` arguments
- [`DeriveNKIBinopEnumerator.lean`](./Test/DeriveEnum/DeriveNKIBinopEnumerator.lean): Derived enumerators for binary operators in the [NKI language](https://github.com/leanprover/KLR/blob/main/KLR/NKI/Basic.lean)
- [`DeriveNKIValueEnumerator.lean`](./Test/DeriveEnum/DeriveNKIValueEnumerator.lean): Derived enumerators for value types in the [NKI language](https://github.com/leanprover/KLR/blob/main/KLR/NKI/Basic.lean)
- [`DeriveRegExpEnumerator.lean`](./Test/DeriveEnum/DeriveRegExpEnumerator.lean): Derived enumerators for regular expressions
- [`DeriveSTLCTermTypeEnumerators.lean`](./Test/DeriveEnum/DeriveSTLCTermTypeEnumerators.lean): Derived enumerators for STLC types and terms
- [`DeriveTreeEnumerator.lean`](./Test/DeriveEnum/DeriveTreeEnumerator.lean): Derived enumerators for binary trees
- [`StructureTest.lean`](./Test/DeriveEnum/StructureTest.lean): Derived enumerators for structures with named fields

**Tests for Constrained Enumerators (`#derive_enumerator`)**:
- [`DeriveBSTEnumerator.lean`](./Test/DeriveEnumSuchThat/DeriveBSTEnumerator.lean): Derived enumerators for Binary Search Trees
- [`DeriveBalancedTreeEnumerator.lean`](./Test/DeriveEnumSuchThat/DeriveBalancedTreeEnumerator.lean): Derived enumerators for balanced trees
- [`DerivePermutationEnumerator.lean`](./Test/DeriveEnumSuchThat/DerivePermutationEnumerator.lean): Derived enumerators for permutations
- [`DeriveRegExpMatchEnumerator.lean`](./Test/DeriveEnumSuchThat/DeriveRegExpMatchEnumerator.lean): Derived enumerators for regex matching
- [`DeriveSTLCEnumerator.lean`](./Test/DeriveEnumSuchThat/DeriveSTLCEnumerator.lean): Derived enumerators for well-typed STLC terms
- [`NonLinearPatternsTest.lean`](./Test/DeriveEnumSuchThat/NonLinearPatternsTest.lean): Derived enumerator for inductive relations exhibiting with non-linear patterns
- [`SimultaneousMatchingTests.lean`](./Test/DeriveEnumSuchThat/SimultaneousMatchingTests.lean): Derived enumerator for inductive relations which require matching on multiple inputs

**Enumerator Infrastructure Tests**:
- [`EnumInstancesTest.lean`](./Test/Enum/EnumInstancesTest.lean): Tests for basic enumerator instances on Nat, Bool, pairs, sums, lists, etc.

**Auxiliary definitions for snapshot tests**:
- [`BinaryTree.lean`](./Test/CommonDefinitions/BinaryTree.lean): Binary tree datatype with `BST` (Binary Search Tree) and `Between` relations
- [`FunctionCallInConclusion.lean`](./Test/CommonDefinitions/FunctionCallInConclusion.lean): Example inductive relation with function calls in constructor conclusions 
- [`ListRelations.lean`](./Test/CommonDefinitions/ListRelations.lean): Various inductive relations over lists, some of which require pattern-matching on multiple inputs 
- [`Permutation.lean`](./Test/CommonDefinitions/Permutation.lean): Inductive relation for list permutations
- [`STLCDefinitions.lean`](./Test/CommonDefinitions/STLCDefinitions.lean): Simply-Typed Lambda Calculus (STLC) definitions including types, terms, typing judgments, and lookup relations

**Plausible Tests** (inherited from the original Plausible repo):
- [`Tactic.lean`](./Test/Tactic.lean): Tests the `plausible` tactic on core Lean types
- [`Testable.lean`](./Test/Testable.lean): Tests for the `Testable` typeclass infrastructure with custom types

For more documentation refer to the module docs.
