# symmetry

Exploratory Haskell library for symmetry-respecting linear maps, in the vein of TensorKit.

Extracted from the `quantum` tensor-network repo so this layer can be cleaned up on its own.

The unique feature is that it is written in Haskell, which has a type system that is much more expressive than Julia, and can encode the relevant mathematical structure at compile time. For example, we can write

```haskell
x :: C 2 ⊗ C 3
x = vec (1,2) ⊗ vec (4,5,6)
```

The top line specifies the type, and should be read as the mathematical statement $x : \mathbb{C}^2 \otimes \mathbb{C}^3$.

Haskell really checks this. For example, if you write

```haskell
x = vec (1,2) ⊗ vec (4,5)
```

you will get a type error: the Clebsch–Gordan / tensor-product dimensions do not match.

## Clebsch–Gordan rules and fusion in the types

The real point of this library is to write symmetry-respecting linear maps (intertwiners). Like TensorKit, the representation of intertwiners takes advantage of Schur's lemma to massively reduce the amount of storage needed for a large linear map. Unlike TensorKit, everything is checked at compile time.

## Why do this?

Without statically checked types, it is very easy to make mistakes. It is also very easy to lose track of what the shapes of arrays should be.

This library is an exploration of the idea that tensor network libraries should really be written in languages with expressive types. A more extreme version would be to use Lean, where the types are in principle powerful enough to prove the correctness of the algorithms themselves. Haskell is a nice middle ground, where the types are reasonably expressive, but the compiled code is engineered to be fast.

## Build

Depends on a sibling checkout of `linearmap-family` (same layout as `quantum`):

```bash
cabal build symmetry:lib:symmetry
```
