# representations

Exploratory Haskell library for working with maps between representations (i.e. symmetry-respecting linear maps, or intertwiners), in the vein of TensorKit.

The unique feature is that it is written in Haskell, which has a type system that is much much more expressive than Julia, and can encode the relevant mathematical structure of e.g. spin representations in the types themselves. For example, we can write

```haskell
x :: C 2 ⊗ C 3
x = vec (1,2) ⊗ vec (4,5,6)
```

The top line specifies the type, and should be read as the mathematical statement $x : \mathbb{C}^2 \otimes \mathbb{C}^3$.

Haskell really checks this. For example, if you write

```haskell
x = vec (1,2) ⊗ vec (4,5)
```

you will see the mistake underlined in red, like so:

![](example.png) 

indicating a type error: the second vector is in $\mathbb{C}^2$, but should be in $\mathbb{C}^3$, given the stated type. The code will not compile.

## Clebsch–Gordan rules and fusion in the types

The real point of this library is to write symmetry-respecting linear maps (intertwiners). Like TensorKit, the representation of intertwiners takes advantage of Schur's lemma to massively reduce the amount of storage needed for a large linear map. Unlike TensorKit, everything is checked at compile time. For instance:

```haskell
f :: ('REP '[2 × SpinHalf] :⊗: 'REP '[1 × SpinHalf]) --> 'REP ((2 × SpinZero) ⊕ (1 × SpinOne))
f = intertwiner (   

  mkBlock (mat (1, 0, 0, 1))
  (mkBlock (mat (1, 1))

  InterNil )) `Comp`Fuse
```

Here, the type should be read as: $f : (2 \times \frac{1}{2}) \otimes (1 \times \frac{1}{2}) \rightarrow (2 \times 0) \oplus (1 \times 1)$, where $\rightarrow$ here means an intertwiner, not just a generic linear map. 

As before, the type is really checked. If you change the spaces of the matrices built by `mat`, the code will be underlined in red in your editor and won't compile.

But Haskell also *infers* types for you, so if in your editor you mouse over the first occurrence of `mat` above, it will tell you that the block has the shape of a $2 \times 2$ matrix. I find this extremely helpful as a user of the code.

## Why do this?

Without statically checked types, it is very easy to make mistakes. It is also very easy to lose track of what the shapes of arrays should be. Since Haskell both checks and infers types, both of these problems are almost entirely solved.

More broadly, this library is an exploration of the idea that tensor network libraries should really be written in languages with expressive types. A more extreme version would be to use Lean, where the types are in principle powerful enough to prove various theorems (e.g. you don't need to assume Schur's lemma or hard code various 6j symbols - you could actually write a program that proves it / derives them). 

Haskell is a nice middle ground, where the types are reasonably expressive, but the compiled code is fast. Probably slower than Julia, but backends to Blas and LAPACK routines in C. Compilation itself is not fast, but that is a developer problem, not a user problem.

## How this works

Getting this to work requires quite a bit of type-level programming, including singletons. From a user perspective, this is all under the hood.


## AI usage

Type-level programming is a bit of an art in Haskell, since it pushes the limits of the type system, often with experimental features. Since I don't particularly care *how* the fancy dependent types are implemented with singletons and so on, this is where I delegated the most to AI.

