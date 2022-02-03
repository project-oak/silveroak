### Arrow References Recommended

- [Generalising Monads to Arrows - John Huges](http://www.cse.chalmers.se/~rjmh/Papers/arrows.pdf)

  The original Arrows paper

- [Generalized Arrows - Adam Megacz Joseph](https://www2.eecs.berkeley.edu/Pubs/TechRpts/2014/EECS-2014-130.pdf)

  The original Arrows formulation requires a function `arr : (x->y) -> a x y`,
  this thesis shows a formulation of arrows that doesn't require this function.
  Additionally it:

    - Proves a categoral foundation for these Generalized Arrows
    - Proves that programming languages can be represented as Generalized Arrows
        (not used in Cava work)
    - Argues Kappa Calculus, which is an object language lacking first-class
        functions, is more appropriate for modeling computation with arrows than other
        approaches.

  Recommended sections:

    - 2.1 - Arrows in Haskell
    - 2.1.1 - The pow Function using Arrows
    - 2.1.3 - Circuits using Arrows
    - 2.2 Generalized Arrows in Haskell
    - 2.2.1 The pow Function using Generalized Arrows

   Optional sections:

     - 2.3 - Circuits using a Two-Level Language 
     - 4.3 - Kappa Calculus as the Minimal Object Language


### Arrow References Additional

- [Programming with Arrows - John Hughes](http://www.cse.chalmers.se/~rjmh/afp-arrows.pdf)
- [The arrow calculus - Sam Lindley, Philip Wadler, and Jeremy Yallop](http://homepages.inf.ed.ac.uk/slindley/papers/arrow-calculus.pdf)


### Optional Kappa Calculus References

The following are the foundational work of Kappa Calculus but Adam Megacz thesis
sections are enough information on Kappa Calculus for this project.

- [Decomposing typed lambda calculus into a couple of categorical programming
languages - Masahito Hasegawa](https://link.springer.com/chapter/10.1007%2F3-540-60164-3_28)

  "He showed that just as the 𝜆-calculus can be used as a "syntax" for
  specifying morphisms in a cartesian closed category, so too can the 𝜅-calculus
  -- roughly the 𝜆-calculus without first-class functions -- be used as a
  "syntax" for specifying morphisms. I recommend studying the figure immediately
  after the first paragraph of section 3 in his paper (very carefully). It
  conveys both the essence of these categories and their relevance to the study
  of programming languages." - https://mathoverflow.net/questions/36866/what-are-%ce%baappa-categories/37180#37180

- [Functional completeness of cartesian categories](https://www.sciencedirect.com/science/article/pii/0003484374900035?via%3Dihub)

  First formulation of ideas 

## Arrow usage in this project

This project currently uses the generalized arrows described by Adam Megacz
work with some notable differences:

- Currently the Arrow sub classes are not broken out into their own classes (e.g
    ArrowDrop)
- Arrows are used "directly" and we don't represent lanuages as generalized
    arrows. Adam's construction of multilevel languages makes heavy use of the
    category theory form.
- Conversion between Kappa Calculus and Arrows does not follow the paper and is
  currently performed via a lambda-closure-conversion-like method. This is as
  the paper method requires encoding the source and target languages as
  generalized arrows or through the papers custom typing tree method.
- Additional forms of equivalence are specified to allow circuit equivalence
    without equality. Currently there is one form of equivalence per Arrow instance,
    although this could change. Each instance equivalence is related to the
    instance:

      - Evaluation equivalence is pointwise equivalence (e.g. `f~g if f(x)~g(x)`)
      - The constructive instance equivalence is structural equivalence with
          some allowed transforms such as `f >>> drop ~ drop`, that is, dropping
          all outputs from some component is equivalent to immediately dropping.
      - Netlist equivalence is not implemented but should perhaps be if the hdl is
          equivalent up to reordering.

## PHOAS

Kappa Calculus is encoded as an inductive type as detailed by 
[Adam Chlipala in Parametric Higher-Order Abstract Syntax (PHOAS) for Mechanized Semantics](http://adam.chlipala.net/papers/PhoasICFP08/).

```Coq
Variable var: object -> object -> Type.

Inductive kappa_sugared : object -> object -> Type :=
| Var: forall x y,    var x y -> kappa_sugared x y
| Abs: forall x y z,  (var unit x -> kappa_sugared y z) -> kappa_sugared (x ** y) z
| App: forall x y z,  kappa_sugared (x ** y) z -> kappa_sugared unit x -> kappa_sugared y z
| Com: forall x y z,  kappa_sugared y z -> kappa_sugared x y -> kappa_sugared x z
| Arr: forall x y,    morphism x y -> kappa_sugared x y
| Let: forall x y z,  kappa_sugared unit x -> (var unit x -> kappa_sugared y z) -> kappa_sugared y z.

Inductive kappa : object -> object -> Type :=
| DVar : forall x y,   var x y -> kappa x y
| DAbs : forall x y z, (var unit x -> kappa y z) -> kappa (x**y) z
| DApp : forall x y z, kappa (x**y) z -> kappa unit x -> kappa y z
| DCompose : forall x y z, kappa y z -> kappa x y -> kappa x z
| DArr : forall x y,   morphism x y -> kappa x y.

Fixpoint desugar {var i o} (e: kappa_sugared var i o) : kappa var i o := ...
```

Lambda-like notation is provided, but it is possible to directly construct
terms:

```
Definition delay : kappa (bit**unit) bit := desugar (
  Abs (fun input_wire =>
    App (Arr (delay_gate)) (Var input_wire)
  )).

Definition fork_then_xor_and : kappa (bit ** unit) (bit ** bit ** unit) :=
desugar (
  Abs (fun input_wire =>
    Let (App (Arr xor_gate) (Var input_wire)) (fun x =>
    Let (App (Arr and_gate) (Var input_wire)) (fun y =>
    App (App (App (Arr id) (Var x) (Var y)
    ))))
  )).
```

## Finite binary tree with a rightmost unit

`Tree a = () | a | (Tree a, Tree a)`

Without a class such as Haskell's `ArrowApply`, curried functions are not available.
Adam Megacz (or prior work?) shows that we can still have parital application by requiring
the input representation is a finite binary tree with a rightmost unit. The
rightmost unit is required for the case of applying the final argument. For
example (note this is pseudo kappa calculus, so all terms have an input and
output type):

```
f: (a, (b, ())) ~> c
A: () ~> a
B: () ~> b

f A: (b, ()) ~> c
f A B: () ~> c
```

Without the rightmost unit, `f A B` either must be treated as a special case, or
has no legal representation.
