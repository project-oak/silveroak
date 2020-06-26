# Intro

Circuit expressions are enclosed in a `<[` `]>` bracket pair.

```
<[ \x => x ]>
```

A number of primitive circuits are built-in such as `xor`, and function
application follows the usual lambda calculus form:

```
<[ \x y => xor x y ]>
```

However, our language is actually a restricted form of lambda calculus called
kappa calulus. The best way to think of this is that you can only express (and typecheck)
expressions that have a representation as a circuit. So for example, passing functions 
as arguments is not allowed as it is not representable as a circuit. The benefit being
that every expression in our language maps directly to a circuit, and component
instantiation should be observable directly from the syntax.

Other circuit expressions defined in the larger Coq scope are accessible by
escaping the definition with `!`:

```
Definition foo := <[\x y => xor x y ]>.

Definition use_foo := <[\x => !foo x x]>.
```

Each circuit definition (and all expressions with in it) have an input type and
an output type.

```
Definition foo : kappa_sugared <<Bit, Bit, Unit>> Bit := <[ xor ]>.
Definition bar : kappa_sugared <<Bit, Bit, Unit>> Bit := <[\x y => xor x y ]>.
```

A variable has the `Unit` input type, which is the empty type. So in `bar`
above, to the right of the binders (`\x y =>`), `x` and `y` both have type `kappa_sugared Unit Bit`.

Bitvector literals are of type `Vector n Bit` and must be prefixed with `#`.
The width of the literal is given by the type it exists at.

```
Definition five_zero_bits : kappa_sugared Unit (Vector 5 Bit) := <[ #0 ]>.
```

# Working with vectors

There are a number of vector functions provided:

- `uncons: Vector (S n) T ~> (T, Vector n T)`
- `mkVec: T ~> Vector 1 T`
- `_ :: _: T ~> Vector n T ~> Vector (S n) T`

Additionally indexing can be performed via the familiar `vector [ index ]` syntax, where index can be any circuit expression.

```
Definition get_zeroth_item : kappa_sugared <<Vector 5 Bit, Unit>> Bit := 
  <[ \my_vec => my_vec[#0] ]>.
```

# Higher order functions

What about useful higher-order functions such as `map`? Although we can't pass
functions as arguments inside a circuit expression, we can write these
combinators as plain Coq functions acting on circuit expressions:

```
Fixpoint map {T} n
  (f : kappa_sugared var <<T, Unit>> T)
  : kappa_sugared var << Vector (S n) T, Unit >> <<Vector (S n) T>> :=
match n with
| 0 => <[ \x => mkVec (!f (x[#0])) ]>
| S n' =>
  <[ \xs =>
      let '(x, xs') = uncons xs in
      !f x :: (!(map n' f) xs')
  ]>
end.
```


