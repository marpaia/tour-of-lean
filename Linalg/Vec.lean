/-
# `Vec` — fixed-length vectors (explained for Rust programmers)

We define our first linear algebra primitive and prove our first theorem
about it. The comments throughout this file cross-reference Rust, because
Rust's generics + const generics + trait system map onto Lean's type
system more cleanly than any other mainstream language.

## The Rust mental model

If you were writing this library in Rust, you'd reach for the array-
backed representation:

    struct Vec<T, const N: usize> {
        data: [T; N],
    }

That's a fixed-length contiguous buffer of `T`s — basically what Rust's
built-in `[T; N]` already gives you.

We're *not* taking that path. We're taking the "function-backed" path,
which has no direct Rust analog but would look something like:

    type Vec<T, const N: usize> = impl Fn(BoundedIdx<N>) -> T;

where `BoundedIdx<N>` is a `usize` that's been validated to be `< N`.
That is: a vector *is* a function from valid indices to entries.

Why this path? Because once vectors are functions, vector equality
reduces to *function equality*, which in Lean reduces to *pointwise*
equality via the `funext` axiom. The practical payoff: most algebraic
lemmas about vectors collapse to "for all i, the entries are equal,"
and Lean usually finishes that in one tactic call. The array-backed
version would require induction on the buffer for every single proof.

(mathlib makes the same choice. We're following them.)
-/

import Mathlib.Algebra.Group.Defs

namespace Linalg

/-- A vector of length `n` over `α`.

Rust analog:
    type Vec<T, const N: usize> = Fn(BoundedIdx<N>) -> T;
              ─┬─  ─────┬─────
               │        │
   `α : Type*`─┘        └─`n : Nat`

Three pieces:
  * `α : Type*` — a type parameter, exactly Rust's `<T>`. The `Type*`
    annotation says "α lives in some universe"; the `*` lets Lean pick
    the universe automatically (Rust has no equivalent — Rust has one
    "level" of types, which is fine until you start defining
    types-of-types, which most programs never do).
  * `n : Nat` — a *value* parameter of type `Nat`. The Rust analog is
    `const N: usize` (a const generic). The big difference: in Rust,
    `N` must be a compile-time constant; in Lean, `n` is just a value,
    and the type checker handles it uniformly whether it's a literal,
    an argument, or a computed expression. This is "dependent types"
    in one bullet point.
  * `Fin n → α` — the body. `Fin n` is "natural numbers strictly less
    than n," i.e. validated indices. There is *no* clean Rust analog;
    you'd have to roll your own `BoundedIdx<const N: usize>` with a
    private constructor that enforces the bound. The Lean win:
    `i : Fin n` *is* a proof of in-bounds-ness, so indexing can never
    fail — no `Option<&T>`, no panic, no runtime check. -/
def Vec (α : Type*) (n : Nat) : Type _ := Fin n → α

namespace Vec

variable {α : Type*} {n : Nat}

/-- Indexing. Just function application, but named so call sites read
*intent* rather than *mechanism*.

Rust analog:
    impl<T, const N: usize> Index<BoundedIdx<N>> for Vec<T, N> {
        type Output = T;
        fn index(&self, i: BoundedIdx<N>) -> &T { ... }
    }

Note `get` cannot return `Option<T>` or panic — `i : Fin n` *guarantees*
the index is in range. Contrast with `<[T]>::get(i: usize)`, which
returns `Option<&T>` precisely because `usize` carries no bound. -/
@[inline] def get (v : Vec α n) (i : Fin n) : α := v i

/-- **Extensionality.** Two vectors are equal iff they agree at every
index.

This *statement* has no Rust analog because Rust has no proof system —
but the *spirit* is what you'd write as a property-based test:

    proptest! {
        fn vectors_eq_iff_pointwise<const N: usize>(v: Vec<i32, N>, w: Vec<i32, N>) {
            prop_assert_eq!(v == w, (0..N).all(|i| v[i] == w[i]));
        }
    }

The Lean version isn't a test — it's a *proof*, valid for all types
`α` and lengths `n` simultaneously. It rests on `funext`: the axiom
that pointwise-equal functions are equal.

The `@[ext]` attribute registers this lemma with the `ext` tactic. From
now on, anywhere you have a goal `v = w` between vectors, writing
`ext i` rewrites the goal to `v i = w i`. There's no Rust analog because
Rust has no tactics — but think of it as the type checker offering you
an automated refactoring on the goal. -/
@[ext]
theorem ext {v w : Vec α n} (h : ∀ i, v i = w i) : v = w := funext h

/-! ## Zero and addition

Both are *pointwise*: the zero vector has `0` in every slot; the sum of
two vectors adds slot by slot.

The `[Zero α]` and `[Add α]` brackets are *typeclass constraints* —
exactly Rust's `where T: Zero` and `where T: Add`. Lean's typeclass
resolution is the same mechanism as Rust's trait resolution: at every
call site the compiler searches for an implementation that satisfies
the constraint, and either finds one or rejects the program. -/

/-- The vector whose every entry is `0`.

Rust analog (assuming `num_traits::Zero`):
    impl<T: Zero, const N: usize> Vec<T, N> {
        fn zero() -> Self { Self::from_fn(|_| T::zero()) }
    } -/
def zero [Zero α] : Vec α n := fun _ => 0

/-- Register `zero` as the canonical `Zero` instance for `Vec α n`.
The `⟨zero⟩` syntax is Lean's anonymous-constructor notation; it builds
a `Zero` record whose single field is our `zero` function.

Rust analog:
    impl<T: Zero, const N: usize> Zero for Vec<T, N> {
        fn zero() -> Self { Vec::zero() }
    } -/
instance [Zero α] : Zero (Vec α n) := ⟨zero⟩

/-- Pointwise addition.

Rust analog:
    impl<T: Add<Output = T> + Copy, const N: usize> Vec<T, N> {
        fn add(self, other: Self) -> Self {
            Self::from_fn(|i| self[i] + other[i])
        }
    } -/
def add [Add α] (v w : Vec α n) : Vec α n := fun i => v i + w i

/-- Register `add` as the canonical `Add` instance. After this line,
the `+` notation works on vectors automatically — exactly like Rust
giving you `v + w` for free once you `impl Add`.

Rust analog:
    impl<T: Add<Output = T>, const N: usize> Add for Vec<T, N> {
        type Output = Self;
        fn add(self, rhs: Self) -> Self { Vec::add(self, rhs) }
    } -/
instance [Add α] : Add (Vec α n) := ⟨add⟩

/-! ### Computation lemmas

These say: indexing into `0` or `v + w` does exactly what you'd expect.
The proofs are `rfl` — *definitional equality* — which means Lean's
kernel sees they're true just by unfolding our definitions, no work
required.

**Rust has nothing like this.** The closest you'd come is a runtime
assertion in a test:

    assert_eq!((v + w)[i], v[i] + w[i]);

Lean lets you state this as a *rewriting rule* and tag it `@[simp]`,
which adds it to a global database of identities that future proofs
chain together automatically. Imagine if rustc had a phase where you
could register "these two expressions are always equal" and the
compiler used your rules to simplify subsequent code. That's `simp`. -/

@[simp] theorem zero_apply [Zero α] (i : Fin n) : (0 : Vec α n) i = 0 := rfl
@[simp] theorem add_apply [Add α] (v w : Vec α n) (i : Fin n) :
    (v + w) i = v i + w i := rfl

/-! ## A first real theorem

`v + 0 = v`. In Rust you'd write this as a property test:

    #[test]
    fn add_zero<T: Add<Output=T> + Zero + PartialEq + Clone, const N: usize>(v: Vec<T, N>) {
        assert_eq!(v.clone() + Vec::zero(), v);
    }

That gives you confidence for the specific values your test happens to
exercise. Lean gives you a *proof* — once `#check` accepts it, the
equation holds for every type `α` satisfying `AddZeroClass` and every
length `n`, forever. No fuzzer required.

Proof structure:
1. `ext i`  — reduce a vector equation to a pointwise one using our
   `@[ext]`-tagged lemma above. The goal becomes `(v + 0) i = v i`.
2. `simp`   — `add_apply` and `zero_apply` rewrite the LHS to
   `v i + 0`. Then mathlib's `AddZeroClass.add_zero` lemma (also tagged
   `@[simp]`) collapses `v i + 0` to `v i`. Done.

**Why `[AddZeroClass α]` rather than `[Add α] [Zero α]`?** Because
having a `+` and a `0` separately isn't enough — we need to know they
*interact correctly*, i.e. that `a + 0 = a` in `α`. `AddZeroClass` is
the typeclass that bundles both operations *plus* that interaction law.

The Rust equivalent would be a bound like `T: Add<Output=T> + Zero`
*plus* an unenforceable documentation comment saying "callers must
ensure `T::zero() + x == x`." Lean puts that requirement into the type,
where it can never be forgotten, violated, or accidentally erased.
This kind of finely-grained typeclass layering (`Zero`, `Add`,
`AddZeroClass`, `AddSemigroup`, `AddMonoid`, `AddGroup`, ...) is the
core technique that makes mathlib scale. -/

theorem add_zero [AddZeroClass α] (v : Vec α n) : v + 0 = v := by
  ext i
  simp

end Vec
end Linalg

/-! ## Sanity check with `#eval`

To print a `Vec α n` we need a `Repr` instance — exactly Rust's
`impl Debug for Vec<T, N>`. A vector is a function, so we materialize it
to a list with `List.ofFn` and reuse the list's `Repr`. -/

namespace Linalg.Vec
variable {α : Type*} {n : Nat}

/-- Rust analog:
    impl<T: Debug, const N: usize> Debug for Vec<T, N> {
        fn fmt(&self, f: &mut Formatter) -> fmt::Result {
            (0..N).map(|i| &self[BoundedIdx::new(i).unwrap()])
                  .collect::<std::vec::Vec<_>>()
                  .fmt(f)
        }
    } -/
instance [Repr α] : Repr (Vec α n) where
  reprPrec v _ := repr (List.ofFn v)

end Linalg.Vec

section Examples
open Linalg

/-- The vector ⟨1, 2, 3⟩. Built by giving a function `Fin 3 → Nat`.

Rust analog:
    let v123: Vec<u32, 3> = Vec::from_fn(|i| i as u32 + 1); -/
def v123 : Vec Nat 3 := fun i => i.val + 1

/-! `#eval` runs an expression at elaboration time — think of it as a
REPL prompt baked into the source file. Rust analog is roughly
`fn main() { println!("{:?}", expr); }` followed by `cargo run`, except
no separate compile/run step: the answer appears inline in your editor. -/

#eval v123                 -- [1, 2, 3]
#eval v123 + v123          -- [2, 4, 6]
#eval (0 : Vec Nat 5)      -- [0, 0, 0, 0, 0]

end Examples
