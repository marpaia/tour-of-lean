/-
# Vectors as functions

A vector of length `n` is, concretely, a list of `n` entries. But there is a
more useful way to look at it: a vector is a *rule* that, given a position,
returns the entry sitting there. In other words, a length-`n` vector over `α`
is a function from its valid indices to `α`.

We take that view literally and *define* `Vec α n` to be the function type
`Fin n → α`, where `Fin n` is the type of natural numbers below `n` — the valid
indices, each one carrying a proof that it is in range.

Why functions rather than a stored array? Because it makes equality cheap to
reason about. Two functions are equal exactly when they agree on every input
(the `funext` principle), so the claim that two vectors are equal reduces to a
claim about their entries, one index at a time — and Lean usually discharges
that in a single step. An array-backed definition would instead force an
induction over the buffer for nearly every lemma. mathlib makes the same choice
for the same reason.
-/

import Mathlib.Algebra.Group.Defs

namespace LinearAlgebra

/-- A vector of length `n` over `α`: a function sending each valid index
`Fin n` to an entry of `α`. Because an `i : Fin n` carries a proof that `i < n`,
indexing can never run off the end — there is simply no out-of-bounds case to
account for. -/
def Vec (α : Type*) (n : Nat) : Type _ := Fin n → α

namespace Vec

variable {α : Type*} {n : Nat}

/-- Indexing into a vector. A vector *is* a function, so this is nothing but
function application — naming it just lets a call site read as "the `i`-th
entry" rather than as a bare application. The index is an `i : Fin n`, in range
by construction, so unlike a list lookup there is no `Option` and no failure to
handle. -/
@[inline] def get (v : Vec α n) (i : Fin n) : α := v i

/-- **Extensionality.** Two vectors are equal precisely when they agree at every
index. Because a vector is a function, this is the `funext` principle —
pointwise-equal functions are equal — applied verbatim.

Tagging the lemma `@[ext]` teaches the `ext` tactic about it: from then on a
goal `v = w` between vectors can be turned into `∀ i, v i = w i` by writing
`ext i`, trading a statement about whole vectors for one about single entries. -/
@[ext]
theorem ext {v w : Vec α n} (h : ∀ i, v i = w i) : v = w := funext h

/-! ## Zero and addition

Both operations are defined *pointwise*: the zero vector holds `0` in every
slot, and a sum adds the two vectors slot by slot. The `[Zero α]` and `[Add α]`
brackets are typeclass assumptions that record what we need of the entries —
there is no zero vector unless `α` itself has a zero, and no sum unless `α`
itself can be added. -/

/-- The vector whose every entry is `0`. -/
def zero [Zero α] : Vec α n := fun _ => 0

/-- Register `zero` as the canonical `Zero` instance for vectors, so that the
literal `0` denotes the zero vector. The `⟨zero⟩` is anonymous-constructor
notation: it builds the one-field `Zero` structure from our function. -/
instance [Zero α] : Zero (Vec α n) := ⟨zero⟩

/-- Pointwise addition: the entry at `i` is the sum of the two entries at `i`. -/
def add [Add α] (v w : Vec α n) : Vec α n := fun i => v i + w i

/-- Register `add` as the canonical `Add` instance, which switches on the `+`
notation for vectors. -/
instance [Add α] : Add (Vec α n) := ⟨add⟩

/-! ### Computation lemmas

These record that indexing interacts with `0` and `+` exactly as one would hope.
Both proofs are `rfl`: the two sides are *definitionally* equal, so the kernel
sees they agree merely by unfolding the definitions, with no reasoning required.
Tagging them `@[simp]` adds them to the simplifier's database, letting later
proofs rewrite `(v + w) i` into `v i + w i` on their own. -/

@[simp] theorem zero_apply [Zero α] (i : Fin n) : (0 : Vec α n) i = 0 := rfl
@[simp] theorem add_apply [Add α] (v w : Vec α n) (i : Fin n) :
    (v + w) i = v i + w i := rfl

/-! ## A first theorem

Adding the zero vector changes nothing: `v + 0 = v`. The hypothesis is
`[AddZeroClass α]` rather than separate `[Add α]` and `[Zero α]` because having
an addition and a zero is not yet enough — we need the law that ties them
together, `a + 0 = a`, to hold in the entry type. `AddZeroClass` is exactly the
class bundling `+`, `0`, and that law, so the proof can lean on it entry by
entry. This layering of small classes — `Zero`, `Add`, `AddZeroClass`,
`AddMonoid`, `AddGroup`, … — each contributing one more law, is the discipline
that lets mathlib state every result at the greatest generality it deserves. -/

theorem add_zero [AddZeroClass α] (v : Vec α n) : v + 0 = v := by
  /- A vector equation is really a family of entry equations. The `@[ext]` lemma
     above lets `ext i` replace the goal `v + 0 = v` with its value at a single
     index, `(v + 0) i = v i`. -/
  ext i
  /- Everything is now a statement about entries of `α`. `simp` rewrites the
     left side with `add_apply` and `zero_apply` down to `v i + 0`, then closes
     it with the `add_zero` law that `AddZeroClass` guarantees for `α`. -/
  simp

/-! ## Displaying a vector

To print a `Vec α n` with `#eval` we need a `Repr` instance — Lean's mechanism
for turning a value into displayable text. A vector is a function, so we first
materialize it into the list of its entries with `List.ofFn`, then hand off to
the list's own `Repr`. -/

instance [Repr α] : Repr (Vec α n) where
  reprPrec v _ := repr (List.ofFn v)

end Vec

/-! ## A quick check

`#eval` evaluates an expression right here as the file is processed and shows
the result inline — effectively a REPL prompt embedded in the source. -/

/-- The vector ⟨1, 2, 3⟩, built by giving the function `Fin 3 → Nat`. -/
def v123 : Vec Nat 3 := fun i => i.val + 1

#eval v123                 -- [1, 2, 3]
#eval v123 + v123          -- [2, 4, 6]
#eval (0 : Vec Nat 5)      -- [0, 0, 0, 0, 0]

end LinearAlgebra
