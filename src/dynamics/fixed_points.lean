/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.nat.basic

/-!
# Fixed and periodic points of a self-map

-/

universe u

variables {α : Type u} {f g : α → α} {x : α} {m n k : ℕ}

namespace function

/-- A point `x` is a fixed point of `f : α → α` if `f x = x`. -/
def is_fixed (f : α → α) (x : α) := f x = x

lemma is_fixed_id (x : α) : is_fixed id x := by rw [is_fixed, id] -- TODO: why this is not `rfl`?

namespace is_fixed

protected lemma eq (hf : is_fixed f x) : f x = x := hf

lemma comp (hf : is_fixed f x) (hg : is_fixed g x) : is_fixed (f ∘ g) x :=
calc f (g x) = f x : congr_arg f hg
         ... = x   : hf

lemma iterate (hf : is_fixed f x) (n : ℕ) : is_fixed (f^[n]) x :=
nat.rec_on n rfl $ λ n ihn, ihn.comp hf

lemma left_of_comp (hfg : is_fixed (f ∘ g) x) (hg : is_fixed g x) : is_fixed f x :=
calc f x = f (g x) : congr_arg f hg.symm
     ... = x       : hfg

lemma to_left_inverse (hf : is_fixed f x) (h : left_inverse g f) : is_fixed g x :=
calc g x = g (f x) : congr_arg g hf.symm
     ... = x       : h x

end is_fixed

/-- A point `x` is a periodic point of `f : α → α` of period `n` if `f^n x = x`.
Note that we do not require `0 < n` in this definition. Most theorems about periodic points
need this assumption. -/
def is_periodic (f : α → α) (n : ℕ) (x : α) := is_fixed (f^[n]) x

lemma is_fixed.is_periodic (hf : is_fixed f x) (n : ℕ) : is_periodic f n x :=
hf.iterate n

lemma is_preiodic_id (n : ℕ) (x : α) : is_periodic id n x := (is_fixed_id x).is_periodic n

lemma is_periodic_zero (f : α → α) (x : α) : is_periodic f 0 x := is_fixed_id x

namespace is_periodic

protected lemma is_fixed (hf : is_periodic f n x) : is_fixed (f^[n]) x := hf

protected lemma add (hn : is_periodic f n x) (hm : is_periodic f m x) :
  is_periodic f (n + m) x :=
by { rw [is_periodic, nat.iterate_add], exact hn.comp hm }

lemma left_of_add (hn : is_periodic f (n + m) x) (hm : is_periodic f m x) :
  is_periodic f n x :=
by { rw [is_periodic, nat.iterate_add] at hn, exact hn.left_of_comp hm }

lemma right_of_add (hn : is_periodic f (n + m) x) (hm : is_periodic f n x) :
  is_periodic f m x :=
by { rw add_comm at hn, exact hn.left_of_add hm }

protected lemma sub (hm : is_periodic f m x) (hn : is_periodic f n x) :
  is_periodic f (m - n) x :=
begin
  cases le_total n m with h h,
  { refine left_of_add _ hn,
    rwa [nat.sub_add_cancel h] },
  { rw [nat.sub_eq_zero_of_le h],
    apply is_periodic_zero }
end

protected lemma mul_const (hm : is_periodic f m x) (n : ℕ) : is_periodic f (m * n) x :=
by simp only [is_periodic, nat.iterate_mul, hm.is_fixed.iterate n]

protected lemma const_mul (hm : is_periodic f m x) (n : ℕ) : is_periodic f (n * m) x :=
by simp only [mul_comm n, hm.mul_const n]

protected lemma iterate (hf : is_periodic f n x) (m : ℕ) : is_periodic (f^[m]) n x :=
by { rw [is_periodic, ← nat.iterate_mul, mul_comm, nat.iterate_mul], exact hf.is_fixed.iterate m }

protected lemma mod (hm : is_periodic f m x) (hn : is_periodic f n x) : is_periodic f (m % n) x :=
begin
  rw [← nat.mod_add_div m n] at hm,
  exact hm.left_of_add (hn.mul_const _)
end

protected lemma gcd (hm : is_periodic f m x) (hn : is_periodic f n x) :
  is_periodic f (m.gcd n) x :=
begin
  revert hm hn,
  refine nat.gcd.induction m n (λ n h0 hn, _) (λ m n hm ih hm hn, _),
  { rwa [nat.gcd_zero_left], },
  { rw [nat.gcd_rec],
    exact ih (hn.mod hm) hm }
end

end is_periodic

/-- The set of fixed points of a map `f : α → α`. -/
def fixed_points (f : α → α) : set α := {x : α | is_fixed f x}

@[simp] lemma mem_fixed_points : x ∈ fixed_points f ↔ is_fixed f x := iff.rfl

/-- The set of periodic points of a map `f : α → α`. -/
def periodic_points (f : α → α) : set α := {x : α | ∃ n, 0 < n ∧ is_periodic f n x}

end function
