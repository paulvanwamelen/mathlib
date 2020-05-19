/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

Fractional ideals of an integral domain.
-/
import ring_theory.localization
import ring_theory.principal_ideal_domain

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions

 * `is_fractional` defines which `R`-submodules of `localization R S` are fractional ideals
 * `fractional_ideal R S` is the type of fractional ideals in `localization R S`
 * `has_coe (ideal R) (fractional_ideal R S)` instance
 * `comm_semiring (fractional_ideal R S)` instance:
   the typical ideal operations generalized to fractional ideals
 * `lattice (fractional_ideal R S)` instance
 * `has_div (fractional_ideal R (non_zero_divisors R))` instance:
   the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statements

  * `mul_left_mono` and `mul_right_mono` state that ideal multiplication is monotone
  * `right_inverse_eq` states that `1 / I` is the inverse of `I` if one exists

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `fractional_ideal` to be the subtype of the predicate `is_fractional`,
instead of having `fractional_ideal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to re-use their respective proof terms.
We can still use `simp` to show `I.1 + J.1 = (I + J).1` and `⊥.1 = 0.1`.

We don't assume that `localization R S` is a field until we need it to define ideal quotients.
When this assumption is needed, we replace `S` with `non_zero_divisors R`,
making `localization R (non_zero_divisors R) = fraction_ring R` into a field since `R` is a domain.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

open localization


universes u v w

namespace ring

section defs

variables (R : Type u) [integral_domain R] (S : set R) [is_submonoid S]

/-- A submodule `I` is a fractional ideal if `a I ⊆ R` for some `a ≠ 0`. -/
def is_fractional (I : submodule R (localization R S)) :=
∃ a ≠ (0 : R), ∀ b ∈ I, is_integer R S (a • b)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

  More precisely, let `R'` be a localization of `R` at some submonoid `S`,
  then a fractional ideal `I ⊆ R'` is an `R`-submodule of `R'`,
  such that there is a nonzero `a : R` with `a I ⊆ R`.
-/
def fractional_ideal := {I : submodule R (localization R S) // is_fractional R S I}

end defs

namespace fractional_ideal

open set
open submodule

variables {R : Type u} [integral_domain R] {S : set R} [is_submonoid S]

instance : has_mem (localization R S) (fractional_ideal R S) := ⟨λ x I, x ∈ I.1⟩

/-- Fractional ideals are equal if their submodules are equal.

  Combined with `submodule.ext` this gives that fractional ideals are equal if
  they have the same elements.
-/
@[ext]
lemma ext {I J : fractional_ideal R S} : I.1 = J.1 → I = J :=
subtype.eq

lemma fractional_of_subset_one (I : submodule R (localization R S)) (h : I ≤ 1) :
  is_fractional R S I :=
begin
  use 1,
  use one_ne_zero,
  intros b hb,
  obtain ⟨b', b'_mem, b'_eq_b⟩ := h hb,
  convert is_integer_coe R b',
  simp [b'_eq_b.symm]
end

instance coe_to_fractional_ideal : has_coe (ideal R) (fractional_ideal R S) :=
⟨ λ I, ⟨ ↑I, fractional_of_subset_one _ (image_subset _ (subset_univ _)) ⟩ ⟩

instance : has_zero (fractional_ideal R S) := ⟨(0 : ideal R)⟩

@[simp]
lemma mem_zero_iff {x : localization R S} : x ∈ (0 : fractional_ideal R S) ↔ x = 0 :=
⟨ (λ ⟨x', x'_mem_zero, x'_eq_x⟩, by simp [x'_eq_x.symm, mem_singleton_iff.1 x'_mem_zero]),
  (λ hx, ⟨0, rfl, by simp [hx]⟩) ⟩

@[simp] lemma val_zero : (0 : fractional_ideal R S).1 = 0 :=
submodule.ext $ λ x, mem_zero_iff

lemma nonzero_iff_val_nonzero {I : fractional_ideal R S} : I.1 ≠ 0 ↔ I ≠ 0 :=
⟨ λ h h', h (by simp [h']),
  λ h h', h (ext (by simp [h'])) ⟩

instance : inhabited (fractional_ideal R S) := ⟨0⟩

instance : has_one (fractional_ideal R S) :=
⟨(1 : ideal R)⟩

lemma mem_one_iff {x : localization R S} : x ∈ (1 : fractional_ideal R S) ↔ ∃ x' : R, ↑x' = x :=
iff.intro (λ ⟨x', _, h⟩, ⟨x', h⟩) (λ ⟨x', h⟩, ⟨x', ⟨x', set.mem_univ _, rfl⟩, h⟩)

lemma coe_mem_one (x : R) : (x : localization R S) ∈ (1 : fractional_ideal R S) :=
mem_one_iff.mpr ⟨x, rfl⟩

@[simp] lemma val_one : (1 : fractional_ideal R S).1 = (1 : ideal R) := rfl

section lattice

/-! ### `lattice` section

  Defines the order on fractional ideals as inclusion of their underlying sets,
  and ports the lattice structure on submodules to fractional ideals.
-/


instance : partial_order (fractional_ideal R S) :=
{ le := λ I J, I.1 ≤ J.1,
  le_refl := λ I, le_refl I.1,
  le_antisymm := λ ⟨I, hI⟩ ⟨J, hJ⟩ hIJ hJI, by { congr, exact le_antisymm hIJ hJI },
  le_trans := λ _ _ _ hIJ hJK, le_trans hIJ hJK }

lemma le_iff {I J : fractional_ideal R S} : I ≤ J ↔ (∀ x ∈ I, x ∈ J) := iff.refl _

lemma zero_le (I : fractional_ideal R S) : 0 ≤ I :=
begin
  intros x hx,
  convert submodule.zero _,
  simpa using hx
end

instance order_bot : order_bot (fractional_ideal R S) :=
{ bot := 0,
  bot_le := zero_le,
  ..fractional_ideal.partial_order }

@[simp] lemma bot_eq_zero : (⊥ : fractional_ideal R S) = 0 :=
rfl

lemma eq_zero_iff {I : fractional_ideal R S} : I = 0 ↔ (∀ x ∈ I, x = (0 : localization R S)) :=
⟨ (λ h x hx, by simpa [h, mem_zero_iff] using hx),
  (λ h, le_bot_iff.mp (λ x hx, mem_zero_iff.mpr (h x hx))) ⟩

lemma fractional_sup (I J : fractional_ideal R S) : is_fractional R S (I.1 ⊔ J.1) :=
begin
  rcases I.2 with ⟨aI, haI, hI⟩,
  rcases J.2 with ⟨aJ, haJ, hJ⟩,
  use aI * aJ,
  use mul_ne_zero haI haJ,
  intros b hb,
  rcases mem_sup.mp hb with ⟨bI, hbI, bJ, hbJ, hbIJ⟩,
  rw [←hbIJ, smul_add],
  apply is_integer_add,
  { rw [mul_comm, mul_smul],
    apply is_integer_smul _ (hI bI hbI) },
  { rw [mul_smul],
    apply is_integer_smul _ (hJ bJ hbJ) }
end

lemma fractional_inf (I J : fractional_ideal R S) : is_fractional R S (I.1 ⊓ J.1) :=
begin
  rcases I.2 with ⟨aI, haI, hI⟩,
  use aI,
  use haI,
  intros b hb,
  rcases mem_inf.mp hb with ⟨hbI, hbJ⟩,
  exact (hI b hbI)
end

instance lattice : lattice (fractional_ideal R S) :=
{ inf := λ I J, ⟨I.1 ⊓ J.1, fractional_inf I J⟩,
  sup := λ I J, ⟨I.1 ⊔ J.1, fractional_sup I J⟩,
  inf_le_left := λ I J, show I.1 ⊓ J.1 ≤ I.1, from inf_le_left,
  inf_le_right := λ I J, show I.1 ⊓ J.1 ≤ J.1, from inf_le_right,
  le_inf := λ I J K hIJ hIK, show I.1 ≤ (J.1 ⊓ K.1), from le_inf hIJ hIK,
  le_sup_left := λ I J, show I.1 ≤ I.1 ⊔ J.1, from le_sup_left,
  le_sup_right := λ I J, show J.1 ≤ I.1 ⊔ J.1, from le_sup_right,
  sup_le := λ I J K hIK hJK, show (I.1 ⊔ J.1) ≤ K.1, from sup_le hIK hJK,
  ..fractional_ideal.partial_order }

instance : semilattice_sup_bot (fractional_ideal R S) :=
{ ..fractional_ideal.order_bot, ..fractional_ideal.lattice }

end lattice

section semiring

instance : has_add (fractional_ideal R S) := ⟨(⊔)⟩

@[simp]
lemma sup_eq_add (I J : fractional_ideal R S) : I ⊔ J = I + J := rfl

@[simp]
lemma val_add (I J : fractional_ideal R S) : (I + J).1 = I.1 + J.1 := rfl

lemma fractional_mul (I J : fractional_ideal R S) : is_fractional R S (I.1 * J.1) :=
begin
  rcases I with ⟨I, aI, haI, hI⟩,
  rcases J with ⟨I, aJ, haJ, hJ⟩,
  use aI * aJ,
  use mul_ne_zero haI haJ,
  intros b hb,
  apply submodule.mul_induction_on hb,
  { intros m hm n hn,
    obtain ⟨n', hn'⟩ := hJ n hn,
    rw [mul_smul, ←algebra.mul_smul_comm, ←hn', mul_comm],
    apply hI,
    exact submodule.smul _ _ hm },
  { rw [smul_zero],
    apply is_integer_coe },
  { intros x y hx hy,
    rw [smul_add],
    apply is_integer_add _ hx hy },
  { intros r x hx,
    rw [←mul_smul, mul_comm, mul_smul],
    apply is_integer_smul _ hx },
end

instance : has_mul (fractional_ideal R S) := ⟨λ I J, ⟨I.1 * J.1, fractional_mul I J⟩⟩

@[simp]
lemma val_mul (I J : fractional_ideal R S) : (I * J).1 = I.1 * J.1 := rfl

lemma mul_left_mono (I : fractional_ideal R S) : monotone ((*) I) :=
λ J J' h, mul_le.mpr (λ x hx y hy, mul_mem_mul hx (h hy))

lemma mul_right_mono (I : fractional_ideal R S) : monotone (λ J, J * I) :=
λ J J' h, mul_le.mpr (λ x hx y hy, mul_mem_mul (h hx) hy)

instance add_comm_monoid : add_comm_monoid (fractional_ideal R S) :=
{ add_assoc := λ I J K, sup_assoc,
  add_comm := λ I J, sup_comm,
  add_zero := λ I, sup_bot_eq,
  zero_add := λ I, bot_sup_eq,
  ..fractional_ideal.has_zero,
  ..fractional_ideal.has_add }

instance comm_monoid : comm_monoid (fractional_ideal R S) :=
{ mul_assoc := λ I J K, ext (submodule.mul_assoc _ _ _),
  mul_comm := λ I J, ext (mul_comm _ _),
  mul_one := λ I, begin
    ext,
    split; intro h,
    { apply mul_le.mpr _ h,
      rintros x hx y ⟨y', y'_mem_R, y'_eq_y⟩,
      erw [←y'_eq_y, mul_comm, coe_mul_eq_smul],
      exact submodule.smul _ _ hx },
    { have : x * 1 ∈ (I * 1) := mul_mem_mul h (coe_mem_one _),
      rwa [mul_one] at this }
  end,
  one_mul := λ I, begin
    ext,
    split; intro h,
    { apply mul_le.mpr _ h,
      rintros x ⟨x', x'_mem_R, x'_eq_x⟩ y hy,
      erw [←x'_eq_x, coe_mul_eq_smul],
      exact submodule.smul _ _ hy },
    { have : 1 * x ∈ (1 * I) := mul_mem_mul (coe_mem_one _) h,
      rwa [one_mul] at this }
  end,
  ..fractional_ideal.has_mul,
  ..fractional_ideal.has_one }

instance comm_semiring : comm_semiring (fractional_ideal R S) :=
{ mul_zero := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hy])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  zero_mul := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hx])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  left_distrib := λ I J K, ext (mul_add _ _ _),
  right_distrib := λ I J K, ext (add_mul _ _ _),
  ..fractional_ideal.add_comm_monoid,
  ..fractional_ideal.comm_monoid }

end semiring

section smul

variables {R' : Type*} [comm_ring R'] [algebra R R']

local attribute [instance] smul_set_action

open algebra

-- TODO: figure out whether we want this instance elsewhere
def submodule_has_scalar : has_scalar R' (submodule R R') :=
⟨ λ x I, { carrier := x • I.carrier,
           add := by { rintros y z ⟨y', hy', rfl⟩ ⟨z', hz', rfl⟩,
                       rw ←smul_add,
                       exact smul_mem_smul_set _ (I.add hy' hz') },
           smul := by { rintros y z ⟨z', hz', rfl⟩,
                        rw [smul_eq_mul, ←algebra.mul_smul_comm],
                        exact smul_mem_smul_set _ (I.smul y hz')},
           zero := by simpa only [smul_zero] using smul_mem_smul_set x I.zero } ⟩

local attribute [instance] submodule_has_scalar

lemma mem_smul_submodule (x y : R') (I : submodule R R') :
  x ∈ y • I ↔ ∃ x' ∈ I, x = y * x' :=
mem_smul_set y I.carrier x

@[simp] lemma smul_one_submodule (x : R') :
  (x • (1 : submodule R R')) = span R {x} :=
begin
  ext y,
  refine ((mem_smul_set x _ y).trans ⟨_, _⟩).trans mem_span_singleton.symm;
    simp_rw [smul_eq_mul, mul_comm x],
  { rintros ⟨y', ⟨y', ⟨⟩, rfl⟩, rfl⟩,
    exact ⟨y', smul_def y' x⟩ },
  { rintros ⟨y', rfl⟩,
    exact ⟨of_id R R' y', ⟨y', ⟨⟩, rfl⟩, smul_def y' x⟩ }
end

@[simp] lemma smul_top (x : localization R S) :
  x • (↑(⊤ : ideal R) : submodule R (localization R S)) = span R {x} :=
begin
  ext y,
  refine ((mem_smul_set x _ y).trans ⟨_, _⟩).trans mem_span_singleton.symm;
  simp_rw [smul_eq_mul, mul_comm x],
  { rintros ⟨y', ⟨y', ⟨⟩, rfl⟩, rfl⟩,
    exact ⟨y', smul_def y' x⟩ },
  { rintros ⟨y', rfl⟩,
    exact ⟨y', ⟨y', ⟨⟩, rfl⟩, smul_def y' x⟩ }
end

lemma span_singleton_mul (x y : R') : (span R {x * y} : submodule R R') = x • span R {y} :=
begin
  ext z,
  rw [mem_smul_submodule, mem_span_singleton],
  split,
  { rintros ⟨a, rfl⟩,
    exact ⟨a • y, mem_span_singleton.mpr ⟨a, rfl⟩, (mul_smul_comm a x y).symm ⟩ },
  { rintros ⟨x', h, rfl⟩,
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp h,
    exact ⟨a, (mul_smul_comm a x y).symm⟩ }
end

lemma fractional_smul (x : localization R S) (I : fractional_ideal R S) :
  is_fractional R S (x • I.1) := sorry -- TODO

instance : has_scalar (localization R S) (fractional_ideal R S) :=
{ smul := λ x I, ⟨ x • I.val, fractional_smul x I ⟩ }

@[simp] lemma val_smul_ideal (x : localization R S) (I : fractional_ideal R S) :
  (x • I).val = x • I.val :=
rfl

@[simp] lemma zero_smul_ideal (I : fractional_ideal R S) :
  (0 : localization R S) • I = 0 :=
begin
  ext,
  erw [val_smul_ideal, mem_smul_set, mem_zero_iff],
  simp_rw [zero_smul],
  exact ⟨ λ ⟨_, _, h⟩, h, λ h, ⟨0, I.val.zero, h⟩ ⟩
end

@[simp] lemma one_smul_ideal (I : fractional_ideal R S) : (1 : localization R S) • I = I :=
begin
  ext,
  erw [val_smul_ideal, mem_smul_set],
  simp_rw one_smul,
  exact ⟨ λ ⟨_, hy, rfl⟩, hy, λ hx, ⟨x, hx, rfl⟩ ⟩
end

@[simp] lemma mul_smul_ideal (x y : localization R S) (I : fractional_ideal R S):
  (x * y) • I = x • y • I :=
begin
  ext z,
  simp_rw [val_smul_ideal],
  split,
  { rintros ⟨z', hz, rfl⟩,
    rw mul_smul,
    exact smul_mem_smul_set x (smul_mem_smul_set y hz) },
  { rintros ⟨z', ⟨z'', hz, rfl⟩, rfl⟩,
    rw ← mul_smul,
    exact smul_mem_smul_set (x * y) hz }
end

-- TODO: finish this when localizations are more stable
lemma exists_ideal_eq_smul (I : fractional_ideal R S) :
  ∃ (a ≠ (0 : R)) (aI : ideal R), ↑aI = (a : localization R S) • I :=
begin
  obtain ⟨a, nonzero, ha⟩ := I.2,
  refine ⟨a, nonzero, _, _⟩,
  sorry,
  sorry
end

lemma smul_one_mul_smul_one (x y : localization R S) :
  (x • (1 : fractional_ideal R S)) * (y • 1) = (x * y) • 1 :=
begin
  ext z,
  simp_rw [val_mul, val_smul_ideal, val_one, ideal.one_eq_top, smul_top, span_mul_span],
  split; refine (λ h, span_mono _ h),
  { exact (λ _ ⟨_, rfl, _, rfl, hxy⟩, hxy) },
  { exact (λ _ hxy, ⟨_, rfl, _, rfl, hxy⟩ ) },
end

end smul

section quotient

/-! ### `quotient` section

This section defines the ideal quotient of fractional ideals.

In this section we need that each non-zero `y : R` has an inverse in
`localization R S`, i.e. that `localization R S` is a field. We satisfy this
assumption by taking `S = non_zero_divisors R`, so that `localization R
(non_zero_divisors R) = fraction_ring R`, which is a field because `R` is a domain.
-/

open_locale classical

instance : zero_ne_one_class (fractional_ideal R (non_zero_divisors R)) :=
{ zero_ne_one := λ h,
  have this : (1 : localization _ _) ∈ (0 : fractional_ideal R (non_zero_divisors R)) :=
    by convert coe_mem_one _,
  one_ne_zero (mem_zero_iff.mp this),
  ..fractional_ideal.has_one,
  ..fractional_ideal.has_zero }

lemma fractional_div_of_nonzero {I J : fractional_ideal R (non_zero_divisors R)} (h : J ≠ 0) :
  is_fractional R (non_zero_divisors R) (I.1 / J.1) :=
begin
  rcases I with ⟨I, aI, haI, hI⟩,
  rcases J with ⟨J, aJ, haJ, hJ⟩,
  obtain ⟨y, mem_J, not_mem_zero⟩ := exists_of_lt (bot_lt_iff_ne_bot.mpr h),
  obtain ⟨y', hy'⟩ := hJ y mem_J,
  use (aI * y'),
  split,
  { apply mul_ne_zero haI,
    intro y'_eq_zero,
    have : ↑aJ * y = 0 := by rw [coe_mul_eq_smul, ←hy', y'_eq_zero, localization.coe_zero],
    obtain aJ_zero | y_zero := mul_eq_zero.mp this,
    { have : aJ = 0 := fraction_ring.of.injective (trans aJ_zero (of_zero _ _).symm),
      contradiction },
    { exact not_mem_zero (mem_zero_iff.mpr y_zero) } },
  intros b hb,
  rw [mul_smul],
  convert hI _ (hb _ (submodule.smul_mem _ aJ mem_J)),
  rw [←hy', mul_coe_eq_smul]
end

noncomputable instance fractional_ideal_has_div :
  has_div (fractional_ideal R (non_zero_divisors R)) :=
⟨ λ I J, if h : J = 0 then 0 else ⟨I.1 / J.1, fractional_div_of_nonzero h⟩ ⟩

noncomputable instance : has_inv (fractional_ideal R (non_zero_divisors R)) := ⟨λ I, 1 / I⟩

lemma div_nonzero {I J : fractional_ideal R (non_zero_divisors R)} (h : J ≠ 0) :
  (I / J) = ⟨I.1 / J.1, fractional_div_of_nonzero h⟩ :=
dif_neg h

lemma inv_nonzero {I : fractional_ideal R (non_zero_divisors R)} (h : I ≠ 0) :
  I⁻¹ = ⟨(1 : fractional_ideal R _).val / I.1, fractional_div_of_nonzero h⟩ :=
div_nonzero h

lemma val_inv_of_nonzero {I : fractional_ideal R (non_zero_divisors R)} (h : I ≠ 0) :
  I⁻¹.val = (1 : ideal R) / I.val :=
by { rw [inv_nonzero h], refl }

@[simp] lemma div_one {I : fractional_ideal R (non_zero_divisors R)} : I / 1 = I :=
begin
  rw [div_nonzero (@one_ne_zero (fractional_ideal R _) _)],
  ext,
  split; intro h,
  { convert mem_div_iff_forall_mul_mem.mp h 1 (coe_mem_one 1), simp },
  { apply mem_div_iff_forall_mul_mem.mpr,
    rintros y ⟨y', _, y_eq_y'⟩,
    rw [mul_comm],
    convert submodule.smul _ y' h,
    simp [y_eq_y'.symm] }
end

lemma ne_zero_of_mul_eq_one (I J : fractional_ideal R (non_zero_divisors R)) (h : I * J = 1) : I ≠ 0 :=
λ hI, @zero_ne_one (fractional_ideal R (non_zero_divisors R)) _ (by { convert h, simp [hI], })

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : fractional_ideal R (non_zero_divisors R)) (h : I * J = 1) :
  J = I⁻¹ :=
begin
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h,
  suffices h' : I * (1 / I) = 1,
  { exact (congr_arg units.inv $
      @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl) },
  rw [div_nonzero hI],
  apply le_antisymm,
  { apply submodule.mul_le.mpr _,
    intros x hx y hy,
    rw [mul_comm],
    exact mem_div_iff_forall_mul_mem.mp hy x hx },
  rw [←h],
  apply mul_left_mono I,
  apply submodule.le_div_iff.mpr _,
  intros y hy x hx,
  rw [mul_comm],
  exact submodule.mul_mem_mul hx hy
end

theorem mul_inv_cancel_iff {I : fractional_ideal R (non_zero_divisors R)} :
  I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
⟨λ h, ⟨I⁻¹, h⟩, λ ⟨J, hJ⟩, by rwa [←right_inverse_eq I J hJ]⟩

end quotient

section invertible_of_principal

variables {R}

open_locale classical

open localization.fraction_ring
open submodule submodule.is_principal

lemma eq_generator_smul_one_of_principal (I : fractional_ideal R (non_zero_divisors R)) [is_principal I.1] :
  I = (generator I.1) • 1 :=
ext (by rw [val_smul_ideal, val_one, ideal.one_eq_top, smul_top, span_singleton_generator I.1])

lemma invertible_of_principal (I : fractional_ideal R (non_zero_divisors R))
  [submodule.is_principal I.1] (h : I ≠ 0) :
  I * I⁻¹ = 1 :=
begin
  refine mul_inv_cancel_iff.mpr ⟨(generator I.1)⁻¹ • 1, _⟩,
  -- Rewrite only the `I` that appears alone.
  conv_lhs { congr, rw eq_generator_smul_one_of_principal I },
  rw [smul_one_mul_smul_one, mul_inv_cancel, one_smul_ideal],
  intro generator_I_eq_zero,
  apply h,
  rw [eq_generator_smul_one_of_principal I, generator_I_eq_zero, zero_smul_ideal]
end

lemma exists_eq_smul_ideal (I : fractional_ideal R (non_zero_divisors R)) :
  ∃ (a : fraction_ring R) (aI : ideal R), I = a • aI :=
begin
  obtain ⟨a_inv, nonzero, aI, ha⟩ := exists_ideal_eq_smul I,
  use [(a_inv : fraction_ring R)⁻¹, aI],
  rw [ha, ←mul_smul_ideal, inv_mul_cancel, one_smul_ideal],
  exact mt (eq_zero_of a_inv) nonzero
end

@[simp]
lemma val_coe_ideal (I : ideal R) : (I : fractional_ideal R (non_zero_divisors R)).1 = I := rfl

instance fractional_ideal.is_principal {R} [principal_ideal_domain R]
  (I : fractional_ideal R (non_zero_divisors R)) : I.val.is_principal :=
⟨ begin
  obtain ⟨a, aI, ha⟩ := exists_eq_smul_ideal I,
  use a * ↑(generator aI),
  conv_lhs { rw [ha, val_smul_ideal, val_coe_ideal, ←span_singleton_generator aI] },
  rw [span_singleton_mul],
  congr,
  ext,
  split,
  { rintros ⟨x', h, rfl⟩,
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp h,
    refine mem_span_singleton.mpr ⟨a, _⟩,
    rw [lin_coe_apply, smul_eq_mul, coe_mul, coe_mul_eq_smul] }, -- TODO: cleanup?
  { rintros h,
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp h,
    refine ⟨a * generator aI, mem_span_singleton.mpr ⟨a, rfl⟩, _⟩,
    rw [lin_coe_apply, coe_mul, coe_mul_eq_smul] },
end⟩

end invertible_of_principal

end fractional_ideal

end ring
