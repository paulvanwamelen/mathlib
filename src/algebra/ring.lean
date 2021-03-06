/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston
-/
import algebra.group.hom
import algebra.group.units
import tactic.norm_cast
import tactic.split_ifs
import algebra.group.units

/-!
# Properties and homomorphisms of semirings and rings

This file proves simple properties of semirings, rings and domains and their unit groups. It also
defines homomorphisms of semirings and rings, both unbundled (e.g. `is_semiring_hom f`)
and bundled (e.g. `ring_hom a β`, a.k.a. `α →+* β`). The unbundled ones are deprecated
and the plan is to slowly remove them from mathlib.

## Main definitions

is_semiring_hom (deprecated), is_ring_hom (deprecated), ring_hom, nonzero_comm_semiring,
nonzero_comm_ring, domain

## Notations

→+* for bundled ring homs (also use for semiring homs)

## Implementation notes

There's a coercion from bundled homs to fun, and the canonical
notation is to use the bundled hom as a function via this coercion.

There is no `semiring_hom` -- the idea is that `ring_hom` is used.
The constructor for a `ring_hom` between semirings needs a proof of `map_zero`, `map_one` and
`map_add` as well as `map_mul`; a separate constructor `ring_hom.mk'` will construct ring homs
between rings from monoid homs given only a proof that addition is preserved.

Throughout the section on `ring_hom` implicit `{}` brackets are often used instead
of type class `[]` brackets. This is done when the instances can be inferred because they are
implicit arguments to the type `ring_hom`. When they can be inferred from the type it is faster
to use this method than to use type class inference.

## Tags

is_ring_hom, is_semiring_hom, ring_hom, semiring_hom, semiring, comm_semiring, ring, comm_ring,
domain, integral_domain, nonzero_comm_semiring, nonzero_comm_ring, units
-/
universes u v w
variable {α : Type u}

set_option default_priority 100 -- see Note [default priority]
set_option old_structure_cmd true

mk_simp_attribute field_simps "The simpset `field_simps` is used by the tactic `field_simp` to
reduce an expression in a field to an expression of the form `n / d` where `n` and `d` are
division-free."

@[ancestor has_mul has_add]
class distrib (α : Type u) extends has_mul α, has_add α :=
(left_distrib : ∀ a b c : α, a * (b + c) = (a * b) + (a * c))
(right_distrib : ∀ a b c : α, (a + b) * c = (a * c) + (b * c))

lemma left_distrib [distrib α] (a b c : α) : a * (b + c) = a * b + a * c :=
distrib.left_distrib a b c

def mul_add := @left_distrib

lemma right_distrib [distrib α] (a b c : α) : (a + b) * c = a * c + b * c :=
distrib.right_distrib a b c

def add_mul := @right_distrib

@[ancestor has_mul has_zero]
class mul_zero_class (α : Type u) extends has_mul α, has_zero α :=
(zero_mul : ∀ a : α, 0 * a = 0)
(mul_zero : ∀ a : α, a * 0 = 0)

@[ematch, simp] lemma zero_mul [mul_zero_class α] (a : α) : 0 * a = 0 :=
mul_zero_class.zero_mul a

@[ematch, simp] lemma mul_zero [mul_zero_class α] (a : α) : a * 0 = 0 :=
mul_zero_class.mul_zero a

@[ancestor has_zero has_one]
class zero_ne_one_class (α : Type u) extends has_zero α, has_one α :=
(zero_ne_one : 0 ≠ (1:α))

@[simp]
lemma zero_ne_one [s: zero_ne_one_class α] : 0 ≠ (1:α) :=
@zero_ne_one_class.zero_ne_one α s

@[simp]
lemma one_ne_zero [s: zero_ne_one_class α] : (1:α) ≠ 0 :=
assume h, @zero_ne_one_class.zero_ne_one α s h.symm

/- semiring -/

@[ancestor add_comm_monoid monoid distrib mul_zero_class]
class semiring (α : Type u) extends add_comm_monoid α, monoid α, distrib α, mul_zero_class α

section semiring
variables [semiring α]

lemma one_add_one_eq_two : 1 + 1 = (2 : α) :=
by unfold bit0

theorem two_mul (n : α) : 2 * n = n + n :=
eq.trans (right_distrib 1 1 n) (by simp)

lemma ne_zero_of_mul_ne_zero_right {a b : α} (h : a * b ≠ 0) : a ≠ 0 :=
assume : a = 0,
have a * b = 0, by rw [this, zero_mul],
h this

lemma ne_zero_of_mul_ne_zero_left {a b : α} (h : a * b ≠ 0) : b ≠ 0 :=
assume : b = 0,
have a * b = 0, by rw [this, mul_zero],
h this

lemma distrib_three_right (a b c d : α) : (a + b + c) * d = a * d + b * d + c * d :=
by simp [right_distrib]

theorem mul_two (n : α) : n * 2 = n + n :=
(left_distrib n 1 1).trans (by simp)

theorem bit0_eq_two_mul (n : α) : bit0 n = 2 * n :=
(two_mul _).symm

@[to_additive] lemma mul_ite {α} [has_mul α] (P : Prop) [decidable P] (a b c : α) :
  a * (if P then b else c) = if P then a * b else a * c :=
by split_ifs; refl

@[to_additive] lemma ite_mul {α} [has_mul α] (P : Prop) [decidable P] (a b c : α) :
  (if P then a else b) * c = if P then a * c else b * c :=
by split_ifs; refl

-- We make `mul_ite` and `ite_mul` simp lemmas,
-- but not `add_ite` or `ite_add`.
-- The problem we're trying to avoid is dealing with
-- summations of the form `s.sum (λ x, f x + ite P 1 0)`,
-- in which `add_ite` followed by `sum_ite` would needlessly slice up
-- the `f x` terms according to whether `P` holds at `x`.
-- There doesn't appear to be a corresponding difficulty so far with
-- `mul_ite` and `ite_mul`.
attribute [simp] mul_ite ite_mul

@[simp] lemma mul_boole {α} [semiring α] (P : Prop) [decidable P] (a : α) :
  a * (if P then 1 else 0) = if P then a else 0 :=
by simp

@[simp] lemma boole_mul {α} [semiring α] (P : Prop) [decidable P] (a : α) :
  (if P then 1 else 0) * a = if P then a else 0 :=
by simp

variable (α)

/-- Either zero and one are nonequal in a semiring, or the semiring is the zero ring. -/
lemma zero_ne_one_or_forall_eq_0 : (0 : α) ≠ 1 ∨ (∀a:α, a = 0) :=
by haveI := classical.dec;
   refine not_or_of_imp (λ h a, _); simpa using congr_arg ((*) a) h.symm

/-- If zero equals one in a semiring, the semiring is the zero ring. -/
lemma eq_zero_of_zero_eq_one (h : (0 : α) = 1) : (∀a:α, a = 0) :=
(zero_ne_one_or_forall_eq_0 α).neg_resolve_left h

/-- If zero equals one in a semiring, all elements of that semiring are equal. -/
theorem subsingleton_of_zero_eq_one (h : (0 : α) = 1) : subsingleton α :=
⟨λa b, by rw [eq_zero_of_zero_eq_one α h a, eq_zero_of_zero_eq_one α h b]⟩

end semiring

namespace add_monoid_hom

/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_left {R : Type*} [semiring R] (r : R) : R →+ R :=
{ to_fun := (*) r,
  map_zero' := mul_zero r,
  map_add' := mul_add r }

@[simp] lemma coe_mul_left {R : Type*} [semiring R] (r : R) : ⇑(mul_left r) = (*) r := rfl

/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mul_right {R : Type*} [semiring R] (r : R) : R →+ R :=
{ to_fun := λ a, a * r,
  map_zero' := zero_mul r,
  map_add' := λ _ _, add_mul _ _ r }

@[simp] lemma mul_right_apply {R : Type*} [semiring R] (a r : R) :
  (mul_right r : R → R) a = a * r := rfl

end add_monoid_hom

/-- Bundled semiring homomorphisms; use this for bundled ring homomorphisms too. -/
structure ring_hom (α : Type*) (β : Type*) [semiring α] [semiring β]
  extends monoid_hom α β, add_monoid_hom α β

infixr ` →+* `:25 := ring_hom

@[priority 1000]
instance {α : Type*} {β : Type*} {rα : semiring α} {rβ : semiring β} : has_coe_to_fun (α →+* β) :=
⟨_, ring_hom.to_fun⟩

@[priority 1000]
instance {α : Type*} {β : Type*} {rα : semiring α} {rβ : semiring β} : has_coe (α →+* β) (α →* β) :=
⟨ring_hom.to_monoid_hom⟩

@[priority 1000]
instance {α : Type*} {β : Type*} {rα : semiring α} {rβ : semiring β} : has_coe (α →+* β) (α →+ β) :=
⟨ring_hom.to_add_monoid_hom⟩

@[simp, norm_cast]
lemma coe_monoid_hom {α : Type*} {β : Type*} {rα : semiring α} {rβ : semiring β} (f : α →+* β) :
  ⇑(f : α →* β) = f := rfl

@[simp, norm_cast]
lemma coe_add_monoid_hom {α : Type*} {β : Type*} {rα : semiring α} {rβ : semiring β} (f : α →+* β) :
  ⇑(f : α →+ β) = f := rfl

namespace ring_hom

variables {β : Type v} {γ : Type w} [rα : semiring α] [rβ : semiring β]

section
include rα rβ

@[simp] lemma coe_mk (f : α → β) (h₁ h₂ h₃ h₄) : ⇑(⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) = f := rfl

variables (f : α →+* β) {x y : α} {rα rβ}

theorem coe_inj ⦃f g : α →+* β⦄ (h : (f : α → β) = g) : f = g :=
by cases f; cases g; cases h; refl

@[ext] theorem ext ⦃f g : α →+* β⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj (funext h)

theorem ext_iff {f g : α →+* β} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

theorem coe_add_monoid_hom_inj : function.injective (coe : (α →+* β) → (α →+ β)) :=
λ f g h, coe_inj $ show ((f : α →+ β) : α → β) = (g : α →+ β), from congr_arg coe_fn h

theorem coe_monoid_hom_inj : function.injective (coe : (α →+* β) → (α →* β)) :=
λ f g h, coe_inj $ show ((f : α →* β) : α → β) = (g : α →* β), from congr_arg coe_fn h

/-- Ring homomorphisms map zero to zero. -/
@[simp] lemma map_zero (f : α →+* β) : f 0 = 0 := f.map_zero'

/-- Ring homomorphisms map one to one. -/
@[simp] lemma map_one (f : α →+* β) : f 1 = 1 := f.map_one'

/-- Ring homomorphisms preserve addition. -/
@[simp] lemma map_add (f : α →+* β) (a b : α) : f (a + b) = f a + f b := f.map_add' a b

/-- Ring homomorphisms preserve multiplication. -/
@[simp] lemma map_mul (f : α →+* β) (a b : α) : f (a * b) = f a * f b := f.map_mul' a b

end

/-- The identity ring homomorphism from a semiring to itself. -/
def id (α : Type*) [semiring α] : α →+* α :=
by refine {to_fun := id, ..}; intros; refl

include rα

@[simp] lemma id_apply (x : α) : ring_hom.id α x = x := rfl

variable {rγ : semiring γ}
include rβ rγ

/-- Composition of ring homomorphisms is a ring homomorphism. -/
def comp (hnp : β →+* γ) (hmn : α →+* β) : α →+* γ :=
{ to_fun := hnp ∘ hmn,
  map_zero' := by simp,
  map_one' := by simp,
  map_add' := λ x y, by simp,
  map_mul' := λ x y, by simp}

/-- Composition of semiring homomorphisms is associative. -/
lemma comp_assoc {δ} {rδ: semiring δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp] lemma coe_comp (hnp : β →+* γ) (hmn : α →+* β) : (hnp.comp hmn : α → γ) = hnp ∘ hmn := rfl

lemma comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) : (hnp.comp hmn : α → γ) x =
  (hnp (hmn x)) := rfl

omit rγ

@[simp] lemma comp_id (f : α →+* β) : f.comp (id α) = f := ext $ λ x, rfl

@[simp] lemma id_comp (f : α →+* β) : (id β).comp f = f := ext $ λ x, rfl

omit rβ

instance : monoid (α →+* α) :=
{ one := id α,
  mul := comp,
  mul_one := comp_id,
  one_mul := id_comp,
  mul_assoc := λ f g h, comp_assoc _ _ _ }

lemma one_def : (1 : α →+* α) = id α := rfl

@[simp] lemma coe_one : ⇑(1 : α →+* α) = _root_.id := rfl

lemma mul_def (f g : α →+* α) : f * g = f.comp g := rfl

@[simp] lemma coe_mul (f g : α →+* α) : ⇑(f * g) = f ∘ g := rfl

include rβ rγ

lemma cancel_right {g₁ g₂ : β →+* γ} {f : α →+* β} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ring_hom.ext $ (forall_iff_forall_surj hf).1 (ext_iff.1 h), λ h, h ▸ rfl⟩

lemma cancel_left {g : β →+* γ} {f₁ f₂ : α →+* β} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ring_hom.ext $ λ x, hg $ by rw [← comp_apply, h, comp_apply], λ h, h ▸ rfl⟩

omit rα rβ rγ

end ring_hom

@[ancestor semiring comm_monoid]
class comm_semiring (α : Type u) extends semiring α, comm_monoid α

section comm_semiring
variables [comm_semiring α] {a b c : α}

instance comm_semiring_has_dvd : has_dvd α :=
has_dvd.mk (λ a b, ∃ c, b = a * c)

-- TODO: this used to not have c explicit, but that seems to be important
--       for use with tactics, similar to exist.intro
theorem dvd.intro (c : α) (h : a * c = b) : a ∣ b :=
exists.intro c h^.symm

def dvd_of_mul_right_eq := @dvd.intro

theorem dvd.intro_left (c : α) (h : c * a = b) : a ∣ b :=
dvd.intro _ (begin rewrite mul_comm at h, apply h end)

def dvd_of_mul_left_eq := @dvd.intro_left

theorem exists_eq_mul_right_of_dvd (h : a ∣ b) : ∃ c, b = a * c := h

theorem dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
exists.elim H₁ H₂

theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : ∃ c, b = c * a :=
dvd.elim h (assume c, assume H1 : b = a * c, exists.intro c (eq.trans H1 (mul_comm a c)))

theorem dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
exists.elim (exists_eq_mul_left_of_dvd h₁) (assume c, assume h₃ : b = c * a, h₂ c h₃)

@[refl, simp] theorem dvd_refl (a : α) : a ∣ a :=
dvd.intro 1 (by simp)

local attribute [simp] mul_assoc mul_comm mul_left_comm

@[trans] theorem dvd_trans (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
match h₁, h₂ with
| ⟨d, (h₃ : b = a * d)⟩, ⟨e, (h₄ : c = b * e)⟩ :=
  ⟨d * e, show c = a * (d * e), by simp [h₃, h₄]⟩
end

def dvd.trans := @dvd_trans

theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
dvd.elim h (assume c, assume H' : a = 0 * c, eq.trans H' (zero_mul c))

/-- Given an element a of a commutative semiring, there exists another element whose product
    with zero equals a iff a equals zero. -/
@[simp] lemma zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
⟨eq_zero_of_zero_dvd, λ h, by rw h⟩

@[simp] theorem dvd_zero (a : α) : a ∣ 0 := dvd.intro 0 (by simp)

@[simp] theorem one_dvd (a : α) : 1 ∣ a := dvd.intro a (by simp)

@[simp] theorem dvd_mul_right (a b : α) : a ∣ a * b := dvd.intro b rfl

@[simp] theorem dvd_mul_left (a b : α) : a ∣ b * a := dvd.intro b (by simp)

theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c :=
dvd.elim h (λ d h', begin rw [h', mul_assoc], apply dvd_mul_right end)

theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b :=
begin rw mul_comm, exact dvd_mul_of_dvd_left h _ end

theorem mul_dvd_mul : ∀ {a b c d : α}, a ∣ b → c ∣ d → a * c ∣ b * d
| a ._ c ._ ⟨e, rfl⟩ ⟨f, rfl⟩ := ⟨e * f, by simp⟩

theorem mul_dvd_mul_left (a : α) {b c : α} (h : b ∣ c) : a * b ∣ a * c :=
mul_dvd_mul (dvd_refl a) h

theorem mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c :=
mul_dvd_mul h (dvd_refl c)

theorem dvd_add (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
dvd.elim h₁ (λ d hd, dvd.elim h₂ (λ e he, dvd.intro (d + e) (by simp [left_distrib, hd, he])))

theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c :=
dvd.elim h (begin intros d h₁, rw [h₁, mul_assoc], apply dvd_mul_right end)

theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c :=
dvd.elim h (λ d ceq, dvd.intro (a * d) (by simp [ceq]))

end comm_semiring

/- ring -/

@[ancestor add_comm_group monoid distrib]
class ring (α : Type u) extends add_comm_group α, monoid α, distrib α

section ring
variables [ring α] {a b c d e : α}

lemma ring.mul_zero (a : α) : a * 0 = 0 :=
have a * 0 + 0 = a * 0 + a * 0, from calc
     a * 0 + 0 = a * (0 + 0)   : by simp
           ... = a * 0 + a * 0 : by rw left_distrib,
show a * 0 = 0, from (add_left_cancel this).symm

lemma ring.zero_mul (a : α) : 0 * a = 0 :=
have 0 * a + 0 = 0 * a + 0 * a, from calc
  0 * a + 0 = (0 + 0) * a   : by simp
        ... = 0 * a + 0 * a : by rewrite right_distrib,
show 0 * a = 0, from  (add_left_cancel this).symm

instance ring.to_semiring : semiring α :=
{ mul_zero := ring.mul_zero, zero_mul := ring.zero_mul, ..‹ring α› }

lemma neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b :=
neg_eq_of_add_eq_zero
  begin rw [← right_distrib, add_right_neg, zero_mul] end

lemma neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
neg_eq_of_add_eq_zero
  begin rw [← left_distrib, add_right_neg, mul_zero] end

@[simp] lemma neg_mul_eq_neg_mul_symm (a b : α) : - a * b = - (a * b) :=
eq.symm (neg_mul_eq_neg_mul a b)

@[simp] lemma mul_neg_eq_neg_mul_symm (a b : α) : a * - b = - (a * b) :=
eq.symm (neg_mul_eq_mul_neg a b)

lemma neg_mul_neg (a b : α) : -a * -b = a * b :=
by simp

lemma neg_mul_comm (a b : α) : -a * b = a * -b :=
by simp

theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a :=
by simp

lemma mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c :=
calc
   a * (b - c) = a * b + a * -c : left_distrib a b (-c)
           ... = a * b - a * c  : by simp [sub_eq_add_neg]

def mul_sub := @mul_sub_left_distrib

lemma mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c :=
calc
  (a - b) * c = a * c  + -b * c : right_distrib a (-b) c
          ... = a * c - b * c   : by simp [sub_eq_add_neg]

def sub_mul := @mul_sub_right_distrib

/-- An element of a ring multiplied by the additive inverse of one is the element's additive
  inverse. -/
lemma mul_neg_one (a : α) : a * -1 = -a := by simp

/-- The additive inverse of one multiplied by an element of a ring is the element's additive
  inverse. -/
lemma neg_one_mul (a : α) : -1 * a = -a := by simp

/-- An iff statement following from right distributivity in rings and the definition
  of subtraction. -/
theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
calc
  a * e + c = b * e + d ↔ a * e + c = d + b * e : by simp [add_comm]
    ... ↔ a * e + c - b * e = d : iff.intro (λ h, begin rw h, simp end) (λ h,
                                                  begin rw ← h, simp end)
    ... ↔ (a - b) * e + c = d   : begin simp [sub_mul, sub_add_eq_add_sub] end

/-- A simplification of one side of an equation exploiting right distributivity in rings
  and the definition of subtraction. -/
theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d :=
assume h,
calc
  (a - b) * e + c = (a * e + c) - b * e : begin simp [sub_mul, sub_add_eq_add_sub] end
              ... = d                   : begin rw h, simp [@add_sub_cancel α] end

/-- If the product of two elements of a ring is nonzero, both elements are nonzero. -/
theorem ne_zero_and_ne_zero_of_mul_ne_zero (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
begin
  split,
  { intro ha, apply h, simp [ha] },
  { intro hb, apply h, simp [hb] }
end

end ring

namespace units
variables [ring α] {a b : α}

/-- Each element of the group of units of a ring has an additive inverse. -/
instance : has_neg (units α) := ⟨λu, ⟨-↑u, -↑u⁻¹, by simp, by simp⟩ ⟩

/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp] protected theorem coe_neg (u : units α) : (↑-u : α) = -u := rfl

/-- Mapping an element of a ring's unit group to its inverse commutes with mapping this element
    to its additive inverse. -/
@[simp] protected theorem neg_inv (u : units α) : (-u)⁻¹ = -u⁻¹ := rfl

/-- An element of a ring's unit group equals the additive inverse of its additive inverse. -/
@[simp] protected theorem neg_neg (u : units α) : - -u = u :=
units.ext $ neg_neg _

/-- Multiplication of elements of a ring's unit group commutes with mapping the first
    argument to its additive inverse. -/
@[simp] protected theorem neg_mul (u₁ u₂ : units α) : -u₁ * u₂ = -(u₁ * u₂) :=
units.ext $ neg_mul_eq_neg_mul_symm _ _

/-- Multiplication of elements of a ring's unit group commutes with mapping the second argument
    to its additive inverse. -/
@[simp] protected theorem mul_neg (u₁ u₂ : units α) : u₁ * -u₂ = -(u₁ * u₂) :=
units.ext $ (neg_mul_eq_mul_neg _ _).symm

/-- Multiplication of the additive inverses of two elements of a ring's unit group equals
    multiplication of the two original elements. -/
@[simp] protected theorem neg_mul_neg (u₁ u₂ : units α) : -u₁ * -u₂ = u₁ * u₂ := by simp

/-- The additive inverse of an element of a ring's unit group equals the additive inverse of
    one times the original element. -/
protected theorem neg_eq_neg_one_mul (u : units α) : -u = -1 * u := by simp

end units

namespace ring_hom

/-- Ring homomorphisms preserve additive inverse. -/
@[simp] theorem map_neg {α β} [ring α] [ring β] (f : α →+* β) (x : α) : f (-x) = -(f x) :=
(f : α →+ β).map_neg x

/-- Ring homomorphisms preserve subtraction. -/
@[simp] theorem map_sub {α β} [ring α] [ring β] (f : α →+* β) (x y : α) :
  f (x - y) = (f x) - (f y) := (f : α →+ β).map_sub x y

/-- A ring homomorphism is injective iff its kernel is trivial. -/
theorem injective_iff {α β} [ring α] [ring β] (f : α →+* β) :
  function.injective f ↔ (∀ a, f a = 0 → a = 0) :=
(f : α →+ β).injective_iff

/-- Makes a ring homomorphism from a monoid homomorphism of rings which preserves addition. -/
def mk' {γ} [semiring α] [ring γ] (f : α →* γ) (map_add : ∀ a b : α, f (a + b) = f a + f b) :
  α →+* γ :=
{ to_fun := f,
  .. add_monoid_hom.mk' f map_add, .. f }

end ring_hom

@[ancestor ring comm_semigroup]
class comm_ring (α : Type u) extends ring α, comm_semigroup α

instance comm_ring.to_comm_semiring [s : comm_ring α] : comm_semiring α :=
{ mul_zero := mul_zero, zero_mul := zero_mul, ..s }

section comm_ring
variables [comm_ring α] {a b c : α}

local attribute [simp] add_assoc add_comm add_left_comm mul_comm

lemma mul_self_sub_mul_self_eq (a b : α) : a * a - b * b = (a + b) * (a - b) :=
begin simp [right_distrib, left_distrib, sub_eq_add_neg] end

lemma mul_self_sub_one_eq (a : α) : a * a - 1 = (a + 1) * (a - 1) :=
begin simp [right_distrib, left_distrib, sub_eq_add_neg], rw [add_left_comm, add_comm (-a), add_left_comm a], simp end

lemma add_mul_self_eq (a b : α) : (a + b) * (a + b) = a*a + 2*a*b + b*b :=
calc (a + b)*(a + b) = a*a + (1+1)*a*b + b*b : by simp [right_distrib, left_distrib]
              ...     = a*a + 2*a*b + b*b     : by rw one_add_one_eq_two

theorem dvd_neg_of_dvd (h : a ∣ b) : (a ∣ -b) :=
dvd.elim h
  (assume c, assume : b = a * c,
    dvd.intro (-c) (by simp [this]))

theorem dvd_of_dvd_neg (h : a ∣ -b) : (a ∣ b) :=
let t := dvd_neg_of_dvd h in by rwa neg_neg at t

theorem dvd_neg_iff_dvd (a b : α) : (a ∣ -b) ↔ (a ∣ b) :=
⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

theorem neg_dvd_of_dvd (h : a ∣ b) : -a ∣ b :=
dvd.elim h
  (assume c, assume : b = a * c,
    dvd.intro (-c) (by simp [this]))

theorem dvd_of_neg_dvd (h : -a ∣ b) : a ∣ b :=
let t := neg_dvd_of_dvd h in by rwa neg_neg at t

theorem neg_dvd_iff_dvd (a b : α) : (-a ∣ b) ↔ (a ∣ b) :=
⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩

theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c :=
dvd_add h₁ (dvd_neg_of_dvd h₂)

theorem dvd_add_iff_left (h : a ∣ c) : a ∣ b ↔ a ∣ b + c :=
⟨λh₂, dvd_add h₂ h, λH, by have t := dvd_sub H h; rwa add_sub_cancel at t⟩

theorem dvd_add_iff_right (h : a ∣ b) : a ∣ c ↔ a ∣ b + c :=
by rw add_comm; exact dvd_add_iff_left h

/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self (a b : α) : a * a - b * b = (a + b) * (a - b) :=
by rw [add_mul, mul_sub, mul_sub, mul_comm a b, sub_add_sub_cancel]

/-- An element a of a commutative ring divides the additive inverse of an element b iff a
  divides b. -/
@[simp] lemma dvd_neg (a b : α) : (a ∣ -b) ↔ (a ∣ b) :=
⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

/-- The additive inverse of an element a of a commutative ring divides another element b iff a
  divides b. -/
@[simp] lemma neg_dvd (a b : α) : (-a ∣ b) ↔ (a ∣ b) :=
⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩

/-- If an element a divides another element c in a commutative ring, a divides the sum of another
  element b with c iff a divides b. -/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
(dvd_add_iff_left h).symm

/-- If an element a divides another element b in a commutative ring, a divides the sum of b and
  another element c iff a divides c. -/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c :=
(dvd_add_iff_right h).symm

/-- An element a divides the sum a + b if and only if a divides b.-/
@[simp] lemma dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
dvd_add_right (dvd_refl a)

/-- An element a divides the sum b + a if and only if a divides b.-/
@[simp] lemma dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
dvd_add_left (dvd_refl a)

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
lemma Vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
  ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c :=
begin
  have : c = -(x * x - b * x) := (neg_eq_of_add_eq_zero h).symm,
  have : c = x * (b - x), by subst this; simp [mul_sub, mul_comm],
  refine ⟨b - x, _, by simp, by rw this⟩,
  rw [this, sub_add, ← sub_mul, sub_self]
end

end comm_ring

/-- Predicate for semirings in which zero does not equal one. -/
class nonzero_semiring (α : Type*) extends semiring α, zero_ne_one_class α

/-- Predicate for commutative semirings in which zero does not equal one. -/
class nonzero_comm_semiring (α : Type*) extends comm_semiring α, zero_ne_one_class α

/-- Predicate for commutative rings in which zero does not equal one. -/
class nonzero_comm_ring (α : Type*) extends comm_ring α, zero_ne_one_class α

-- This could be generalized, for example if we added `nonzero_ring` into the hierarchy,
-- but it doesn't seem worth doing just for these lemmas.
lemma succ_ne_self [nonzero_comm_ring α] (a : α) : a + 1 ≠ a :=
λ h, one_ne_zero ((add_right_inj a).mp (by simp [h]))

-- As with succ_ne_self.
lemma pred_ne_self [nonzero_comm_ring α] (a : α) : a - 1 ≠ a :=
λ h, one_ne_zero (neg_inj ((add_right_inj a).mp (by { convert h, simp })))

/-- A nonzero commutative semiring is a nonzero semiring. -/
@[priority 100] -- see Note [lower instance priority]
instance nonzero_comm_semiring.to_nonzero_semiring {α : Type*} [ncs : nonzero_comm_semiring α] :
  nonzero_semiring α :=
{..ncs}

/-- A nonzero commutative ring is a nonzero commutative semiring. -/
@[priority 100] -- see Note [lower instance priority]
instance nonzero_comm_ring.to_nonzero_comm_semiring {α : Type*} [I : nonzero_comm_ring α] :
  nonzero_comm_semiring α :=
{ zero_ne_one := by convert zero_ne_one,
  ..show comm_semiring α, by apply_instance }

/-- An element of the unit group of a nonzero commutative semiring represented as an element
    of the semiring is nonzero. -/
lemma units.coe_ne_zero [nonzero_comm_semiring α] (u : units α) : (u : α) ≠ 0 :=
λ h : u.1 = 0, by simpa [h, zero_ne_one] using u.3

/-- Makes a nonzero commutative ring from a commutative ring containing at least two distinct
    elements. -/
def nonzero_comm_ring.of_ne [comm_ring α] {x y : α} (h : x ≠ y) : nonzero_comm_ring α :=
{ one := 1,
  zero := 0,
  zero_ne_one := λ h01, h $ by rw [← one_mul x, ← one_mul y, ← h01, zero_mul, zero_mul],
  ..show comm_ring α, by apply_instance }

/-- Makes a nonzero commutative semiring from a commutative semiring containing at least two
    distinct elements. -/
def nonzero_comm_semiring.of_ne [comm_semiring α] {x y : α} (h : x ≠ y) : nonzero_comm_semiring α :=
{ one := 1,
  zero := 0,
  zero_ne_one := λ h01, h $ by rw [← one_mul x, ← one_mul y, ← h01, zero_mul, zero_mul],
  ..show comm_semiring α, by apply_instance }

@[ancestor has_mul has_zero]
class no_zero_divisors (α : Type u) extends has_mul α, has_zero α :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)

lemma eq_zero_or_eq_zero_of_mul_eq_zero [no_zero_divisors α] {a b : α} (h : a * b = 0) : a = 0 ∨ b = 0 :=
no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero a b h

lemma eq_zero_of_mul_self_eq_zero [no_zero_divisors α] {a : α} (h : a * a = 0) : a = 0 :=
or.elim (eq_zero_or_eq_zero_of_mul_eq_zero h) (assume h', h') (assume h', h')

/-- A domain is a ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`. Alternatively, a domain
  is an integral domain without assuming commutativity of multiplication. -/
class domain (α : Type u) extends ring α, no_zero_divisors α, zero_ne_one_class α

section domain
variable [domain α]

/-- Simplification theorems for the definition of a domain. -/
@[simp] theorem mul_eq_zero {a b : α} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
⟨eq_zero_or_eq_zero_of_mul_eq_zero, λo,
  or.elim o (λh, by rw h; apply zero_mul) (λh, by rw h; apply mul_zero)⟩

@[simp] theorem zero_eq_mul {a b : α} : 0 = a * b ↔ a = 0 ∨ b = 0 :=
by rw [eq_comm, mul_eq_zero]

lemma mul_self_eq_zero {α} [domain α] {x : α} : x * x = 0 ↔ x = 0 := by simp
lemma zero_eq_mul_self {α} [domain α] {x : α} : 0 = x * x ↔ x = 0 := by simp

/-- The product of two nonzero elements of a domain is nonzero. -/
theorem mul_ne_zero' {a b : α} (h₁ : a ≠ 0) (h₂ : b ≠ 0) : a * b ≠ 0 :=
λ h, or.elim (eq_zero_or_eq_zero_of_mul_eq_zero h) h₁ h₂

/-- Right multiplication by a nonzero element in a domain is injective. -/
theorem domain.mul_left_inj {a b c : α} (ha : a ≠ 0) : b * a = c * a ↔ b = c :=
by rw [← sub_eq_zero, ← mul_sub_right_distrib, mul_eq_zero];
    simp [ha]; exact sub_eq_zero

/-- Left multiplication by a nonzero element in a domain is injective. -/
theorem domain.mul_right_inj {a b c : α} (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
by rw [← sub_eq_zero, ← mul_sub_left_distrib, mul_eq_zero];
    simp [ha]; exact sub_eq_zero

/-- An element of a domain fixed by right multiplication by an element other than one must
  be zero. -/
theorem eq_zero_of_mul_eq_self_right' {a b : α} (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
by apply (mul_eq_zero.1 _).resolve_right (sub_ne_zero.2 h₁);
    rw [mul_sub_left_distrib, mul_one, sub_eq_zero, h₂]

/-- An element of a domain fixed by left multiplication by an element other than one must
  be zero. -/
theorem eq_zero_of_mul_eq_self_left' {a b : α} (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
by apply (mul_eq_zero.1 _).resolve_left (sub_ne_zero.2 h₁);
    rw [mul_sub_right_distrib, one_mul, sub_eq_zero, h₂]

/-- For elements a, b of a domain, if a*b is nonzero, so is b*a. -/
theorem mul_ne_zero_comm' {a b : α} (h : a * b ≠ 0) : b * a ≠ 0 :=
mul_ne_zero' (ne_zero_of_mul_ne_zero_left h) (ne_zero_of_mul_ne_zero_right h)

end domain

/- integral domains -/

@[ancestor comm_ring no_zero_divisors zero_ne_one_class]
class integral_domain (α : Type u) extends comm_ring α, no_zero_divisors α, zero_ne_one_class α

section integral_domain
variables [integral_domain α] {a b c d e : α}

lemma mul_eq_zero_iff_eq_zero_or_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
⟨eq_zero_or_eq_zero_of_mul_eq_zero, λo,
  or.elim o (λh, by rw h; apply zero_mul) (λh, by rw h; apply mul_zero)⟩

lemma mul_ne_zero (h₁ : a ≠ 0) (h₂ : b ≠ 0) : a * b ≠ 0 :=
λ h, or.elim (eq_zero_or_eq_zero_of_mul_eq_zero h) (assume h₃, h₁ h₃) (assume h₄, h₂ h₄)

lemma eq_of_mul_eq_mul_right (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
have b * a - c * a = 0, from sub_eq_zero_of_eq h,
have (b - c) * a = 0,   by rw [mul_sub_right_distrib, this],
have b - c = 0,         from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha,
eq_of_sub_eq_zero this

lemma eq_of_mul_eq_mul_left (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
have a * b - a * c = 0, from sub_eq_zero_of_eq h,
have a * (b - c) = 0,   by rw [mul_sub_left_distrib, this],
have b - c = 0,         from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha,
eq_of_sub_eq_zero this

lemma eq_zero_of_mul_eq_self_right (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
have hb : b - 1 ≠ 0, from
  assume : b - 1 = 0,
  have b = 0 + 1, from eq_add_of_sub_eq this,
  have b = 1,     by rwa zero_add at this,
  h₁ this,
have a * b - a = 0,   by simp [h₂],
have a * (b - 1) = 0, by rwa [mul_sub_left_distrib, mul_one],
  show a = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hb

lemma eq_zero_of_mul_eq_self_left (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
eq_zero_of_mul_eq_self_right h₁ (by rwa mul_comm at h₂)

lemma mul_self_eq_mul_self_iff (a b : α) : a * a = b * b ↔ a = b ∨ a = -b :=
iff.intro
  (assume : a * a = b * b,
    have (a - b) * (a + b) = 0,
      by rewrite [mul_comm, ← mul_self_sub_mul_self_eq, this, sub_self],
    have a - b = 0 ∨ a + b = 0, from eq_zero_or_eq_zero_of_mul_eq_zero this,
    or.elim this
      (assume : a - b = 0, or.inl (eq_of_sub_eq_zero this))
      (assume : a + b = 0, or.inr (eq_neg_of_add_eq_zero this)))
  (assume : a = b ∨ a = -b, or.elim this
    (assume : a = b,  by rewrite this)
    (assume : a = -b, by rewrite [this, neg_mul_neg]))

lemma mul_self_eq_one_iff (a : α) : a * a = 1 ↔ a = 1 ∨ a = -1 :=
have a * a = 1 * 1 ↔ a = 1 ∨ a = -1, from mul_self_eq_mul_self_iff a 1,
by rwa mul_one at this

/-- An integral domain is a domain. -/
instance integral_domain.to_domain : domain α :=
{..‹integral_domain α›, ..(by apply_instance : semiring α)}

/-- Right multiplcation by a nonzero element of an integral domain is injective. -/
theorem eq_of_mul_eq_mul_right_of_ne_zero (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
have b * a - c * a = 0, by simp [h],
have (b - c) * a = 0, by rw [mul_sub_right_distrib, this],
have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right ha,
eq_of_sub_eq_zero this

/-- Left multiplication by a nonzero element of an integral domain is injective. -/
theorem eq_of_mul_eq_mul_left_of_ne_zero (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
have a * b - a * c = 0, by simp [h],
have a * (b - c) = 0, by rw [mul_sub_left_distrib, this],
have b - c = 0, from (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left ha,
eq_of_sub_eq_zero this

/-- Given two elements b, c of an integral domain and a nonzero element a, a*b divides a*c iff
  b divides c. -/
theorem mul_dvd_mul_iff_left (ha : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c :=
exists_congr $ λ d, by rw [mul_assoc, domain.mul_right_inj ha]

/-- Given two elements a, b of an integral domain and a nonzero element c, a*c divides b*c iff
  a divides b. -/
theorem mul_dvd_mul_iff_right (hc : c ≠ 0) : a * c ∣ b * c ↔ a ∣ b :=
exists_congr $ λ d, by rw [mul_right_comm, domain.mul_left_inj hc]

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
lemma units.inv_eq_self_iff (u : units α) : u⁻¹ = u ↔ u = 1 ∨ u = -1 :=
by conv {to_lhs, rw [inv_eq_iff_mul_eq_one, ← mul_one (1 : units α), units.ext_iff, units.coe_mul,
  units.coe_mul, mul_self_eq_mul_self_iff, ← units.ext_iff, ← units.coe_neg, ← units.ext_iff] }

/-- An integral domain is a nonzero commutative ring. -/
instance integral_domain.to_nonzero_comm_ring
  (α : Type*) [integral_domain α] : nonzero_comm_ring α :=
{ ..‹integral_domain α› }

end integral_domain

/- units in various rings -/

namespace units

section semiring
variables [semiring α]

@[simp] theorem mul_left_eq_zero_iff_eq_zero
  {r : α} (u : units α) : r * u = 0 ↔ r = 0 :=
⟨λ h, (mul_left_inj u).1 $ (zero_mul (u : α)).symm ▸ h,
 λ h, h.symm ▸ zero_mul (u : α)⟩

@[simp] theorem mul_right_eq_zero_iff_eq_zero
  {r : α} (u : units α) : (u : α) * r = 0 ↔ r = 0 :=
⟨λ h, (mul_right_inj u).1 $ (mul_zero (u : α)).symm ▸ h,
 λ h, h.symm ▸ mul_zero (u : α)⟩

end semiring

section comm_semiring
variables [comm_semiring α] (a b : α) (u : units α)

/-- Elements of the unit group of a commutative semiring represented as elements of the semiring
    divide any element of the semiring. -/
@[simp] lemma coe_dvd : ↑u ∣ a := ⟨↑u⁻¹ * a, by simp⟩

/-- In a commutative semiring, an element a divides an element b iff a divides all
    associates of b. -/
@[simp] lemma dvd_coe_mul : a ∣ b * u ↔ a ∣ b :=
iff.intro
  (assume ⟨c, eq⟩, ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, units.mul_inv_cancel_right]⟩)
  (assume ⟨c, eq⟩, eq.symm ▸ dvd_mul_of_dvd_left (dvd_mul_right _ _) _)

/-- An element of a commutative semiring divides a unit iff the element divides one. -/
@[simp] lemma dvd_coe : a ∣ ↑u ↔ a ∣ 1 :=
suffices a ∣ 1 * ↑u ↔ a ∣ 1, by simpa,
dvd_coe_mul _ _ _

/-- In a commutative semiring, an element a divides an element b iff all associates of a divide b.-/
@[simp] lemma coe_mul_dvd : a * u ∣ b ↔ a ∣ b :=
iff.intro
  (assume ⟨c, eq⟩, ⟨c * ↑u, eq.symm ▸ by ac_refl⟩)
  (assume h, suffices a * ↑u ∣ b * 1, by simpa, mul_dvd_mul h (coe_dvd _ _))

end comm_semiring

section domain
variables [domain α]

/-- Every unit in a domain is nonzero. -/
@[simp] theorem ne_zero : ∀(u : units α), (↑u : α) ≠ 0
| ⟨u, v, (huv : 0 * v = 1), hvu⟩ rfl := by simpa using huv

end domain

end units

namespace is_unit

section semiring
variables [semiring α]

theorem mul_left_eq_zero_iff_eq_zero {r u : α}
  (hu : is_unit u) : r * u = 0 ↔ r = 0 :=
by cases hu with u hu; exact hu.symm ▸ units.mul_left_eq_zero_iff_eq_zero u

theorem mul_right_eq_zero_iff_eq_zero {r u : α}
  (hu : is_unit u) : u * r = 0 ↔ r = 0 :=
by cases hu with u hu; exact hu.symm ▸ units.mul_right_eq_zero_iff_eq_zero u

end semiring

end is_unit

/-- A predicate to express that a ring is an integral domain.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms. -/
structure is_integral_domain (R : Type u) [ring R] : Prop :=
(mul_comm : ∀ (x y : R), x * y = y * x)
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ x y : R, x * y = 0 → x = 0 ∨ y = 0)
(zero_ne_one : (0 : R) ≠ 1)

/-- Every integral domain satisfies the predicate for integral domains. -/
lemma integral_domain.to_is_integral_domain (R : Type u) [integral_domain R] :
  is_integral_domain R :=
{ .. (‹_› : integral_domain R) }

/-- If a ring satisfies the predicate for integral domains,
then it can be endowed with an `integral_domain` instance
whose data is definitionally equal to the existing data. -/
def is_integral_domain.to_integral_domain (R : Type u) [ring R] (h : is_integral_domain R) :
  integral_domain R :=
{ .. (‹_› : ring R), .. (‹_› : is_integral_domain R) }
