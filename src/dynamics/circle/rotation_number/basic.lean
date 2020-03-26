import category_theory.endomorphism category_theory.types analysis.normed_space.quasi_hom
  tactic.monotonicity tactic.find tactic.fin_cases

open category_theory (End)
open_locale smul

/-- A lift of a monotone degree one map `S¹ → S¹`. -/
structure circle_deg1_lift : Type :=
(to_fun : End ℝ)
(mono' : monotone to_fun)
(deg1' : ∀ x, to_fun (x + 1) = to_fun x + 1)

instance : has_coe_to_fun circle_deg1_lift := ⟨λ _, End ℝ, circle_deg1_lift.to_fun⟩

namespace circle_deg1_lift

variables (f g : circle_deg1_lift)

lemma mono  : monotone f := f.mono'

lemma deg1 : ∀ x, f (x + 1) = f x + 1 := f.deg1'

theorem coe_inj : ∀ ⦃f g : circle_deg1_lift ⦄, (f : End ℝ) = g → f = g :=
assume ⟨f, fm, fd⟩ ⟨g, gm, gd⟩ h, by congr; exact h

@[ext] theorem ext ⦃f g : circle_deg1_lift ⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj $ funext h

instance : has_mul circle_deg1_lift :=
⟨λ f g,
  { to_fun := f * g,
    mono' := f.mono.comp g.mono,
    deg1' := λ x, show f (g (x + 1)) = f (g x) + 1, by rw [g.deg1, f.deg1] }⟩

instance : has_one circle_deg1_lift := ⟨⟨1, monotone_id, λ _, rfl⟩⟩

instance : monoid circle_deg1_lift :=
{ mul := (*),
  one := 1,
  mul_one := λ f, coe_inj $ mul_one f.to_fun,
  one_mul := λ f, coe_inj $ one_mul f.to_fun,
  mul_assoc := λ f₁ f₂ f₃, coe_inj $ mul_assoc f₁.to_fun f₂.to_fun f₃.to_fun }

def translation : multiplicative ℝ →* circle_deg1_lift :=
{ to_fun := λ x, ⟨λ y, x + y, λ y₁ y₂ h, add_le_add_left h x, λ y, (add_assoc _ _ _).symm⟩,
  map_one' := ext $ zero_add,
  map_mul' := λ x y, ext $ λ z, add_assoc _ _ _ }

lemma map_add_nat (x : ℝ) : ∀ n : ℕ, f (x + n) = f x + n
| 0 := by simp only [nat.cast_zero, add_zero]
| (n+1) := by simp only [nat.cast_add, (add_assoc _ _ _).symm, nat.cast_one, f.deg1, map_add_nat n]

lemma map_add_int (x : ℝ) : ∀ n : ℤ, f (x + n) = f x + n
| (n : ℕ) := f.map_add_nat x n
| -[1+n] :=
begin
  rw [int.cast_neg_succ_of_nat, ← sub_eq_add_neg, ← sub_eq_add_neg],
  conv_rhs { rw [← sub_add_cancel x ((n + 1) : ℕ), f.map_add_nat] },
  simp only [nat.cast_succ, add_sub_cancel]
end

lemma map_sub_int (x : ℝ) (n : ℤ) : f (x - n) = f x - n :=
by rw [sub_eq_add_neg, sub_eq_add_neg, ← int.cast_neg, f.map_add_int, int.cast_neg]

lemma map_int_of_map_zero (n : ℤ) : f n = f 0 + n :=
by rw [← f.map_add_int, zero_add]

lemma map_le_of_map_zero (x : ℝ) : f x ≤ f 0 + ⌈x⌉ :=
calc f x ≤ f ⌈x⌉     : f.mono $ le_ceil _
     ... = f 0 + ⌈x⌉ : f.map_int_of_map_zero _

lemma map_ge_of_map_zero (x : ℝ) : f 0 + ⌊x⌋ ≤ f x :=
calc f 0 + ⌊x⌋ = f ⌊x⌋ : (f.map_int_of_map_zero _).symm
           ... ≤ f x   : f.mono $ floor_le _

lemma mul_map_zero_le : (f * g) 0 ≤ f 0 + ⌈g 0⌉ := f.map_le_of_map_zero (g 0)

lemma mul_map_zero_ge : f 0 + ⌊g 0⌋ ≤ (f * g) 0 := f.map_ge_of_map_zero (g 0)

lemma floor_mul_map_zero_le : ⌊(f * g) 0⌋ ≤ ⌊f 0⌋ + ⌈g 0⌉ :=
calc ⌊(f * g) 0⌋ ≤ ⌊f 0 + ⌈g 0⌉⌋ : floor_mono $ f.mul_map_zero_le g
             ... = ⌊f 0⌋ + ⌈g 0⌉ : floor_add_int _ _

lemma floor_mul_map_zero_ge : ⌊f 0⌋ + ⌊g 0⌋ ≤ ⌊(f * g) 0⌋ :=
calc ⌊f 0⌋ + ⌊g 0⌋ = ⌊f 0 + ⌊g 0⌋⌋ : (floor_add_int _ _).symm
               ... ≤ ⌊(f * g) 0⌋ : floor_mono $ f.mul_map_zero_ge g

lemma floor_map_zero_coboundary_mem_Icc : ⌊(f * g) 0⌋ - ⌊g 0⌋ - ⌊f 0⌋ ∈ set.Icc (0 : ℤ) 1 :=
⟨by linarith only [f.floor_mul_map_zero_ge g],
  by linarith only [f.floor_mul_map_zero_le g, ceil_le_floor_add_one (g 0)]⟩

lemma floor_map_zero_coboundary_mem_Icc_real :
  (⌊(f * g) 0⌋ - ⌊g 0⌋ - ⌊f 0⌋ : ℝ) ∈ set.Icc (0 : ℝ) 1 :=
and.intro
  (by simpa only [int.cast_sub]
    using (@int.cast_le ℝ _ _ _).2 (f.floor_map_zero_coboundary_mem_Icc g).1)
  (by simpa only [int.cast_sub]
    using (@int.cast_le ℝ _ _ _).2 (f.floor_map_zero_coboundary_mem_Icc g).2)

noncomputable theory

def quasi_hom_eval_zero : quasi_mul_add_hom circle_deg1_lift ℝ :=
quasi_mul_add_hom.mk' (λ f, f 0) 1 $ λ f g,
begin
  rw [dist_eq_norm, real.norm_eq_abs, abs_le],
  split,
  { rw [le_sub_iff_add_le', add_assoc],
    apply le_trans _ (f.mul_map_zero_ge g),
    exact add_le_add_left (le_of_lt $ sub_one_lt_floor _) _ },
  { rw [sub_le_iff_le_add', add_assoc],
    apply le_trans (f.mul_map_zero_le g),
    exact add_le_add_left (le_of_lt $ ceil_lt_add_one _) _ }
end

def quasi_hom_aux : quasi_mul_add_hom circle_deg1_lift ℝ :=
begin
  refine ⟨λ f, ⌊f 0⌋ + (1 / 2), 1 / 2, assume f g, _⟩,
  rw [dist_eq_norm],
  convert_to ∥(⌊(f * g) 0⌋ : ℝ) - ⌊g 0⌋ - ⌊f 0⌋ - 1 / 2∥ ≤ 1 / 2,
  { apply congr_arg, ring },
  { refine abs_le.2 ⟨_, _⟩,
    { linarith [(f.floor_map_zero_coboundary_mem_Icc_real g).1] },
    { linarith [(f.floor_map_zero_coboundary_mem_Icc_real g).2] } }
end

def translation_number : ℝ := floor_map_zero_add_one_half.approx f

lemma translation_number_eq_of_semiconj {f g₁ g₂ : circle_deg1_lift} (H : semiconj_by f g₁ g₂) :
  g₁.translation_number = g₂.translation_number :=
floor_map_zero_add_one_half.approx_eq_of_semiconj H

lemma translation_number_map_id : translation_number 1 = 0 := floor_map_zero_add_one_half.approx_one

lemma translation_number_map_mul_of_commute {f g : circle_deg1_lift} (h : commute f g) :
  (f * g).translation_number = f.translation_number + g.translation_number :=
floor_map_zero_add_one_half.approx_mul_of_commute h

lemma translation_number_conj_eq (f : units circle_deg1_lift) (g : circle_deg1_lift) :
  (↑f * g * ↑(f⁻¹)).translation_number = g.translation_number :=
(translation_number_eq_of_semiconj (semiconj_by.units_conj_mk _ _)).symm

lemma tendsto_translation_number

end circle_deg1_lift
