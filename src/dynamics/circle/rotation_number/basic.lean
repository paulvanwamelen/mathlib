import tactic.monotonicity
import tactic.find
import tactic.fin_cases
import analysis.specific_limits

/-!
### TODO: move
These definitions and lemmas should be moved to other files
-/

-- TODO: move to a new `algebra.conj`
def {u} units.conj_hom (M : Type u) [monoid M] : units M →* mul_aut M :=
{ to_fun := λ u,
  { to_fun := λ x, ↑u * x * ↑(u⁻¹),
    inv_fun := λ x, ↑(u⁻¹) * x * u,
    left_inv := λ x, by simp  [mul_assoc],
    right_inv := λ x, by simp [mul_assoc],
    map_mul' := λ x y, by simp [mul_assoc] },
  map_one' := by { ext, simp },
  map_mul' := λ u₁ u₂, by { ext x, simp [mul_assoc] } }

-- TODO: add `mul_equiv.map_pow` to `group_power`
-- TODO: move to `group_power`
@[simp] lemma units.conj_pow {M : Type*} [monoid M] (u : units M) (x : M) (n : ℕ) :
  (u * x * ↑(u⁻¹) : M)^n = u * x^n * ↑(u⁻¹) :=
((units.conj_hom M u).to_monoid_hom.map_pow x n).symm

-- TODO: move to `group_power`
@[simp] lemma units.conj_pow' {M : Type*} [monoid M] (u : units M) (x : M) (n : ℕ) :
  (↑(u⁻¹) * x * u : M)^n = ↑(u⁻¹) * x^n * u :=
(u⁻¹).conj_pow x n

open category_theory (End) filter set
open_locale topological_space classical

/-!
### Definition and monoid structure
-/

/-- A lift of a monotone degree one map `S¹ → S¹`. -/
structure circle_deg1_lift : Type :=
(to_fun : ℝ → ℝ)
(monotone' : monotone to_fun)
(map_add_one' : ∀ x, to_fun (x + 1) = to_fun x + 1)

instance : has_coe_to_fun circle_deg1_lift := ⟨λ _, ℝ → ℝ, circle_deg1_lift.to_fun⟩

namespace circle_deg1_lift

variables (f g : circle_deg1_lift)

protected lemma monotone  : monotone f := f.monotone'

@[simp] lemma map_add_one : ∀ x, f (x + 1) = f x + 1 := f.map_add_one'

@[simp] lemma map_one_add (x : ℝ) : f (1 + x) = 1 + f x := by rw [add_comm, map_add_one, add_comm]

theorem coe_inj : ∀ ⦃f g : circle_deg1_lift ⦄, (f : ℝ → ℝ) = g → f = g :=
assume ⟨f, fm, fd⟩ ⟨g, gm, gd⟩ h, by congr; exact h

@[ext] theorem ext ⦃f g : circle_deg1_lift ⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj $ funext h

theorem ext_iff {f g : circle_deg1_lift} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

instance : monoid circle_deg1_lift :=
{ mul := λ f g,
  { to_fun := f ∘ g,
    monotone' := f.monotone.comp g.monotone,
    map_add_one' := λ x, by simp [map_add_one] },
  one := ⟨id, monotone_id, λ _, rfl⟩,
  mul_one := λ f, coe_inj $ function.comp.right_id f,
  one_mul := λ f, coe_inj $ function.comp.left_id f,
  mul_assoc := λ f₁ f₂ f₃, coe_inj rfl }

@[simp] lemma coe_mul : ⇑(f * g) = f ∘ g := rfl

@[simp] lemma coe_one : ⇑(1 : circle_deg1_lift) = id := rfl

def translate : multiplicative ℝ →* units circle_deg1_lift :=
by refine (units.map _).comp (to_units $ multiplicative ℝ).to_monoid_hom; exact
{ to_fun := λ x, ⟨λ y, x.to_add + y, λ y₁ y₂ h, add_le_add_left h _, λ y, (add_assoc _ _ _).symm⟩,
  map_one' := ext $ zero_add,
  map_mul' := λ x y, ext $ λ z, add_assoc _ _ _ }

@[simp] lemma translate_apply (x y : ℝ) : translate (multiplicative.of_add x) y = x + y := rfl

@[simp]
lemma translate_inv_apply (x y : ℝ) : (translate $ multiplicative.of_add x)⁻¹ y = -x + y := rfl

lemma commute_translate_one : commute f (translate $ multiplicative.of_add 1) :=
ext f.map_one_add

lemma commute_translate_int (m : ℤ) : commute f (translate $ multiplicative.of_add m) :=
by { rw [← gsmul_one, of_add_gsmul, translate.map_gpow],
  exact f.commute_translate_one.units_gpow_right _ }

@[simp] lemma map_int_add (m : ℤ) (x : ℝ) : f (m + x) = m + f x :=
ext_iff.1 (f.commute_translate_int m) x

@[simp] lemma map_add_int (x : ℝ) (m : ℤ) : f (x + m) = f x + m :=
by simpa only [add_comm] using f.map_int_add m x

@[simp] lemma map_sub_int (x : ℝ) (n : ℤ) : f (x - n) = f x - n :=
by simpa only [int.cast_neg] using f.map_add_int x (-n)

@[simp] lemma map_add_nat (x : ℝ) (n : ℕ) : f (x + n) = f x + n :=
f.map_add_int x n

@[simp] lemma map_nat_add (n : ℕ) (x : ℝ) : f (n + x) = n + f x :=
f.map_int_add n x

@[simp] lemma map_sub_nat (x : ℝ) (n : ℕ) : f (x - n) = f x - n :=
f.map_sub_int x n

instance units_coe_fn : has_coe_to_fun (units circle_deg1_lift) :=
⟨λ _, ℝ → ℝ, λ u, u⟩

@[simp, norm_cast] lemma units_coe_coe (f : units circle_deg1_lift) :
  ((f : circle_deg1_lift) : End ℝ) = f := rfl

lemma coe_pow : ∀ n : ℕ, ⇑(f^n) = (f^[n])
| 0 := rfl
| (n+1) := by {ext x, simp [coe_pow n, pow_succ'] }

lemma map_int_of_map_zero (n : ℤ) : f n = f 0 + n :=
by rw [← f.map_add_int, zero_add]

lemma map_le_of_map_zero (x : ℝ) : f x ≤ f 0 + ⌈x⌉ :=
calc f x ≤ f ⌈x⌉     : f.monotone $ le_ceil _
     ... = f 0 + ⌈x⌉ : f.map_int_of_map_zero _

lemma map_ge_of_map_zero (x : ℝ) : f 0 + ⌊x⌋ ≤ f x :=
calc f 0 + ⌊x⌋ = f ⌊x⌋ : (f.map_int_of_map_zero _).symm
           ... ≤ f x   : f.monotone $ floor_le _

lemma mul_map_zero_le : (f * g) 0 ≤ f 0 + ⌈g 0⌉ := f.map_le_of_map_zero (g 0)

lemma mul_map_zero_lt : (f * g) 0 < f 0 + g 0 + 1 :=
calc (f * g) 0 ≤ f 0 + ⌈g 0⌉ : f.mul_map_zero_le  g
... < f 0 + (g 0 + 1) :  add_lt_add_left (ceil_lt_add_one _) _
... = f 0 + g 0 + 1 : (add_assoc _ _ _).symm

lemma le_mul_map_zero : f 0 + ⌊g 0⌋ ≤ (f * g) 0 := f.map_ge_of_map_zero (g 0)

lemma lt_mul_map_zero : f 0 + g 0 - 1 < (f * g) 0 :=
calc f 0 + g 0 - 1 = f 0 + (g 0 - 1) : add_assoc _ _ _
               ... < f 0 + ⌊g 0⌋ : add_lt_add_left (sub_one_lt_floor _) _
               ... ≤ (f * g) 0 : f.le_mul_map_zero g

lemma dist_mul_map_zero_lt : dist (f 0 + g 0) ((f * g) 0) < 1 :=
begin
  rw [dist_comm, real.dist_eq, abs_lt, lt_sub_iff_add_lt', sub_lt_iff_lt_add'],
  exact ⟨f.lt_mul_map_zero g, f.mul_map_zero_lt g⟩
end

lemma floor_mul_map_zero_le : ⌊(f * g) 0⌋ ≤ ⌊f 0⌋ + ⌈g 0⌉ :=
calc ⌊(f * g) 0⌋ ≤ ⌊f 0 + ⌈g 0⌉⌋ : floor_mono $ f.mul_map_zero_le g
             ... = ⌊f 0⌋ + ⌈g 0⌉ : floor_add_int _ _

lemma le_floor_mul_map_zero : ⌊f 0⌋ + ⌊g 0⌋ ≤ ⌊(f * g) 0⌋ :=
calc ⌊f 0⌋ + ⌊g 0⌋ = ⌊f 0 + ⌊g 0⌋⌋ : (floor_add_int _ _).symm
               ... ≤ ⌊(f * g) 0⌋   : floor_mono $ f.le_mul_map_zero g

lemma ceil_mul_map_zero_le : ⌈(f * g) 0⌉ ≤ ⌈f 0⌉ + ⌈g 0⌉ :=
calc ⌈(f * g) 0⌉ ≤ ⌈f 0 + ⌈g 0⌉⌉ : ceil_mono $ f.mul_map_zero_le g
             ... = ⌈f 0⌉ + ⌈g 0⌉ : ceil_add_int _ _

lemma le_ceil_mul_map_zero : ⌈f 0⌉ + ⌊g 0⌋ ≤ ⌈(f * g) 0⌉ :=
calc ⌈f 0⌉ + ⌊g 0⌋ = ⌈f 0 + ⌊g 0⌋⌉ : (ceil_add_int _ _).symm
               ... ≤ ⌈(f * g) 0⌉   : ceil_mono $ f.le_mul_map_zero g

lemma dist_sqr_map_zero_lt : dist (2 * f 0) ((f^2) 0) < 1 :=
by simp only [pow_two, two_mul, f.dist_mul_map_zero_lt f]

lemma dist_map_zero_lt_of_semiconj {f g₁ g₂ : circle_deg1_lift} (h : semiconj_by f g₁ g₂) :
  dist (g₁ 0) (g₂ 0) < 2 :=
calc dist (g₁ 0) (g₂ 0) ≤ dist (g₁ 0) ((f * g₁) 0 - f 0) + dist _ (g₂ 0) : dist_triangle _ _ _
... = dist (f 0 + g₁ 0) ((f * g₁) 0) + dist (g₂ 0 + f 0) ((g₂ * f) 0) :
  by simp only [h.eq, real.dist_eq, sub_sub, add_comm (f 0), sub_sub_assoc_swap,
    abs_sub ((g₂ * f) 0)]
... < _ : add_lt_add (f.dist_mul_map_zero_lt g₁) (g₂.dist_mul_map_zero_lt f)

noncomputable theory

def rotnum_aux_seq (n : ℕ) : ℝ := (f^(2^n)) 0 / 2^n

lemma rotnum_aux_seq_def : f.rotnum_aux_seq = λ n : ℕ, (f^(2^n)) 0 / 2^n := rfl

lemma rotnum_aux_seq_zero : f.rotnum_aux_seq 0 = f 0 := by simp [rotnum_aux_seq]

lemma rotnum_aux_seq_dist_lt (n : ℕ) :
  dist (f.rotnum_aux_seq n) (f.rotnum_aux_seq (n+1)) < (1 / 2) / (2^n) :=
begin
  have : 0 < (2^(n+1):ℝ) := pow_pos zero_lt_two _,
  rw [div_div_eq_div_mul, ← pow_succ, ← abs_of_pos this],
  replace := abs_pos_iff.2 (ne_of_gt this),
  convert (div_lt_div_right this).2 (f^(2^n)).dist_sqr_map_zero_lt,
  simp_rw [rotnum_aux_seq, real.dist_eq],
  rw [← abs_div, sub_div, ← pow_mul, ← nat.pow_succ, pow_succ,
    mul_div_mul_left _ _ (@two_ne_zero ℝ _)]
end

def translation_number : ℝ :=
lim ((at_top : filter ℕ).map f.rotnum_aux_seq)

lemma tendsto_translation_number_aux :
  tendsto f.rotnum_aux_seq at_top (𝓝 f.translation_number) :=
le_nhds_lim_of_cauchy $ cauchy_seq_of_le_geometric_two 1
  (λ n, le_of_lt $ f.rotnum_aux_seq_dist_lt n)

lemma dist_map_zero_translation_number_le :
  dist (f 0) f.translation_number ≤ 1 :=
f.rotnum_aux_seq_zero ▸ dist_le_of_le_geometric_two_of_tendsto₀ 1
  (λ n, le_of_lt $ f.rotnum_aux_seq_dist_lt n) f.tendsto_translation_number_aux

lemma tendsto_translation_number_of_dist_bounded_aux (x : ℕ → ℝ) (C : ℝ)
  (H : ∀ n : ℕ, dist ((f^n) 0) (x n) ≤ C) :
  tendsto (λ n : ℕ, x (2^n) / (2^n)) at_top (𝓝 f.translation_number) :=
begin
  refine f.tendsto_translation_number_aux.congr_dist (squeeze_zero (λ _, dist_nonneg) _ _),
  { exact λ n, C / 2^n },
  { intro n,
    have : 0 < (2^n:ℝ) := pow_pos zero_lt_two _,
    convert (div_le_div_right this).2 (H (2^n)),
    rw [rotnum_aux_seq, real.dist_eq, ← sub_div, abs_div, abs_of_pos this, real.dist_eq] },
  { exact mul_zero C ▸ tendsto_const_nhds.mul (tendsto_inv_at_top_zero.comp $
      tendsto_pow_at_top_at_top_of_gt_1 one_lt_two) }
end

lemma translation_number_eq_of_dist_bounded {f g : circle_deg1_lift} (C : ℝ)
  (H : ∀ n : ℕ, dist ((f^n) 0) ((g^n) 0) ≤ C) :
  f.translation_number = g.translation_number :=
eq.symm $ tendsto_nhds_unique at_top_ne_bot g.tendsto_translation_number_aux $
  f.tendsto_translation_number_of_dist_bounded_aux _ C H

@[simp] lemma translation_number_map_id : translation_number 1 = 0 :=
tendsto_nhds_unique at_top_ne_bot (tendsto_translation_number_aux 1) $
  by simp [rotnum_aux_seq_def, tendsto_const_nhds]

lemma translation_number_eq_of_semiconj {f g₁ g₂ : circle_deg1_lift} (H : semiconj_by f g₁ g₂) :
  g₁.translation_number = g₂.translation_number :=
translation_number_eq_of_dist_bounded 2 $ λ n, le_of_lt $
  dist_map_zero_lt_of_semiconj $ H.pow_right n

lemma translation_number_map_mul_of_commute {f g : circle_deg1_lift} (h : commute f g) :
  (f * g).translation_number = f.translation_number + g.translation_number :=
begin
  have : tendsto (λ n : ℕ, ((λ k, (f^k) 0 + (g^k) 0) (2^n)) / (2^n)) at_top
    (𝓝 $ f.translation_number + g.translation_number) :=
    ((f.tendsto_translation_number_aux.add g.tendsto_translation_number_aux).congr $
      λ n, (add_div ((f^(2^n)) 0) ((g^(2^n)) 0) ((2:ℝ)^n)).symm),
  refine tendsto_nhds_unique at_top_ne_bot
    ((f * g).tendsto_translation_number_of_dist_bounded_aux _ 1 (λ n, _))
    this,
  rw [h.mul_pow, dist_comm],
  exact le_of_lt ((f^n).dist_mul_map_zero_lt (g^n))
end

@[simp] lemma translation_number_pow :
  ∀ n : ℕ, (f^n).translation_number = n * f.translation_number
| 0 := by simp
| (n+1) := by rw [pow_succ', translation_number_map_mul_of_commute (commute.pow_self f n),
  translation_number_pow n, nat.cast_add_one, add_mul, one_mul]

lemma translation_number_conj_eq (f : units circle_deg1_lift) (g : circle_deg1_lift) :
  (↑f * g * ↑(f⁻¹)).translation_number = g.translation_number :=
(translation_number_eq_of_semiconj (semiconj_by.units_conj_mk _ _)).symm

lemma translation_number_conj_eq' (f : units circle_deg1_lift) (g : circle_deg1_lift) :
  (↑(f⁻¹) * g * f).translation_number = g.translation_number :=
translation_number_conj_eq f⁻¹ g

lemma dist_pow_map_zero_mul_translation_number_le (n:ℕ) :
  dist ((f^n) 0) (n * f.translation_number) ≤ 1 :=
f.translation_number_pow n ▸ (f^n).dist_map_zero_translation_number_le

lemma tendsto_translation_number₀' :
  tendsto (λ n:ℕ, (f^(n+1)) 0 / (n+1)) at_top (𝓝 f.translation_number) :=
begin
  refine (tendsto_iff_dist_tendsto_zero.2 $ squeeze_zero (λ _, dist_nonneg) (λ n, _)
    ((tendsto_const_div_at_top_nhds_0_nat 1).comp (tendsto_add_at_top_nat 1))),
  dsimp,
  have : (0:ℝ) < n + 1 := n.cast_add_one_pos,
  rw [real.dist_eq, div_sub' _ _ _ (ne_of_gt this), abs_div, ← real.dist_eq, abs_of_pos this,
    div_le_div_right this, ← nat.cast_add_one],
  apply dist_pow_map_zero_mul_translation_number_le
end

lemma tendsto_translation_number₀ :
  tendsto (λ n:ℕ, ((f^n) 0) / n) at_top (𝓝 f.translation_number) :=
(tendsto_add_at_top_iff_nat 1).1 f.tendsto_translation_number₀'

lemma tendsto_translation_number (x : ℝ) :
  tendsto (λ n:ℕ, ((f^n) x - x) / n) at_top (𝓝 f.translation_number) :=
begin
  rw [← translation_number_conj_eq' (translate $ multiplicative.of_add x)],
  convert tendsto_translation_number₀ _,
  ext1 n,
  simp [sub_eq_neg_add]
end

lemma tendsto_translation_number' (x : ℝ) :
  tendsto (λ n:ℕ, ((f^(n+1)) x - x) / (n+1)) at_top (𝓝 f.translation_number) :=
(tendsto_add_at_top_iff_nat 1).2 (f.tendsto_translation_number x)

lemma map_pow_eq_of_map_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x + m) (n : ℕ) :
  (f^n) x = x + n * m :=
begin
  induction n with n ihn, { simp },
  rw [pow_succ, coe_mul, function.comp_app, ihn, nat.cast_succ, add_mul, one_mul,
    ← int.cast_coe_nat, ← int.cast_mul, f.map_add_int, h, add_right_comm, add_assoc]
end

lemma translation_number_of_map_eq_add_int {x : ℝ} {m : ℤ}
  (h : f x = x + m) :
  f.translation_number = m :=
begin
  apply tendsto_nhds_unique at_top_ne_bot (f.tendsto_translation_number' x),
  simp [f.map_pow_eq_of_map_eq_add_int h, mul_div_cancel_left, tendsto_const_nhds,
    nat.cast_add_one_ne_zero]
end

lemma translation_number_of_map_pow_eq_add_int {x : ℝ} {n : ℕ} {m : ℤ}
  (h : (f^n) x = x + m) (hn : 0 < n) :
  f.translation_number = m / n :=
begin
  have := (f^n).translation_number_of_map_eq_add_int h,
  rwa [translation_number_pow, mul_comm, ← eq_div_iff] at this,
  exact nat.cast_ne_zero.2 (ne_of_gt hn)
end

lemma le_floor_pow_map_zero (n : ℕ) : ↑n * ⌊f 0⌋ ≤ ⌊(f^n) 0⌋ :=
begin
  induction n with n ihn, { simp },
  simp [pow_succ],
end

lemma map_pow_sub_le_mul_of_forall_map_sub_le {z : ℝ} (hz : ∀ x, f x - x ≤ z) (n : ℕ) (x : ℝ) :
  (f^n) x - x ≤ n * z :=
begin
  induction n generalizing x with n ihn, { simp },
end
-- | 0 x := by simp
-- | (n+1) x :=
  -- calc (f^(n+1)) x - x = ((f^n) (f x) - f x) + (f x - x) : by simp [pow_succ', sub_add_sub_cancel]
  -- ... ≤ n * z + z : add_le_add (map_pow_sub_le_mul_of_forall_map_sub_le n (f x)) (hz x)
  -- ... = (n + 1) * z : by rw [add_mul, one_mul]

lemma mul_le_map_pow_sub_of_forall_le_map_sub {z : ℝ}
  (hz : ∀ x, z ≤ f x - x) : ∀ (n : ℕ) (x : ℝ), ↑n * z ≤ (f^n) x - x
| 0 x := by { rw [pow_zero], simp }
| (n+1) x :=
  calc (↑n + 1) * z = n * z + z : by rw [add_mul, one_mul]
  ... ≤ ((f^n) (f x) - f x) + (f x - x) :
    add_le_add (mul_le_map_pow_sub_of_forall_le_map_sub n (f x)) (hz x)
  ... = (f^(n+1)) x - x : by rw [sub_add_sub_cancel, pow_succ', mul_apply]

lemma translation_number_le_of_forall_map_sub_le {z : ℝ}
  (hz : ∀ x, f x -x ≤ z) :
  f.translation_number ≤ z :=
begin
  refine (le_of_tendsto' at_top_ne_bot (f.tendsto_translation_number' 0) $ assume n, _),
  rw [div_le_iff', ← nat.cast_add_one],
  exacts [f.map_pow_sub_le_mul_of_forall_map_sub_le hz _ _, n.cast_add_one_pos]
end

lemma le_translation_number_of_forall_le_map_sub {z : ℝ}
  (hz : ∀ x, z ≤ f x - x) :
  z ≤ f.translation_number :=
begin
  refine (ge_of_tendsto' at_top_ne_bot (f.tendsto_translation_number' 0) $ assume n, _),
  rw [le_div_iff', ← nat.cast_add_one],
  exacts [f.mul_le_map_pow_sub_of_forall_le_map_sub hz _ _, n.cast_add_one_pos]
end

lemma translation_number_mem_Icc₀ :
  f.translation_number ∈ set.Icc (⌊f 0⌋ : ℝ) (⌊f 0⌋ + 1) :=
begin
  have := le_trans (quasi_hom_aux.dist_approx_le f) norm_cbd_quasi_hom_aux_le,
  rw [dist_comm, ← metric.mem_closed_ball, closed_ball_Icc] at this,
  simpa [-one_div_eq_inv, add_halves, translation_number] using this
end

lemma translation_number_mem_Icc (x : ℝ) :
  f.translation_number ∈ set.Icc (⌊f x - x⌋ : ℝ) (⌊f x - x⌋ + 1) :=
begin
  rw [← translation_number_conj_eq' (translate x), ← quasi_hom_eval_zero_conj_translate,
    quasi_hom_eval_zero_apply],
  apply translation_number_mem_Icc₀
end

lemma translation_number_mem_Icc_of_pow (n : ℕ) (hn : 0 < n) (x : ℝ) :
  f.translation_number ∈ Icc ((⌊(f^n) x - x⌋ : ℝ) / n) ((⌊(f^n) x - x⌋ + 1) / n) :=
begin
  have : 0 < (n:ℝ), from nat.cast_pos.2 hn,
  rw [mem_Icc, div_le_iff this, le_div_iff this, mul_comm, ← translation_number_pow, ← mem_Icc],
  exact translation_number_mem_Icc (f^n) x
end

lemma translation_number_mem_Icc_of_pow₀ (n : ℕ) (hn : 0 < n) :
  f.translation_number ∈ Icc ((⌊(f^n) 0⌋ : ℝ) / n) ((⌊(f^n) 0⌋ + 1) / n) :=
by simpa using f.translation_number_mem_Icc_of_pow n hn 0

lemma map_sub_lt_of_translation_number_lt {m : ℤ}
  (h : f.translation_number < m) (x : ℝ) : f x - x < m :=
floor_lt.1 (int.cast_lt.1 $ lt_of_le_of_lt (f.translation_number_mem_Icc x).1 h)

lemma lt_map_sub_of_lt_translation_number {m : ℤ}
  (h : ↑m < f.translation_number) (x : ℝ) : ↑m < f x - x :=
begin
  have := lt_of_lt_of_le h (f.translation_number_mem_Icc x).2,
  norm_cast at this,
  refine lt_of_le_of_ne (le_floor.1 $ int.le_of_lt_add_one this) (λ H, _),
  replace H : f x = x + m, by rwa [← sub_eq_iff_eq_add', eq_comm],
  replace H := f.translation_number_of_map_eq_add_int H,
  exact ne_of_gt h H
end

lemma map_mem_Ioo_of_translation_number {m : ℤ}
  (h : f.translation_number ∈ Ioo (m:ℝ) (m + 1)) (x) :
  f x - x ∈ Ioo (m:ℝ) (m + 1) :=
⟨f.lt_map_sub_of_lt_translation_number h.1 x,
  by { cases h, norm_cast at *, apply f.map_sub_lt_of_translation_number_lt, assumption } ⟩

lemma map_fract_sub_fract_eq (x : ℝ) :
  f (fract x) - fract x = f x - x:=
by conv_rhs { rw [← fract_add_floor x, f.map_add_int, add_sub_comm, sub_self, add_zero] }

lemma forall_map_sub_of_Icc (P : ℝ → Prop)
  (h : ∀ x ∈ Icc (0:ℝ) 1, P (f x - x)) (x : ℝ) : P (f x - x) :=
f.map_fract_sub_fract_eq x ▸ h _ ⟨fract_nonneg _, le_of_lt (fract_lt_one _)⟩

lemma translation_number_lt_of_forall_map_sub_lt (hf : continuous f) {z : ℝ}
  (hz : ∀ x, f x - x < z) : f.translation_number < z :=
begin
  obtain ⟨x, xmem, hx⟩ : ∃ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, f y - y ≤ f x - x,
    from compact_Icc.exists_forall_ge (nonempty_Icc.2 zero_le_one)
      (hf.sub continuous_id).continuous_on,
  replace hx := f.forall_map_sub_of_Icc (λ a, a ≤ f x - x) hx,
  replace hx := f.translation_number_le_of_forall_map_sub_le hx,
  exact lt_of_le_of_lt hx (hz x)
end

lemma lt_translation_number_of_forall_lt_map_sub (hf : continuous f) {z : ℝ}
  (hz : ∀ x, z < f x - x) : z < f.translation_number :=
begin
  obtain ⟨x, xmem, hx⟩ : ∃ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, f x - x ≤ f y - y,
    from compact_Icc.exists_forall_le (nonempty_Icc.2 zero_le_one)
      (hf.sub continuous_id).continuous_on,
  replace hx := f.forall_map_sub_of_Icc _ hx,
  replace hx := f.le_translation_number_of_forall_le_map_sub hx,
  exact lt_of_lt_of_le (hz x) hx,
end

lemma exists_sub_eq_translation_number (hf : continuous f) :
  ∃ x, f x - x = f.translation_number :=
begin
  obtain ⟨a, ha⟩ : ∃ x, f x - x ≤ f.translation_number,
  { by_contradiction H,
    push_neg at H,
    exact lt_irrefl _ (f.lt_translation_number_of_forall_lt_map_sub hf H) },
  obtain ⟨b, hb⟩ : ∃ x, f.translation_number ≤ f x - x,
  { by_contradiction H,
    push_neg at H,
    exact lt_irrefl _ (f.translation_number_lt_of_forall_map_sub_lt hf H) },
  exact intermediate_value_univ a b (hf.sub continuous_id) ⟨ha, hb⟩
end

lemma translation_number_eq_int_iff (hf : continuous f) {m : ℤ} :
  f.translation_number = m ↔ ∃ x, f x - x = m :=
begin
  refine ⟨λ h, h ▸ f.exists_sub_eq_translation_number hf, _⟩,
  rintros ⟨x, hx⟩,
  exact f.translation_number_of_map_eq_add_int (sub_eq_iff_eq_add'.1 hx)
end

lemma continuous_pow (hf : continuous f) (n : ℕ) :
  continuous ⇑(f^n : circle_deg1_lift) :=
by { rw coe_pow, exact hf.iterate n }

lemma translation_number_eq_rat_iff (hf : continuous f) {m : ℤ}
  {n : ℕ} (hn : 0 < n) :
  f.translation_number = m / n ↔ ∃ x, (f^n) x - x = m :=
begin
  rw [eq_div_iff, mul_comm, ← translation_number_pow]; [skip, exact ne_of_gt (nat.cast_pos.2 hn)],
  exact (f^n).translation_number_eq_int_iff (f.continuous_pow hf n)
end

end circle_deg1_lift

namespace circle_deg1_lift

variables {G : Type*} [group G] (f g : G →* circle_deg1_lift)
  (H : ∀ x, (f x).translation_number = (g x).translation_number)

def semiconj_translation : circle_deg1_lift :=
begin
  use λ x, Sup ((λ N : ℕ × ℕ, ↑N.1 * f.translation_number - N.2) '' {N | (f^N.1) 0 - N.2 ≤ x}),
  
end

def semiconj_translation_of_irrational (f : circle_deg1_lift) (hf : continuous f)
  (hrot : irrational f.translation_number) :
  { g : circle_deg1_lift // semiconj_by g f (translate f.translation_number) } :=
begin
  refine ⟨⟨λ x, ⨆ n:ℕ, (f^n)
end

end circle_deg1_lift
