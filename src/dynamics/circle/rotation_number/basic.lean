import category_theory.endomorphism category_theory.types analysis.normed_space.quasi_hom
  tactic.monotonicity tactic.find tactic.fin_cases

@[simp] lemma nat.cast_add_one_ne_zero {α : Type*} [linear_ordered_semiring α] (n : ℕ) :
  (n + 1 : α) ≠ 0 :=
ne_of_gt n.cast_add_one_pos

lemma monotone.mul_const {α : Type*} [linear_ordered_semiring α] {β : Type*} [preorder β]
  {f : β → α} (hf : monotone f) {c : α} (hc : 0 < c) :
  monotone (λ x, (f x) * c) :=
λ x y hxy, (mul_le_mul_right hc).2 (hf hxy)

lemma monotone.const_mul {α : Type*} [linear_ordered_semiring α] {β : Type*} [preorder β]
  {f : β → α} (hf : monotone f) {c : α} (hc : 0 < c) :
  monotone (λ x, c * (f x)) :=
λ x y hxy, (mul_le_mul_left hc).2 (hf hxy)

lemma monotone.div_const {α : Type*} [linear_ordered_field α] {β : Type*} [preorder β]
  {f : β → α} (hf : monotone f) {c : α} (hc : 0 < c) :
  monotone (λ x, (f x) / c) :=
hf.mul_const (inv_pos.2 hc)

open_locale smul

lemma continuous.iterate {α : Type*} [topological_space α] {f : α → α} (h : continuous f) :
  ∀ n, continuous (f^[n])
| 0 := continuous_id
| (n + 1) := (continuous.iterate n).comp h

def to_mul {α : Type*} (x : α) : multiplicative α := x
def of_mul {α : Type*} (x : multiplicative α) : α := x

attribute [irreducible] multiplicative

@[simp] lemma to_mul_gsmul {A : Type*} [add_group A] (m : ℤ) (x : A) :
  to_mul (m •ℤ x) = (to_mul x)^m := rfl

@[simp] lemma of_mul_gpow {A : Type*} [add_group A] (x : multiplicative A) (m : ℤ) :
  of_mul (x^m) = m •ℤ of_mul x := rfl

open category_theory (End) filter set
open_locale topological_space classical


/-- A lift of a monotone degree one map `S¹ → S¹`. -/
structure circle_deg1_lift : Type :=
(to_fun : End ℝ)
(mono' : monotone to_fun)
(map_add_one' : ∀ x, to_fun (x + 1) = to_fun x + 1)

instance : has_coe_to_fun circle_deg1_lift := ⟨λ _, End ℝ, circle_deg1_lift.to_fun⟩

namespace circle_deg1_lift

variables (f g : circle_deg1_lift)

lemma mono  : monotone f := f.mono'

lemma map_add_one : ∀ x, f (x + 1) = f x + 1 := f.map_add_one'

lemma map_one_add (x) : f (1 + x) = 1 + f x := by simpa only [add_comm] using f.map_add_one x

theorem coe_inj : ∀ ⦃f g : circle_deg1_lift ⦄, (f : End ℝ) = g → f = g :=
assume ⟨f, fm, fd⟩ ⟨g, gm, gd⟩ h, by congr; exact h

@[ext] theorem ext ⦃f g : circle_deg1_lift ⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj $ funext h

theorem ext_iff {f g : circle_deg1_lift} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

instance : has_mul circle_deg1_lift :=
⟨λ f g,
  { to_fun := f * g,
    mono' := f.mono.comp g.mono,
    map_add_one' := λ x, by simp [map_add_one] }⟩

@[simp] lemma mul_apply (f g : circle_deg1_lift) (x) : (f * g) x = f (g x) := rfl

instance : has_one circle_deg1_lift := ⟨⟨1, monotone_id, λ _, rfl⟩⟩

@[simp] lemma one_apply (x) : (1 : circle_deg1_lift) x = x := rfl

instance : monoid circle_deg1_lift :=
{ mul := (*),
  one := 1,
  mul_one := λ f, coe_inj $ mul_one f.to_fun,
  one_mul := λ f, coe_inj $ one_mul f.to_fun,
  mul_assoc := λ f₁ f₂ f₃, coe_inj $ mul_assoc f₁.to_fun f₂.to_fun f₃.to_fun }

@[simp, squash_cast] lemma units_coe_coe (f : units circle_deg1_lift) :
  ((f : circle_deg1_lift) : End ℝ) = f := rfl

lemma coe_pow : ∀ n : ℕ, ⇑(f^n) = (f^[n])
| 0 := rfl
| (n+1) := by {ext x, rw [pow_succ', mul_apply, coe_pow n, nat.iterate_succ] }

def translate : multiplicative ℝ →* units circle_deg1_lift :=
by refine (units.map _).comp (to_units $ multiplicative ℝ).to_monoid_hom; exact
{ to_fun := λ x, ⟨λ y, (of_mul x) + y, λ y₁ y₂ h, add_le_add_left h _, λ y, (add_assoc _ _ _).symm⟩,
  map_one' := ext $ zero_add,
  map_mul' := λ x y, ext $ λ z, add_assoc _ _ _ }

@[simp] lemma translate_apply (x y : ℝ) : translate (to_mul x) y = x + y := rfl

@[simp] lemma translate_inv_apply (x y : ℝ) : (translate $ to_mul x)⁻¹ y = -x + y := rfl

lemma commute_translate_one : commute f (translate $ to_mul 1) :=
ext f.map_one_add

lemma commute_translate_int (m : ℤ) : commute f (translate $ to_mul m) :=
by { rw [← gsmul_one, to_mul_gsmul, translate.map_gpow],
  exact f.commute_translate_one.units_gpow_right _ }

lemma map_int_add (m : ℤ) (x : ℝ) : f (m + x) = m + f x :=
ext_iff.1 (f.commute_translate_int m) x

lemma map_add_int (x : ℝ) (m : ℤ) : f (x + m) = f x + m :=
by simpa only [add_comm] using f.map_int_add m x

lemma map_sub_int (x : ℝ) (n : ℤ) : f (x - n) = f x - n :=
by simpa using f.map_add_int x (-n)

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
begin
  rcases floor_map_zero_coboundary_mem_Icc f g with ⟨hl, hr⟩,
  split; assumption_mod_cast
end

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

@[simp] lemma quasi_hom_eval_zero_apply : quasi_hom_eval_zero f = f 0 := rfl

def conj_translate (x : ℝ) : circle_deg1_lift →* circle_deg1_lift :=
{ to_fun := λ f, ↑((translate x)⁻¹) * f * translate x,
  map_one' := by rw [mul_one, units.inv_mul],
  map_mul' := λ f g, by simp only [mul_assoc, units.mul_inv_cancel_left] }

@[simp] lemma conj_translate_apply (x y : ℝ) : conj_translate x f y = f (x + y) - x :=
neg_add_eq_sub _ _

lemma quasi_hom_eval_zero_conj_translate (x : ℝ) :
  quasi_hom_eval_zero (conj_translate x f) = f x - x :=
by simp

def quasi_hom_aux : quasi_mul_add_hom circle_deg1_lift ℝ :=
quasi_mul_add_hom.mk' (λ f, ⌊f 0⌋ + (1 / 2)) (1 / 2) $ λ f g,
begin
  rw [← add_assoc, dist_add_right, add_right_comm, dist_eq_norm, ← sub_sub, ← dist_eq_norm,
    ← metric.mem_closed_ball, closed_ball_Icc, sub_add_eq_sub_sub_swap, sub_self, add_halves],
  exact f.floor_map_zero_coboundary_mem_Icc_real g
end

@[simp] lemma quasi_hom_aux_apply : quasi_hom_aux f = ⌊f 0⌋ + (1 / 2) := rfl

lemma norm_cbd_quasi_hom_aux_le : quasi_hom_aux.norm_cbd ≤ 1 / 2 :=
quasi_mul_add_hom.norm_cbd_mk'_le _ _ _

lemma dist_quasi_hom_eval_zero_aux_le :
  dist (quasi_hom_eval_zero f) (quasi_hom_aux f) ≤ 1/2 :=
by simp [dist_eq_norm, real.norm_eq_abs, abs_le, floor_le, ← sub_sub,
  -one_div_eq_inv, sub_le_iff_le_add, add_comm (1:ℝ), le_of_lt (lt_floor_add_one _)]

def translation_number : ℝ := quasi_hom_aux.approx f

lemma translation_number_eq_quasi_hom_eval_zero_approx :
  f.translation_number = quasi_hom_eval_zero.approx f :=
(quasi_mul_add_hom.approx_eq_of_dist_le dist_quasi_hom_eval_zero_aux_le f).symm

lemma translation_number_eq_of_semiconj {f g₁ g₂ : circle_deg1_lift} (H : semiconj_by f g₁ g₂) :
  g₁.translation_number = g₂.translation_number :=
quasi_hom_aux.approx_eq_of_semiconj H

lemma translation_number_map_id : translation_number 1 = 0 := quasi_hom_aux.approx_one

lemma translation_number_map_mul_of_commute {f g : circle_deg1_lift} (h : commute f g) :
  (f * g).translation_number = f.translation_number + g.translation_number :=
quasi_hom_aux.approx_mul_of_commute h

lemma translation_number_conj_eq (f : units circle_deg1_lift) (g : circle_deg1_lift) :
  (↑f * g * ↑(f⁻¹)).translation_number = g.translation_number :=
(translation_number_eq_of_semiconj (semiconj_by.units_conj_mk _ _)).symm

lemma translation_number_conj_eq' (f : units circle_deg1_lift) (g : circle_deg1_lift) :
  (↑(f⁻¹) * g * f).translation_number = g.translation_number :=
by simpa only [inv_inv] using translation_number_conj_eq f⁻¹ g

lemma translation_number_pow (n : ℕ) :
  (f^n).translation_number = n * f.translation_number :=
quasi_hom_aux.approx_pow f n

lemma tendsto_translation_number (x : ℝ) :
  tendsto (λ n:ℕ, ((f^n) x - x) / n) at_top (𝓝 f.translation_number) :=
begin
  rw [← translation_number_conj_eq' (translate x),
    translation_number_eq_quasi_hom_eval_zero_approx],
  simp only [← quasi_hom_eval_zero_conj_translate, div_eq_inv_mul, ← smul_eq_mul,
    (conj_translate _).map_pow],
  apply quasi_hom_eval_zero.tendsto_approx
end

lemma tendsto_translation_number' (x : ℝ) :
  tendsto (λ n:ℕ, ((f^(n+1)) x - x) / (n+1)) at_top (𝓝 f.translation_number) :=
(tendsto_add_at_top_iff_nat 1).2 (f.tendsto_translation_number x)

lemma map_pow_eq_of_map_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x + m) :
  ∀ n : ℕ, (f^n) x = x + n * m
| 0 := by rw [pow_zero, one_apply, nat.cast_zero, zero_mul, add_zero]
| (n+1) := by rw [pow_succ', mul_apply, h, map_add_int, map_pow_eq_of_map_eq_add_int,
  nat.cast_add_one, add_mul, add_assoc, one_mul]

lemma translation_number_of_map_eq_add_int {x : ℝ} {m : ℤ}
  (h : f x = x + m) :
  f.translation_number = m :=
begin
  apply tendsto_nhds_unique at_top_ne_bot (f.tendsto_translation_number' x),
  simp [f.map_pow_eq_of_map_eq_add_int h, mul_div_cancel_left, tendsto_const_nhds]
end

lemma translation_number_of_map_pow_eq_add_int {x : ℝ} {n : ℕ} {m : ℤ}
  (h : (f^n) x = x + m) (hn : 0 < n) :
  f.translation_number = m / n :=
begin
  have := (f^n).translation_number_of_map_eq_add_int h,
  rwa [translation_number_pow, mul_comm, ← eq_div_iff] at this,
  exact nat.cast_ne_zero.2 (ne_of_gt hn)
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

-- TODO: why does `simp` fail to simplify inside `coe_fn`?
lemma map_pow_sub_le_mul_of_forall_map_sub_le {z : ℝ}
  (hz : ∀ x, f x - x ≤ z) : ∀ (n : ℕ) (x : ℝ), (f^n) x - x ≤ n * z
| 0 x := by { rw [pow_zero], simp }
| (n+1) x :=
  calc (f^(n+1)) x - x = ((f^n) (f x) - f x) + (f x - x) :
    by rw [sub_add_sub_cancel, pow_succ', mul_apply]
  ... ≤ n * z + z : add_le_add (map_pow_sub_le_mul_of_forall_map_sub_le n (f x)) (hz x)
  ... = (n + 1) * z : by rw [add_mul, one_mul]

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
