import algebra.commute analysis.normed_space.basic analysis.specific_limits
  topology.metric_space.contracting

@[move_cast] lemma nnreal.coe_bit0 {r : nnreal} : ((bit0 r:nnreal):ℝ) = bit0 r := rfl
@[move_cast] lemma nnreal.coe_bit1 {r : nnreal} : ((bit1 r:nnreal):ℝ) = bit1 r := rfl

instance nonempty_monoid {M : Type*} [monoid M] : nonempty M := ⟨1⟩

open set filter
open_locale classical topological_space

lemma real.mul_csupr {ι : Type*} [nonempty ι] {f : ι → ℝ} (h : bdd_above (range f))
  {c : ℝ} (hc : 0 ≤ c) :
  c * supr f = supr (λ x, c * f x) :=
csupr_of_csupr_of_monotone_of_continuous (continuous_const.mul continuous_id)
  (monotone_mul_left_of_nonneg hc) h

noncomputable theory

structure quasi_mul_add_hom (M : Type*) [monoid M] (V : Type*) [normed_group V] :=
(to_fun : M → V)
(cbd_bounded' : ∃ C, ∀ x y, dist (to_fun (x * y)) (to_fun x + to_fun y) ≤ C)

namespace quasi_mul_add_hom

variables {M : Type*} [monoid M] {V : Type*} [normed_group V]

instance : has_coe_to_fun (quasi_mul_add_hom M V) :=
⟨λ _, M → V, quasi_mul_add_hom.to_fun⟩

def mk' (f : M → V) (C : ℝ) (hC : ∀ x y, dist (f (x * y)) (f x + f y) ≤ C) :
  quasi_mul_add_hom M V :=
⟨f, C, hC⟩

lemma mk_apply (f : M → V) (h x) : (quasi_mul_add_hom.mk f h : M → V) x = f x := rfl

lemma mk'_apply (f : M → V) (C hC x) : (quasi_mul_add_hom.mk' f C hC : M → V) x = f x := rfl

lemma coe_inj ⦃f g : quasi_mul_add_hom M V⦄ (H : (f : M → V) = g) : f = g :=
by { cases f, cases g, cases H, refl }

@[ext] lemma ext ⦃f g : quasi_mul_add_hom M V⦄ (H : ∀ x, f x = g x) : f = g :=
coe_inj (funext H)

variables (f g : quasi_mul_add_hom M V)

lemma cbd_bounded : ∃ C, ∀ x y, dist (f (x * y)) (f x + f y) ≤ C := f.cbd_bounded'

def norm_cbd :=
⨆ p : M × M,  dist (f (p.1 * p.2)) (f p.1 + f p.2)

lemma norm_cbd_bdd_above : bdd_above (range $ λ p : M × M, dist (f (p.1 * p.2)) (f p.1 + f p.2)) :=
f.cbd_bounded.imp $ λ C hC _ ⟨p, hp⟩, hp ▸ hC p.1 p.2

lemma map_mul_ineq (x y) : dist (f (x * y)) (f x + f y) ≤ f.norm_cbd :=
@le_csupr _ _ _ _ f.norm_cbd_bdd_above (x, y)

lemma norm_cbd_le {C} (hC : ∀ x y, dist (f (x * y)) (f x + f y) ≤ C) : f.norm_cbd ≤ C :=
csupr_le (λ p, hC p.1 p.2)

lemma norm_cbd_mk'_le (f : M → V) (C hC) : (mk' f C hC).norm_cbd ≤ C := norm_cbd_le _ hC

lemma norm_cbd_nonneg : 0 ≤ f.norm_cbd :=
le_trans dist_nonneg (f.map_mul_ineq 1 1)

def nnnorm_cbd : nnreal := ⟨f.norm_cbd, f.norm_cbd_nonneg⟩

lemma coe_nnnorm_cbd : (f.nnnorm_cbd : ℝ) = f.norm_cbd := rfl

def comp_hom {N : Type*} [monoid N] (g : N →* M) : quasi_mul_add_hom N V :=
mk' (λ x, f (g x)) f.norm_cbd $ λ x y, by simpa only [g.map_mul] using f.map_mul_ineq (g x) (g y)

@[simp] lemma comp_hom_apply {N : Type*} [monoid N] (g : N →* M) (x) : f.comp_hom g x = f (g x) := rfl

lemma norm_cbd_comp_hom_le {N : Type*} [monoid N] (g : N →* M) :
  (f.comp_hom g).norm_cbd ≤ f.norm_cbd :=
norm_cbd_mk'_le _ _ _

instance : add_comm_group (quasi_mul_add_hom M V) :=
{ add := λ f g, mk' (λ x, f x + g x) (f.norm_cbd + g.norm_cbd) $
    assume x y,
    calc dist (f (x * y) + g (x * y)) ((f x + g x) + (f y + g y)) =
      dist (f (x * y) + g (x * y)) ((f x + f y) + (g x + g y)) : by { congr' 1, ac_refl }
    ... ≤  _ : dist_add_add_le_of_le (f.map_mul_ineq x y) (g.map_mul_ineq x y),
  add_assoc := λ f₁ f₂ f₃, coe_inj (add_assoc f₁ f₂ f₃),
  zero := ⟨0, 0, λ _ _, by simp only [pi.zero_apply, zero_add, dist_self]⟩,
  zero_add := λ f, coe_inj (zero_add (f : M → V)),
  add_zero := λ f, coe_inj (add_zero (f : M → V)),
  add_comm := λ f g, coe_inj (add_comm (f : M → V) g),
  neg := λ f, ⟨-f, by { simp only [pi.neg_apply, (neg_add _ _).symm, dist_neg_neg], exact f.2 }⟩,
  add_left_neg := λ f, coe_inj (add_left_neg (f : M → V)) }

lemma add_apply (x : M) : (f + g) x = f x + g x := rfl
lemma zero_apply (x : M) : (0 : quasi_mul_add_hom M V) x = 0 := rfl
lemma norm_cbd_add_le : (f + g).norm_cbd ≤ f.norm_cbd + g.norm_cbd :=
norm_cbd_mk'_le _ _ _

instance : emetric_space (quasi_mul_add_hom M V) :=
{ edist := λ f g, ⨆ x, edist (f x) (g x),
  edist_self := λ f, by simp only [edist_self, supr_const],
  eq_of_edist_eq_zero := λ f g h, ext $ λ x, edist_eq_zero.1 $ le_zero_iff_eq.1 $ h ▸ le_supr _ x,
  edist_comm := λ f g, by simp only [edist_comm],
  edist_triangle := λ f g h, supr_le $ λ x, le_trans (edist_triangle _ (g x) _)
    (add_le_add' (le_supr _ x) (le_supr _ x)) }

lemma edist_def : edist f g = ⨆ x, edist (f x) (g x) := rfl

variables {f g}
lemma edist_le_iff {C} : edist f g ≤ C ↔ ∀ x, edist (f x) (g x) ≤ C := supr_le_iff
variables (f g)

lemma edist_le_edist (x) : edist (f x) (g x) ≤ edist f g :=
le_supr _ x

lemma lipschitz_with_eval (x : M) : lipschitz_with 1 (λ f : quasi_mul_add_hom M V, f x) :=
lipschitz_with.of_edist_le $ λ f g, le_supr _ x

open filter
lemma cbd_closed_ball_is_complete [complete_space V] (C : ℝ) :
  is_complete {f : quasi_mul_add_hom M V | f.norm_cbd ≤ C} :=
begin
  assume l hl hlC,
  -- As usual, we construct the limit function as the pointwise limit
  rw [le_principal_iff, ← filter.eventually] at hlC,
  have : ∀ x, ∃ y, tendsto (λ f : quasi_mul_add_hom M V, f x) l (𝓝 y),
    from λ x, complete_space.complete (cauchy_map (lipschitz_with_eval x).uniform_continuous hl),
  choose g hg,
  -- We prove that the limit function belongs to the set `{f | f.norm_cbd ≤ C}`
  have hgC : ∀ x y, dist (g (x * y)) (g x + g y) ≤ C,
  { intros x y,
    have : ∀ᶠ (f : quasi_mul_add_hom M V) in l, dist (f (x * y)) (f x + f y) ≤ C,
      from hlC.mono (λ f hf, le_trans (f.map_mul_ineq x y) hf),
    exact le_of_tendsto hl.1 (tendsto_dist (hg (x * y)) ((hg x).add (hg y))) this },
  refine ⟨⟨g, C, hgC⟩, norm_cbd_le _ hgC, _⟩,
  -- Now we prove convergence
  refine (nhds_basis_uniformity uniformity_basis_edist_le).ge_iff.2 (λ ε ε0, _),
  rcases (uniformity_basis_edist_le.cauchy_iff.1 hl).2 ε ε0 with ⟨s, hsl, hs⟩,
  refine mem_sets_of_superset hsl (λ f hf, edist_le_iff.2 $ λ x, _),
  change edist (f x) (g x) ≤ ε,
  refine le_of_tendsto hl.1 (tendsto_edist tendsto_const_nhds (hg x)) (mem_sets_of_superset hsl _),
  exact λ f' hf', edist_le_iff.1 (hs f f' hf hf') x
end

instance [normed_space ℝ V] : module ℝ (quasi_mul_add_hom M V) :=
{ smul := λ c f, ⟨λ x, c • (f x), ∥c∥ * f.norm_cbd,
  begin
    assume x y,
    rw [← smul_add, dist_smul],
    exact mul_le_mul_of_nonneg_left (f.map_mul_ineq x y) (norm_nonneg c)
  end⟩,
  one_smul := λ f, ext $ λ x, one_smul _ (f x),
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul _ _ _,
  smul_add := λ c f g, ext $ λ x, smul_add _ _ _,
  smul_zero := λ c, ext $ λ x, smul_zero _,
  add_smul := λ c₁ c₂ f, ext $ λ x, add_smul _ _ _,
  zero_smul := λ f, ext $ λ x, zero_smul _ _ }

variables [normed_space ℝ V]

lemma smul_def (c : ℝ) (x : M) : (c • f) x = c • (f x) := rfl

lemma edist_smul (c : ℝ) : edist (c • f) (c • g) = nnnorm c * edist f g :=
by simp only [edist_def, supr_le_iff, smul_def, ennreal.mul_supr, edist_nndist,
  nndist_smul, ennreal.coe_mul]

lemma smul_lipschitz_with (c : ℝ) :
  lipschitz_with (nnnorm c) (λ f : quasi_mul_add_hom M V, c • f) :=
λ f g, le_of_eq $ edist_smul f g c

lemma norm_cbd_smul (c : ℝ) (f : quasi_mul_add_hom M V) :
  (c • f).norm_cbd = (abs c) * f.norm_cbd :=
by simp only [norm_cbd, real.mul_csupr f.norm_cbd_bdd_above (abs_nonneg c), smul_def,
  (smul_add _ _ _).symm, dist_smul, real.norm_eq_abs]

end quasi_mul_add_hom

def quasi_arith_seq (V : Type*) [normed_group V] :=
quasi_mul_add_hom (multiplicative ℕ) V

namespace quasi_arith_seq

variables {V : Type*} [ngV : normed_group V] [nsV : normed_space ℝ V] [csV : complete_space V]
include ngV

def mk' (f : ℕ → V) (C : ℝ) (hC : ∀ k l, dist (f (k + l)) (f k + f l) ≤ C) :
  quasi_arith_seq V :=
⟨f, C, hC⟩

instance : has_coe_to_fun (quasi_arith_seq V) := ⟨λ _, ℕ → V, quasi_mul_add_hom.to_fun⟩
instance : add_comm_group (quasi_arith_seq V) := quasi_mul_add_hom.add_comm_group
instance : emetric_space (quasi_arith_seq V) := quasi_mul_add_hom.emetric_space
instance [normed_space ℝ V] : module ℝ (quasi_arith_seq V) := quasi_mul_add_hom.module

variables (f g : quasi_arith_seq V)

lemma cbd_bounded : ∃ C, ∀ x y, dist (f (x + y)) (f x + f y) ≤ C :=
f.cbd_bounded

export quasi_mul_add_hom (norm_cbd)

lemma map_add_ineq (x y) : dist (f (x + y)) (f x + f y) ≤ f.norm_cbd :=
f.map_mul_ineq x y

lemma norm_cbd_le {C} (hC : ∀ k l, dist (f (k + l)) (f k + f l) ≤ C) : f.norm_cbd ≤ C :=
f.norm_cbd_le hC

lemma norm_cbd_nonneg : 0 ≤ f.norm_cbd := f.norm_cbd_nonneg

lemma norm_cbd_mk'_le (f : ℕ → V) (C hC) : (mk' f C hC).norm_cbd ≤ C := norm_cbd_le _ hC

lemma coe_nnnorm_cbd : (f.nnnorm_cbd : ℝ) = f.norm_cbd := rfl

lemma edist_def : edist f g = ⨆ x, edist (f x) (g x) := rfl

lemma edist_le_edist (k) : edist (f k) (g k) ≤ edist f g :=
le_supr _ k

lemma lipschitz_with_eval (k : ℕ) : lipschitz_with 1 (λ f : quasi_arith_seq V, f k) :=
quasi_mul_add_hom.lipschitz_with_eval k

def arg_rescale (n : ℕ) : quasi_arith_seq V :=
mk' (λ k, f (n * k)) f.norm_cbd $
assume k l : ℕ,
calc dist (f (n * (k + l))) (f (n * k) + f (n * l)) =
  dist (f (n * k + n * l)) (f (n * k) + f (n * l)) : by rw [mul_add]
... ≤ _ : f.map_add_ineq (n * k) (n * l)

lemma arg_rescale_def (n k : ℕ) : f.arg_rescale n k = f (n * k) := rfl

lemma arg_rescale_lipschitz (n : ℕ) :
  lipschitz_with 1 (λ f : quasi_arith_seq V, f.arg_rescale n) :=
begin
  refine lipschitz_with.of_edist_le (λ f g, _),
  simp only [edist_def],
  exact supr_le_supr2 (λ k : ℕ, ⟨n * k, le_refl _⟩)
end

lemma norm_cbd_arg_rescale_le (n : ℕ) :
  (f.arg_rescale n).norm_cbd ≤ f.norm_cbd :=
norm_cbd_mk'_le _ _ _

lemma cbd_closed_ball_is_complete [complete_space V] (C : ℝ) :
  is_complete {f : quasi_arith_seq V | f.norm_cbd ≤ C} :=
quasi_mul_add_hom.cbd_closed_ball_is_complete C

include nsV

lemma smul_def (c : ℝ) (n : ℕ) : (c • f) n = c • (f n) := rfl

lemma edist_smul (c : ℝ) : edist (c • f) (c • g) = nnnorm c * edist f g :=
quasi_mul_add_hom.edist_smul f g c

lemma norm_cbd_smul (c : ℝ) (f : quasi_arith_seq V) :
  (c • f).norm_cbd = (abs c) * f.norm_cbd :=
f.norm_cbd_smul c

lemma smul_lipschitz_with (c : ℝ) :
  lipschitz_with (nnnorm c) (λ f : quasi_arith_seq V, c • f) :=
quasi_mul_add_hom.smul_lipschitz_with c

def zoom2 : quasi_arith_seq V := (2⁻¹:ℝ) • (f.arg_rescale 2)

lemma zoom2_contracting : contracting_with 2⁻¹ (@zoom2 V ngV _) :=
begin
  use nnreal.two_inv_lt_one,
  convert (smul_lipschitz_with _).comp (arg_rescale_lipschitz 2),
  apply nnreal.eq,
  rw [mul_one, coe_nnnorm, real.norm_eq_abs, abs_of_pos (inv_pos.2 $ @two_pos ℝ _)],
  refl
end

lemma edist_zoom2_le : edist f f.zoom2 ≤ 2⁻¹ * f.nnnorm_cbd :=
begin
  rw [edist_def, supr_le_iff],
  intro k,
  rw [zoom2, smul_def, arg_rescale_def, edist_nndist, ← ennreal.coe_inv_two, ← ennreal.coe_mul,
    ennreal.coe_le_coe, ← nnreal.coe_le_coe, nnreal.coe_mul, ← dist_nndist, coe_nnnorm_cbd],
  conv { congr, congr,
    rw [← one_smul ℝ (f k), ← mul_inv_cancel (@two_ne_zero ℝ _), two_mul, add_smul, ← smul_add] },
  rw [two_mul, dist_smul, real.norm_eq_abs, abs_of_pos (inv_pos.2 $ @two_pos ℝ _), dist_comm],
  exact mul_le_mul_of_nonneg_left (f.map_add_ineq _ _) (inv_nonneg.2 $ le_of_lt two_pos)
end

lemma norm_cbd_zoom2_le : f.zoom2.norm_cbd ≤ 2⁻¹ * f.norm_cbd :=
begin
  rw [zoom2, norm_cbd_smul, ← abs_of_pos (inv_pos.2 $ @two_pos ℝ _), abs_abs],
  exact mul_le_mul_of_nonneg_left (f.norm_cbd_arg_rescale_le _) (abs_nonneg _)
end

lemma norm_cbd_zoom2_le' : f.zoom2.norm_cbd ≤ f.norm_cbd :=
le_trans f.norm_cbd_zoom2_le $
begin
  conv_rhs { rw [← one_mul f.norm_cbd] },
  rw [← one_div_eq_inv],
  exact mul_le_mul_of_nonneg_right (le_of_lt one_half_lt_one) f.norm_cbd_nonneg
end

lemma zoom2_app (k) : f.zoom2 k = (2⁻¹:ℝ) • f (2 * k) := rfl

lemma iter_zoom2_app_one :
  ∀ n (f : quasi_arith_seq V), (zoom2^[n] f 1) = (2⁻¹:ℝ)^n • (f $ 2^n)
| 0 f := (one_smul _ _).symm
| (n+1) f := by rw [nat.iterate_succ, iter_zoom2_app_one n, f.zoom2_app, smul_smul, pow_succ',
  nat.pow_succ, mul_comm 2]

include csV

def slope (f : quasi_arith_seq V) : V :=
begin
  have : maps_to zoom2 {g : quasi_arith_seq V | norm_cbd g ≤ f.norm_cbd}
    {g | norm_cbd g ≤ f.norm_cbd},
  { intros g hg,
    exact le_trans g.norm_cbd_zoom2_le' hg },
  refine (zoom2_contracting.restrict this).efixed_point' _ (cbd_closed_ball_is_complete _)
    this f (le_refl $ norm_cbd f) (lt_of_le_of_lt f.edist_zoom2_le _) 1,
  exact ennreal.mul_lt_top (ennreal.lt_top_iff_ne_top.2 (ennreal.inv_ne_top.2 ennreal.two_ne_zero))
    ennreal.coe_lt_top
end

lemma slope_eq_of_edist_lt_top (h : edist f g < ⊤) :
  f.slope = g.slope :=
begin
  rw [slope, slope],
  refine congr_fun (congr_arg _ _) 1,
  apply contracting_with.efixed_point_eq_of_edist_lt_top',
  exacts [zoom2_contracting, h]
end

lemma slope_eq_of_dist_le (C : ℝ) (h : ∀ k, dist (f k) (g k) ≤ C) :
  f.slope = g.slope :=
begin
  apply slope_eq_of_edist_lt_top,
  refine lt_of_le_of_lt _ (ennreal.coe_lt_top : ↑(nnreal.of_real C) < ⊤),
  simp only [edist_def, supr_le_iff, edist_nndist, ennreal.coe_le_coe,
    ← nnreal.coe_le_coe, ← dist_nndist],
  intro n,
  exact le_trans (h n) (nnreal.le_coe_of_real C)
end

lemma dist_slope_le_aux (n : ℕ) :
  dist ((2⁻¹:ℝ)^n • (f $ 2^n)) f.slope ≤ f.norm_cbd * (2⁻¹:ℝ)^n :=
begin
  rw [dist_nndist, ← coe_nnnorm_cbd, ← iter_zoom2_app_one, ← nnreal.coe_one],
  norm_cast,
  rw [← ennreal.coe_le_coe, ← edist_nndist],
  apply le_trans (edist_le_edist _ _ 1),
  apply le_trans (contracting_with.apriori_edist_iterate_efixed_point_le' _ _ _ _ _ _),
  convert (ennreal.mul_right_mono (ennreal.mul_right_mono $ edist_zoom2_le _)),
  simp only [],
  rw [ennreal.coe_mul, ennreal.coe_pow, ennreal.coe_inv_two, ennreal.one_sub_inv_two,
    ennreal.inv_inv],
  conv_rhs { rw [mul_comm, ← mul_assoc, ← mul_assoc,
    ennreal.mul_inv_cancel ennreal.two_ne_zero ennreal.coe_ne_top, one_mul] }
end

lemma dist_slope_le : dist (f 1) f.slope ≤ f.norm_cbd :=
by simpa only [nat.pow_zero, pow_zero, nat.iterate_zero, one_smul, mul_one]
  using f.dist_slope_le_aux 0

lemma tendsto_slope_aux :
  tendsto (λ n:ℕ, (2⁻¹:ℝ)^n • (f $ 2^n)) at_top (𝓝 f.slope) :=
begin
  simp only [(iter_zoom2_app_one _ _).symm],
  apply ((lipschitz_with_eval 1).continuous.tendsto _).comp,
  apply contracting_with.tendsto_iterate_efixed_point'
end

lemma slope_add : (f + g).slope = f.slope + g.slope :=
begin
  refine tendsto_nhds_unique at_top_ne_bot (f + g).tendsto_slope_aux _,
  convert f.tendsto_slope_aux.add g.tendsto_slope_aux,
  ext n,
  apply smul_add
end

end quasi_arith_seq

namespace quasi_mul_add_hom

variables {M : Type*} [monoid M] {V : Type*} [normed_group V]
  [nsV : normed_space ℝ V] [csV : complete_space V] (f : quasi_mul_add_hom M V)

def on_powers (x : M) : quasi_arith_seq V :=
{ to_fun := λ n:ℕ, f (x ^ n),
  cbd_bounded' := ⟨f.norm_cbd, λ k l, by { erw [pow_add], apply f.map_mul_ineq }⟩}

lemma on_powers_def (x : M) (n : ℕ) : f.on_powers x n = f (x ^ n) := rfl

lemma on_powers_norm_cbd_le (x) : (f.on_powers x).norm_cbd ≤ f.norm_cbd :=
(f.on_powers x).norm_cbd_le $ λ k l, by { rw [on_powers_def, pow_add], apply f.map_mul_ineq }

include nsV csV

def approx (x : M) : V := (f.on_powers x).slope

lemma approx_mul_of_commute {x y : M} (h : commute x y) :
  f.approx (x * y) = f.approx x + f.approx y :=
begin
  delta approx,
  rw [← quasi_arith_seq.slope_add],
  apply quasi_arith_seq.slope_eq_of_dist_le _ _ f.norm_cbd,
  intro n,
  convert f.map_mul_ineq (x^n) (y^n),
  exact congr_arg f (h.mul_pow n)
end

lemma approx_one : f.approx 1 = 0 :=
add_self_iff_eq_zero.1 $
by rw [← f.approx_mul_of_commute (commute.one_left 1), one_mul]

lemma approx_pow (x : M) : ∀ n : ℕ, f.approx (x^n) = (n:ℝ) • f.approx x
| 0 := by simp only [nat.cast_zero, zero_smul, pow_zero, approx_one]
| (n+1) := by simp only [nat.cast_succ, pow_succ, add_smul, one_smul,
  f.approx_mul_of_commute (commute.self_pow x n), approx_pow n, add_comm]

lemma approx_units_inv (x : units M) : f.approx (x⁻¹ : units M) = - f.approx x :=
eq_neg_iff_add_eq_zero.2 $ by simpa only [x.inv_mul, f.approx_one]
  using (f.approx_mul_of_commute (commute.refl x).units_coe.units_inv_left).symm

lemma dist_le_of_semiconj {a x y : M} (h : semiconj_by a x y) :
  dist (f x) (f y) ≤ 2 * f.norm_cbd :=
begin
  rw [two_mul, ← dist_add_left (f a)],
  refine le_trans (dist_triangle _ (f (a * x)) _)
    (add_le_add _ _),
  { rw [dist_comm], apply f.map_mul_ineq },
  { rw [h.eq, add_comm], apply f.map_mul_ineq }
end

lemma approx_eq_of_semiconj {a x y : M} (h : semiconj_by a x y) :
  f.approx x = f.approx y :=
begin
  refine quasi_arith_seq.slope_eq_of_dist_le _ _ (2 * f.norm_cbd) (λ n, _),
  exact f.dist_le_of_semiconj (h.pow_right n)
end

lemma dist_approx_le (x : M) : dist (f x) (f.approx x) ≤ f.norm_cbd :=
by simpa only [on_powers_def, pow_one]
  using le_trans (f.on_powers x).dist_slope_le (f.on_powers_norm_cbd_le x)

lemma dist_frac_pow_approx_le (x : M) (n : ℕ) (hn : 0 < n):
  dist ((n:ℝ)⁻¹ • f (x^n)) (f.approx x) ≤ f.norm_cbd / n :=
begin
  have A : 0 < (n:ℝ), from nat.cast_pos.2 hn,
  have := f.dist_approx_le (x^n),
  rwa [approx_pow, ← one_smul ℝ (f (x^n)), ← mul_inv_cancel (ne_of_gt A), mul_smul,
    dist_smul, real.norm_eq_abs, abs_of_pos A, ← le_div_iff' A] at this
end

lemma tendsto_approx (x : M) :
  tendsto (λ n:ℕ, (n:ℝ)⁻¹ • f (x^n)) at_top (𝓝 $ f.approx x) :=
begin
  refine tendsto_iff_dist_tendsto_zero.2 _,
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (tendsto_const_div_at_top_nhds_0_nat f.norm_cbd) _ _,
  exact univ_mem_sets' (λ _, dist_nonneg),
  apply eventually.mono (mem_at_top 1),
  assume n hn,
  exact f.dist_frac_pow_approx_le _ _ (nat.lt_of_succ_le hn)
end

lemma approx_eq_of_dist_le {f g : quasi_mul_add_hom M V} {C : ℝ}
  (h : ∀ x, dist (f x) (g x) ≤ C) (x) :
  f.approx x = g.approx x :=
quasi_arith_seq.slope_eq_of_dist_le _ _ C (λ k, h (x^k))

end quasi_mul_add_hom
