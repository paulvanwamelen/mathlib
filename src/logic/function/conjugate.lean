import logic.function.basic

namespace function

variables {α : Type*} {β : Type*} {γ : Type*}

/-- We say that `f : α → β` conjugates `ga : α → α` to `gb : β → β` if `f ∘ ga = gb ∘ f`. -/
def conjugates (f : α → β) (ga : α → α) (gb : β → β) := ∀ x, f (ga x) = gb (f x)

namespace conjugates

variables {f fab : α → β} {fbc : β → γ} {ga ga' : α → α} {gb gb' : β → β} {gc gc' : γ → γ}

protected lemma comp_eq (h : conjugates f ga gb) : f ∘ ga = gb ∘ f := funext h

protected lemma eq (h : conjugates f ga gb) (x : α) : f (ga x) = gb (f x) := h x

lemma comp_right  (h : conjugates f ga gb) (h' : conjugates f ga' gb') :
  conjugates f (ga ∘ ga') (gb ∘ gb') :=
λ x, by rw [comp_app, h.eq, h'.eq]

lemma comp_left (hab : conjugates fab ga gb) (hbc : conjugates fbc gb gc) :
  conjugates (fbc ∘ fab) ga gc :=
λ x, by simp only [comp_app, hab.eq, hbc.eq]

lemma id_right : conjugates f id id := λ _, rfl

lemma id_left : conjugates id ga ga := λ _, rfl

-- lemma symm_left {e : α ≃ β} (h : conjugates e ga gb) : conjugates e.symm gb ga :=
-- λ x, e.symm_apply_eq.2 $ by rw [h.eq, e.apply_symm_apply]

lemma inverses_right (h : conjugates f ga gb) (ha : right_inverse ga' ga)
  (hb : left_inverse gb' gb) :
  conjugates f ga' gb' :=
λ x, by rw [← hb (f (ga' x)), ← h.eq, ha x]

-- lemma symm_right {ea : α ≃ α} {eb : β ≃ β} (h : conjugates f ea eb) :
--   conjugates f ea.symm eb.symm :=
-- h.inverses_right ea.right_inverse_symm eb.left_inverse_symm

end conjugates

/-- Two maps `f g : α → α` commute if `f ∘ g = g ∘ f`. -/
def commute (f g : α → α) := conjugates f g g

lemma conjugates.commute {f g : α → α} (h : conjugates f g g) : commute f g := h

namespace commute

variables {f f' g g' : α → α}

@[refl] lemma refl (f : α → α) : commute f f := λ _, eq.refl _

@[symm] lemma symm (h : commute f g) : commute g f := λ x, (h x).symm

lemma comp_right (h : commute f g) (h' : commute f g') : commute f (g ∘ g') :=
h.comp_right h'

lemma comp_left (h : commute f g) (h' : commute f' g) : commute (f ∘ f') g :=
(h.symm.comp_right h'.symm).symm

lemma id_right : commute f id := conjugates.id_right

lemma id_left : commute id f := conjugates.id_left

end commute

/-- A map `f` conjugates a binary operation `ga` to a binary operation `gb` if
for all `x`, `y` we have `f (ga x y) = gb (f x) (f y)`. E.g., a `monoid_hom`
conjugates `(*)` to `(*)`. -/
def conjugates₂ (f : α → β) (ga : α → α → α) (gb : β → β → β) : Prop :=
∀ x y, f (ga x y) = gb (f x) (f y)

namespace conjugates₂

variables {f : α → β} {ga : α → α → α} {gb : β → β → β}

protected lemma eq (h : conjugates₂ f ga gb) (x y : α) : f (ga x y) = gb (f x) (f y) := h x y

protected lemma comp_eq (h : conjugates₂ f ga gb) :
  bicompr f ga = bicompl gb f f :=
funext $ λ x, funext $ h x

lemma id_left (op : α → α → α) : conjugates₂ id op op := λ _ _, rfl

lemma comp {f' : β → γ} {gc : γ → γ → γ} (hf' : conjugates₂ f' gb gc) (hf : conjugates₂ f ga gb) :
  conjugates₂ (f' ∘ f) ga gc :=
λ x y, by simp only [hf'.eq, hf.eq, comp_app]

end conjugates₂

end function
