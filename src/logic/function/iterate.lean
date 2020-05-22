import logic.function.conjugate

universes u v

variables {α : Type u} {β : Type v}
namespace function

variable (f : α → α)

@[simp] theorem iterate_zero : f^[0] = id := rfl

theorem iterate_zero_apply (x : α) : f^[0] x = x := rfl

@[simp] theorem iterate_succ (n : ℕ) : f^[n.succ] = (f^[n]) ∘ f := rfl

theorem iterate_succ_apply (n : ℕ) (x : α) : f^[n.succ] x = (f^[n]) (f x) := rfl

theorem iterate_id (n : ℕ) : nat.iterate (id : α → α) n = id :=
nat.rec_on n rfl $ λ n ihn, by rw [iterate_succ, ihn, comp.left_id]

theorem iterate_add : ∀ (m n : ℕ), f^[m + n] = (f^[m]) ∘ (f^[n])
| m 0 := rfl
| m (nat.succ n) := by rw [iterate_succ, iterate_succ, iterate_add]

theorem iterate_add_apply (m n : ℕ) (x : α) : f^[m + n] x = (f^[m] (f^[n] x)) :=
by rw iterate_add

@[simp] theorem iterate_one : f^[1] = f := funext $ λ a, rfl

lemma iterate_mul (m : ℕ) : ∀ n, f^[m * n] = (f^[m]^[n])
| 0 := by simp only [nat.mul_zero, iterate_zero]
| (n + 1) := by simp only [nat.mul_succ, nat.mul_one, iterate_one, iterate_add, iterate_mul n]

variable {f}

theorem iterate_fixed {x} (h : f x = x) (n : ℕ) : f^[n] x = x :=
nat.rec_on n rfl $ λ n ihn, by rw [iterate_succ_apply, h, ihn]

theorem injective.iterate (Hinj : injective f) (n : ℕ) : injective (f^[n]) :=
nat.rec_on n injective_id $ λ n ihn, ihn.comp Hinj

theorem surjective.iterate (Hsurj : surjective f) (n : ℕ) : surjective (f^[n]) :=
nat.rec_on n surjective_id $ λ n ihn, ihn.comp Hsurj

theorem bijective.iterate (Hbij : bijective f) (n : ℕ) : bijective (f^[n]) :=
⟨Hbij.1.iterate n, Hbij.2.iterate n⟩

namespace conjugates

lemma iterate_right {f : α → β} {ga : α → α} {gb : β → β} (h : conjugates f ga gb) (n : ℕ) :
  conjugates f (ga^[n]) (gb^[n]) :=
nat.rec_on n id_right $ λ n ihn, ihn.comp_right h

lemma iterate_left {g : ℕ → α → α} (H : ∀ n, conjugates f (g n) (g $ n + 1)) (n k : ℕ) :
  conjugates (f^[n]) (g k) (g $ n + k) :=
begin
  induction n with n ihn generalizing k,
  { rw [nat.zero_add], exact id_left },
  { rw [nat.succ_eq_add_one, nat.add_right_comm, nat.add_assoc],
    exact (H k).comp_left (ihn (k + 1)) }
end

end conjugates

namespace commute

variable {g : α → α}

lemma iterate_right (h : commute f g) (n : ℕ) : commute f (g^[n]) := h.iterate_right n

lemma iterate_left (h : commute f g) (n : ℕ) : commute (f^[n]) g := (h.symm.iterate_right n).symm

lemma iterate_iterate (h : commute f g) (m n : ℕ) : commute (f^[m]) (g^[n]) :=
(h.iterate_left m).iterate_right n

lemma iterate_eq_of_map_eq (h : commute f g) (n : ℕ) {x} (hx : f x = g x) : f^[n] x = (g^[n]) x :=
nat.rec_on n rfl $ λ n ihn,
by simp only [iterate_succ_apply, hx, (h.iterate_left n).eq, ihn, ((refl g).iterate_right n).eq]

end commute

lemma conjugates₂.iterate {f : α → α} {op : α → α → α} (hf : conjugates₂ f op op) (n : ℕ) :
  conjugates₂ (f^[n]) op op :=
nat.rec_on n (conjugates₂.id_left op) (λ n ihn, ihn.comp hf)

variable (f)

theorem iterate_succ' (n : ℕ) : f^[n.succ] = f ∘ (f^[n]) :=
by rw [iterate_succ, ((commute.refl f).iterate_right n).comp_eq]

theorem iterate_succ_apply' (n : ℕ) (x : α) : f^[n.succ] x = f (f^[n] x) :=
by rw [iterate_succ']

variable {f}

theorem left_inverse.iterate {g : α → α} (hg : left_inverse g f) (n : ℕ) :
  left_inverse (g^[n]) (f^[n]) :=
nat.rec_on n (λ _, rfl) $ λ n ihn, by { rw [iterate_succ', iterate_succ], exact ihn.comp hg }

theorem right_inverse.iterate {g : α → α} (hg : right_inverse g f) (n : ℕ) :
  right_inverse (g^[n]) (f^[n]) :=
hg.iterate n

end function
