import linear_algebra.bilinear_form
import analysis.normed_space.inner_product

noncomputable theory

open submodule bilin_form
open_locale real_inner_product_space classical

section bilin_form_eq

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]
  [complete_space E]

lemma bilin_form_sub_div_mul_eq_zero
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0)
  (v w : E) : B v w - B v v / ⟪v, v⟫ * ⟪v, w⟫ = 0 :=
begin
  by_cases hv : v ≠ 0,
  { have minor₁ : ⟪v, v⟫ ≠ 0 := λ W, hv (inner_self_eq_zero.mp W),
    have minor₂ : is_complete ↑(span ℝ {v} : submodule ℝ E),
    { rw [span_singleton_eq_range, ← set.image_univ],
      exact (is_closed_map_smul_left v set.univ is_closed_univ).is_complete },
    rw ← complete_space_coe_iff_is_complete at minor₂; resetI,
    rcases exists_sum_mem_mem_orthogonal (span ℝ {v} : submodule ℝ E) w with ⟨x, hx, y, hy, hxy⟩,
    rcases mem_span_singleton.mp hx with ⟨s, hs⟩,
    simp only [hxy, ← hs, add_right, inner_add_right, real_inner_smul_right, smul_right, 
               inner_right_of_mem_orthogonal (mem_span_singleton_self v) hy,
               hB v y (inner_right_of_mem_orthogonal (mem_span_singleton_self v) hy)],
    field_simp [minor₁],
    ring },
  { rw [not_not.mp hv],
    simp only [zero_left, div_zero, zero_mul, sub_zero, inner_zero_left] }
end

lemma sym_bilin_form_div_inner_self_const_aux
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0) (hB' : sym_bilin_form.is_sym B)
  {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : ⟪v, w⟫ ≠ 0) : B v v / ⟪v, v⟫ = B w w / ⟪w, w⟫ :=
begin
  let p := bilin_form_sub_div_mul_eq_zero hB v w,
  let q := bilin_form_sub_div_mul_eq_zero hB w v,
  rw [sym_bilin_form.sym hB', ← q, sub_eq_sub_iff_sub_eq_sub, sub_self] at p,
  have p' := p.symm,
  rw [sub_eq_zero, real_inner_comm v w] at p',
  exact mul_right_cancel' hvw p'
end

/-- One has to state this with the hypotheses that `v ≠ 0` and `w ≠ 0`, because even though the
  equality holds under Lean's definition of zero division, the equality does not hold for a 
  trivial versus nontrivial pair. -/
lemma sym_bilin_form_div_inner_self_const
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0) (hB' : sym_bilin_form.is_sym B)
  {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) : B v v / ⟪v, v⟫ = B w w / ⟪w, w⟫ :=
begin
  by_cases hvw : ⟪v, w⟫ ≠ 0,
  { exact sym_bilin_form_div_inner_self_const_aux hB hB' hv hw hvw },
  { rw not_not at hvw,
    let u := v + w,
    have minor₁ : u ≠ 0 :=
    λ p, begin
      have : ⟪v, w⟫ < 0 :=
      calc ⟪v, w⟫ = ⟪v + w - w, w⟫ : by rw add_sub_cancel
        ... = ⟪u - w, w⟫ : by simp only [u]
        ... = ⟪u, w⟫ - ⟪w, w⟫ : by rw inner_sub_left
        ... = 0 - ⟪w, w⟫ : by rw [p, inner_zero_left]
        ... = - (∥w∥ * ∥w∥) : by rw [zero_sub, real_inner_self_eq_norm_sq, neg_mul_eq_neg_mul]
        ... < 0 : neg_lt_zero.mpr (mul_self_pos $ ne_of_gt $ norm_pos_iff.mpr hw),
      exact (ne_of_lt this) hvw,
    end,
    have minor₂ : ⟪v, u⟫ ≠ 0,
    { simp only [u, inner_add_right, hvw, add_zero], exact λ p, hv (inner_self_eq_zero.mp p), },
    have minor₃ : ⟪w, u⟫ ≠ 0,
    { simp only [u, inner_add_right, real_inner_comm, hvw, zero_add],
      exact λ p, hw (inner_self_eq_zero.mp p), },
    let p := sym_bilin_form_div_inner_self_const_aux hB hB' hv minor₁ minor₂,
    let q := sym_bilin_form_div_inner_self_const_aux hB hB' hw minor₁ minor₃,
    rw ← q at p,
    exact p },
end

lemma sym_bilin_form_eq_const_mul_inner
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0)
  (hB' : sym_bilin_form.is_sym B) :
  ∃ (r : ℝ), ∀ (v w : E), B v w = r * ⟪v, w⟫ :=
begin
  cases subsingleton_or_nontrivial E with h h; resetI,
  { refine ⟨0, λ v w, _⟩,
    simp only [subsingleton.elim v 0, bilin_form.zero_left, zero_mul] },
  { rcases exists_ne (0 : E) with ⟨v₀, hv₀⟩,
    refine ⟨B v₀ v₀ / ⟪v₀, v₀⟫, λ v w, _⟩,
    by_cases h' : v = 0,
    { rw [h', inner_zero_left, hB 0 w (inner_zero_left), mul_zero] },
    { rw [← sub_eq_zero],
      rw sym_bilin_form_div_inner_self_const hB hB' hv₀ h',
      exact bilin_form_sub_div_mul_eq_zero hB v w } }
end

/-- The scaling factor. This factor must be defined as an extension of a bilinear form that
  satifies some property locally because the conformality of the local inverse of a conformal map is
  local, and the corresponding bilinear form does not inherits nice properties from the former for
  inputs outside the source of the local inverse. -/
def bilin_form_factor {B : E → (bilin_form ℝ E)} {s : set E}
  (hB : ∀ x (hx : x ∈ s) u v, ⟪u, v⟫ = 0 → B x u v = 0) 
  (hB' : ∀ x (hx : x ∈ s), sym_bilin_form.is_sym (B x)) (x : E) : ℝ :=
dite (x ∈ s) 
(λ (hx : x ∈ s), classical.some $ sym_bilin_form_eq_const_mul_inner (hB x hx) $ hB' x hx)
(λ (hx : ¬ x ∈ s), 0)

lemma bilin_form_factor_spec {B : E → (bilin_form ℝ E)} {s : set E}
  (hB : ∀ x (hx : x ∈ s) u v, ⟪u, v⟫ = 0 → B x u v = 0) 
  (hB' : ∀ x (hx : x ∈ s), sym_bilin_form.is_sym (B x)) {x : E} (hx : x ∈ s) :
  ∀ u v, B x u v = (bilin_form_factor hB hB' x) * ⟪u, v⟫ :=
begin
  simp only [bilin_form_factor, dif_pos hx],
  exact classical.some_spec (sym_bilin_form_eq_const_mul_inner (hB x hx) $ hB' x hx)
end

end bilin_form_eq