import linear_algebra.bilinear_form
import analysis.normed_space.inner_product

noncomputable theory

open finite_dimensional bilin_form
open_locale real_inner_product_space classical

section bilin_form_eq

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]
  [finite_dimensional ℝ E]

lemma bilin_form_sub_div_mul_eq_zero
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0)
  (v w : E) : B v w - B v v / ⟪v, v⟫ * ⟪v, w⟫ = 0 :=
begin
  by_cases hv : v ≠ 0,
  { let v' := ∥v∥⁻¹ • v,
    let s : set E := {v'},
    have triv₁ : ⟪v, v⟫ ≠ 0 := λ p, hv (inner_self_eq_zero.mp p),
    have triv₂ : ∥v∥ ≠ 0 := λ p, hv (norm_eq_zero.mp p),
    have triv₀ : v = ∥v∥ • v',
    { simp_rw [v', smul_smul, mul_inv_cancel triv₂, one_smul], },
    have minor₁ : orthonormal ℝ (coe : s → E) :=
    begin
      rw orthonormal_subtype_iff_ite,
      intros x hx y hy,
      simp only [s, set.mem_singleton_iff] at hx hy,
      rw ← hy at hx,
      simp_rw [if_pos hx, hx, hy, v', real_inner_smul_left,
              real_inner_smul_right, real_inner_self_eq_norm_sq],
      field_simp [triv₂],
    end,
    rcases exists_subset_is_orthonormal_basis minor₁ with ⟨u, H, b, hb₁, hb₂⟩,
    have triv₃ : v' ∈ u,
    { apply H, simp_rw [s], exact set.mem_singleton _, },
    have minor₂ : ∀ (i : u), (⟨v', triv₃⟩ : u) ≠ i → ⟪v', ↑i⟫ = 0,
    { intros i hi, let q := hb₁.2 hi, simp only [hb₂, subtype.coe_mk] at q, exact q, },
    have minor₃ : ∀ (i : u), (⟨v', triv₃⟩ : u) ≠ i → B v' ↑i = 0,
    { intros i hi, exact hB v' i (minor₂ i hi), },
    let L : E → ℝ := λ x, B v x - B v v / ⟪v, v⟫ * ⟪v, x⟫,
    have minor₄ : ∀ (i : u), L (b i) = 0 :=
    λ i, begin
      by_cases h : (⟨v', triv₃⟩ : u) = i,
      { simp only [L, hb₂, h.symm, subtype.coe_mk, v'],
        simp only [real_inner_smul_right, smul_right],
        field_simp [triv₁, triv₂],
        ring, },
      { simp only [L, hb₂],
        nth_rewrite 0 triv₀,
        nth_rewrite 5 triv₀,
        rw [real_inner_smul_left, smul_left, minor₂ i h, minor₃ i h],
        ring, },
    end,
    have key₁ : is_linear_map ℝ L :=
    { map_add := λ x y, by
      { simp only [L], simp only [add_right, inner_add_right], ring, },
      map_smul := λ s x, by
      { simp only [L], simp only [smul_right, real_inner_smul_right, smul_eq_mul], ring, }, },
    have key₂ : is_linear_map.mk' _ key₁ = 0 := b.ext minor₄,
    exact calc B v w - B v v / ⟪v, v⟫ * ⟪v, w⟫ = L w : rfl
      ... = (is_linear_map.mk' L key₁ : E → ℝ) w : by rw ← is_linear_map.mk'_apply key₁ w
      ... = (0 : E →ₗ[ℝ] ℝ) w : by rw key₂
      ... = 0 : linear_map.zero_apply w },
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

/-- The scaling factor -/
def bilin_form_factor {B : E → (bilin_form ℝ E)} {s : set E}
  (hB : ∀ x (hx : x ∈ s) u v, ⟪u, v⟫ = 0 → B x u v = 0) 
  (hB' : ∀ x (hx : x ∈ s), sym_bilin_form.is_sym (B x)) {x : E} (hx : x ∈ s) : ℝ :=
classical.some (sym_bilin_form_eq_const_mul_inner (hB x hx) $ hB' x hx)

lemma bilin_form_factor_spec {B : E → (bilin_form ℝ E)} {s : set E}
  (hB : ∀ x (hx : x ∈ s) u v, ⟪u, v⟫ = 0 → B x u v = 0) 
  (hB' : ∀ x (hx : x ∈ s), sym_bilin_form.is_sym (B x)) {x : E} (hx : x ∈ s) :
  ∀ u v, B x u v = (bilin_form_factor hB hB' hx) * ⟪u, v⟫ :=
classical.some_spec (sym_bilin_form_eq_const_mul_inner (hB x hx) $ hB' x hx)

end bilin_form_eq