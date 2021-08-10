import linear_algebra.bilinear_form
import analysis.calculus.conformal
import analysis.calculus.times_cont_diff

noncomputable theory

open finite_dimensional bilin_form
open_locale real_inner_product_space classical

section bilin_form_eq

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]
  [finite_dimensional ℝ E]

lemma bilin_form_sub_div_mul_eq_zero
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0)
  {v : E} (hv : v ≠ 0) (w : E) : B v w - B v v / ⟪v, v⟫ * ⟪v, w⟫ = 0 :=
begin
  let v' := ∥v∥⁻¹ • v,
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
    ... = 0 : linear_map.zero_apply w,
end

lemma sym_bilin_form_div_inner_self_const_aux
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0) (hB' : sym_bilin_form.is_sym B)
  {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : ⟪v, w⟫ ≠ 0) : B v v / ⟪v, v⟫ = B w w / ⟪w, w⟫ :=
begin
  let p := bilin_form_sub_div_mul_eq_zero hB hv w,
  let q := bilin_form_sub_div_mul_eq_zero hB hw v,
  rw [sym_bilin_form.sym hB', ← q, sub_eq_sub_iff_sub_eq_sub, sub_self] at p,
  let p' := p.symm,
  rw [sub_eq_zero, real_inner_comm v w] at p',
  exact mul_right_cancel' hvw p',
end

lemma sym_bilin_form_div_inner_self_const
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0) (hB' : sym_bilin_form.is_sym B)
  {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) : B v v / ⟪v, v⟫ = B w w / ⟪w, w⟫ :=
begin
  by_cases hvw : ⟪v, w⟫ ≠ 0,
  { exact sym_bilin_form_div_inner_self_const_aux hB hB' hv hw hvw, },
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
    exact p, },
end

lemma sym_bilin_form_eq_const_mul_inner [nontrivial E]
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0)
  (hB' : sym_bilin_form.is_sym B) :
  ∃ (r : ℝ), ∀ (v w : E), B v w = r * ⟪v, w⟫ :=
begin
  rcases exists_ne (0 : E) with ⟨v₀, hv₀⟩,
  let r := B v₀ v₀ / ⟪v₀, v₀⟫,
  refine ⟨r, λ v w, _⟩,
  by_cases h' : v = 0,
  { rw [h', inner_zero_left, hB 0 w (inner_zero_left), mul_zero], },
  { rw [← sub_eq_zero],
    simp only [r],
    rw sym_bilin_form_div_inner_self_const hB hB' hv₀ h',
    exact bilin_form_sub_div_mul_eq_zero hB h' w, },
end

/-- The scaling factor -/
def bilin_form_scale_factor [nontrivial E] {B : E → (bilin_form ℝ E)} 
  (hB : ∀ x u v, ⟪u, v⟫ = 0 → B x u v = 0) (hB' : ∀ x, sym_bilin_form.is_sym (B x)) (x : E) : ℝ :=
classical.some (sym_bilin_form_eq_const_mul_inner (hB x) $ hB' x)

lemma bilin_form_scale_factor_spec [nontrivial E] {B : E → (bilin_form ℝ E)} 
  (hB : ∀ x u v, ⟪u, v⟫ = 0 → B x u v = 0) (hB' : ∀ x, sym_bilin_form.is_sym (B x)) (x : E) :
  ∀ u v, B x u v = (bilin_form_scale_factor hB hB' x) * ⟪u, v⟫ :=
classical.some_spec (sym_bilin_form_eq_const_mul_inner (hB x) $ hB' x)

end bilin_form_eq

section fderiv_eval

/-- Evaluation map of a continuous linear map -/
def continuous_linear_map_eval_at {E : Type*} (𝕜 F : Type*) [normed_group E] [normed_group F] 
  [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (x : E) : 
  (E →L[𝕜] F) →ₗ[𝕜] F :=
{ to_fun := λ f, f x,
  map_add' := by simp,
  map_smul' := by simp }

namespace continuous_linear_map_eval_at

variables {E : Type*} (𝕜 F : Type*) [normed_group E] [normed_group F] 
  [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (x : E)

@[simp] lemma continuous_linear_map_eval_at_apply {f : E →L[𝕜] F} :
  (continuous_linear_map_eval_at 𝕜 F x) f = f x :=
rfl

lemma is_bounded_linear_eval_at : is_bounded_linear_map 𝕜 (continuous_linear_map_eval_at 𝕜 F x) :=
{ to_is_linear_map := (continuous_linear_map_eval_at 𝕜 F x).is_linear,
  bound := begin
    by_cases x = 0,
    { refine ⟨1, zero_lt_one, λ f, _⟩,
      simp only [h, one_mul, continuous_linear_map_eval_at_apply, 
                 f.map_zero, norm_zero, norm_nonneg] },
    { refine ⟨∥x∥, norm_pos_iff.mpr h, λ f, _⟩,
      simpa [continuous_linear_map_eval_at_apply, mul_comm] using f.le_op_norm x }
  end }

lemma times_cont_diff_top : times_cont_diff 𝕜 ⊤ (continuous_linear_map_eval_at 𝕜 F x) :=
(is_bounded_linear_eval_at 𝕜 F x).times_cont_diff

end continuous_linear_map_eval_at

open conformal_at

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]

def map_scale_factor {f' : E → (E →L[ℝ] F)} {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) : ℝ :=
classical.some h

lemma map_scale_factor_spec {f' : E → (E →L[ℝ] F)} {x : E}
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  0 < map_scale_factor h ∧ ∀ u v, ⟪f' x u, f' x v⟫ = (map_scale_factor h) * ⟪u, v⟫ :=
classical.some_spec h

lemma map_scale_factor_times_cont_diff_at {f' : E → (E →L[ℝ] F)} {v : E} (hv : v ≠ 0) (x : E)
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) 
  {n : ℕ} (H : times_cont_diff_at ℝ n f' x) : 
  times_cont_diff_at ℝ n (λ x, map_scale_factor $ h x) x :=
begin
  have minor₁ : ∥v∥ ≠ 0 := λ w, hv (norm_eq_zero.mp w),
  have minor₂ : ∀ x, map_scale_factor (h x)= ∥f' x v∥ ^ 2 / ∥v∥ ^ 2 :=
  λ x, by rw [← mul_div_cancel (map_scale_factor $ h x) (pow_ne_zero 2 minor₁),
              pow_two, ← real_inner_self_eq_norm_sq, ← (map_scale_factor_spec $ h x).2,
              real_inner_self_eq_norm_sq, ← pow_two],
  have minor₃ : (λ x, map_scale_factor $ h x) =
    λ x, ∥(λ y, ((continuous_linear_map_eval_at ℝ F v) ∘ f') y) x∥ ^ 2 / ∥v∥ ^ 2,
  { ext1 x,
    simp only [minor₂ x, continuous_linear_map_eval_at.continuous_linear_map_eval_at_apply,
               function.comp_app], },
  rw [minor₃],
  apply times_cont_diff_at.div_const,
  apply times_cont_diff_at.norm_sq,
  simp only [congr_arg],
  apply times_cont_diff_at.comp,
  { exact 
    ((continuous_linear_map_eval_at.times_cont_diff_top ℝ F v).of_le le_top).times_cont_diff_at },
  { exact H }
end

lemma map_scale_factor_eq_conformal_factor {f : E → F} (h : conformal f) :
  (λ x, map_scale_factor $ conformal_at_iff'.mp $ h.conformal_at x) = 
  λ x, (h.conformal_at x).conformal_factor_at :=
rfl

lemma conformal_factor_times_cont_diff {f : E → F} {v : E} (hv : v ≠ 0) {n : ℕ}
  (y : E) (h : conformal f) (h' : differentiable ℝ f) (H : times_cont_diff_at ℝ (n + 1) f y) :
  times_cont_diff_at ℝ n (λ x, (h.conformal_at x).conformal_factor_at) y :=
begin
  rcases times_cont_diff_at_succ_iff_has_fderiv_at.mp H with ⟨f', ⟨u, hu, hx⟩, hf'⟩,
  rw [← map_scale_factor_eq_conformal_factor],
  refine map_scale_factor_times_cont_diff_at hv y (λ x, conformal_at_iff'.mp $ h.conformal_at x) _,
  have : set.eq_on (fderiv ℝ f) f' u,
  { intros x hxu,
    exact h'.differentiable_at.has_fderiv_at.unique (hx x hxu) },
  refine hf'.congr_of_eventually_eq _,
  exact filter.eventually_eq_of_mem hu this
end

end fderiv_eval

section tot_diff_eq

open conformal_at

variables {E : Type*} [inner_product_space ℝ E] {x : E}


end tot_diff_eq

section experiment

open conformal_at

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] {f' : E → (E →L[ℝ] F)}

def map_scale_factor_inv_sqrt {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) : ℝ :=
real.sqrt (map_scale_factor h)⁻¹

lemma map_scale_factor_inv_sqrt_prop {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  map_scale_factor_inv_sqrt h ≠ 0 ∧ 
  ∀ u v, ⟪f' x u, f' x v⟫ = ((map_scale_factor_inv_sqrt h)⁻¹) ^ 2 * ⟪u, v⟫ :=
begin
  refine ⟨real.sqrt_ne_zero'.mpr (inv_pos.mpr (map_scale_factor_spec h).1), λ u v, _⟩,
  simp only [(map_scale_factor_spec h).2, map_scale_factor_inv_sqrt, real.sqrt_inv,
             inv_inv', real.sq_sqrt (le_of_lt (map_scale_factor_spec h).1)]
end

lemma map_scale_factor_inv_sqrt_times_cont_diff_at {v : E} (hv : v ≠ 0) (x : E)
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) 
  {n : ℕ} (H : times_cont_diff_at ℝ n f' x) :
  times_cont_diff_at ℝ n (λ x, map_scale_factor_inv_sqrt $ h x) x :=
begin
  simp only [map_scale_factor_inv_sqrt],
  have := ne_of_gt (map_scale_factor_spec $ h x).1,
  refine times_cont_diff_at.sqrt _ (inv_ne_zero this),
  exact times_cont_diff_at.inv (map_scale_factor_times_cont_diff_at hv x h H) this
end



end experiment