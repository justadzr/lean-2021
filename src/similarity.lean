import analysis.calculus.conformal
import analysis.calculus.times_cont_diff

noncomputable theory

open finite_dimensional bilin_form
open_locale real_inner_product_space classical

section eval

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

lemma coe_eval_at : ((is_bounded_linear_eval_at 𝕜 F x).to_continuous_linear_map : 
  (E →L[𝕜] F) →ₗ[𝕜] F) =  continuous_linear_map_eval_at 𝕜 F x :=
rfl

lemma times_cont_diff_top : times_cont_diff 𝕜 ⊤ (continuous_linear_map_eval_at 𝕜 F x) :=
(is_bounded_linear_eval_at 𝕜 F x).times_cont_diff

end continuous_linear_map_eval_at

end eval

section similarity1

open conformal_at

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]

def similarity_factor {f' : E → (E →L[ℝ] F)} {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) : ℝ :=
classical.some h

lemma similarity_factor_prop {f' : E → (E →L[ℝ] F)} {x : E}
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  0 < similarity_factor h ∧ ∀ u v, ⟪f' x u, f' x v⟫ = (similarity_factor h) * ⟪u, v⟫ :=
classical.some_spec h

lemma similarity_factor_times_cont_diff_at {f' : E → (E →L[ℝ] F)} {v : E} (hv : v ≠ 0) (x : E)
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) 
  {n : ℕ} (H : times_cont_diff_at ℝ n f' x) : 
  times_cont_diff_at ℝ n (λ x, similarity_factor $ h x) x :=
begin
  have minor₁ : ∥v∥ ≠ 0 := λ w, hv (norm_eq_zero.mp w),
  have minor₂ : ∀ x, similarity_factor (h x)= ∥f' x v∥ ^ 2 / ∥v∥ ^ 2 :=
  λ x, by rw [← mul_div_cancel (similarity_factor $ h x) (pow_ne_zero 2 minor₁),
              pow_two, ← real_inner_self_eq_norm_sq, ← (similarity_factor_prop $ h x).2,
              real_inner_self_eq_norm_sq, ← pow_two],
  have minor₃ : (λ x, similarity_factor $ h x) =
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

lemma similarity_factor_eq_conformal_factor {f : E → F} (h : conformal f) :
  (λ x, similarity_factor $ conformal_at_iff'.mp $ h.conformal_at x) = 
  λ x, (h.conformal_at x).conformal_factor_at :=
rfl

lemma conformal_factor_times_cont_diff {f : E → F} {v : E} (hv : v ≠ 0) {n : ℕ}
  (y : E) (h : conformal f) (h' : differentiable ℝ f) (H : times_cont_diff_at ℝ (n + 1) f y) :
  times_cont_diff_at ℝ n (λ x, (h.conformal_at x).conformal_factor_at) y :=
begin
  rcases times_cont_diff_at_succ_iff_has_fderiv_at.mp H with ⟨f', ⟨u, hu, hx⟩, hf'⟩,
  rw [← similarity_factor_eq_conformal_factor],
  refine similarity_factor_times_cont_diff_at hv y (λ x, conformal_at_iff'.mp $ h.conformal_at x) _,
  have : set.eq_on (fderiv ℝ f) f' u,
  { intros x hxu,
    exact h'.differentiable_at.has_fderiv_at.unique (hx x hxu) },
  refine hf'.congr_of_eventually_eq _,
  exact filter.eventually_eq_of_mem hu this
end

end similarity1

section similarity2

open conformal_at

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] {f' : E → (E →L[ℝ] F)}

def similarity_factor_sqrt {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) : ℝ :=
real.sqrt (similarity_factor h)

lemma similarity_factor_sqrt_prop {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  similarity_factor_sqrt h ≠ 0 ∧ 
  ∀ u v, ⟪f' x u, f' x v⟫ = (similarity_factor_sqrt h) ^ 2 * ⟪u, v⟫ :=
begin
  refine ⟨real.sqrt_ne_zero'.mpr (similarity_factor_prop h).1, λ u v, _⟩,
  simp only [(similarity_factor_prop h).2, similarity_factor_sqrt, 
             real.sq_sqrt (le_of_lt (similarity_factor_prop h).1)]
end

lemma similarity_factor_sqrt_sq_eq {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  similarity_factor_sqrt h ^ 2 = similarity_factor h :=
by simp only [similarity_factor_sqrt, real.sq_sqrt (le_of_lt (similarity_factor_prop h).1)]

lemma similarity_factor_sqrt_times_cont_diff_at {v : E} (hv : v ≠ 0) (x : E)
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) 
  {n : ℕ} (H : times_cont_diff_at ℝ n f' x) :
  times_cont_diff_at ℝ n (λ x, similarity_factor_sqrt $ h x) x :=
begin
  simp only [similarity_factor_sqrt],
  refine times_cont_diff_at.sqrt _ (ne_of_gt (similarity_factor_prop $ h x).1),
  exact similarity_factor_times_cont_diff_at hv x h H
end

lemma similarity_factor_sqrt_eq
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  (λ x, (similarity_factor_sqrt $ h x) ^ 2) = (λ x, similarity_factor $ h x) :=
begin
  ext1 y, 
  simp only [similarity_factor_sqrt, real.sq_sqrt (le_of_lt (similarity_factor_prop $ h y).1)]
end

end similarity2

section similarity3

open conformal_at

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] {f' : E → (E →L[ℝ] F)}

def similarity_factor_sqrt_inv {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) : ℝ :=
(similarity_factor_sqrt h)⁻¹

lemma similarity_factor_sqrt_inv_eq_comp_inv
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  (λ x, similarity_factor_sqrt_inv $ h x) = (λ x, x⁻¹) ∘ (λ x, similarity_factor_sqrt $ h x) :=
begin
  ext1,
  simp only [function.comp_app, similarity_factor_sqrt_inv]
end

lemma similarity_factor_sqrt_inv_prop {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  similarity_factor_sqrt_inv h ≠ 0 ∧ 
  ∀ u v, ⟪f' x u, f' x v⟫ = ((similarity_factor_sqrt_inv h)⁻¹) ^ 2 * ⟪u, v⟫ :=
begin
  refine ⟨inv_ne_zero (similarity_factor_sqrt_prop h).1, λ u v, _⟩,
  simp only [(similarity_factor_sqrt_prop h).2, similarity_factor_sqrt_inv, inv_inv']
end

lemma similarity_factor_sqrt_inv_times_cont_diff_at {v : E} (hv : v ≠ 0) (x : E)
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) 
  {n : ℕ} (H : times_cont_diff_at ℝ n f' x) :
  times_cont_diff_at ℝ n (λ x, similarity_factor_sqrt_inv $ h x) x :=
begin
  simp only [similarity_factor_sqrt_inv],
  refine times_cont_diff_at.inv _ (similarity_factor_sqrt_prop $ h x).1,
  exact similarity_factor_sqrt_times_cont_diff_at hv x h H
end

lemma similarity_factor_sqrt_inv_fderiv {v : E} (hv : v ≠ 0) (x : E)
  (h : ∀ y, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' y u, f' y v⟫ = c * ⟪u, v⟫) 
  {n : ℕ} (hn : 0 < n) (H : times_cont_diff_at ℝ n f' x) :
  (fderiv ℝ (λ y, similarity_factor_sqrt_inv $ h y) x : E → ℝ) = 
  -(fderiv ℝ (λ y, similarity_factor_sqrt $ h y) x) * (λ y, (similarity_factor $ h x)⁻¹) :=
begin
  have minor₁ := (similarity_factor_sqrt_prop $ h x).1,
  have minor₂ : (1 : with_top ℕ) ≤ n :=
    by { apply with_top.coe_le_coe.mpr, linarith [hn] },
  have minor₃ := (similarity_factor_sqrt_times_cont_diff_at hv x h H).differentiable_at minor₂,
  rw [similarity_factor_sqrt_inv_eq_comp_inv, fderiv.comp _ (differentiable_at_inv _), fderiv_inv];
  [skip, exact minor₁, exact minor₃, exact minor₁],
  simp only [continuous_linear_map.coe_comp'],
  ext1 y,
  simp only [function.comp_app, continuous_linear_map.smul_right_apply,
             continuous_linear_map.one_apply, smul_eq_mul, pi.mul_apply,
             pi.neg_apply, pi.inv_apply],
  rw [similarity_factor_sqrt_sq_eq (h x), neg_mul_comm]
end

lemma similarity_factor_sqrt_inv_eq
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  (λ x, (similarity_factor_sqrt_inv $ h x)⁻¹ ^ 2) = (λ x, similarity_factor $ h x) :=
begin
  ext1 y,
  simp only [similarity_factor_sqrt_inv, inv_inv'],
  have := congr_fun (similarity_factor_sqrt_eq h) y,
  simpa [congr_arg] using this
end

lemma similarity_factor_sqrt_inv_eq' {x : E}
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  (similarity_factor_sqrt_inv $ h x)⁻¹ ^ 2 = similarity_factor (h x) :=
congr (similarity_factor_sqrt_inv_eq h) rfl

end similarity3