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

section similarity

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

end fderiv_eval