import analysis.normed_space.conformal_linear_map
import analysis.calculus.times_cont_diff

noncomputable theory
open filter
open_locale real_inner_product_space classical filter topological_space

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

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] {f' : E → (E →L[ℝ] F)}

section similarity1

def similarity_factor {x : E} (h : ∀ᶠ x' in 𝓝 x, is_conformal_map (f' x')) : ℝ :=
classical.some ((is_conformal_map_iff _).mp h.self_of_nhds)

lemma eventually_conformal_of_eventually_eq {x : E} {f'' : E → (E →L[ℝ] F)}
  (hf' : ∀ᶠ x' in 𝓝 x, is_conformal_map $ f' x') (Heven : f' =ᶠ[𝓝 x] f'') :
  ∀ᶠ x' in 𝓝 x, is_conformal_map (f'' x') :=
begin
  rcases Heven.exists_mem with ⟨s, hs, heq⟩,
  rcases filter.eventually_iff_exists_mem.mp hf' with ⟨s', hs', heq'⟩,
  refine filter.eventually_iff_exists_mem.mpr ⟨s ∩ s', filter.inter_sets _ hs hs', λ y hy, _⟩,
  exact (heq hy.1) ▸ (heq' y hy.2)
end

lemma similarity_factor_prop {x : E} (h : ∀ᶠ x' in 𝓝 x, is_conformal_map (f' x')) :
  0 < similarity_factor h ∧ ∀ u v, ⟪f' x u, f' x v⟫ = (similarity_factor h) * ⟪u, v⟫ :=
classical.some_spec ((is_conformal_map_iff _).mp h.self_of_nhds)

lemma similarity_factor_eq_of_eventually_eq [nontrivial E] {x : E} {f'' : E → (E →L[ℝ] F)}
  (hf' : ∀ᶠ x' in 𝓝 x, is_conformal_map $ f' x') (Heven : f' =ᶠ[𝓝 x] f'') :
  similarity_factor (eventually_conformal_of_eventually_eq hf' Heven) = similarity_factor hf' :=
begin
  rcases exists_ne (0 : E) with ⟨u, hu⟩,
  have minor₁ := (similarity_factor_prop hf').2 u u,
  have minor₂ := (similarity_factor_prop $ eventually_conformal_of_eventually_eq hf' Heven).2 u u,
  have minor₃ : ⟪u, u⟫ ≠ 0 := λ w, hu (inner_self_eq_zero.mp w),
  have key : ⟪f' x u, f' x u⟫ = ⟪f'' x u, f'' x u⟫ := by rw Heven.self_of_nhds,
  rw [minor₁, minor₂] at key,
  exact mul_right_cancel' minor₃ key.symm
end

/-- TODO: Change hypo `h` into a `∀` statement. -/
lemma similarity_factor_times_cont_diff_at [nontrivial E] (x : E)
  (h : ∀ x', ∀ᶠ y in 𝓝 x', is_conformal_map (f' y)) {n : ℕ} (H : times_cont_diff_at ℝ n f' x) : 
  times_cont_diff_at ℝ n (λ y, similarity_factor $ h y) x :=
begin
  rcases exists_ne (0 : E) with ⟨v, hv⟩,
  have minor₁ : ∥v∥ ≠ 0 := λ w, hv (norm_eq_zero.mp w),
  have minor₂ : ∀ y, similarity_factor (h y) = ∥f' y v∥ ^ 2 / ∥v∥ ^ 2 :=
  λ y, by rw [← mul_div_cancel (similarity_factor $ h y) (pow_ne_zero 2 minor₁), pow_two, 
              ← real_inner_self_eq_norm_sq, ← (similarity_factor_prop $ h y).2, 
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

end similarity1

section similarity2

def similarity_factor_sqrt {x : E} (h : ∀ᶠ x' in 𝓝 x, is_conformal_map (f' x')) : ℝ :=
real.sqrt (similarity_factor h)

lemma similarity_factor_sqrt_eq' {x : E} (h : ∀ᶠ x' in 𝓝 x, is_conformal_map (f' x')) :
  similarity_factor_sqrt h ^ 2 = similarity_factor h :=
by simp only [similarity_factor_sqrt, real.sq_sqrt (le_of_lt (similarity_factor_prop h).1)]

lemma similarity_factor_sqrt_eq (h : ∀ x', ∀ᶠ y in 𝓝 x', is_conformal_map $ f' y) :
  (λ x, (similarity_factor_sqrt $ h x) ^ 2) = (λ x, similarity_factor $ h x) :=
begin
  ext1 y, 
  simp only [similarity_factor_sqrt, real.sq_sqrt (le_of_lt (similarity_factor_prop $ h y).1)]
end

lemma similarity_factor_sqrt_eq_of_eventually_eq [nontrivial E] {x : E} {f'' : E → (E →L[ℝ] F)}
  (hf' : ∀ᶠ x' in 𝓝 x, is_conformal_map $ f' x') (Heven : f' =ᶠ[𝓝 x] f'') :
  similarity_factor_sqrt (eventually_conformal_of_eventually_eq hf' Heven) = 
  similarity_factor_sqrt hf' :=
by simp only [similarity_factor_sqrt, similarity_factor_eq_of_eventually_eq]

lemma similarity_factor_sqrt_prop {x : E} (h : ∀ᶠ x' in 𝓝 x, is_conformal_map (f' x')) : 
  similarity_factor_sqrt h ≠ 0 ∧ 
  ∀ u v, ⟪f' x u, f' x v⟫ = (similarity_factor_sqrt h) ^ 2 * ⟪u, v⟫ :=
begin
  refine ⟨real.sqrt_ne_zero'.mpr (similarity_factor_prop h).1, λ u v, _⟩,
  simp only [(similarity_factor_prop h).2, similarity_factor_sqrt, 
             real.sq_sqrt (le_of_lt (similarity_factor_prop h).1)]
end

lemma similarity_factor_sqrt_times_cont_diff_at [nontrivial E] (x : E)
  (h : ∀ x', ∀ᶠ y in 𝓝 x', is_conformal_map $ f' y) {n : ℕ} (H : times_cont_diff_at ℝ n f' x) :
  times_cont_diff_at ℝ n (λ y, similarity_factor_sqrt $ h y) x :=
begin
  simp only [similarity_factor_sqrt],
  refine times_cont_diff_at.sqrt _ (ne_of_gt (similarity_factor_prop $ h x).1),
  exact similarity_factor_times_cont_diff_at x h H
end

end similarity2

section similarity3

def similarity_factor_sqrt_inv {x : E} (h : ∀ᶠ x' in 𝓝 x, is_conformal_map (f' x')) : ℝ :=
(similarity_factor_sqrt h)⁻¹

lemma similarity_factor_sqrt_inv_eq' {x : E} (h : ∀ᶠ x' in 𝓝 x, is_conformal_map (f' x')) :
  (similarity_factor_sqrt_inv h)⁻¹ ^ 2 = similarity_factor h :=
by simp only [similarity_factor_sqrt_inv, similarity_factor_sqrt, 
              inv_inv', real.sq_sqrt (le_of_lt (similarity_factor_prop h).1)]

lemma similarity_factor_sqrt_inv_eq (h : ∀ x', ∀ᶠ y in 𝓝 x', is_conformal_map $ f' y) :
  (λ x, (similarity_factor_sqrt_inv $ h x)⁻¹ ^ 2) = (λ x, similarity_factor $ h x) :=
begin
  ext1 y,
  simp only [similarity_factor_sqrt_inv, inv_inv'],
  have := congr_fun (similarity_factor_sqrt_eq h) y,
  simpa [congr_arg] using this
end

lemma similarity_factor_sqrt_inv_eq_of_eventually_eq [nontrivial E] {x : E} {f'' : E → (E →L[ℝ] F)}
  (hf' : ∀ᶠ x' in 𝓝 x, is_conformal_map $ f' x') (Heven : f' =ᶠ[𝓝 x] f'') :
  similarity_factor_sqrt_inv (eventually_conformal_of_eventually_eq hf' Heven) = 
  similarity_factor_sqrt_inv hf' :=
by simp only [similarity_factor_sqrt_inv, similarity_factor_sqrt_eq_of_eventually_eq]

lemma similarity_factor_sqrt_inv_eq_comp_inv (h : ∀ x', ∀ᶠ y in 𝓝 x', is_conformal_map $ f' y) :
  (λ x, similarity_factor_sqrt_inv $ h x) = (λ x, x⁻¹) ∘ (λ x, similarity_factor_sqrt $ h x) :=
begin
  ext1,
  simp only [function.comp_app, similarity_factor_sqrt_inv]
end

lemma similarity_factor_sqrt_inv_prop {x : E} (h : ∀ᶠ x' in 𝓝 x, is_conformal_map (f' x')) :
  similarity_factor_sqrt_inv h ≠ 0 ∧ 
  ∀ u v, ⟪f' x u, f' x v⟫ = ((similarity_factor_sqrt_inv h)⁻¹) ^ 2 * ⟪u, v⟫ :=
begin
  refine ⟨inv_ne_zero (similarity_factor_sqrt_prop h).1, λ u v, _⟩,
  simp only [(similarity_factor_sqrt_prop h).2, similarity_factor_sqrt_inv, inv_inv']
end

lemma similarity_factor_sqrt_inv_times_cont_diff_at [nontrivial E] (x : E)
  (h : ∀ x', ∀ᶠ y in 𝓝 x', is_conformal_map $ f' y) {n : ℕ} (H : times_cont_diff_at ℝ n f' x) :
  times_cont_diff_at ℝ n (λ x, similarity_factor_sqrt_inv $ h x) x :=
begin
  simp only [similarity_factor_sqrt_inv],
  refine times_cont_diff_at.inv _ (similarity_factor_sqrt_prop $ h x).1,
  exact similarity_factor_sqrt_times_cont_diff_at x h H
end

lemma similarity_factor_sqrt_inv_fderiv [nontrivial E] 
  (x : E) (h : ∀ x', ∀ᶠ y in 𝓝 x', is_conformal_map $ f' y) 
  {n : ℕ} (hn : 0 < n) (H : times_cont_diff_at ℝ n f' x) :
  (fderiv ℝ (λ y, similarity_factor_sqrt_inv $ h y) x : E → ℝ) = 
  -(fderiv ℝ (λ y, similarity_factor_sqrt $ h y) x) * (λ y, (similarity_factor $ h x)⁻¹) :=
begin
  have minor₁ := (similarity_factor_sqrt_prop $ h x).1,
  have minor₂ : (1 : with_top ℕ) ≤ n :=
    by { apply with_top.coe_le_coe.mpr, linarith [hn] },
  have minor₃ := (similarity_factor_sqrt_times_cont_diff_at x h H).differentiable_at minor₂,
  rw [similarity_factor_sqrt_inv_eq_comp_inv, fderiv.comp _ (differentiable_at_inv _), fderiv_inv];
  [skip, exact minor₁, exact minor₃, exact minor₁],
  simp only [continuous_linear_map.coe_comp'],
  ext1 y,
  simp only [function.comp_app, continuous_linear_map.smul_right_apply,
             continuous_linear_map.one_apply, smul_eq_mul, pi.mul_apply,
             pi.neg_apply, pi.inv_apply],
  rw [similarity_factor_sqrt_eq' (h x), neg_mul_comm]
end

end similarity3