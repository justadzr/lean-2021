import analysis.normed_space.conformal_linear_map
import analysis.calculus.conformal
import analysis.calculus.times_cont_diff

noncomputable theory
open filter continuous_linear_map
open_locale real_inner_product_space classical filter topological_space

section conformality

lemma is_conformal_map.symm {R X Y : Type*} [nondiscrete_normed_field R]
  [normed_group X] [normed_group Y] [normed_space R X] [normed_space R Y]
  {f' : X ≃L[R] Y} (hf' : is_conformal_map (f' : X →L[R] Y)) : 
  is_conformal_map (f'.symm : Y →L[R] X) :=
begin
  rcases hf' with ⟨c, hc, li, hli⟩,
  simp only [f'.coe_coe] at hli,
  have surj : li.to_linear_map.range = ⊤ :=
  begin
    refine linear_map.range_eq_top.mpr (λ y, ⟨c • f'.symm y, _⟩),
    simp only [li.coe_to_linear_map, li.map_smul],
    have : c • li (f'.symm y) = f' (f'.symm y) := by simp only [hli, pi.smul_apply],
    rw [this, f'.apply_symm_apply]
  end,
  let le := linear_equiv.of_bijective li.to_linear_map
    (linear_map.ker_eq_bot.mpr li.injective) surj,
  let lie : X ≃ₗᵢ[R] Y :=
  { to_linear_equiv := le,
    norm_map' := by simp },
  refine ⟨c⁻¹, inv_ne_zero hc, lie.symm.to_linear_isometry, _⟩,
  ext1 y,
  have key : (li : X → Y) = lie,
  { ext1 x,
    simp only [linear_isometry_equiv.coe_mk, linear_equiv.of_bijective_apply, 
        li.coe_to_linear_map] },
  rw [f'.symm.coe_coe, f'.symm_apply_eq, hli],
  simp only [pi.smul_apply, function.comp_app, li.map_smul, lie.symm.coe_to_linear_isometry],
  rw [key, lie.apply_symm_apply, smul_smul, mul_inv_cancel hc, one_smul]
end

/-- The inversion map in a sphere at `x₀` of radius `|r|`. -/
def inversion {X : Type*} [normed_group X] [normed_space ℝ X] (r : ℝ) (x₀ : X) : X → X := 
λ x, x₀ + (r ^ 2 * (∥x - x₀∥ ^ 2)⁻¹) • (x - x₀)

lemma fderiv_inversion {X : Type*} [inner_product_space ℝ X] 
  (r : ℝ) (x₀ : X) {x : X} (hx : x ≠ x₀) : fderiv ℝ (inversion r x₀) x = 0 :=
begin
  have : ⟪x - x₀, x - x₀⟫ ≠ 0 := λ w, (sub_ne_zero.mpr hx) (inner_self_eq_zero.mp w),
  simp only [inversion],
  rw [fderiv_const_add, fderiv_smul _ (differentiable_at_id'.sub_const _), 
      fderiv_sub_const, fderiv_id', fderiv_const_mul],
  simp only [pow_two, ← real_inner_self_eq_norm_sq],
  rw [fderiv.comp (differentiable_at_inv.mpr this), fderiv_inv],
end

lemma conformal_at_inversion {E : Type*} [inner_product_space ℝ E]
  (r : ℝ) {x : E} (hx : x ≠ 0) (x₀ : E) :
  conformal_at (inversion r x₀) x :=
begin
  refine conformal_at_iff_is_conformal_map_fderiv.mpr _,
end

end conformality

section similarity_all

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]

section similarity1

def similarity_factor {f' : E →L[ℝ] F} (h : is_conformal_map f') : ℝ :=
classical.some ((is_conformal_map_iff _).mp h)

lemma similarity_factor_prop {f' : E →L[ℝ] F} (h : is_conformal_map f') :
  0 < similarity_factor h ∧ ∀ u v, ⟪f' u, f' v⟫ = (similarity_factor h) * ⟪u, v⟫ :=
classical.some_spec ((is_conformal_map_iff _).mp h)

lemma is_conformal_map_of_eq {f' : E →L[ℝ] F} {f'' : E →L[ℝ] F}
  (hf' : is_conformal_map f') (H : f' = f'') : is_conformal_map f'' := 
H ▸ hf'

lemma similarity_factor_eq_of_eq [nontrivial E] {f' : E →L[ℝ] F} {f'' : E →L[ℝ] F}
  (hf' : is_conformal_map f') (H : f' = f'') :
  similarity_factor (is_conformal_map_of_eq hf' H) = similarity_factor hf' :=
begin
  rcases exists_ne (0 : E) with ⟨u, hu⟩,
  have minor₁ := (similarity_factor_prop hf').2 u u,
  have minor₂ := (similarity_factor_prop $ is_conformal_map_of_eq hf' H).2 u u,
  have minor₃ : ⟪u, u⟫ ≠ 0 := λ w, hu (inner_self_eq_zero.mp w),
  have key : ⟪f' u, f' u⟫ = ⟪f'' u, f'' u⟫ := by rw H,
  rw [minor₁, minor₂] at key,
  exact mul_right_cancel' minor₃ key.symm
end

variables {f' : E → (E →L[ℝ] F)}

/-- TODO: refine the hypothesis `h` -/
lemma similarity_factor_times_cont_diff_at [nontrivial E] (x : E)
  (h : ∀ y, is_conformal_map $ f' y) {n : ℕ} (H : times_cont_diff_at ℝ n f' x) : 
  times_cont_diff_at ℝ n (λ y, similarity_factor $ h y) x :=
begin
  rcases exists_ne (0 : E) with ⟨v, hv⟩,
  have minor₁ : ∥v∥ ≠ 0 := λ w, hv (norm_eq_zero.mp w),
  have minor₂ : ∀ y, similarity_factor (h y) = ∥f' y v∥ ^ 2 / ∥v∥ ^ 2 :=
  λ y, by rw [← mul_div_cancel (similarity_factor $ h y) (pow_ne_zero 2 minor₁), pow_two, 
              ← real_inner_self_eq_norm_sq, ← (similarity_factor_prop $ h y).2, 
              real_inner_self_eq_norm_sq, ← pow_two],
  have minor₃ : (λ x, similarity_factor $ h x) =
    λ x, ∥(λ y, ((apply ℝ F v) ∘ f') y) x∥ ^ 2 / ∥v∥ ^ 2,
  { ext1 x,
    simp only [minor₂ x, apply_apply, function.comp_app] },
  rw [minor₃],
  apply times_cont_diff_at.div_const,
  apply times_cont_diff_at.norm_sq,
  simp only [congr_arg],
  exact times_cont_diff_at.comp _ (apply ℝ F v).times_cont_diff.times_cont_diff_at H
end

end similarity1

section similarity2

def similarity_factor_sqrt {f' : E →L[ℝ] F} (h : is_conformal_map f') : ℝ :=
real.sqrt (similarity_factor h)

lemma similarity_factor_sqrt_eq' {f' : E →L[ℝ] F} (h : is_conformal_map f') :
  similarity_factor_sqrt h ^ 2 = similarity_factor h :=
by simp only [similarity_factor_sqrt, real.sq_sqrt (le_of_lt (similarity_factor_prop h).1)]

lemma similarity_factor_sqrt_prop {f' : E →L[ℝ] F} (h : is_conformal_map f') : 
  similarity_factor_sqrt h ≠ 0 ∧ 
  ∀ u v, ⟪f' u, f' v⟫ = (similarity_factor_sqrt h) ^ 2 * ⟪u, v⟫ :=
begin
  refine ⟨real.sqrt_ne_zero'.mpr (similarity_factor_prop h).1, λ u v, _⟩,
  simp only [(similarity_factor_prop h).2, similarity_factor_sqrt, 
             real.sq_sqrt (le_of_lt (similarity_factor_prop h).1)]
end

variables {f' : E → (E →L[ℝ] F)}

/-- TODO: refine the hypothesis `h` -/
lemma similarity_factor_sqrt_times_cont_diff_at [nontrivial E] (x : E)
  (h : ∀ y, is_conformal_map $ f' y) {n : ℕ} (H : times_cont_diff_at ℝ n f' x) :
  times_cont_diff_at ℝ n (λ y, similarity_factor_sqrt $ h y) x :=
begin
  simp only [similarity_factor_sqrt],
  refine times_cont_diff_at.sqrt _ (ne_of_gt (similarity_factor_prop $ h x).1),
  exact similarity_factor_times_cont_diff_at x h H
end

lemma similarity_factor_sqrt_eq (h : ∀ y, is_conformal_map $ f' y) :
  (λ x, (similarity_factor_sqrt $ h x) ^ 2) = (λ x, similarity_factor $ h x) :=
begin
  ext1 y, 
  simp only [similarity_factor_sqrt, real.sq_sqrt (le_of_lt (similarity_factor_prop $ h y).1)]
end

lemma similarity_factor_sqrt_eq_of_eq [nontrivial E]
  {f' : E →L[ℝ] F} {f'' : E →L[ℝ] F} (hf' : is_conformal_map f') (H : f' = f'') :
  similarity_factor_sqrt (is_conformal_map_of_eq hf' H) = similarity_factor_sqrt hf' :=
by simp only [similarity_factor_sqrt, similarity_factor_eq_of_eq]

end similarity2

section similarity3

def similarity_factor_sqrt_inv {f' : E →L[ℝ] F} (h : is_conformal_map f') : ℝ :=
(similarity_factor_sqrt h)⁻¹

lemma similarity_factor_sqrt_inv_eq' {f' : E →L[ℝ] F} (h : is_conformal_map f') :
  (similarity_factor_sqrt_inv h)⁻¹ ^ 2 = similarity_factor h :=
by simp only [similarity_factor_sqrt_inv, similarity_factor_sqrt, 
              inv_inv', real.sq_sqrt (le_of_lt (similarity_factor_prop h).1)]

lemma similarity_factor_sqrt_inv_prop {f' : E →L[ℝ] F} (h : is_conformal_map f') :
  similarity_factor_sqrt_inv h ≠ 0 ∧ 
  ∀ u v, ⟪f' u, f' v⟫ = ((similarity_factor_sqrt_inv h)⁻¹) ^ 2 * ⟪u, v⟫ :=
begin
  refine ⟨inv_ne_zero (similarity_factor_sqrt_prop h).1, λ u v, _⟩,
  simp only [(similarity_factor_sqrt_prop h).2, similarity_factor_sqrt_inv, inv_inv']
end

variables {f' : E → (E →L[ℝ] F)}

/-- TODO: refine the hypothesis `h` -/
lemma similarity_factor_sqrt_inv_eq (h : ∀ y, is_conformal_map $ f' y) :
  (λ x, (similarity_factor_sqrt_inv $ h x)⁻¹ ^ 2) = (λ x, similarity_factor $ h x) :=
begin
  ext1 y,
  simp only [similarity_factor_sqrt_inv, inv_inv'],
  have := congr_fun (similarity_factor_sqrt_eq h) y,
  simpa [congr_arg] using this
end

lemma similarity_factor_sqrt_inv_eq_of_eq [nontrivial E]
  {f' : E →L[ℝ] F} {f'' : E →L[ℝ] F} (hf' : is_conformal_map f') (H : f' = f'') :
  similarity_factor_sqrt_inv (is_conformal_map_of_eq hf' H) = similarity_factor_sqrt_inv hf' :=
by simp only [similarity_factor_sqrt_inv, similarity_factor_sqrt_eq_of_eq]

/-- TODO: refine the hypothesis `h` -/
lemma similarity_factor_sqrt_inv_eq_comp_inv (h : ∀ y, is_conformal_map $ f' y) :
  (λ x, similarity_factor_sqrt_inv $ h x) = (λ x, x⁻¹) ∘ (λ x, similarity_factor_sqrt $ h x) :=
begin
  ext1,
  simp only [function.comp_app, similarity_factor_sqrt_inv]
end

/-- TODO: refine the hypothesis `h` -/
lemma similarity_factor_sqrt_inv_times_cont_diff_at [nontrivial E] (x : E)
  (h : ∀ y, is_conformal_map $ f' y) {n : ℕ} (H : times_cont_diff_at ℝ n f' x) :
  times_cont_diff_at ℝ n (λ x, similarity_factor_sqrt_inv $ h x) x :=
begin
  simp only [similarity_factor_sqrt_inv],
  refine times_cont_diff_at.inv _ (similarity_factor_sqrt_prop $ h x).1,
  exact similarity_factor_sqrt_times_cont_diff_at x h H
end

/-- TODO: refine the hypothesis `h` -/
lemma similarity_factor_sqrt_inv_fderiv [nontrivial E] (x : E) (h : ∀ y, is_conformal_map $ f' y) 
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

end similarity_all

section similarity_arithmetic

variables {E F G : Type*} 
  [inner_product_space ℝ G] [inner_product_space ℝ E] [inner_product_space ℝ F]

lemma similarity_factor_comp [nontrivial E] {f' : E →L[ℝ] F} {f'' : F →L[ℝ] G}
  (hf' : is_conformal_map f') (hf'' : is_conformal_map f'') :
  similarity_factor (hf''.comp hf') = 
  (similarity_factor hf'') * (similarity_factor hf') :=
begin
  rcases exists_ne (0 : E) with ⟨u, hu⟩,
  have := ((similarity_factor_prop $ hf''.comp hf').2 u u).symm,
  simp only [coe_comp', function.comp_app, (similarity_factor_prop hf'').2, 
             (similarity_factor_prop hf').2, ← mul_assoc] at this,
  exact mul_right_cancel' (λ w, hu $ inner_self_eq_zero.mp w) this
end

lemma similarity_factor_symm [nontrivial E] {f' : E ≃L[ℝ] F} 
  (hf' : is_conformal_map (f' : E →L[ℝ] F)) : 
  similarity_factor hf' = (similarity_factor hf'.symm)⁻¹ :=
begin
  rcases exists_ne (0 : E) with ⟨u, hu⟩,
  have := ((similarity_factor_prop $ hf'.symm).2 (f' u) $ f' u).symm,
  simp only [f'.symm.coe_coe, f'.symm_apply_apply] at this, 
  rw [← f'.coe_coe, (similarity_factor_prop hf').2, ← mul_assoc] at this,
  nth_rewrite 1 ← one_mul ⟪u, u⟫ at this,
  have key := mul_right_cancel' (λ w, hu $ inner_self_eq_zero.mp w) this,
  exact ((mul_eq_one_iff_inv_eq' $ ne_of_gt (similarity_factor_prop hf'.symm).1).mp key).symm
end

end similarity_arithmetic

