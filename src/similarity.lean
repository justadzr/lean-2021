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

lemma conformal_at.symm {X Y : Type*} 
  [normed_group X] [normed_group Y] [normed_space ℝ X] [normed_space ℝ Y]
  {f : local_homeomorph X Y} {x : X} (hx : x ∈ f.source) 
  (hf : conformal_at f x) (hf' : function.surjective (fderiv ℝ f x)) :
  conformal_at f.symm (f x) :=
begin
  refine conformal_at_iff_is_conformal_map_fderiv.mpr _,
end

end conformality

section conformality_all

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]

section conformality1

def conformal_factor {f' : E →L[ℝ] F} (h : is_conformal_map f') : ℝ :=
classical.some ((is_conformal_map_iff _).mp h)

lemma conformal_factor_prop {f' : E →L[ℝ] F} (h : is_conformal_map f') :
  0 < conformal_factor h ∧ ∀ u v, ⟪f' u, f' v⟫ = (conformal_factor h) * ⟪u, v⟫ :=
classical.some_spec ((is_conformal_map_iff _).mp h)

lemma is_conformal_map_of_eq {f' : E →L[ℝ] F} {f'' : E →L[ℝ] F}
  (hf' : is_conformal_map f') (H : f' = f'') : is_conformal_map f'' := 
H ▸ hf'

lemma conformal_factor_eq_of_eq [nontrivial E] {f' : E →L[ℝ] F} {f'' : E →L[ℝ] F}
  (hf' : is_conformal_map f') (H : f' = f'') :
  conformal_factor (is_conformal_map_of_eq hf' H) = conformal_factor hf' :=
begin
  rcases exists_ne (0 : E) with ⟨u, hu⟩,
  have minor₁ := (conformal_factor_prop hf').2 u u,
  have minor₂ := (conformal_factor_prop $ is_conformal_map_of_eq hf' H).2 u u,
  have minor₃ : ⟪u, u⟫ ≠ 0 := λ w, hu (inner_self_eq_zero.mp w),
  have key : ⟪f' u, f' u⟫ = ⟪f'' u, f'' u⟫ := by rw H,
  rw [minor₁, minor₂] at key,
  exact mul_right_cancel' minor₃ key.symm
end

variables {f' : E → (E →L[ℝ] F)}

/-- TODO: refine the hypothesis `h` -/
lemma conformal_factor_times_cont_diff_at [nontrivial E] (x : E)
  (h : ∀ y, is_conformal_map $ f' y) {n : ℕ} (H : times_cont_diff_at ℝ n f' x) : 
  times_cont_diff_at ℝ n (λ y, conformal_factor $ h y) x :=
begin
  rcases exists_ne (0 : E) with ⟨v, hv⟩,
  have minor₁ : ∥v∥ ≠ 0 := λ w, hv (norm_eq_zero.mp w),
  have minor₂ : ∀ y, conformal_factor (h y) = ∥f' y v∥ ^ 2 / ∥v∥ ^ 2 :=
  λ y, by rw [← mul_div_cancel (conformal_factor $ h y) (pow_ne_zero 2 minor₁), pow_two, 
              ← real_inner_self_eq_norm_sq, ← (conformal_factor_prop $ h y).2, 
              real_inner_self_eq_norm_sq, ← pow_two],
  have minor₃ : (λ x, conformal_factor $ h x) =
    λ x, ∥(λ y, ((apply ℝ F v) ∘ f') y) x∥ ^ 2 / ∥v∥ ^ 2,
  { ext1 x,
    simp only [minor₂ x, apply_apply, function.comp_app] },
  rw [minor₃],
  apply times_cont_diff_at.div_const,
  apply times_cont_diff_at.norm_sq,
  simp only [congr_arg],
  exact times_cont_diff_at.comp _ (apply ℝ F v).times_cont_diff.times_cont_diff_at H
end

end conformality1

section conformality2

def conformal_factor_sqrt {f' : E →L[ℝ] F} (h : is_conformal_map f') : ℝ :=
real.sqrt (conformal_factor h)

lemma conformal_factor_sqrt_eq' {f' : E →L[ℝ] F} (h : is_conformal_map f') :
  conformal_factor_sqrt h ^ 2 = conformal_factor h :=
by simp only [conformal_factor_sqrt, real.sq_sqrt (le_of_lt (conformal_factor_prop h).1)]

lemma conformal_factor_sqrt_prop {f' : E →L[ℝ] F} (h : is_conformal_map f') : 
  conformal_factor_sqrt h ≠ 0 ∧ 
  ∀ u v, ⟪f' u, f' v⟫ = (conformal_factor_sqrt h) ^ 2 * ⟪u, v⟫ :=
begin
  refine ⟨real.sqrt_ne_zero'.mpr (conformal_factor_prop h).1, λ u v, _⟩,
  simp only [(conformal_factor_prop h).2, conformal_factor_sqrt, 
             real.sq_sqrt (le_of_lt (conformal_factor_prop h).1)]
end

variables {f' : E → (E →L[ℝ] F)}

/-- TODO: refine the hypothesis `h` -/
lemma conformal_factor_sqrt_times_cont_diff_at [nontrivial E] (x : E)
  (h : ∀ y, is_conformal_map $ f' y) {n : ℕ} (H : times_cont_diff_at ℝ n f' x) :
  times_cont_diff_at ℝ n (λ y, conformal_factor_sqrt $ h y) x :=
begin
  simp only [conformal_factor_sqrt],
  refine times_cont_diff_at.sqrt _ (ne_of_gt (conformal_factor_prop $ h x).1),
  exact conformal_factor_times_cont_diff_at x h H
end

lemma conformal_factor_sqrt_eq (h : ∀ y, is_conformal_map $ f' y) :
  (λ x, (conformal_factor_sqrt $ h x) ^ 2) = (λ x, conformal_factor $ h x) :=
begin
  ext1 y, 
  simp only [conformal_factor_sqrt, real.sq_sqrt (le_of_lt (conformal_factor_prop $ h y).1)]
end

lemma conformal_factor_sqrt_eq_of_eq [nontrivial E]
  {f' : E →L[ℝ] F} {f'' : E →L[ℝ] F} (hf' : is_conformal_map f') (H : f' = f'') :
  conformal_factor_sqrt (is_conformal_map_of_eq hf' H) = conformal_factor_sqrt hf' :=
by simp only [conformal_factor_sqrt, conformal_factor_eq_of_eq]

end conformality2

section conformality3

def conformal_factor_sqrt_inv {f' : E →L[ℝ] F} (h : is_conformal_map f') : ℝ :=
(conformal_factor_sqrt h)⁻¹

lemma conformal_factor_sqrt_inv_eq' {f' : E →L[ℝ] F} (h : is_conformal_map f') :
  (conformal_factor_sqrt_inv h)⁻¹ ^ 2 = conformal_factor h :=
by simp only [conformal_factor_sqrt_inv, conformal_factor_sqrt, 
              inv_inv', real.sq_sqrt (le_of_lt (conformal_factor_prop h).1)]

lemma conformal_factor_sqrt_inv_prop {f' : E →L[ℝ] F} (h : is_conformal_map f') :
  conformal_factor_sqrt_inv h ≠ 0 ∧ 
  ∀ u v, ⟪f' u, f' v⟫ = ((conformal_factor_sqrt_inv h)⁻¹) ^ 2 * ⟪u, v⟫ :=
begin
  refine ⟨inv_ne_zero (conformal_factor_sqrt_prop h).1, λ u v, _⟩,
  simp only [(conformal_factor_sqrt_prop h).2, conformal_factor_sqrt_inv, inv_inv']
end

variables {f' : E → (E →L[ℝ] F)}

/-- TODO: refine the hypothesis `h` -/
lemma conformal_factor_sqrt_inv_eq (h : ∀ y, is_conformal_map $ f' y) :
  (λ x, (conformal_factor_sqrt_inv $ h x)⁻¹ ^ 2) = (λ x, conformal_factor $ h x) :=
begin
  ext1 y,
  simp only [conformal_factor_sqrt_inv, inv_inv'],
  have := congr_fun (conformal_factor_sqrt_eq h) y,
  simpa [congr_arg] using this
end

lemma conformal_factor_sqrt_inv_eq_of_eq [nontrivial E]
  {f' : E →L[ℝ] F} {f'' : E →L[ℝ] F} (hf' : is_conformal_map f') (H : f' = f'') :
  conformal_factor_sqrt_inv (is_conformal_map_of_eq hf' H) = conformal_factor_sqrt_inv hf' :=
by simp only [conformal_factor_sqrt_inv, conformal_factor_sqrt_eq_of_eq]

/-- TODO: refine the hypothesis `h` -/
lemma conformal_factor_sqrt_inv_eq_comp_inv (h : ∀ y, is_conformal_map $ f' y) :
  (λ x, conformal_factor_sqrt_inv $ h x) = (λ x, x⁻¹) ∘ (λ x, conformal_factor_sqrt $ h x) :=
begin
  ext1,
  simp only [function.comp_app, conformal_factor_sqrt_inv]
end

/-- TODO: refine the hypothesis `h` -/
lemma conformal_factor_sqrt_inv_times_cont_diff_at [nontrivial E] (x : E)
  (h : ∀ y, is_conformal_map $ f' y) {n : ℕ} (H : times_cont_diff_at ℝ n f' x) :
  times_cont_diff_at ℝ n (λ x, conformal_factor_sqrt_inv $ h x) x :=
begin
  simp only [conformal_factor_sqrt_inv],
  refine times_cont_diff_at.inv _ (conformal_factor_sqrt_prop $ h x).1,
  exact conformal_factor_sqrt_times_cont_diff_at x h H
end

/-- TODO: refine the hypothesis `h` -/
lemma conformal_factor_sqrt_inv_fderiv [nontrivial E] (x : E) (h : ∀ y, is_conformal_map $ f' y) 
  {n : ℕ} (hn : 0 < n) (H : times_cont_diff_at ℝ n f' x) :
  (fderiv ℝ (λ y, conformal_factor_sqrt_inv $ h y) x : E → ℝ) = 
  -(fderiv ℝ (λ y, conformal_factor_sqrt $ h y) x) * (λ y, (conformal_factor $ h x)⁻¹) :=
begin
  have minor₁ := (conformal_factor_sqrt_prop $ h x).1,
  have minor₂ : (1 : with_top ℕ) ≤ n :=
    by { apply with_top.coe_le_coe.mpr, linarith [hn] },
  have minor₃ := (conformal_factor_sqrt_times_cont_diff_at x h H).differentiable_at minor₂,
  rw [conformal_factor_sqrt_inv_eq_comp_inv, fderiv.comp _ (differentiable_at_inv.mpr _), 
      fderiv_inv]; [skip, exact minor₃, exact minor₁],
  simp only [continuous_linear_map.coe_comp'],
  ext1 y,
  simp only [function.comp_app, continuous_linear_map.smul_right_apply,
             continuous_linear_map.one_apply, smul_eq_mul, pi.mul_apply,
             pi.neg_apply, pi.inv_apply],
  rw [conformal_factor_sqrt_eq' (h x), neg_mul_comm]
end

end conformality3

end conformality_all

section conformality_arithmetic

variables {E F G : Type*} 
  [inner_product_space ℝ G] [inner_product_space ℝ E] [inner_product_space ℝ F]

lemma conformal_factor_comp [nontrivial E] {f' : E →L[ℝ] F} {f'' : F →L[ℝ] G}
  (hf' : is_conformal_map f') (hf'' : is_conformal_map f'') :
  conformal_factor (hf''.comp hf') = 
  (conformal_factor hf'') * (conformal_factor hf') :=
begin
  rcases exists_ne (0 : E) with ⟨u, hu⟩,
  have := ((conformal_factor_prop $ hf''.comp hf').2 u u).symm,
  simp only [coe_comp', function.comp_app, (conformal_factor_prop hf'').2, 
             (conformal_factor_prop hf').2, ← mul_assoc] at this,
  exact mul_right_cancel' (λ w, hu $ inner_self_eq_zero.mp w) this
end

lemma conformal_factor_sqrt_comp [nontrivial E] {f' : E →L[ℝ] F} {f'' : F →L[ℝ] G}
  (hf' : is_conformal_map f') (hf'' : is_conformal_map f'') :
  conformal_factor_sqrt (hf''.comp hf') = 
  (conformal_factor_sqrt hf'') * (conformal_factor_sqrt hf') :=
by simp only [conformal_factor_sqrt, conformal_factor_comp hf' hf'', 
  real.sqrt_mul' _ (le_of_lt (conformal_factor_prop hf').1)]

lemma conformal_factor_sqrt_inv_comp [nontrivial E] {f' : E →L[ℝ] F} {f'' : F →L[ℝ] G}
  (hf' : is_conformal_map f') (hf'' : is_conformal_map f'') :
  conformal_factor_sqrt_inv (hf''.comp hf') = 
  (conformal_factor_sqrt_inv hf'') * (conformal_factor_sqrt_inv hf') :=
by simp only [conformal_factor_sqrt_inv, conformal_factor_sqrt_comp hf' hf'', mul_inv']

lemma conformal_factor_symm [nontrivial E] {f' : E ≃L[ℝ] F} 
  (hf' : is_conformal_map (f' : E →L[ℝ] F)) : 
  conformal_factor hf' = (conformal_factor hf'.symm)⁻¹ :=
begin
  rcases exists_ne (0 : E) with ⟨u, hu⟩,
  have := ((conformal_factor_prop $ hf'.symm).2 (f' u) $ f' u).symm,
  simp only [f'.symm.coe_coe, f'.symm_apply_apply] at this, 
  rw [← f'.coe_coe, (conformal_factor_prop hf').2, ← mul_assoc] at this,
  nth_rewrite 1 ← one_mul ⟪u, u⟫ at this,
  have key := mul_right_cancel' (λ w, hu $ inner_self_eq_zero.mp w) this,
  exact ((mul_eq_one_iff_inv_eq' $ ne_of_gt (conformal_factor_prop hf'.symm).1).mp key).symm
end

lemma conformal_factor_sqrt_symm [nontrivial E] {f' : E ≃L[ℝ] F} 
  (hf' : is_conformal_map (f' : E →L[ℝ] F)) :
  conformal_factor_sqrt hf' = (conformal_factor_sqrt hf'.symm)⁻¹ :=
by rw [conformal_factor_sqrt, conformal_factor_symm hf', real.sqrt_inv, ← conformal_factor_sqrt]

lemma conformal_factor_sqrt_inv_symm [nontrivial E] {f' : E ≃L[ℝ] F} 
  (hf' : is_conformal_map (f' : E →L[ℝ] F)) :
  conformal_factor_sqrt_inv hf' = (conformal_factor_sqrt_inv hf'.symm)⁻¹ :=
by rw [conformal_factor_sqrt_inv, conformal_factor_sqrt_symm hf', ← conformal_factor_sqrt_inv]

end conformality_arithmetic

section conformal_inversion

/-- The inversion map in a sphere at `x₀` of radius `r ^ 1/2`. -/
def inversion {X : Type*} [normed_group X] [normed_space ℝ X] 
  {r : ℝ} (hr : 0 < r) (x₀ : X) : X → X := 
λ x, x₀ + (r * (∥x - x₀∥ ^ 2)⁻¹) • (x - x₀)

/-- Do we need this `≠` condition as `0⁻¹ = 0` in Lean? -/
lemma fderiv_inversion {X : Type*} [inner_product_space ℝ X] 
  {r : ℝ} (hr : 0 < r) {x₀ : X} {y x : X} (hx : x ≠ x₀) : 
  fderiv ℝ (inversion hr x₀) x y = r • (∥x - x₀∥ ^ 4)⁻¹ • 
  (∥x - x₀∥ ^ 2 • y - (2 : ℝ) • ⟪y, x - x₀⟫ • (x - x₀)) :=
begin
  have triv₁ : ⟪x - x₀, x - x₀⟫ ≠ 0 := λ w, (sub_ne_zero.mpr hx) (inner_self_eq_zero.mp w),
  have triv₂ : ∥x - x₀∥ ≠ 0 := λ w, hx (norm_sub_eq_zero_iff.mp w),
  simp only [inversion],
  rw [fderiv_const_add, fderiv_smul _ (differentiable_at_id'.sub_const _), 
      fderiv_sub_const, fderiv_id', fderiv_const_mul],
  simp only [pow_two, ← real_inner_self_eq_norm_sq],
  have minor₁ := differentiable_at_inv.mpr triv₁,
  rw [fderiv.comp, fderiv_inv],
  simp only [add_apply, smul_right_apply, smul_apply, coe_comp', function.comp_app, one_apply,
             id_apply],
  rw fderiv_inner_apply (differentiable_at_id'.sub_const x₀) (differentiable_at_id'.sub_const x₀),
  rw [fderiv_sub_const, fderiv_id'],
  simp only [id_apply, congr_arg],
  { rw [real_inner_self_eq_norm_sq, ← pow_two] at triv₁,
    nth_rewrite 2 real_inner_comm,
    simp only [smul_smul, real_inner_self_eq_norm_sq, ← pow_two, smul_sub, smul_smul],
    simp only [smul_eq_mul, mul_add, add_mul, add_smul],
    nth_rewrite 10 mul_comm,
    have : ∥x - x₀∥ ^ 2 * (∥x - x₀∥ ^ 4)⁻¹ = (∥x - x₀∥ ^ 2)⁻¹ := 
      by field_simp [triv₁]; rw ← pow_add; norm_num; rw div_self (pow_ne_zero _ triv₂),
    rw this,
    simp only [← pow_mul],
    norm_num,
    simp only [← neg_add, sub_neg_eq_add, ← sub_add, two_mul, mul_add, add_smul],
    rw [real_inner_comm, real_inner_comm, real_inner_comm, real_inner_comm],
    ring_nf,
    simp only [← add_assoc, ← sub_eq_add_neg] },
  { exact differentiable_at_inv.mpr triv₁ },
  { exact (differentiable_at_id'.sub_const x₀).inner (differentiable_at_id'.sub_const x₀) },
  { refine (differentiable_at_inv.mpr _).comp _ (differentiable_at_id'.sub_const x₀).norm_sq,
    convert triv₁,
    rw [real_inner_self_eq_norm_sq, pow_two] },  
  { apply_instance },
  { refine ((differentiable_at_inv.mpr _).comp _ 
      (differentiable_at_id'.sub_const x₀).norm_sq).const_smul _,
    convert triv₁,
    rw [real_inner_self_eq_norm_sq, pow_two] }
end

lemma is_conformal_map_fderiv_inversion_aux {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x x₀ : E} (hx : x ≠ x₀) (v : E) :
  ⟪fderiv ℝ (inversion hr x₀) x v, fderiv ℝ (inversion hr x₀) x v⟫ = 
  r ^ 2 * (∥x - x₀∥ ^ 4)⁻¹ * ⟪v, v⟫ :=
begin
  let x' := x - x₀,
  have this : ∥x'∥ ^ 4 ≠ 0 := 
    pow_ne_zero 4 (ne_of_gt $ norm_pos_iff.mpr $ λ w, (sub_ne_zero.mpr hx) w),
  simp only [← x', fderiv_inversion hr hx, real_inner_smul_left, real_inner_smul_right],
  rw [inner_sub_left, inner_sub_right],
  nth_rewrite 1 inner_sub_right,
  simp only [real_inner_smul_left, real_inner_smul_right],
  rw [real_inner_self_eq_norm_sq x', ← pow_two],
  nth_rewrite 4 real_inner_comm,
  ring_nf,
  simp only [pow_two],
  field_simp [this],
  ring
end

lemma is_conformal_map_fderiv_inversion_aux' {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x x₀ : E} (hx : x ≠ x₀) (u v : E) :
  ⟪fderiv ℝ (inversion hr x₀) x u, fderiv ℝ (inversion hr x₀) x v⟫ = 
  r ^ 2 * (∥x - x₀∥ ^ 4)⁻¹ * ⟪u, v⟫ :=
begin
  have minor₁ := is_conformal_map_fderiv_inversion_aux hr hx u,
  have minor₂ := is_conformal_map_fderiv_inversion_aux hr hx v,
  have minor₃ := is_conformal_map_fderiv_inversion_aux hr hx (u + v),
  simp only [continuous_linear_map.map_add, inner_add_left, inner_add_right] at minor₃,
  rw [minor₁, minor₂] at minor₃,
  nth_rewrite 1 real_inner_comm at minor₃,
  nth_rewrite 5 real_inner_comm at minor₃,
  simp only [mul_add, add_assoc] at minor₃,
  have minor₄ := add_left_cancel minor₃,
  simp only [← add_assoc] at minor₄,
  simpa [← mul_two] using add_right_cancel minor₄
end

lemma is_conformal_map_fderiv_inversion {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x x₀ : E} (hx : x ≠ x₀) :
  is_conformal_map (fderiv ℝ (inversion hr x₀) x) :=
begin
  have triv₁ : 0 < (∥x - x₀∥ ^ 4)⁻¹ := inv_pos.mpr 
    (pow_pos (norm_pos_iff.mpr $ λ w, (sub_ne_zero.mpr hx) w) _),
  exact (is_conformal_map_iff _).mpr ⟨r ^ 2 * (∥x - x₀∥ ^ 4)⁻¹, mul_pos (pow_pos hr _) triv₁, 
    is_conformal_map_fderiv_inversion_aux' hr hx⟩
end

lemma conformal_at_inversion {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x x₀ : E} (hx : x ≠ x₀) :
  conformal_at (inversion hr x₀) x :=
conformal_at_iff_is_conformal_map_fderiv.mpr (is_conformal_map_fderiv_inversion hr hx)

lemma conformal_factor_inversion {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x x₀ : E} (hx : x ≠ x₀) :
  conformal_factor (is_conformal_map_fderiv_inversion hr hx) = r ^ 2 * (∥x - x₀∥ ^ 4)⁻¹ :=
begin
  haveI : nontrivial E := nontrivial_of_ne x x₀ hx,
  rcases exists_ne (0 : E) with ⟨u, hu⟩,
  have triv : ⟪u, u⟫ ≠ 0 := λ w, hu (inner_self_eq_zero.mp w),
  have key := (conformal_factor_prop $ is_conformal_map_fderiv_inversion hr hx).2 u u,
  rw is_conformal_map_fderiv_inversion_aux' hr hx at key,
  exact (mul_right_cancel' triv key).symm
end

lemma conformal_factor_sqrt_inversion {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x x₀ : E} (hx : x ≠ x₀) :
  conformal_factor_sqrt (is_conformal_map_fderiv_inversion hr hx) = r * (∥x - x₀∥ ^ 2)⁻¹ :=
begin
  have : ∥x - x₀∥ ^ 4 = (∥x - x₀∥ ^ 2) ^ 2,
  { simp only [← pow_mul],
    norm_num },
  rw [conformal_factor_sqrt, conformal_factor_inversion hr hx],
  simp [this, real.sqrt_sq (sq_nonneg _), real.sqrt_sq (le_of_lt hr)]
end

lemma conformal_factor_sqrt_inv_inversion {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x x₀ : E} (hx : x ≠ x₀) :
  conformal_factor_sqrt_inv (is_conformal_map_fderiv_inversion hr hx) = r⁻¹ * ∥x - x₀∥ ^ 2 :=
by rw [conformal_factor_sqrt_inv, conformal_factor_sqrt_inversion hr hx, mul_inv', inv_inv']

lemma continuous_on_inversion {E : Type*} [inner_product_space ℝ E]
  {r : ℝ} (hr : 0 < r) {x₀ : E} {s : set E} (hs : x₀ ∉ s) : continuous_on (inversion hr x₀) s :=
begin
  rw inversion,
  simp only [← smul_smul],
  refine (continuous_on_const).add (continuous_on.const_smul 
    (continuous_on.smul _ $ continuous_on_id.sub continuous_on_const) _),
  exact continuous_on.inv' ((continuous_on.norm $ continuous_on_id.sub continuous_on_const).pow 2) 
    (λ x hx w, (ne_of_mem_of_not_mem hx hs) $ sub_eq_zero.mp $ norm_eq_zero.mp $ pow_eq_zero w)
end

-- lemma inversion_local_homeomorph {E : Type*} [inner_product_space ℝ E]
--   {r : ℝ} (hr : 0 < r) {x₀ : E} {s : set E} (hs : x₀ ∉ s) : local_homeomorph E E :=
-- { to_fun := inversion hr x₀,
--   inv_fun := inversion hr x₀,
--   source := s,
--   target := (inversion hr x₀) '' s,
--   map_source' := λ x hx, set.mem_image_of_mem _ hx,
--   map_target' := _,
--   left_inv' := _,
--   right_inv' := _,
--   open_source := _,
--   open_target := _,
--   continuous_to_fun := _,
--   continuous_inv_fun := _ }

-- { to_fun := inversion hr x₀,
--   inv_fun := inversion hr x₀,
--   left_inv := λ x, begin
--     by_cases hx : x = x₀,
--     { simp [inversion, hx] },
--     { have : ∥x - x₀∥ ≠ 0 := λ w, hx (sub_eq_zero.mp $ norm_eq_zero.mp w),
--       simp only [inversion, congr_arg, add_sub_cancel'],
--       simp only [norm_smul, smul_smul, ← smul_eq_mul, real.norm_of_nonneg (le_of_lt hr)],
--       simp only [real.norm_of_nonneg (inv_nonneg.mpr $ sq_nonneg _), smul_eq_mul],
--       simp only [← inv_pow', mul_inv', inv_inv', pow_two],
--       ring_nf,
--       field_simp [this, pow_ne_zero 2 (ne_of_gt hr)] }    
--   end,
--   right_inv := λ x, begin
--     by_cases hx : x = x₀,
--     { simp [inversion, hx] },
--     { have : ∥x - x₀∥ ≠ 0 := λ w, hx (sub_eq_zero.mp $ norm_eq_zero.mp w),
--       simp only [inversion, congr_arg, add_sub_cancel'],
--       simp only [norm_smul, smul_smul, ← smul_eq_mul, real.norm_of_nonneg (le_of_lt hr)],
--       simp only [real.norm_of_nonneg (inv_nonneg.mpr $ sq_nonneg _), smul_eq_mul],
--       simp only [← inv_pow', mul_inv', inv_inv', pow_two],
--       ring_nf,
--       field_simp [this, pow_ne_zero 2 (ne_of_gt hr)] }    
--   end,
--   continuous_to_fun := _,
--   continuous_inv_fun := _ }

end conformal_inversion
