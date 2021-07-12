import tactic
import analysis.complex.basic
import data.matrix.notation
import linear_algebra.matrix.determinant
import analysis.normed_space.inner_product

noncomputable theory

section conformal

-- Should the field `𝕜` here be `is_R_or_C` or just simply `ℝ`?

/-!
Failed to build conformal maps on general `inner_product_space`. Instead, focus on Euclidean spaces.
-/

def conformal_at 
{X Y : Type*} [inner_product_space ℝ X] [inner_product_space ℝ Y] 
(f : X → Y) (x : X) :=
∃ (f' : X →L[ℝ] Y) (c : ℝ) (lie : X ≃ₗᵢ[ℝ] Y),
has_fderiv_at f f' x ∧ ¬ c = 0 ∧ ⇑f' = (λ y, c • y) ∘ lie

def conformal 
{X Y : Type*} [inner_product_space ℝ X] [inner_product_space ℝ Y]
(f : X → Y) :=
∀ (x : X), conformal_at f x

variables {X Y : Type*} [inner_product_space ℝ X] [inner_product_space ℝ Y] 

theorem conformal_at.differentiable_at {f : X → Y} {x : X} (h : conformal_at f x) :
differentiable_at ℝ f x := let ⟨f', c, lie, h₁, h₂, h₃⟩ := h in h₁.differentiable_at

theorem conformal.differentiable {f : X → Y} (h : conformal f) :
differentiable ℝ f := λ x, (h x).differentiable_at

theorem conformal_at.id (x : X) : conformal_at id x := 
⟨continuous_linear_map.id ℝ X, 1, linear_isometry_equiv.refl ℝ X, ⟨has_fderiv_at_id _, one_ne_zero, by ext; simp⟩⟩

theorem conformal.id : conformal (id : X → X) := λ x, conformal_at.id x

theorem conformal_at.const_smul {c : ℝ} (h : ¬ c = 0) (x : X) : conformal_at (λ (x': X), c • x') x :=
⟨c • continuous_linear_map.id ℝ X, c, linear_isometry_equiv.refl ℝ X, ⟨by apply has_fderiv_at.const_smul (has_fderiv_at_id x) c; simp, h, by ext; simp⟩⟩

theorem conformal.const_smul {c : ℝ} (h : ¬ c = 0) : 
conformal (λ (x : X), c • x) := λ x, conformal_at.const_smul h x

variables {Z : Type*} [inner_product_space ℝ Z]

theorem conformal_at.comp {f : X → Y} {g : Y → Z} {x : X} 
(hf : conformal_at f x) (hg : conformal_at g (f x)) :
conformal_at (g ∘ f) x :=
begin
  rcases hf with ⟨f', cf, lief, hf₁, hf₂, hf₃⟩,
  rcases hg with ⟨g', cg, lieg, hg₁, hg₂, hg₃⟩,
  use [g'.comp f', cg * cf, lief.trans lieg],
  exact ⟨has_fderiv_at.comp x hg₁ hf₁, 
        mul_ne_zero hg₂ hf₂, 
        by ext; rw [continuous_linear_map.coe_comp' f' g', hf₃, hg₃]; 
        simp; exact smul_smul cg cf _⟩,
end

theorem conformal.comp {f : X → Y} {g : Y → Z} (hf : conformal f) (hg : conformal g) :
conformal (g ∘ f) := λ x, conformal_at.comp (hf x) (hg (f x))

theorem conformal_at_iff {f : X → Y} {x : X} {f' : X ≃L[ℝ] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) :
conformal_at f x ↔ ∃ (c : ℝ) (hc : c > 0), ∀ (u v : X), inner (f' u) (f' v) = (c : ℝ) * (inner u v) :=
begin
  split,
  {
    intros h',
    rcases h' with ⟨f₁, c₁, lie, h₁, h₂, h₃⟩,
    use [c₁ ^ 2, sq_pos_of_ne_zero _ h₂],
    intros u v,
    rw [← continuous_linear_equiv.coe_coe f', 
        ← continuous_linear_equiv.coe_def_rev f', has_fderiv_at.unique h h₁, h₃],
    simp only [function.comp_apply, real_inner_smul_left, real_inner_smul_right, 
               linear_isometry_equiv.inner_map_map],
    rw [← mul_assoc, pow_two],
  },
  {
    intros h',
    rcases h' with ⟨c₁, hc₁, huv⟩,
    let c := real.sqrt c₁⁻¹,
    have hc : ¬ c = 0 := λ w, by simp only [c] at w; 
      exact (real.sqrt_ne_zero'.mpr $ inv_pos.mpr hc₁) w,
    let c_map := linear_equiv.smul_of_ne_zero ℝ Y c hc,
    let f₁ := f'.to_linear_equiv.trans c_map,
    have minor : ⇑f₁ = (λ (y : Y), c • y) ∘ f' := rfl,
    have minor' : ⇑f' = (λ (y : Y), c⁻¹ • y) ∘ f₁ := by ext;
      rw [minor, function.comp_apply, function.comp_apply, 
          smul_smul, inv_mul_cancel hc, one_smul],
    have key : ∀ (u v : X), inner (f₁ u) (f₁ v) = inner u v := λ u v, by
      rw [minor, function.comp_app, function.comp_app, real_inner_smul_left, 
          real_inner_smul_right, huv u v, ← mul_assoc, ← mul_assoc, 
          real.mul_self_sqrt $ le_of_lt $ inv_pos.mpr hc₁, 
          inv_mul_cancel $ ne_of_gt hc₁, one_mul],
    exact ⟨f'.to_continuous_linear_map, c⁻¹, f₁.isometry_of_inner key, 
            ⟨h, inv_ne_zero hc, minor'⟩⟩,
  },
end

def conformal_at.char_fun {f : X → Y} (x : X) {f' : X ≃L[ℝ] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) (H : conformal_at f x) : ℝ :=
by choose c hc huv using (conformal_at_iff h).mp H; exact c

def inner_product_angle (u v : X) : ℝ :=
inner u v / (∥u∥ * ∥v∥)
@[simp] theorem inner_product_angle.def {u v : X} :
inner_product_angle u v = inner u v / (∥u∥ * ∥v∥) := rfl

theorem conformal_at_preserves_angle {f : X → Y} {x : X} {f' : X ≃L[ℝ] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) (H : conformal_at f x) :
∀ (u v : X), inner_product_angle (f' u) (f' v) = (inner_product_angle u v : ℝ) :=
begin
  intros u v, 
  rcases H with ⟨f₁, c₁, lie, h₁, h₂, h₃⟩,
  have minor : ¬ ∥c₁∥ = 0 := λ w, h₂ (norm_eq_zero.mp w),
  have : f'.to_continuous_linear_map = f₁ := has_fderiv_at.unique h h₁,
  rw [← continuous_linear_equiv.coe_coe f', ← continuous_linear_equiv.coe_def_rev f'],
  repeat {rw inner_product_angle.def},
  rw [this, h₃],
  repeat {rw function.comp_apply},
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, 
      linear_isometry_equiv.inner_map_map],
  repeat {rw [norm_smul, linear_isometry_equiv.norm_map]},
  rw [← mul_assoc],
  exact calc c₁ * c₁ * inner u v / (∥c₁∥ * ∥u∥ * ∥c₁∥ * ∥v∥) 
          = c₁ * c₁ * inner u v / (∥c₁∥ * ∥c₁∥ * ∥u∥ * ∥v∥) : by simp only [mul_comm, mul_assoc]
      ... = c₁ * c₁ * inner u v / (abs c₁ * abs c₁ * ∥u∥ * ∥v∥) : by rw [real.norm_eq_abs]
      ... = c₁ * c₁ * inner u v / (c₁ * c₁ * ∥u∥ * ∥v∥) : by rw [← pow_two, ← sq_abs, pow_two]
      ... = c₁ * (c₁ * inner u v) / (c₁ * (c₁ * (∥u∥ * ∥v∥))) : by simp only [mul_assoc]
      ... = (c₁ * inner u v) / (c₁ * (∥u∥ * ∥v∥)) : by rw mul_div_mul_left _ _ h₂
      ... = inner u v / (∥u∥ * ∥v∥) : by rw mul_div_mul_left _ _ h₂,
end

end conformal

section complex_conformal

open complex

variables {f : ℂ → ℂ} {z : ℂ}

-- This is a baby version of the Jacobian of a real differentiable complex function

def complex_jacobian_at (h : differentiable_at ℝ f z) : matrix (fin 2) (fin 2) ℝ :=
![![fderiv ℝ (re ∘ f) z 1, fderiv ℝ (re ∘ f) z I], ![fderiv ℝ (im ∘ f) z 1, fderiv ℝ (im ∘ f) z I]]

@[simp] theorem complex_jacobian_at.def (h : differentiable_at ℝ f z) :
complex_jacobian_at h = ![![fderiv ℝ (re ∘ f) z 1, fderiv ℝ (re ∘ f) z I], 
                          ![fderiv ℝ (im ∘ f) z 1, fderiv ℝ (im ∘ f) z I]] := rfl

@[simp] theorem complex_jacobian_at_det_eq (h : differentiable_at ℝ f z) :
(complex_jacobian_at h).det = (fderiv ℝ (re ∘ f) z 1) * fderiv ℝ (im ∘ f) z I - (fderiv ℝ (re ∘ f) z I) * fderiv ℝ (im ∘ f) z 1 :=
begin
  rw matrix.det_succ_row_zero, repeat {rw [fin.sum_univ_succ]}, simp_rw [fin.sum_univ_zero],
  simp, rw ← sub_eq_add_neg _ _,
end

-- Time saving stuff

@[simp] theorem cmatrix_two_apply00 (a b c d : ℂ) : ![![a, b], ![c, d]] 0 0 = a := rfl
@[simp] theorem cmatrix_two_apply01 (a b c d : ℂ) : ![![a, b], ![c, d]] 0 1 = b := rfl
@[simp] theorem cmatrix_two_apply10 (a b c d : ℂ) : ![![a, b], ![c, d]] 1 0 = c := rfl
@[simp] theorem cmatrix_two_apply11 (a b c d : ℂ) : ![![a, b], ![c, d]] 1 1 = d := rfl
@[simp] theorem rmatrix_two_apply00 (a b c d : ℝ) : ![![a, b], ![c, d]] 0 0 = a := rfl
@[simp] theorem rmatrix_two_apply01 (a b c d : ℝ) : ![![a, b], ![c, d]] 0 1 = b := rfl
@[simp] theorem rmatrix_two_apply10 (a b c d : ℝ) : ![![a, b], ![c, d]] 1 0 = c := rfl
@[simp] theorem rmatrix_two_apply11 (a b c d : ℝ) : ![![a, b], ![c, d]] 1 1 = d := rfl

@[simp] theorem cvec_two_apply (a b : ℂ) : ![a, b] 0 = a := rfl
@[simp] theorem cvec_two_apply' (a b : ℂ) : ![a, b] 1 = b := rfl
@[simp] theorem rvec_two_apply (a b : ℝ) : ![a, b] 0 = a := rfl
@[simp] theorem rvec_two_apply' (a b : ℝ) : ![a, b] 1 = b := rfl

lemma quick_re (z : ℂ) : has_fderiv_at re re_clm z := re_clm.has_fderiv_at
lemma quick_re' (z : ℂ) : differentiable_at ℝ re z := (quick_re z).differentiable_at
lemma quick_re'' (z : ℂ) : fderiv ℝ re z = re_clm := (quick_re z).fderiv
lemma quick_re_comp (z z': ℂ) (h : differentiable_at ℝ f z) : (fderiv ℝ f z z').re = fderiv ℝ (re ∘ f) z z' :=
begin
  rw fderiv.comp z (quick_re' $ f z) h,
  simp only [function.app, function.comp_app, continuous_linear_map.coe_comp'],
  rw [quick_re'' (f z), re_clm_apply],
end


lemma quick_im (z : ℂ) : has_fderiv_at im im_clm z := im_clm.has_fderiv_at
lemma quick_im' (z : ℂ) : differentiable_at ℝ im z := (quick_im z).differentiable_at
lemma quick_im'' (z : ℂ) : fderiv ℝ im z = im_clm := (quick_im z).fderiv
lemma quick_im_comp (z z': ℂ) (h : differentiable_at ℝ f z) : (fderiv ℝ f z z').im = fderiv ℝ (im ∘ f) z z' :=
begin
  rw fderiv.comp z (quick_im' $ f z) h,
  simp only [function.app, function.comp_app, continuous_linear_map.coe_comp'],
  rw [quick_im'' (f z), im_clm_apply],
end
/-!
## Important:
The following two lemmas are modified versions of Cauchy-Riemann equations written by [hrmacbeth](https://github.com/hrmacbeth) 
in the file `complex.basic` in the `complex-diff` branch of mathlib. Some theorems in that branch conflict with
the current mathlib, which contains the most essential `linear_isometry_equiv` we need.
-/

/-- First Cauchy-Riemann equation: for a complex-differentiable function `f`, the `x`-derivative of
`re ∘ f` is equal to the `y`-derivative of `im ∘ f`. -/
theorem fderiv_re_comp_eq_fderiv_im_comp (h : differentiable_at ℂ f z) :
  fderiv ℝ (re ∘ f) z 1 = fderiv ℝ (im ∘ f) z I :=
begin
  let hz := h.has_fderiv_at.restrict_scalars ℝ,
  have hI : I = I • 1 := by simp,
  simp only [continuous_linear_map.coe_comp', continuous_linear_map.coe_restrict_scalars', function.comp_app, 
            ((quick_re $ f z).comp z hz).fderiv, ((quick_im $ f z).comp z hz).fderiv],
  rw [hI, continuous_linear_map.map_smul],
  simp,
end

/-- Second Cauchy-Riemann equation: for a complex-differentiable function `f`, the `x`-derivative of
`im ∘ f` is equal to the negative of the `y`-derivative of `re ∘ f`. -/
theorem fderiv_re_comp_eq_neg_fderiv_im_comp (h : differentiable_at ℂ f z) :
  fderiv ℝ (re ∘ f) z I = - fderiv ℝ (im ∘ f) z 1 :=
begin
  have hz := h.has_fderiv_at.restrict_scalars ℝ,
  have hI : I = I • 1 := by simp,
  simp only [continuous_linear_map.coe_comp', continuous_linear_map.coe_restrict_scalars', function.comp_app,
            ((quick_re $ f z).comp z hz).fderiv, ((quick_im $ f z).comp z hz).fderiv],
  rw [hI, continuous_linear_map.map_smul],
  simp,
end

theorem real_fderiv_to_matrix (h : differentiable_at ℝ f z) : 
(linear_map.to_matrix complex.basis_one_I complex.basis_one_I) (fderiv ℝ f z) = complex_jacobian_at h :=
begin
  ext,
  rw linear_map.to_matrix_apply _ _ _ _ _,
  simp only [coe_basis_one_I, coe_basis_one_I_repr],
  fin_cases i,
  { 
    fin_cases j,
    {
      repeat {rw cvec_two_apply}, rw rvec_two_apply,
      simp only [complex_jacobian_at, rmatrix_two_apply00],
      exact quick_re_comp z 1 h,
    },
    {
      repeat {rw cvec_two_apply'}, rw rvec_two_apply,
      simp only [complex_jacobian_at, rmatrix_two_apply01],
      exact quick_re_comp z I h,
    },
  },
  { 
    fin_cases j,
    {
      repeat {rw cvec_two_apply}, rw rvec_two_apply',
      simp only [complex_jacobian_at, rmatrix_two_apply10],
      exact quick_im_comp z 1 h,
    },
    {
      repeat {rw cvec_two_apply}, rw rvec_two_apply',
      simp only [complex_jacobian_at, rmatrix_two_apply11],
      exact quick_im_comp z I h,
    },
  },
end

theorem fderiv_decomp (h : differentiable_at ℂ f z) :
fderiv ℂ f z 1 = fderiv ℝ (re ∘ f) z 1 + (fderiv ℝ (im ∘ f) z 1) * I :=
begin
  let h' := h.restrict_scalars ℝ,
  have : fderiv ℂ f z 1 = (fderiv ℂ f z 1).re + (fderiv ℂ f z 1).im * I := 
    by simp only [re_add_im],
  have triv := has_fderiv_at.unique h'.has_fderiv_at (h.has_fderiv_at.restrict_scalars ℝ),
  rw [this, ← quick_re_comp z 1 h', ← quick_im_comp z 1 h', 
      triv, continuous_linear_map.coe_restrict_scalars'],
end

theorem fderiv_decomp' (h : differentiable_at ℂ f z) :
fderiv ℂ f z 1 = (fderiv ℝ f z 1).re + (fderiv ℝ f z 1).im * I :=
(quick_re_comp z 1 $ h.restrict_scalars ℝ).symm ▸ ((quick_im_comp z 1 $ h.restrict_scalars ℝ).symm ▸ fderiv_decomp h)

theorem complex_jacobian_det_eq_fderiv_norm_sq (h : differentiable_at ℂ f z) :
(complex_jacobian_at $ h.restrict_scalars ℝ).det = norm_sq (fderiv ℂ f z 1) :=
begin
  let h' := h.restrict_scalars ℝ,
  rw [complex_jacobian_at_det_eq, ← fderiv_re_comp_eq_fderiv_im_comp h, 
    fderiv_re_comp_eq_neg_fderiv_im_comp h],
  rw [← neg_mul_eq_neg_mul, sub_neg_eq_add, 
      ← quick_re_comp z 1 h', ← quick_im_comp z 1 h', fderiv_decomp' h],
  simp only [norm_sq_apply, re_add_im],
end

@[simp] theorem complex_jacobian_det_eq_zero_iff (h : differentiable_at ℂ f z) :
(complex_jacobian_at $ h.restrict_scalars ℝ).det = 0 ↔ fderiv ℂ f z 1 = 0 := by rw complex_jacobian_det_eq_fderiv_norm_sq h; simp

@[simp] theorem complex_jacobian_det_ne_zero_iff (h : differentiable_at ℂ f z) :
¬ (complex_jacobian_at $ h.restrict_scalars ℝ).det = 0 ↔ ¬ fderiv ℂ f z 1 = 0 := not_iff_not_of_iff $ complex_jacobian_det_eq_zero_iff h

/-
I could only do this for holomorphic/antiholomorphic + nonzero Jacobian → conformal, but couldn't show
conformal + nonzero Jacobian → holomorphic ∨ antiholomorphic because Cauchy-Riemann → holomorphic
is not proved yet.
-/

theorem conformal_at_if_holomorph_deriv_ne_zero
{f : ℂ → ℂ} {z : ℂ} (h : differentiable_at ℝ f z) (H : ¬ (complex_jacobian_at h).det = 0) :
(differentiable_at ℂ f z ∨ ∃ (g : ℂ → ℂ) (hg : differentiable_at ℂ g z), f = conj ∘ g) →
conformal_at f z := λ p,
begin
  cases p,
  {

  },
  {
    sorry,
  },
end

end complex_conformal

-- def conformal_at 
-- (𝕜 : Type*) [is_R_or_C 𝕜] {X Y : Type*} 
-- [inner_product_space 𝕜 X] [normed_space ℝ X] [is_scalar_tower ℝ 𝕜 X] 
-- [inner_product_space 𝕜 Y] [normed_space ℝ Y] [is_scalar_tower ℝ 𝕜 Y] 
-- (f : X → Y) (x : X) :=
-- ∃ (f' : X →L[ℝ] Y) (c : 𝕜) (lie : X ≃ₗᵢ[𝕜] Y),
-- has_fderiv_at f f' x ∧ ¬ c = 0 ∧ ⇑f' = (λ y, c • y) ∘ lie

-- def conformal 
-- (𝕜 : Type*) [is_R_or_C 𝕜] {X Y : Type*} 
-- [inner_product_space 𝕜 X] [normed_space ℝ X] [is_scalar_tower ℝ 𝕜 X] 
-- [inner_product_space 𝕜 Y] [normed_space ℝ Y] [is_scalar_tower ℝ 𝕜 Y] 
-- (f : X → Y) :=
-- ∀ (x : X), conformal_at 𝕜 f x

-- variables {𝕜 : Type*} [is_R_or_C 𝕜] {X Y : Type*} 
-- [inner_product_space 𝕜 X] [normed_space ℝ X] [is_scalar_tower ℝ 𝕜 X] 
-- [inner_product_space 𝕜 Y] [normed_space ℝ Y] [is_scalar_tower ℝ 𝕜 Y]

-- theorem conformal_at.differentiable_at {f : X → Y} {x : X} (h : conformal_at 𝕜 f x) :
-- differentiable_at ℝ f x := let ⟨f', c, lie, h₁, h₂, h₃⟩ := h in h₁.differentiable_at

-- theorem conformal.differentiable {f : X → Y} (h : conformal 𝕜 f) :
-- differentiable ℝ f := λ x, (h x).differentiable_at

-- theorem conformal_at.id (x : X) : conformal_at 𝕜 id x := 
-- ⟨continuous_linear_map.id ℝ X, 1, linear_isometry_equiv.refl ℝ X, ⟨has_fderiv_at_id _, one_ne_zero, by ext; simp⟩⟩

-- theorem conformal.id : conformal 𝕜 (id : X → X) := λ x, conformal_at.id x

-- theorem conformal_at.const_smul {c : 𝕜} (h : ¬ c = 0) (x : X) : conformal_at 𝕜 (λ (x': X), c • x') x :=
-- ⟨c • continuous_linear_map.id ℝ X, c, linear_isometry_equiv.refl ℝ X, ⟨by apply has_fderiv_at.const_smul (has_fderiv_at_id x) c; simp, h, by ext; simp⟩⟩

-- theorem conformal.const_smul {c : 𝕜} (h : ¬ c = 0) : 
-- conformal 𝕜 (λ (x : X), c • x) := λ x, conformal_at.const_smul h x

-- variables {Z : Type*} [inner_product_space 𝕜 Z] [normed_space ℝ Z] [is_scalar_tower ℝ 𝕜 Z]

-- theorem conformal_at.comp {f : X → Y} {g : Y → Z} {x : X} 
-- (hf : conformal_at 𝕜 f x) (hg : conformal_at 𝕜 g (f x)) :
-- conformal_at 𝕜 (g ∘ f) x :=
-- begin
--   rcases hf with ⟨f', cf, lief, hf₁, hf₂, hf₃⟩,
--   rcases hg with ⟨g', cg, lieg, hg₁, hg₂, hg₃⟩,
--   use [g'.comp f', cg * cf, lief.trans lieg],
--   exact ⟨has_fderiv_at.comp x hg₁ hf₁, 
--         mul_ne_zero hg₂ hf₂, 
--         by ext; rw [continuous_linear_map.coe_comp' f' g', hf₃, hg₃]; 
--         simp; exact smul_smul cg cf _⟩,
-- end

-- theorem conformal.comp {f : X → Y} {g : Y → Z} (hf : conformal 𝕜 f) (hg : conformal 𝕜 g) :
-- conformal 𝕜 (g ∘ f) := λ x, conformal_at.comp (hf x) (hg (f x))

-- theorem conformal_at_iff {f : X → Y} {x : X} {f' : X ≃L[ℝ] Y}
-- (h : has_fderiv_at f f'.to_continuous_linear_map x) :
-- conformal_at 𝕜 f x ↔ ∃ (c : ℝ) (hc : c > 0), ∀ (u v : X), inner (f' u) (f' v) = (c : 𝕜) * (inner u v) :=
-- begin
--   split,
--   {
--     sorry,
--     -- intros h',
--     -- rcases h' with ⟨f₁, c₁, lie, h₁, h₂, h₃⟩,
--     -- use [is_R_or_C.norm_sq c₁, is_R_or_C.norm_sq_pos.mpr h₂],
--     -- intros u v,
--     -- rw [← continuous_linear_equiv.coe_coe f', ← continuous_linear_equiv.coe_def_rev f'],
--     -- rw [has_fderiv_at.unique h h₁, h₃],
--     -- simp only [function.comp_apply, inner_smul_left, inner_smul_right, 
--     --            linear_isometry_equiv.inner_map_map],
--     -- rw ← mul_assoc, nth_rewrite 1 mul_comm, rw is_R_or_C.conj_mul_eq_norm_sq_left,
--   },
--   {
--     intros H,
--     rcases H with ⟨c₁, hc₁, huv⟩,
--     have hc₁' : ¬ (c₁ : 𝕜) = 0 := λ w, (ne_of_gt hc₁) (is_R_or_C.of_real_eq_zero.mp w),
--     let c := real.sqrt c₁⁻¹,
--     have hc : ¬ c = 0 := λ w, by simp only [c] at w; exact (real.sqrt_ne_zero'.mpr $ inv_pos.mpr hc₁) w,
--     have hc' : c • c • (c₁ : 𝕜)= 1 := by 
--       repeat {rw [is_R_or_C.of_real_smul, 
--                 ← is_R_or_C.of_real_mul]}; simp only [c];
--       rw [← mul_assoc, real.mul_self_sqrt $ le_of_lt $ inv_pos.mpr hc₁, 
--             inv_mul_cancel $ ne_of_gt hc₁];
--       exact is_R_or_C.of_real_one,
--     let c_map := linear_equiv.smul_of_ne_zero ℝ Y c hc,
--     let f₁ := f'.to_linear_equiv.trans c_map,
--     have : (λ (y : Y), (c : 𝕜) • y) = (λ (y : Y), c • y) := by ext; rw [is_R_or_C.of_real_alg, smul_assoc, one_smul],
--     have minor : ⇑f₁ = (λ (y : Y), (c : 𝕜) • y) ∘ f' := by rw this; refl,
--     have minor' : ⇑f' = (λ (y : Y), c⁻¹ • y) ∘ f₁ := by ext; rw this at minor;
--       rw [minor, function.comp_apply, function.comp_apply, smul_smul, inv_mul_cancel hc, one_smul],
--     have key : ∀ (u v : X), inner (f₁ u) (f₁ v) = inner u v := λ u v, begin
--       rw [minor], simp_rw [function.comp_app], 
--       rw [inner_smul_real_left, inner_smul_real_right, 
--           huv u v, ← smul_mul_assoc, ← smul_mul_assoc],
--       rw hc', exact one_mul _,
--     end,
--     -- haveI restr_to_real : inner_product_space ℝ X := inner_product_space.is_R_or_C_to_real 𝕜 X,
--     -- haveI restr_to_real' : inner_product_space ℝ Y := inner_product_space.is_R_or_C_to_real 𝕜 Y,
--     let f₂ : X ≃ₗᵢ[ℝ] Y := ⟨f₁, λ x, by simp only [norm_eq_sqrt_inner, key]⟩,
--     use [f'.to_continuous_linear_map, (c : 𝕜)⁻¹, f₂],
--     -- exact ⟨h, inv_ne_zero hc, minor'⟩,
--   },
-- end

-- def conformal_at.char_fun {f : X → Y} (x : X) {f' : X ≃L[ℝ] Y}
-- (h : has_fderiv_at f f'.to_continuous_linear_map x) (H : conformal_at 𝕜 f x) : ℝ :=
-- by choose c hc huv using (conformal_at_iff h).mp H; exact c

-- def inner_product_angle {E : Type*} [inner_product_space 𝕜 E] (u v : E) : 𝕜 :=
-- inner u v / (∥u∥ * ∥v∥)
-- @[simp] theorem inner_product_angle.def {E : Type*} [inner_product_space 𝕜 E] (u v : E) :
-- inner_product_angle u v = (inner u v / (∥u∥ * ∥v∥) : 𝕜) := rfl

-- theorem conformal_at_preserves_angle {f : X → Y} {x : X} {f' : X ≃L[𝕜] Y}
-- (h : has_fderiv_at f f'.to_continuous_linear_map x) (H : conformal_at 𝕜 f x) :
-- ∀ (u v : X), inner_product_angle (f' u) (f' v) = (inner_product_angle u v : 𝕜) :=
-- begin
--   intros u v, 
--   rcases H with ⟨f₁, c₁, lie, h₁, h₂, h₃⟩,
--   have minor : ¬ ∥c₁∥ = 0 := λ w, h₂ (norm_eq_zero.mp w),
--   have minor' : ¬ (∥c₁∥ : 𝕜) = 0 := λ w, minor (is_R_or_C.of_real_eq_zero.mp w),
--   have : f'.to_continuous_linear_map = f₁ := has_fderiv_at.unique h h₁,
--   rw [← continuous_linear_equiv.coe_coe f', ← continuous_linear_equiv.coe_def_rev f'],
--   repeat {rw inner_product_angle.def},
--   rw [this, h₃],
--   repeat {rw function.comp_apply},
--   rw [inner_smul_left, inner_smul_right, ← mul_assoc, 
--       linear_isometry_equiv.inner_map_map, is_R_or_C.conj_mul_eq_norm_sq_left],
--   repeat {rw [norm_smul, linear_isometry_equiv.norm_map]},
--   rw [is_R_or_C.norm_sq_eq_def', ← is_R_or_C.of_real_mul, ← mul_assoc],
--   nth_rewrite 2 mul_comm,
--   rw [← mul_assoc, pow_two],
--   repeat {rw [is_R_or_C.of_real_mul, mul_assoc]},
--   repeat {rw mul_div_mul_left _ _ minor'},
-- end

-- variables {f : ℂ → ℂ} {z : ℂ}

-- -- This is a baby version of the Jacobian of a real differentiable complex function

-- def complex_jacobian_at (h : differentiable_at ℝ f z) : matrix (fin 2) (fin 2) ℝ :=
-- ![![fderiv ℝ (re ∘ f) z 1, fderiv ℝ (re ∘ f) z I], ![fderiv ℝ (im ∘ f) z 1, fderiv ℝ (im ∘ f) z I]]

-- @[simp] theorem complex_jacobian_at.def (h : differentiable_at ℝ f z) :
-- complex_jacobian_at h = ![![fderiv ℝ (re ∘ f) z 1, fderiv ℝ (re ∘ f) z I], 
--                           ![fderiv ℝ (im ∘ f) z 1, fderiv ℝ (im ∘ f) z I]] := rfl

-- def complex_jacobian_det_at (h : differentiable_at ℝ f z) : ℝ :=
-- (fderiv ℝ (re ∘ f) z 1) * fderiv ℝ (im ∘ f) z I - (fderiv ℝ (re ∘ f) z I) * fderiv ℝ (im ∘ f) z 1

-- variables (h : differentiable_at ℝ f z)

-- @[simp] theorem complex_jacobian_at_det_eq (h : differentiable_at ℝ f z) :
-- (complex_jacobian_at h).det = (fderiv ℝ (re ∘ f) z 1) * fderiv ℝ (im ∘ f) z I - (fderiv ℝ (re ∘ f) z I) * fderiv ℝ (im ∘ f) z 1 :=
-- begin
--   rw matrix.det_succ_row_zero, repeat {rw [fin.sum_univ_succ]}, simp_rw [fin.sum_univ_zero],
--   simp, rw ← sub_eq_add_neg _ _,
-- end

-- @[simp] theorem cmatrix_two_apply00 (a b c d : ℂ) : ![![a, b], ![c, d]] 0 0 = a := rfl
-- @[simp] theorem cmatrix_two_apply01 (a b c d : ℂ) : ![![a, b], ![c, d]] 0 1 = b := rfl
-- @[simp] theorem cmatrix_two_apply10 (a b c d : ℂ) : ![![a, b], ![c, d]] 1 0 = c := rfl
-- @[simp] theorem cmatrix_two_apply11 (a b c d : ℂ) : ![![a, b], ![c, d]] 1 1 = d := rfl
-- @[simp] theorem rmatrix_two_apply00 (a b c d : ℝ) : ![![a, b], ![c, d]] 0 0 = a := rfl
-- @[simp] theorem rmatrix_two_apply01 (a b c d : ℝ) : ![![a, b], ![c, d]] 0 1 = b := rfl
-- @[simp] theorem rmatrix_two_apply10 (a b c d : ℝ) : ![![a, b], ![c, d]] 1 0 = c := rfl
-- @[simp] theorem rmatrix_two_apply11 (a b c d : ℝ) : ![![a, b], ![c, d]] 1 1 = d := rfl

-- @[simp] theorem cvec_two_apply (a b : ℂ) : ![a, b] 0 = a := rfl
-- @[simp] theorem cvec_two_apply' (a b : ℂ) : ![a, b] 1 = b := rfl
-- @[simp] theorem rvec_two_apply (a b : ℝ) : ![a, b] 0 = a := rfl
-- @[simp] theorem rvec_two_apply' (a b : ℝ) : ![a, b] 1 = b := rfl

-- theorem real_fderiv_to_matrix (h : differentiable_at ℝ f z) (x : ℂ) : 
-- (linear_map.to_matrix complex.basis_one_I complex.basis_one_I) (fderiv ℝ f z) = complex_jacobian_at h :=
-- begin
--   let h' := h.restrict_scalars ℝ,
--   ext,
--   rw linear_map.to_matrix_apply _ _ _ _ _,
--   simp only [coe_basis_one_I, coe_basis_one_I_repr],
--   fin_cases i,
--   { 
--     fin_cases j,
--     repeat {rw cvec_two_apply}, rw rvec_two_apply, 
--     simp only [complex_jacobian_at, rmatrix_two_apply00],
--     sorry,
--   },
--   { sorry, },
-- end

-- theorem complex_jacobian_det_eq_fderiv_norm_sq (h : differentiable_at ℝ f z) :
-- complex_jacobian_det_at h = norm_sq (fderiv ℂ f z 1) :=
-- begin
--   sorry,
-- end

-- @[simp] theorem complex_jacobian_det_eq_zero_iff (h : differentiable_at ℝ f z) :
-- complex_jacobian_det_at h = 0 ↔ fderiv ℂ f z 1 = 0 := by rw complex_jacobian_det_eq_fderiv_norm_sq h; simp

-- @[simp] theorem complex_jacobian_det_ne_zero_iff (h : differentiable_at ℝ f z) :
-- ¬ complex_jacobian_det_at h = 0 ↔ ¬ fderiv ℂ f z 1 = 0 := not_iff_not_of_iff $ complex_jacobian_det_eq_zero_iff h

-- theorem conformal_at_iff_holomorph_deriv_ne_zero
-- {f : ℂ → ℂ} {z : ℂ} (h : differentiable_at ℝ f z) :
-- ¬ deriv f z = 0 ↔ conformal_at ℝ f z :=
-- begin
--   split,
--   {

--   },
--   sorry,
-- end

