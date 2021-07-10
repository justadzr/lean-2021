import tactic
import analysis.complex.basic
import analysis.normed_space.inner_product

noncomputable theory

namespace conformal

def conformal_at 
(𝕜 : Type*) [is_R_or_C 𝕜] {X Y : Type*} 
[inner_product_space 𝕜 X] [inner_product_space 𝕜 Y] (f : X → Y) (x : X) :=
∃ (f' : X →L[𝕜] Y) (c : 𝕜) (lie : X ≃ₗᵢ[𝕜] Y), 
has_fderiv_at f f' x ∧ ¬ c = 0 ∧ ⇑f' = (λ y, c • y) ∘ lie

def conformal (𝕜 : Type*) [is_R_or_C 𝕜] {X Y : Type*} 
[inner_product_space 𝕜 X] [inner_product_space 𝕜 Y] (f : X → Y) :=
∀ (x : X), conformal_at 𝕜 f x

variables {𝕜 : Type*} [is_R_or_C 𝕜] {X Y : Type*} [inner_product_space 𝕜 X] [inner_product_space 𝕜 Y]

theorem conformal_at.differentiable_at {f : X → Y} {x : X} (h : conformal_at 𝕜 f x) :
differentiable_at 𝕜 f x := let ⟨f', c, lie, h₁, h₂, h₃⟩ := h in h₁.differentiable_at

theorem conformal.differentiable {f : X → Y} (h : conformal 𝕜 f) :
differentiable 𝕜 f := λ x, (h x).differentiable_at

theorem conformal_at.id (x : X) : conformal_at 𝕜 id x := 
⟨continuous_linear_map.id 𝕜 X, 1, linear_isometry_equiv.refl 𝕜 X, ⟨has_fderiv_at_id _, one_ne_zero, by ext; simp⟩⟩

theorem conformal.id : conformal 𝕜 (id : X → X) := λ x, conformal_at.id x

theorem conformal_at.const_smul {c : 𝕜} (h : ¬ c = 0) (x : X) : conformal_at 𝕜 (λ (x': X), c • x') x :=
⟨c • continuous_linear_map.id 𝕜 X, c, linear_isometry_equiv.refl 𝕜 X, ⟨by apply has_fderiv_at.const_smul (has_fderiv_at_id x) c; simp, h, by ext; simp⟩⟩

theorem conformal.const_smul {c : 𝕜} (h : ¬ c = 0) : 
conformal 𝕜 (λ (x : X), c • x) := λ x, conformal_at.const_smul h x

variables {Z : Type*} [inner_product_space 𝕜 Z]

theorem conformal_at.comp {f : X → Y} {g : Y → Z} {x : X} 
(hf : conformal_at 𝕜 f x) (hg : conformal_at 𝕜 g (f x)) :
conformal_at 𝕜 (g ∘ f) x :=
begin
  rcases hf with ⟨f', cf, lief, hf₁, hf₂, hf₃⟩,
  rcases hg with ⟨g', cg, lieg, hg₁, hg₂, hg₃⟩,
  use [g'.comp f', cg * cf, lief.trans lieg],
  exact ⟨has_fderiv_at.comp x hg₁ hf₁, 
        mul_ne_zero hg₂ hf₂, 
        by ext; rw [continuous_linear_map.coe_comp' f' g', hf₃, hg₃]; 
        simp; exact smul_smul cg cf _⟩,
end

theorem conformal.comp {f : X → Y} {g : Y → Z} (hf : conformal 𝕜 f) (hg : conformal 𝕜 g) :
conformal 𝕜 (g ∘ f) := λ x, conformal_at.comp (hf x) (hg (f x))

theorem conformal_at_iff {f : X → Y} {x : X} {f' : X ≃L[𝕜] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) :
conformal_at 𝕜 f x ↔ ∃ (c : ℝ) (hc : c > 0), ∀ (u v : X), inner (f' u) (f' v) = (c : 𝕜) * (inner u v) :=
begin
  split,
  {
    intros h',
    rcases h' with ⟨f₁, c₁, lie, h₁, h₂, h₃⟩,
    use [is_R_or_C.norm_sq c₁, is_R_or_C.norm_sq_pos.mpr h₂],
    intros u v,
    rw [← continuous_linear_equiv.coe_coe f', ← continuous_linear_equiv.coe_def_rev f'],
    rw [has_fderiv_at.unique h h₁, h₃],
    simp, rw [inner_smul_left, inner_smul_right], 
    simp, rw [← mul_assoc, is_R_or_C.conj_mul_eq_norm_sq_left c₁],
  },
  {
    intros H,
    rcases H with ⟨c₁, Hc₁, Huv⟩,
    have hc₁ : ¬ (c₁ : 𝕜) = 0 := λ w, (ne_of_gt Hc₁) (is_R_or_C.of_real_eq_zero.mp w),
    let c := ((real.sqrt c₁)⁻¹ : 𝕜),
    have hc : ¬ c = 0 := λ w, by simp at w; exact (real.sqrt_ne_zero'.mpr Hc₁) w,
    have hc' : ↑(is_R_or_C.norm_sq c) * (c₁ : 𝕜) = 1 :=
    begin
      simp, rw [is_R_or_C.norm_sq_eq_def'],
      simp, rw [← is_R_or_C.of_real_mul, real.mul_self_sqrt (le_of_lt Hc₁)],
      exact inv_mul_cancel hc₁,
    end,
    let c_map := linear_equiv.smul_of_ne_zero 𝕜 Y c hc,
    let f₁ := f'.to_linear_equiv.trans c_map,
    have minor : ⇑f₁ = (λ (y : Y), c • y) ∘ f' := rfl,
    have minor' : ⇑f' = (λ (y : Y), c⁻¹ • y) ∘ f₁ := by ext;
      rw [minor, function.comp_apply, function.comp_apply, smul_smul, inv_mul_cancel hc, one_smul],
    have key : ∀ (u v : X), inner (f₁ u) (f₁ v) = inner u v := λ u v, begin
      rw minor,
      exact calc inner (((λ (y : Y), c • y) ∘ f') u) (((λ (y : Y), c • y) ∘ f') v) = inner (c • (f' u)) (c • (f' v)) : by rw function.comp
      ... = (is_R_or_C.conj c) * c * inner (f' u) (f' v) : by rw [inner_smul_left, inner_smul_right, mul_assoc]
      ... = ↑(is_R_or_C.norm_sq c) * inner (f' u) (f' v) : by rw is_R_or_C.conj_mul_eq_norm_sq_left
      ... = ↑(is_R_or_C.norm_sq c) * ↑c₁ * inner u v : by rw [Huv u v, mul_assoc]
      ... = inner u v : by rw [hc', one_mul],
    end,
    use [f'.to_continuous_linear_map, c⁻¹, f₁.isometry_of_inner key],
    exact ⟨h, inv_ne_zero hc, minor'⟩,
  },
end

def inner_product_angle {E : Type*} [inner_product_space 𝕜 E] (u v : E) : 𝕜 :=
inner u v / (∥u∥ * ∥v∥)
@[simp] theorem inner_product_angle.def {E : Type*} [inner_product_space 𝕜 E] (u v : E) :
inner_product_angle u v = (inner u v / (∥u∥ * ∥v∥) : 𝕜) := rfl

theorem conformal_at_angle {f : X → Y} {x : X} {f' : X ≃L[𝕜] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) (H : conformal_at 𝕜 f x) :
∀ (u v : X), inner_product_angle (f' u) (f' v) = (inner_product_angle u v : 𝕜) :=
begin
  intros u v, 
  rcases H with ⟨f₁, c₁, lie, h₁, h₂, h₃⟩,
  have minor : ¬ ∥c₁∥ = 0 := λ w, h₂ (norm_eq_zero.mp w),
  have minor' : ¬ (∥c₁∥ : 𝕜) = 0 := λ w, minor (is_R_or_C.of_real_eq_zero.mp w),
  have : f'.to_continuous_linear_map = f₁ := has_fderiv_at.unique h h₁,
  rw [← continuous_linear_equiv.coe_coe f', ← continuous_linear_equiv.coe_def_rev f'],
  repeat {rw inner_product_angle.def},
  rw [this, h₃],
  repeat {rw function.comp_apply},
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, 
      linear_isometry_equiv.inner_map_map, is_R_or_C.conj_mul_eq_norm_sq_left],
  repeat {rw [norm_smul, linear_isometry_equiv.norm_map]},
  rw [is_R_or_C.norm_sq_eq_def', ← is_R_or_C.of_real_mul, ← mul_assoc],
  nth_rewrite 2 mul_comm,
  rw [← mul_assoc, pow_two],
  repeat {rw [is_R_or_C.of_real_mul, mul_assoc]},
  repeat {rw mul_div_mul_left _ _ minor'},
end



-- structure conformal 
-- (𝕜 X Y : Type*) [is_R_or_C 𝕜] 
-- [inner_product_space 𝕜 X] [inner_product_space 𝕜 Y] :=
-- (to_fun : X → Y)
-- (const_at : X → 𝕜)
-- (fderiv_at : X → (X →L[𝕜] Y))
-- (const_at_ne_zero : ∀ x, const_at x ≠ 0)
-- (lie_at : X → linear_isometry_equiv 𝕜 X Y)
-- (has_fderiv_at' : ∀ x, has_fderiv_at to_fun (fderiv_at x) x)
-- (conformality' : ∀ x, ⇑(fderiv_at x) = (λ y, (const_at x) • y) ∘ (lie_at x))

end conformal