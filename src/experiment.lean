import analysis.complex.isometry
import analysis.complex.real_deriv
import analysis.calculus.conformal

noncomputable theory

open complex linear_isometry linear_isometry_equiv continuous_linear_map
     finite_dimensional linear_map

section A
  
variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables {𝕜' : Type*} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
variables {E : Type*} [normed_group E] [normed_space 𝕜 E] [normed_space 𝕜' E]
variables [is_scalar_tower 𝕜 𝕜' E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
variables [is_scalar_tower 𝕜 𝕜' F]
variables {f : E → F} {f' : E →L[𝕜'] F} {s : set E} {x : E}

lemma differentiable_at_iff_exists_linear_map (hf : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜' f x ↔ ∃ (g' : E →L[𝕜'] F), g'.restrict_scalars 𝕜 = fderiv 𝕜 f x :=
sorry

end A

section B

variables {E : Type*} [normed_group E] [normed_space ℝ E] [normed_space ℂ E]
  [is_scalar_tower ℝ ℂ E] {z : ℂ} {g : ℂ →L[ℝ] E} {f : ℂ → E}

lemma is_conformal_map_of_complex_linear
  {map : ℂ →L[ℂ] E} (nonzero : map ≠ 0) : is_conformal_map (map.restrict_scalars ℝ) :=
sorry


lemma conformal_at_of_holomorph_or_antiholomorph_at_aux
  (hf : differentiable_at ℝ f z) (hf' : fderiv ℝ f z ≠ 0)
  (h : differentiable_at ℂ f z ∨ differentiable_at ℂ (f ∘ conj) (conj z)) :
  conformal_at f z :=
begin
  rw [conformal_at_iff_is_conformal_map_fderiv],
  cases h with h₁ h₂,
  { rw [differentiable_at_iff_exists_linear_map ℝ hf] at h₁;
       [skip, apply_instance, apply_instance, apply_instance],
    rcases h₁ with ⟨map, hmap⟩,
    have minor₁ : fderiv ℝ f z = map.restrict_scalars ℝ := hmap.symm,
    rw minor₁,
    refine is_conformal_map_of_complex_linear _,},
end

end B