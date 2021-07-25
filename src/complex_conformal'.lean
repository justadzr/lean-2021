/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import analysis.complex.isometry
import analysis.calculus.conformal

noncomputable theory

section complex_conformal

open complex linear_isometry linear_isometry_equiv continuous_linear_map
     finite_dimensional linear_map

def is_conj_complex_linear (f' : ℂ → ℂ) := ∃ (g' : ℂ →L[ℂ] ℂ), (f' : ℂ → ℂ) = conj ∘ g'

def antiholomorphic_at (f : ℂ → ℂ) (z : ℂ) :=
∃ (g : ℂ → ℂ) (hg' : differentiable_at ℂ g z), f = conj ∘ g

lemma self_smul_one (x : ℂ) : x = x • 1 := by simp

lemma complex_linear_one_ne_zero {f' : ℂ → ℂ} (h : f' ≠ 0)
  (hf' : is_linear_map ℂ f') :
  f' 1 ≠ 0 :=
λ w, begin
  have : f' = 0 := by funext;
    nth_rewrite 0 self_smul_one x; simp only [hf'.map_smul, w, smul_zero, pi.zero_apply],
  exact h this,
end

lemma conj_complex_linear_one_ne_zero {f' : ℂ → ℂ} (h : f' ≠ 0)
  (hf' : is_conj_complex_linear f') :
  f' 1 ≠ 0 :=
λ w, begin
  rcases hf' with ⟨g', hg'⟩,
  have minor : conj (g' 1) = 0 := by simp only [hg', function.comp_app] at w; exact w,
  have key : (g' : ℂ → ℂ) ≠ 0 := λ w,
    by rw [w, pi.comp_zero, conj_eq_zero.mpr rfl] at hg'; exact h hg',
  exact complex_linear_one_ne_zero key g'.to_linear_map.is_linear (conj_eq_zero.mp minor),
end

variables {f : ℂ → ℂ} {z : ℂ} {f' : ℂ →L[ℝ] ℂ}

lemma is_conformal_map_of_complex_linear (nonzero : (f' : ℂ → ℂ) ≠ 0) (h : is_linear_map ℂ f') :
  is_conformal_map f' :=
begin
  have minor₁ : ∥f' 1∥ ≠ 0 := ne_of_gt (norm_pos_iff.mpr $ complex_linear_one_ne_zero nonzero h),
  have minor₂ : complex.abs ((f' 1) / ∥f' 1∥) = 1 := by simp only [complex.abs_div, abs_of_real];
    simp only [← norm_eq_abs, abs_norm_eq_norm, div_self minor₁],
  have key : (f' : ℂ → ℂ) =
    ∥f' 1∥ • rotation ⟨(f' 1) / ∥f' 1∥, (mem_circle_iff_abs _).mpr minor₂⟩ :=
  begin
    funext, simp only [pi.smul_apply, rotation_apply],
    nth_rewrite 0 self_smul_one x,
    simp only [h.map_smul],
    simp only [smul_eq_mul, set_like.coe_mk, smul_coe],
    rw [← mul_assoc],
    nth_rewrite 2 mul_comm,
    nth_rewrite 1 mul_assoc,
    rw [inv_mul_cancel (of_real_ne_zero.mpr minor₁), mul_one, mul_comm],
  end,
  exact ⟨∥f' 1∥, minor₁,
        (rotation ⟨(f' 1) / ∥f' 1∥, (mem_circle_iff_abs _).mpr minor₂⟩).to_linear_isometry, key⟩,
end

lemma is_conformal_map_of_conj_complex_linear (nonzero : (f' : ℂ → ℂ) ≠ 0)
  (h : is_linear_map ℂ f') : is_conformal_map (conj_cle.to_continuous_linear_map.comp f') :=
begin
  rcases is_conformal_map_of_complex_linear nonzero h with ⟨c, hc, li, hg'⟩,
  refine ⟨c, hc, conj_lie.to_linear_isometry.comp li, _⟩,
  rw [continuous_linear_map.coe_comp', continuous_linear_equiv.coe_def_rev,
      continuous_linear_equiv.coe_coe, hg'],
  funext,
  simp only [function.comp_app, conj_cle_apply, pi.smul_apply],
  rw [← conj_lie_apply, conj_lie.map_smul,
      linear_isometry.coe_comp, function.comp_app, coe_to_linear_isometry],
end

end complex_conformal