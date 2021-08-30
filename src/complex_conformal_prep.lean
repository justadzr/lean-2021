import analysis.complex.isometry
import analysis.complex.real_deriv

section fderiv

open continuous_linear_map

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
variables {𝕜' : Type*} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
variables {E : Type*} [normed_group E] [normed_space 𝕜 E] [normed_space 𝕜' E]
variables [is_scalar_tower 𝕜 𝕜' E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
variables [is_scalar_tower 𝕜 𝕜' F]
variables {f : E → F} {f' : E →L[𝕜'] F} {s : set E} {x : E}

lemma has_fderiv_within_at_of_eq {s : set E} {g' : E →L[𝕜] F} (h : has_fderiv_within_at f g' s x)
  (H : f'.restrict_scalars 𝕜 = g') : has_fderiv_within_at f f' s x :=
by { simp only [has_fderiv_within_at, has_fderiv_at_filter] at h ⊢,
     rwa [← f'.coe_restrict_scalars', H] }

lemma has_fderiv_at_of_eq {g' : E →L[𝕜] F} (h : has_fderiv_at f g' x)
  (H : f'.restrict_scalars 𝕜 = g') : has_fderiv_at f f' x :=
by simp only [has_fderiv_at, has_fderiv_at_filter] at h ⊢; rwa [← f'.coe_restrict_scalars', H]

lemma fderiv_eq_fderiv (h : differentiable_at 𝕜' f x) :
  (fderiv 𝕜 f x : E → F) = fderiv 𝕜' f x :=
by rw [(h.restrict_scalars 𝕜).has_fderiv_at.unique (h.has_fderiv_at.restrict_scalars 𝕜),
       coe_restrict_scalars']

lemma differentiable_within_at_iff_exists_linear_map {s : set E}
  (hf : differentiable_within_at 𝕜 f s x) (hs : unique_diff_within_at 𝕜 s x) :
  differentiable_within_at 𝕜' f s x ↔
  ∃ (g' : E →L[𝕜'] F), g'.restrict_scalars 𝕜 = fderiv_within 𝕜 f s x :=
begin
  split,
  { rintros ⟨g', hg'⟩,
    exact ⟨g', hs.eq (hg'.restrict_scalars 𝕜) hf.has_fderiv_within_at⟩, },
  { rintros ⟨f', hf'⟩,
    exact ⟨f', has_fderiv_within_at_of_eq 𝕜 hf.has_fderiv_within_at hf'⟩, },
end

lemma differentiable_at_iff_exists_linear_map (hf : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜' f x ↔ ∃ (g' : E →L[𝕜'] F), g'.restrict_scalars 𝕜 = fderiv 𝕜 f x :=
by { rw [← differentiable_within_at_univ, ← fderiv_within_univ],
     exact differentiable_within_at_iff_exists_linear_map 𝕜
     hf.differentiable_within_at unique_diff_within_at_univ, }

end fderiv

section complex_real_deriv
/-! ### Antiholomorphy of complex functions -/
open complex continuous_linear_map

variables {E : Type*} [normed_group E] [normed_space ℝ E]
  {z : ℂ} {f : ℂ → E}

lemma has_fderiv_at_conj (z : ℂ) : has_fderiv_at conj conj_cle.to_continuous_linear_map z :=
conj_cle.has_fderiv_at

lemma fderiv_conj_eq_conj_fderiv {z : ℂ} (h : differentiable_at ℝ f z) :
  (fderiv ℝ f z).comp conj_cle.to_continuous_linear_map = fderiv ℝ (f ∘ conj) (conj z) :=
begin
  rw ← conj_conj z at h,
  let p := fderiv.comp (conj z) h (has_fderiv_at_conj $ conj z).differentiable_at,
  rw [conj_conj, (has_fderiv_at_conj $ conj z).fderiv] at p,
  exact p.symm,
end

/-- A (real-differentiable) complex function `f` is antiholomorphic if and only if there exists some
    complex linear map `g'` that equals to the composition of `f`'s differential and the conjugate
    function -/
lemma antiholomorph_at_iff_exists_complex_linear_conj
  [normed_space ℂ E] [is_scalar_tower ℝ ℂ E]
  (hf : differentiable_at ℝ f z) : differentiable_at ℂ (f ∘ conj) (conj z) ↔
  ∃ (g' : ℂ →L[ℂ] E), g'.restrict_scalars ℝ =
  (fderiv ℝ f z).comp conj_cle.to_continuous_linear_map :=
begin
  split,
  { intros h,
    rw ← conj_conj z at hf,
    rcases (differentiable_at_iff_exists_linear_map ℝ $
      hf.comp (conj z) (has_fderiv_at_conj $ conj z).differentiable_at).mp h with ⟨f', hf'⟩,
    rw conj_conj at hf,
    rw ← fderiv_conj_eq_conj_fderiv hf at hf',
    exact ⟨f', hf'⟩, },
  { rintros ⟨g', hg'⟩,
    rw ← conj_conj z at hf hg',
    exact ⟨g', has_fderiv_at_of_eq ℝ
      (hf.has_fderiv_at.comp (conj z) $ has_fderiv_at_conj $ conj z) hg'⟩, },
end

end complex_real_deriv