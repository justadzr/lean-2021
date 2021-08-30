import analysis.calculus.times_cont_diff
import analysis.calculus.fderiv_symmetric
import analysis.calculus.conformal
import similarity
import data.matrix.notation

noncomputable theory

open conformal_at submodule set continuous_linear_map
open_locale classical real_inner_product_space filter topological_space

lemma quick1 {E : Type*} [inner_product_space ℝ E] (u : E) : ![u] = fin.snoc 0 u :=
begin
  ext y,
  simp only [fin.snoc],
  rw dif_neg (not_lt.mpr $ zero_le y.val),
  simp
end

lemma diff1 {E F G : Type*} [normed_group E] [normed_group F] [normed_group G]
  [normed_space ℝ E] [normed_space ℝ F]
  [normed_space ℝ G] {x v : E} {u : G} {f : E → F} (hf : differentiable_at ℝ f x) :
  (fderiv ℝ (λ y, (f y, u)) x v).2 = 0 :=
begin
  have A : (fderiv ℝ (λ y, (f y, u)) x v).2 = 
    (continuous_linear_map.snd ℝ F G).comp (fderiv ℝ (λ y, (f y, u)) x) v := by simp,
  rw A,
  rw ← (continuous_linear_map.snd ℝ F G).fderiv,
  rw [← fderiv.comp, coe_snd'],
  have B : prod.snd ∘ (λ y, (f y, u)) = λ y, u := by ext1; simp,
  rw [B, fderiv_const_apply, zero_apply],
  { exact continuous_linear_map.differentiable_at _ },
  { refine differentiable_at.prod hf _,
    exact differentiable_at_const _ }
end  

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] {f : E → F}
  {s : set E} (hs : is_open s)

lemma A {f' : E →L[ℝ] F} (h : is_conformal_map f') {u v : E} :
  ⟪u, v⟫ = 0 ↔ ⟪f' u, f' v⟫ = 0 :=
begin
  rcases (is_conformal_map_iff _).mp h with ⟨c, p, q⟩,
  split,
  { intros huv,
    convert q u v,
    rw [huv, mul_zero] },
  { intros huv,
    rw q u v at huv,
    exact eq_zero_of_ne_zero_of_mul_left_eq_zero (ne_of_gt p) huv } 
end

lemma A' {x : E} {f' : E → (E →L[ℝ] F)} {u v : E} (huv : ⟪u, v⟫ = 0) 
  (h : ∀ᶠ x' in 𝓝 x, is_conformal_map $ f' x') :
  (λ x, ⟪f' x u, f' x v⟫) =ᶠ[𝓝 x] λ x, (0 : ℝ) :=
begin
  apply (filter.eventually_of_forall $ λ x, huv).mp,
  simp only [congr_arg],
  rcases filter.eventually_iff_exists_mem.mp h with ⟨s, hs, hys⟩,
  exact filter.eventually_iff_exists_mem.mpr ⟨s, hs, λ y hy p, (A $ hys y hy).mp p⟩
end

include hs

lemma eval_fderiv1 {u v x : E} (hx : x ∈ s) {p : E → formal_multilinear_series ℝ E F}
  (hf : has_ftaylor_series_up_to_on 2 f p s) : 
  fderiv ℝ (λ y, p y 1 ![u]) x v = p x 2 ![u, v] :=
begin
  have : (λ y, p y 1 ![u]) = (λ (q : (E →L[ℝ] F) × E), q.1 q.2) ∘ 
    (λ y, (continuous_multilinear_curry_fin1 ℝ _ _ (p y 1), u)),
  { ext1,
    simp only [function.comp_app, continuous_multilinear_curry_fin1_apply],
    rw quick1 },
  rw [this, fderiv.comp, is_bounded_bilinear_map_apply.fderiv],
  simp only [coe_comp', function.comp_app, is_bounded_bilinear_map_deriv_coe],
  rw @diff1 _ _ _ _ _ _ _ _ _ (λ y, continuous_multilinear_curry_fin1 ℝ _ _ (p y 1)),
end

-- lemma eval_fderiv3 {u x : E} (hx : x ∈ s)
--   {n₀ : ℕ} (hf : times_cont_diff_at ℝ n₀ f x) {n : ℕ} (hn : n < n₀) {m : fin (n + 1) → E} :
--   fderiv ℝ (λ y, iterated_fderiv) x u = p x (n + 2) (fin.snoc m u)

lemma diff_aux {f' : E → (E →L[ℝ] F)} {x u : E} 
  (hf : ∀ᶠ (y : E) in 𝓝 x, has_fderiv_at f (f' y) y) (hf' : differentiable_at ℝ f' x) :
  fderiv ℝ (λ y, f' y u) x = fderiv ℝ f' x u :=
begin
  have : (λ y, f' y u) = λ y, ((apply ℝ F u) ∘ f') y :=
    by simp only [function.comp_app, apply_apply],
  simp only [this, congr_arg],
  rw fderiv.comp _ (continuous_linear_map.differentiable_at _) hf',
  ext1 v,
  simp only [continuous_linear_map.fderiv, coe_comp', function.comp_app, apply_apply],
  exact second_derivative_symmetric_of_eventually hf hf'.has_fderiv_at _ _
end

variables {p : E → formal_multilinear_series ℝ E F}

lemma D' (u v w : E) {x : E} (hx : x ∈ s) (hf : has_ftaylor_series_up_to_on 2 f p s) :
  fderiv ℝ (λ y, ⟪fderiv ℝ f y u, fderiv ℝ f y v⟫) x w = 
  ⟪p x 2 ![u, w], fderiv ℝ f x v⟫ + 
  ⟪fderiv ℝ f x u, iterated_fderiv ℝ 2 f x ![v, w]⟫ :=
begin
  rw fderiv_inner_apply,
  have : ∀ᶠ (y : E) in 𝓝 x, has_fderiv_at f (fderiv ℝ f y) y :=
  begin
    refine filter.eventually_iff_exists_mem.mpr ⟨s, hs.mem_nhds hx, λ y hy, _⟩,
    convert ((hf.differentiable_on $ with_top.coe_le_coe.mpr one_le_two) 
      y hy).has_fderiv_within_at.has_fderiv_at (hs.mem_nhds hy),
    rw fderiv_within_of_open hs hy
  end,
  rw diff_aux,
end

lemma D {u v w : E} {x : E} (hx : x ∈ s) (hf : has_ftaylor_series_up_to_on 2 f p s)
  (huv : ⟪u, v⟫ = 0) (hwu : ⟪w, u⟫ = 0) (hvw : ⟪v, w⟫ = 0) :
  ⟪p x 2 ![u, v], p x 1 ![w]⟫ = 0 :=
begin
  have m₁ := D' u v w hx hf,
  have m₂ := D' v w u hx hf,
  have m₃ := D' w u v hx hf,
  rw add_comm at m₁ m₃,
  nth_rewrite 0 real_inner_comm at m₃ m₁,
  nth_rewrite 1 real_inner_comm at m₁,
end