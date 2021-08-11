import analysis.calculus.conformal
import similarity
import data.matrix.notation
import analysis.calculus.times_cont_diff
import analysis.calculus.fderiv_symmetric

noncomputable theory

open conformal_at submodule set
open_locale classical real_inner_product_space

section linear_alg_prep

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] {x : E}

lemma A {f' : E → (E →L[ℝ] F)} {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) {u v : E} :
  ⟪u, v⟫ = 0 ↔ ⟪f' x u, f' x v⟫ = 0 :=
begin
  rcases h with ⟨c, p, q⟩,
  split,
  { intros huv,
    convert q u v,
    rw [huv, mul_zero] },
  { intros huv,
    rw q u v at huv,
    exact eq_zero_of_ne_zero_of_mul_left_eq_zero (ne_of_gt p) huv } 
end

lemma A' {f' : E → (E →L[ℝ] F)} {u v : E} (huv : ⟪u, v⟫ = 0)
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  (λ x, ⟪f' x u, f' x v⟫) = λ x, (0 : ℝ) :=
by {ext1, rwa ← A (h x) }

lemma B {f' : E → (E →L[ℝ] F)} {x : E} {K : submodule ℝ E} (hf : function.surjective (f' x))
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  (Kᗮ).map (f' x : E →ₗ[ℝ] F) = (K.map (f' x))ᗮ :=
begin
  ext1 y'',
  simp only [mem_map, mem_orthogonal],
  split,
  { rintros ⟨u, hu, huy⟩,
    intros v hv,
    rcases hv with ⟨z, hz, hzv⟩,
    rw [← huy, ← hzv, continuous_linear_map.coe_coe, ← A h],
    exact hu z hz },
  { intros H,
    rcases hf y'' with ⟨y', hy'⟩,
    refine ⟨y', λ u hu, _, hy'⟩,
    rw [A h, hy'],
    exact H (f' x u) ⟨u, hu, rfl⟩ }
end

lemma C {f' : E → (E →L[ℝ] F)} {x : E} (hf : function.surjective (f' x))
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) {u v : E} {w : F}
  (H : ∀ (t : E), t ∈ (span ℝ ({u} ∪ {v} : set E))ᗮ → ⟪w, f' x t⟫ = 0) :
  w ∈ (span ℝ ({f' x u} ∪ {f' x v} : set F)) :=
begin
  have triv₁ : {f' x u} ∪ {f' x v} = f' x '' ({u} ∪ {v}) :=
    by simp only [image_union, image_singleton],
  rw [triv₁, ← continuous_linear_map.coe_coe, ← map_span],
  have triv₂ : is_complete (span ℝ ({u} ∪ {v} : set E) : set E),
  { haveI : finite_dimensional ℝ (span ℝ ({u} ∪ {v} : set E)) :=
      finite_dimensional.span_of_finite ℝ ((finite_singleton _).union $ finite_singleton _),
    exact complete_of_finite_dimensional _ },
  haveI : complete_space (span ℝ ({u} ∪ {v} : set E)) := triv₂.complete_space_coe,
  rw [← orthogonal_orthogonal (span ℝ ({u} ∪ {v} : set E)), B hf h, mem_orthogonal],
  intros y hy,
  rw [mem_map] at hy,
  rcases hy with ⟨y', hy', Hy'⟩,
  rw [real_inner_comm, ← Hy'],
  exact H y' hy'
end

end linear_alg_prep

section tot_diff_eq
open continuous_linear_map_eval_at
open_locale topological_space

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] {f : E → F}

lemma D21 {y : E} (hf : times_cont_diff_at ℝ 2 f y) :
  ∀ᶠ (x : E) in 𝓝 y, has_fderiv_at f (fderiv ℝ f x) x :=
begin
  rcases times_cont_diff_at_succ_iff_has_fderiv_at.mp hf with ⟨f', ⟨s, hs, hxs⟩, hf'⟩,
  have minor₁ : ∀ (x : E), x ∈ s → differentiable_at ℝ f x := λ x hx, ⟨f' x, hxs x hx⟩,
  have minor₂ : ∀ (x : E), x ∈ s → has_fderiv_at f (fderiv ℝ f x) x := 
    λ x hx, (minor₁ x hx).has_fderiv_at,
  rw filter.eventually_iff_exists_mem,
  exact ⟨s, hs, minor₂⟩
end

lemma D22 {y : E} (hf : times_cont_diff_at ℝ 2 f y) :
  times_cont_diff_at ℝ 1 (fderiv ℝ f) y :=
begin
  have triv₁ : (1 : with_top ℕ) ≤ 2 := by { apply with_top.coe_le_coe.mpr, exact one_le_two },
  rcases times_cont_diff_at_succ_iff_has_fderiv_at.mp hf with ⟨f', ⟨s, hs, hxs⟩, hf'⟩,
  have minor₁ : ∀ (x : E), x ∈ s → differentiable_at ℝ f x := λ x hx, ⟨f' x, hxs x hx⟩,
  have minor₂ : set.eq_on (fderiv ℝ f) f' s,
  { intros x hxmem,
    have := (hf.differentiable_at triv₁).has_fderiv_at,
    exact (minor₁ x hxmem).has_fderiv_at.unique (hxs x hxmem) },
  exact hf'.congr_of_eventually_eq (filter.eventually_eq_of_mem hs minor₂)
end

lemma D23 {y : E} (hf : times_cont_diff_at ℝ 2 f y) :
  differentiable_at ℝ (fderiv ℝ f) y :=
(D22 hf).differentiable_at (le_of_eq rfl)

lemma DD1 {f' : E → (E →L[ℝ] F)} {y u : E} (hf : ∀ᶠ (x : E) in 𝓝 y, has_fderiv_at f (f' x) x)
  (hf' : differentiable_at ℝ f' y) :
  fderiv ℝ (λ x, f' x u) y = fderiv ℝ f' y u :=
begin
  have : (λ x, f' x u) = λ x, ((continuous_linear_map_eval_at ℝ F u) ∘ f') x :=
    by simp only [function.comp_app, continuous_linear_map_eval_at_apply],
  simp only [this, congr_arg],
  rw fderiv.comp _ ((times_cont_diff_top ℝ F u).differentiable le_top).differentiable_at hf',
  rw (is_bounded_linear_eval_at ℝ F u).fderiv,
  ext1 v,
  simp only [continuous_linear_map.coe_comp', function.comp_app, 
             continuous_linear_map_eval_at_apply],
  rw [← continuous_linear_map.coe_coe, coe_eval_at, continuous_linear_map_eval_at_apply],
  exact second_derivative_symmetric_of_eventually hf hf'.has_fderiv_at _ _
end

lemma DD2 {y : E} (hf : times_cont_diff_at ℝ 2 f y) (u : E) :
  differentiable_at ℝ (λ x, fderiv ℝ f x u) y :=
begin
  have : (λ x, fderiv ℝ f x u) = λ x, ((continuous_linear_map_eval_at ℝ F u) ∘ fderiv ℝ f) x :=
    by simp only [function.comp_app, continuous_linear_map_eval_at_apply],
  rw [this],
  simp only [congr_arg],
  apply differentiable_at.comp,
  { refine (times_cont_diff.differentiable _ le_top).differentiable_at,
    exact times_cont_diff_top _ _ _ },
  { exact D23 hf }
end

lemma D' (u v w : E) {y : E} (hf : times_cont_diff_at ℝ 2 f y)  :
  fderiv ℝ (λ x, ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫) y w = 
  ⟪fderiv ℝ (fderiv ℝ f) y u w, fderiv ℝ f y v⟫ + 
  ⟪fderiv ℝ f y u, fderiv ℝ (fderiv ℝ f) y v w⟫ :=
begin
  rw [fderiv_inner_apply (DD2 hf _) (DD2 hf _)],
  simp only [congr_arg, DD1 (D21 hf) (D23 hf), congr_arg, add_comm]
end

lemma D {x : E} (hf : conformal f) (hf' : times_cont_diff_at ℝ 2 f x) {u v w : E} :
  ⟪u, v⟫ = 0 → ⟪w, u⟫ = 0 → ⟪w, v⟫ = 0 → ⟪fderiv ℝ (fderiv ℝ f) x u v, fderiv ℝ f x w⟫ = 0 :=
λ huv hwu hwv, begin
  rw real_inner_comm at hwv,
  have m₁ := D' u v w hf',
  have m₂ := D' v w u hf',
  have m₃ := D' w u v hf',
  have triv₁ :  ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = c * ⟪u, v⟫ :=
  λ x, conformal_at_iff'.mp (hf.conformal_at x),
  rw [A' huv triv₁] at m₁,
  rw [A' hwv triv₁] at m₂,
  rw [A' hwu triv₁] at m₃,
  rw [fderiv_const, pi.zero_apply, continuous_linear_map.zero_apply] at m₁ m₂ m₃,
  rw add_comm at m₁ m₃,
  nth_rewrite 0 real_inner_comm at m₃ m₁,
  nth_rewrite 1 real_inner_comm at m₁,
  rw [second_derivative_symmetric_of_eventually (D21 hf') (D23 hf').has_fderiv_at v u,
      second_derivative_symmetric_of_eventually (D21 hf') (D23 hf').has_fderiv_at w u] at m₂,
  rw [second_derivative_symmetric_of_eventually (D21 hf') (D23 hf').has_fderiv_at w v] at m₃,
  have triv₂ : ∀ {a b c : ℝ}, a + b = 0 → b + c = 0 → a + c = 0 → a = 0 :=
  λ a b c hab hbc hac, begin
    rw [← hab, ← zero_add (a + b), ← hac, ← add_assoc, ← zero_add (b + c)] at hbc,
    nth_rewrite 3 add_comm at hbc,
    rw [add_assoc, add_assoc] at hbc,
    nth_rewrite 1 ← add_assoc at hbc,
    nth_rewrite 4 add_comm at hbc,
    exact (add_self_eq_zero.mp $ add_right_cancel hbc.symm)
  end,
  exact triv₂ m₃.symm m₁.symm m₂.symm
end

lemma G'' {x : E} (hf : conformal f) (hf' : times_cont_diff_at ℝ 2 f x) 
  (h : function.surjective (fderiv ℝ f x)) {u v : E} (huv : ⟪u, v⟫ = 0) :
  fderiv ℝ (fderiv ℝ f) x u v ∈ span ℝ ({fderiv ℝ f x u} ∪ {fderiv ℝ f x v} : set F) := 
begin
  refine C h (conformal_at_iff'.mp $ hf.conformal_at _) (λ t ht, _),
  rw mem_orthogonal at ht,
  have triv₁ : u ∈ span ℝ ({u} ∪ {v} : set E) := subset_span (or.intro_left _ $ mem_singleton _),
  have triv₂ : v ∈ span ℝ ({u} ∪ {v} : set E) := subset_span (or.intro_right _ $ mem_singleton _),
  have minor₁ := ht u triv₁,
  have minor₂ := ht v triv₂,
  rw real_inner_comm at minor₁ minor₂,
  exact D hf hf' huv minor₁ minor₂
end

lemma G' {x : E} (hf : conformal f) (hf' : times_cont_diff_at ℝ 2 f x) 
  (h : function.surjective (fderiv ℝ f x)) {u v w : E} (huv : ⟪u, v⟫ = 0) : 
  fderiv ℝ (fderiv ℝ f) x u v = 
  (⟪fderiv ℝ f x u, fderiv ℝ (fderiv ℝ f) x u v⟫ / ↑∥fderiv ℝ f x u∥ ^ 2) • fderiv ℝ f x u +
  (⟪fderiv ℝ f x v, fderiv ℝ (fderiv ℝ f) x u v⟫ / ↑∥fderiv ℝ f x v∥ ^ 2) • fderiv ℝ f x v :=
begin
  rw [← orthogonal_projection_singleton, ← orthogonal_projection_singleton],
  have := G'' hf hf' h huv,
  rw [span_union, mem_sup] at this,
  rcases this with ⟨p₁, hp₁, p₂, hp₂, hp₁p₂⟩,
  have triv₁ : fderiv ℝ (fderiv ℝ f) x u v - p₂ = p₁ := 
    by rw [← hp₁p₂, ← add_sub, sub_self, add_zero],
  have triv₂ : fderiv ℝ (fderiv ℝ f) x u v - p₁ = p₂ := 
    by { rw [← hp₁p₂, add_comm], rw [← add_sub, sub_self, add_zero] },
  rcases mem_span_singleton.mp hp₁ with ⟨s₁, hs₁⟩,
  rcases mem_span_singleton.mp hp₂ with ⟨s₂, hs₂⟩,
  have key₁ : ∀ (w : F), w ∈  span ℝ ({fderiv ℝ f x u} : set F) →
    ⟪fderiv ℝ (fderiv ℝ f) x u v - p₁, w⟫ = 0 :=
  λ w hw, begin
    rcases mem_span_singleton.mp hw with ⟨s, hs⟩,
    rw [← hs, triv₂, ← hs₂, real_inner_smul_left, real_inner_smul_right],
    rw [real_inner_comm, A (conformal_at_iff'.mp $ hf.conformal_at x)] at huv,
    rw [huv, mul_zero, mul_zero],
  end,
  have key₂ : ∀ (w : F), w ∈  span ℝ ({fderiv ℝ f x v} : set F) →
    ⟪fderiv ℝ (fderiv ℝ f) x u v - p₂, w⟫ = 0 :=
  λ w hw, begin
    rcases mem_span_singleton.mp hw with ⟨s, hs⟩,
    rw [← hs, triv₁, ← hs₁, real_inner_smul_left, real_inner_smul_right],
    rw [A (conformal_at_iff'.mp $ hf.conformal_at x)] at huv,
    rw [huv, mul_zero, mul_zero],
  end,
  have key₃ := eq_orthogonal_projection_of_mem_of_inner_eq_zero hp₁ key₁,
  have key₄ := eq_orthogonal_projection_of_mem_of_inner_eq_zero hp₂ key₂,
  rw [key₃, key₄],
  exact hp₁p₂.symm,
end

#check similarity_factor_sqrt_eq

lemma G {x' : E} (hf : conformal f) (hf' : times_cont_diff_at ℝ 2 f x') {u v : E} (hu : u ≠ 0) :
  ⟪fderiv ℝ (fderiv ℝ f) x' u v, fderiv ℝ f x' u⟫ + 
  ⟪fderiv ℝ f x' u, fderiv ℝ (fderiv ℝ f) x' u v⟫ =
  2 * similarity_factor_sqrt (conformal_at_iff'.mp $ hf.conformal_at x') * (fderiv ℝ 
  (λ y, similarity_factor_sqrt $ conformal_at_iff'.mp $ hf.conformal_at y) x' v) * ⟪u, u⟫:=
begin
  rw ← D' u u v hf',
  have : (λ (y : E), ⟪fderiv ℝ f y u, fderiv ℝ f y u⟫) = 
    (λ y, ⟪u, u⟫ * id y) ∘ (λ y, similarity_factor $ conformal_at_iff'.mp $ hf.conformal_at y),
  { ext1 y,
    simp only [function.comp_app, congr_arg],
    rw mul_comm,
    exact (similarity_factor_prop $ conformal_at_iff'.mp $ hf.conformal_at y).2 u u },
  have minor₁ := λ y, conformal_at_iff'.mp $ hf.conformal_at y,
  have minor₂ := (similarity_factor_times_cont_diff_at hu x' minor₁ $ D22 hf').differentiable_at 
    (le_of_eq rfl),
  have minor₃ := (similarity_factor_sqrt_times_cont_diff_at hu x' minor₁ 
    $ D22 hf').differentiable_at (le_of_eq rfl),
  rw [this, fderiv.comp _ (differentiable_at_id.const_mul _) minor₂, 
      fderiv_const_mul differentiable_at_id ⟪u, u⟫, fderiv_id],
  rw ← similarity_factor_sqrt_eq minor₁,
  simp only [pow_two], 
  rw [fderiv_mul minor₃ minor₃, continuous_linear_map.coe_comp'],
  simp only [function.comp_app, continuous_linear_map.coe_add', pi.add_apply, 
             continuous_linear_map.smul_apply, smul_eq_mul, continuous_linear_map.coe_id'],
  simp only [id],
  ring
end

end tot_diff_eq

-- h = u
-- k = v
-- l = w