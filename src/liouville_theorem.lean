import analysis.calculus.conformal
import similarity
import data.matrix.notation
import analysis.calculus.times_cont_diff
import analysis.calculus.fderiv_symmetric

noncomputable theory

open conformal_at submodule set
open_locale classical real_inner_product_space filter topological_space

section linear_conformal_prep

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] {x : E}

lemma eventually_is_conformal_map_of_eventually_conformal {f : E → F} 
  (hf : ∀ᶠ x' in 𝓝 x, conformal_at f x') : ∀ᶠ x' in 𝓝 x, is_conformal_map (fderiv ℝ f x') :=
hf.mono (λ y hy, conformal_at_iff_is_conformal_map_fderiv.mp hy)

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

lemma A' {f' : E → (E →L[ℝ] F)} {u v : E} (huv : ⟪u, v⟫ = 0) 
  (h : ∀ᶠ x' in 𝓝 x, is_conformal_map $ f' x') :
  (λ x, ⟪f' x u, f' x v⟫) =ᶠ[𝓝 x] λ x, (0 : ℝ) :=
begin
  apply (filter.eventually_of_forall $ λ x, huv).mp,
  simp only [congr_arg],
  rcases filter.eventually_iff_exists_mem.mp h with ⟨s, hs, hys⟩,
  exact filter.eventually_iff_exists_mem.mpr ⟨s, hs, λ y hy p, (A $ hys y hy).mp p⟩
end

lemma B {f' : E →L[ℝ] F} {K : submodule ℝ E} 
  (hf : function.surjective f') (h : is_conformal_map f') :
  (Kᗮ).map (f' : E →ₗ[ℝ] F) = (K.map f')ᗮ :=
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
    exact H (f' u) ⟨u, hu, rfl⟩ }
end

lemma C {f' : E →L[ℝ] F} (hf : function.surjective f') (h : is_conformal_map f') {u v : E} {w : F}
  (H : ∀ (t : E), t ∈ (span ℝ ({u} ∪ {v} : set E))ᗮ → ⟪w, f' t⟫ = 0) :
  w ∈ (span ℝ ({f' u} ∪ {f' v} : set F)) :=
begin
  have triv₁ : {f' u} ∪ {f' v} = f' '' ({u} ∪ {v}) :=
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

end linear_conformal_prep

open continuous_linear_map
open_locale topological_space

lemma DD1 {E F : Type*} [normed_group E] [normed_space ℝ E] [normed_group F] [normed_space ℝ F] 
  {f : E → F} {f' : E → (E →L[ℝ] F)} {y u : E} (hf : ∀ᶠ (x : E) in 𝓝 y, has_fderiv_at f (f' x) x)
  (hf' : differentiable_at ℝ f' y) : fderiv ℝ (λ x, f' x u) y = fderiv ℝ f' y u :=
begin
  have : (λ x, f' x u) = λ x, ((apply ℝ _ _) ∘ f') x :=
    by simp only [function.comp_app, apply_apply],
  simp only [this, congr_arg],
  rw fderiv.comp _ (apply ℝ F u).differentiable_at hf',
  ext1 v,
  simp only [(apply ℝ F u).fderiv, coe_comp', function.comp_app, apply_apply],
  exact second_derivative_symmetric_of_eventually hf hf'.has_fderiv_at _ _
end

lemma DD1' {E F : Type*} [normed_group E] [normed_space ℝ E] [normed_group F] [normed_space ℝ F]  
  {f' : E → E →L[ℝ] F} {f'' : E → (E →L[ℝ] E →L[ℝ] F)} {y u v w : E} 
  (hf : ∀ᶠ (x : E) in 𝓝 y, has_fderiv_at f' (f'' x) x) (hf' : differentiable_at ℝ f'' y) :
  fderiv ℝ (λ x, f'' x u v) y w = fderiv ℝ f'' y w u v :=
begin
  have triv : (λ x, f'' x u v) = λ x, ((apply ℝ _ _) ∘ 
    (λ x', f'' x' u)) x :=
    by simp only [function.comp_app, apply_apply],
  simp only [triv],
  rw [fderiv.comp _ (apply ℝ F v).differentiable_at, DD1 hf hf'],
  rw second_derivative_symmetric_of_eventually hf hf'.has_fderiv_at _ _,
  simp only [congr_arg, coe_comp', (apply ℝ F v).fderiv, apply_apply, function.comp_app],
  exact (apply ℝ (E →L[ℝ] F) u).differentiable_at.comp _ hf'
end

section diff_prep

variables {E F : Type*} [normed_group E] [normed_group F] 
  [normed_space ℝ E] [normed_space ℝ F] {f : E → F}

lemma D21 {y : E} {n : ℕ} (hf : times_cont_diff_at ℝ n.succ f y) :
  ∀ᶠ (x : E) in 𝓝 y, has_fderiv_at f (fderiv ℝ f x) x :=
begin
  rcases times_cont_diff_at_succ_iff_has_fderiv_at.mp hf with ⟨f', ⟨s, hs, hxs⟩, hf'⟩,
  have minor₁ : ∀ (x : E), x ∈ s → differentiable_at ℝ f x := λ x hx, ⟨f' x, hxs x hx⟩,
  have minor₂ : ∀ (x : E), x ∈ s → has_fderiv_at f (fderiv ℝ f x) x := 
    λ x hx, (minor₁ x hx).has_fderiv_at,
  rw filter.eventually_iff_exists_mem,
  exact ⟨s, hs, minor₂⟩
end

lemma D22 {y : E} {n : ℕ} (hf : times_cont_diff_at ℝ n.succ f y) :
  times_cont_diff_at ℝ n (fderiv ℝ f) y :=
begin
  have triv₁ : (n : with_top ℕ) ≤ n + 1 := 
    by { apply with_top.coe_le_coe.mpr, exact nat.le_succ _ },
  have triv₂ : (1 : with_top ℕ) ≤ n + 1 := 
    by { apply with_top.coe_le_coe.mpr, linarith },
  rcases times_cont_diff_at_succ_iff_has_fderiv_at.mp hf with ⟨f', ⟨s, hs, hxs⟩, hf'⟩,
  have minor₁ : ∀ (x : E), x ∈ s → differentiable_at ℝ f x := λ x hx, ⟨f' x, hxs x hx⟩,
  have minor₂ : set.eq_on (fderiv ℝ f) f' s,
  { intros x hxmem,
    have := (hf.differentiable_at triv₂).has_fderiv_at,
    exact (minor₁ x hxmem).has_fderiv_at.unique (hxs x hxmem) },
  exact hf'.congr_of_eventually_eq (filter.eventually_eq_of_mem hs minor₂)
end

lemma D23 {y : E} {n : ℕ} (hn : 0 < n) (hf : times_cont_diff_at ℝ (n + 1) f y) :
  differentiable_at ℝ (fderiv ℝ f) y :=
(D22 hf).differentiable_at (with_top.coe_le_coe.mpr $ nat.succ_le_of_lt hn)

lemma DD2 {y : E} {n : ℕ} (hn : 0 < n) (hf : times_cont_diff_at ℝ (n + 1) f y) (u : E) :
  differentiable_at ℝ (λ x, fderiv ℝ f x u) y :=
(apply ℝ F u).differentiable_at.comp _ (D23 hn hf)

end diff_prep

section tot_diff_eq

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] {f : E → F}

lemma D' (u v w : E) {y : E} {n : ℕ} (hn : 0 < n) (hf : times_cont_diff_at ℝ (n + 1) f y)  :
  fderiv ℝ (λ x, ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫) y w = 
  ⟪fderiv ℝ (fderiv ℝ f) y u w, fderiv ℝ f y v⟫ + 
  ⟪fderiv ℝ f y u, fderiv ℝ (fderiv ℝ f) y v w⟫ :=
begin
  rw [fderiv_inner_apply (DD2 hn hf _) (DD2 hn hf _)],
  simp only [congr_arg, DD1 (D21 hf) (D23 hn hf), congr_arg, add_comm]
end

variables {x : E} (hf : ∀ᶠ x' in 𝓝 x, conformal_at f x') {f' : E → (E →L[ℝ] F)} 
  (Hf : ∀ (x' : E), is_conformal_map $ f' x') (Heven : fderiv ℝ f =ᶠ[𝓝 x] f')

localized "notation `conf_diff` := eventually_is_conformal_map_of_eventually_conformal hf"
  in liouville_do_not_use
localized "notation `conf_diff'` := 
  (eventually_is_conformal_map_of_eventually_conformal hf).self_of_nhds" 
  in liouville_do_not_use

include hf

lemma D (hf' : times_cont_diff_at ℝ 2 f x) {u v w : E} 
  (huv : ⟪u, v⟫ = 0) (hwu : ⟪w, u⟫ = 0) (hwv : ⟪w, v⟫ = 0) :
  ⟪fderiv ℝ (fderiv ℝ f) x u v, fderiv ℝ f x w⟫ = 0 :=
begin
  rw real_inner_comm at hwv,
  have m₁ := D' u v w zero_lt_one hf',
  have m₂ := D' v w u zero_lt_one hf',
  have m₃ := D' w u v zero_lt_one hf',
  rw [(A' huv conf_diff).fderiv_eq] at m₁,
  rw [(A' hwv conf_diff).fderiv_eq] at m₂,
  rw [(A' hwu conf_diff).fderiv_eq] at m₃,
  rw [fderiv_const, pi.zero_apply, continuous_linear_map.zero_apply] at m₁ m₂ m₃,
  rw add_comm at m₁ m₃,
  nth_rewrite 0 real_inner_comm at m₃ m₁,
  nth_rewrite 1 real_inner_comm at m₁,
  rw [second_derivative_symmetric_of_eventually (D21 hf') (D23 zero_lt_one hf').has_fderiv_at v u,
      second_derivative_symmetric_of_eventually (D21 hf') (D23 zero_lt_one hf').has_fderiv_at w u] 
      at m₂,
  rw [second_derivative_symmetric_of_eventually (D21 hf') (D23 zero_lt_one hf').has_fderiv_at w v] 
      at m₃,
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

lemma G'' (hf' : times_cont_diff_at ℝ 2 f x)
  (h : function.surjective (fderiv ℝ f x)) {u v : E} (huv : ⟪u, v⟫ = 0) :
  fderiv ℝ (fderiv ℝ f) x u v ∈ span ℝ ({fderiv ℝ f x u} ∪ {fderiv ℝ f x v} : set F) := 
begin
  refine C h conf_diff' (λ t ht, _),
  rw mem_orthogonal at ht,
  have triv₁ : u ∈ span ℝ ({u} ∪ {v} : set E) := subset_span (or.intro_left _ $ mem_singleton _),
  have triv₂ : v ∈ span ℝ ({u} ∪ {v} : set E) := subset_span (or.intro_right _ $ mem_singleton _),
  have minor₁ := ht u triv₁,
  have minor₂ := ht v triv₂,
  rw real_inner_comm at minor₁ minor₂,
  exact D hf hf' huv minor₁ minor₂
end

lemma G' (hf' : times_cont_diff_at ℝ 2 f x) 
  (h : function.surjective (fderiv ℝ f x)) {u v : E} (huv : ⟪u, v⟫ = 0) : 
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
    rcases mem_span_singleton.mp hw with ⟨s', hs'⟩,
    rw [← hs', triv₂, ← hs₂, real_inner_smul_left, real_inner_smul_right],
    rw [real_inner_comm, A conf_diff'] at huv,
    rw [huv, mul_zero, mul_zero]
  end,
  have key₂ : ∀ (w : F), w ∈  span ℝ ({fderiv ℝ f x v} : set F) →
    ⟪fderiv ℝ (fderiv ℝ f) x u v - p₂, w⟫ = 0 :=
  λ w hw, begin
    rcases mem_span_singleton.mp hw with ⟨s', hs'⟩,
    rw [← hs', triv₁, ← hs₁, real_inner_smul_left, real_inner_smul_right],
    rw [A conf_diff'] at huv,
    rw [huv, mul_zero, mul_zero]
  end,
  rw [eq_orthogonal_projection_of_mem_of_inner_eq_zero hp₁ key₁, 
      eq_orthogonal_projection_of_mem_of_inner_eq_zero hp₂ key₂],
  exact hp₁p₂.symm
end

localized "notation `psuedo_conf` := λ y, @filter.eventually_of_forall _ _ (𝓝 y) (λ x', Hf x')"
  in liouville_do_not_use

include Hf Heven

lemma G [nontrivial E] (hf' : times_cont_diff_at ℝ 2 f x) (u v : E)  : 
  ⟪fderiv ℝ (fderiv ℝ f) x u v, fderiv ℝ f x u⟫ + 
  ⟪fderiv ℝ f x u, fderiv ℝ (fderiv ℝ f) x u v⟫ =
  2 * ((similarity_factor_sqrt conf_diff) * 
  (fderiv ℝ (λ y, similarity_factor_sqrt $ psuedo_conf y) x v) * ⟪u, u⟫) :=
begin
  rcases filter.eventually_eq_iff_exists_mem.mp Heven with ⟨s, hs, heq⟩,
  rw ← D' u u v zero_lt_one hf',
  have : (λ (y : E), ⟪fderiv ℝ f y u, fderiv ℝ f y u⟫) =ᶠ[𝓝 x] 
    (λ y, ⟪u, u⟫ * id y) ∘ (λ y, similarity_factor $ psuedo_conf y),
  { rw filter.eventually_eq_iff_exists_mem,
    refine ⟨s, hs, _⟩,
    intros z hz,
    simp only [function.comp_app, congr_arg],
    rw [mul_comm, heq hz],
    exact (similarity_factor_prop $ psuedo_conf z).2 u u },
  have minor₁ := (D22 hf').congr_of_eventually_eq Heven.symm,
  have minor₂ := (similarity_factor_times_cont_diff_at x psuedo_conf minor₁).differentiable_at 
    (le_of_eq rfl),
  have minor₃ := (similarity_factor_sqrt_times_cont_diff_at x psuedo_conf minor₁).differentiable_at 
    (le_of_eq rfl),
  rw [this.fderiv_eq, fderiv.comp _ (differentiable_at_id.const_mul _) minor₂, 
      fderiv_const_mul differentiable_at_id ⟪u, u⟫, fderiv_id],
  rw ← similarity_factor_sqrt_eq psuedo_conf,
  simp only [pow_two], 
  rw [fderiv_mul minor₃ minor₃, coe_comp'],
  simp only [function.comp_app, coe_add', pi.add_apply, 
             continuous_linear_map.smul_apply, smul_eq_mul, coe_id'],
  simp only [_root_.id],
  rw similarity_factor_sqrt_eq_of_eventually_eq conf_diff Heven,
  ring
end

lemma GG' {u v : E} (hu : u ≠ 0) (hf' : times_cont_diff_at ℝ 2 f x) : 
  ⟪fderiv ℝ (fderiv ℝ f) x u v, fderiv ℝ f x u⟫ / ⟪u, u⟫ = 
  similarity_factor_sqrt conf_diff * (fderiv ℝ (λ y, similarity_factor_sqrt $ psuedo_conf y) x v) :=
begin
  haveI : nontrivial E := nontrivial_of_ne u 0 hu,
  have key := G hf Hf Heven hf' u v,
  rw [real_inner_comm, ← two_mul, real_inner_comm] at key,
  have triv : ⟪u, u⟫ ≠ 0 := λ W, hu (inner_self_eq_zero.mp W),
  rw div_eq_iff_mul_eq triv,
  convert (mul_left_cancel' _ key).symm,
  exact two_ne_zero  
end

lemma GG1 {u v : E} (hu : u ≠ 0) (hf' : times_cont_diff_at ℝ 2 f x) : 
  ⟪fderiv ℝ f x u, fderiv ℝ (fderiv ℝ f) x u v⟫ / ∥fderiv ℝ f x u∥ ^ 2 =
  (fderiv ℝ (λ y, similarity_factor_sqrt $ psuedo_conf y) x v) *
  similarity_factor_sqrt_inv conf_diff :=
begin
  rw [pow_two, ← real_inner_self_eq_norm_sq],
  have triv₁ : ⟪u, u⟫ ≠ 0 := λ W, hu (inner_self_eq_zero.mp W),
  rw [← div_mul_div_cancel _ triv₁,
      (similarity_factor_sqrt_inv_prop conf_diff).2,
      real_inner_comm, GG' hf Hf Heven hu hf'],
  simp only [similarity_factor_sqrt_inv, inv_inv', congr_arg],
  field_simp [triv₁, (similarity_factor_sqrt_prop conf_diff).1],
  ring
end

lemma GG2 {u v : E} (hv : v ≠ 0) (hf' : times_cont_diff_at ℝ 2 f x) :
  ⟪fderiv ℝ f x v, fderiv ℝ (fderiv ℝ f) x u v⟫ / ∥fderiv ℝ f x v∥ ^ 2 =
  (fderiv ℝ (λ y, similarity_factor_sqrt $ psuedo_conf y) x u) *
  similarity_factor_sqrt_inv (conf_diff) :=
begin
  rw second_derivative_symmetric_of_eventually (D21 hf') (D23 zero_lt_one hf').has_fderiv_at u v,
  exact GG1 hf Hf Heven hv hf'
end

-- lemma GGG {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) (huv : ⟪u, v⟫ = 0)
--   (hf' : times_cont_diff_at ℝ 2 f x) (h : function.surjective (fderiv ℝ f x)): 
--   (similarity_factor_sqrt_inv conf_diff) • (fderiv ℝ (fderiv ℝ f) x u v) +
--   (fderiv ℝ (λ y, similarity_factor_sqrt_inv $ psuedo_conf y) x v) • fderiv ℝ f x u + 
--   (fderiv ℝ (λ y, similarity_factor_sqrt_inv $ psuedo_conf y) x u) • fderiv ℝ f x v = 0 :=
-- begin
--   haveI : nontrivial E := nontrivial_of_ne u 0 hu,
--   have minor₁ := (D22 hf').congr_of_eventually_eq Heven.symm,
--   have key := similarity_factor_sqrt_inv_fderiv x psuedo_conf zero_lt_one minor₁,
--   rw [G' hf hf' h huv, key],
--   simp only [is_R_or_C.coe_real_eq_id, _root_.id],
--   rw [GG1 hf Hf Heven hu hf', GG2 hf Hf Heven hv hf'],
--   simp only [smul_add, smul_smul, pi.neg_apply, pi.mul_apply, congr_arg],
--   rw [← similarity_factor_sqrt_inv_eq', inv_pow', inv_inv', pow_two],
--   rw similarity_factor_sqrt_inv_eq_of_eventually_eq conf_diff Heven,
--   nth_rewrite 1 add_comm,
--   simp only [← add_assoc, ← add_smul, add_assoc, ← add_smul],
--   rw [neg_mul_eq_neg_mul_symm, neg_add_eq_sub],
--   simp only [mul_assoc, mul_comm, sub_self, zero_smul],
--   simp
-- end

open filter
open_locale filter

lemma GGG_eventually_eq {u v : E} {s : set E} (hxs : x ∈ s) 
  (hs : is_open s) (hu : u ≠ 0) (hv : v ≠ 0) (huv : ⟪u, v⟫ = 0)
  (hf' : ∀ y ∈ s, times_cont_diff_at ℝ 2 f y) (h : ∀ y ∈ s, function.surjective (fderiv ℝ f y)) : 
  (λ x', (similarity_factor_sqrt_inv $ psuedo_conf x') • (fderiv ℝ (fderiv ℝ f) x' u v) +
  (fderiv ℝ (λ y, similarity_factor_sqrt_inv $ psuedo_conf y) x' v) • fderiv ℝ f x' u + 
  (fderiv ℝ (λ y, similarity_factor_sqrt_inv $ psuedo_conf y) x' u) • fderiv ℝ f x' v) =ᶠ[𝓝 x] 
  λ x', (0 : F) :=
begin
  haveI : nontrivial E := nontrivial_of_ne u 0 hu,
  rcases eventually_iff_exists_mem.mp hf with ⟨s₁, hs₁, hy₁⟩,
  rcases eventually_eq_iff_exists_mem.mp Heven with ⟨s₂, hs₂, hy₂⟩,
  have triv₁ : (s₁ ∩ s₂) ∩ s ∈ 𝓝 x := inter_mem (inter_mem hs₁ hs₂) 
    (hs.mem_nhds hxs),
  rcases mem_nhds_iff.mp triv₁ with ⟨t, ht, hxt₁, hxt₂⟩,
  refine eventually_eq_of_mem (hxt₁.mem_nhds hxt₂) (λ y hy, _),
  have minor₁ : ∀ᶠ x' in 𝓝 y, conformal_at f x' :=
    eventually_iff_exists_mem.mpr ⟨t, hxt₁.mem_nhds hy, λ y' hy', hy₁ y' (ht hy').1.1⟩,
  have minor₂ : fderiv ℝ f =ᶠ[𝓝 y] f' :=
    eventually_iff_exists_mem.mpr ⟨t, hxt₁.mem_nhds hy, λ y' hy', hy₂ (ht hy').1.2⟩,
  simp only [congr_arg],
  have key₁ := (hf' y (ht hy).2),
  have key₂ := h y (ht hy).2,
  have minor₃ := (D22 key₁).congr_of_eventually_eq minor₂.symm,
  have key := similarity_factor_sqrt_inv_fderiv y psuedo_conf zero_lt_one minor₃,
  rw [G' minor₁ key₁ key₂ huv, key],
  simp only [is_R_or_C.coe_real_eq_id, _root_.id],
  rw [GG1 minor₁ Hf minor₂ hu key₁, GG2 minor₁ Hf minor₂ hv key₁],
  simp only [smul_add, smul_smul, pi.neg_apply, pi.mul_apply, congr_arg],
  rw [← similarity_factor_sqrt_inv_eq', inv_pow', inv_inv', pow_two],
  rw similarity_factor_sqrt_inv_eq_of_eventually_eq (psuedo_conf y) minor₂.symm,
  nth_rewrite 1 add_comm,
  simp only [← add_assoc, ← add_smul, add_assoc, ← add_smul],
  rw [neg_mul_eq_neg_mul_symm, neg_add_eq_sub],
  simp only [mul_assoc, mul_comm, sub_self, zero_smul],
  simp
end

lemma J1 {u : E} (v w : E) (hu : u ≠ 0) (hf' : ∀ᶠ x' in 𝓝 x, times_cont_diff_at ℝ 3 f x') :
  fderiv ℝ (λ x, (fderiv ℝ (λ y, similarity_factor_sqrt_inv $ psuedo_conf y) x v) • 
  fderiv ℝ f x u) x w = fderiv ℝ (fderiv ℝ $ λ y, similarity_factor_sqrt_inv $ 
  psuedo_conf y) x w v • fderiv ℝ f x u +  
  fderiv ℝ (λ y, similarity_factor_sqrt_inv $ psuedo_conf y) x v • fderiv ℝ (fderiv ℝ f) x w u :=
begin
  haveI : nontrivial E := nontrivial_of_ne u 0 hu,
  have minor₀ := similarity_factor_sqrt_inv_times_cont_diff_at x psuedo_conf 
    ((D22 hf'.self_of_nhds).congr_of_eventually_eq Heven.symm),
  have minor₁ := hf.mono (λ x' hx', hx'.differentiable_at.has_fderiv_at),
  have minor₂ := D23 zero_lt_two hf'.self_of_nhds,
  have minor₃ : ∀ᶠ x' in 𝓝 x, times_cont_diff_at ℝ 2 (fderiv ℝ f) x' := hf'.mono (λ a ha, D22 ha),
  have minor₄ : ∀ᶠ x' in 𝓝 x, has_fderiv_at (λ y, similarity_factor_sqrt_inv $ psuedo_conf y) 
    (fderiv ℝ (λ y, similarity_factor_sqrt_inv $ psuedo_conf y) x') x' :=
    D21 (similarity_factor_sqrt_inv_times_cont_diff_at _ psuedo_conf $
    minor₃.self_of_nhds.congr_of_eventually_eq Heven.symm),
  have minor₅ := D23 zero_lt_one minor₀,
  rw fderiv_smul,
  simp only [continuous_linear_map.add_apply, continuous_linear_map.smul_apply, 
             continuous_linear_map.smul_right_apply, congr_arg],
  rw [DD1 minor₁ minor₂, DD1 minor₄ minor₅], 
  simp only [congr_arg],
  rw [second_derivative_symmetric_of_eventually minor₁ minor₂.has_fderiv_at,
      second_derivative_symmetric_of_eventually minor₄ minor₅.has_fderiv_at, add_comm],
  exact DD2 zero_lt_one (similarity_factor_sqrt_inv_times_cont_diff_at _ 
    psuedo_conf $ minor₃.self_of_nhds.congr_of_eventually_eq Heven.symm) v,
  exact DD2 zero_lt_two hf'.self_of_nhds u
end

lemma J2 {u : E} (v w : E) (hu : u ≠ 0) (hf' : times_cont_diff_at ℝ 4 f x) :
  fderiv ℝ (λ x', (similarity_factor_sqrt_inv $ psuedo_conf x') • fderiv ℝ (fderiv ℝ f) x' u v) x w 
  = fderiv ℝ (λ x', similarity_factor_sqrt_inv $ psuedo_conf x') x w • 
  fderiv ℝ (fderiv ℝ f) x u v + similarity_factor_sqrt_inv conf_diff •
  fderiv ℝ (fderiv ℝ $ fderiv ℝ f) x w u v :=
begin
  haveI : nontrivial E := nontrivial_of_ne u 0 hu,
  have := similarity_factor_sqrt_inv_times_cont_diff_at x psuedo_conf 
    ((D22 hf').congr_of_eventually_eq Heven.symm),
  rw fderiv_smul,
  simp only [add_apply, smul_apply, smul_right_apply, congr_arg],
  rw [DD1' (D21 $ D22 hf') (D23 zero_lt_two $ D22 hf')],
  simp only [add_comm, congr_arg],
  rw similarity_factor_sqrt_inv_eq_of_eventually_eq _ Heven,
  exact this.differentiable_at (with_top.coe_le_coe.mpr $ nat.succ_le_succ zero_le_two),
  exact (apply ℝ F v).differentiable_at.comp _ 
    ((apply ℝ (E →L[ℝ] F) u).differentiable_at.comp _ $ D23 zero_lt_two $ D22 hf'),
end

lemma tot1 {u v w : E} {s : set E} 
  (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (huv : ⟪u, v⟫ = 0) (huw : ⟪u, w⟫ = 0)
  (hf' : ∀ᶠ x' in 𝓝 x, times_cont_diff_at ℝ 4 f x') 
  (h : ∀ᶠ x' in 𝓝 x , function.surjective (fderiv ℝ f x')) :
  fderiv ℝ (fderiv ℝ (λ y, similarity_factor_sqrt_inv $ psuedo_conf y) x) u v = 0 :=
begin
  have triv₁ : (2 : with_top ℕ) ≤ 4,
  { apply with_top.coe_le_coe.mpr,
    norm_num },
  have triv₂ : (3 : with_top ℕ) ≤ 4,
  { apply with_top.coe_le_coe.mpr,
    norm_num },
  have triv₃ : (1 : with_top ℕ) ≤ 3,
  { apply with_top.coe_le_coe.mpr,
    norm_num },
  have triv₄ : (1 : with_top ℕ) ≤ 4,
  { apply with_top.coe_le_coe.mpr,
    norm_num },  
  haveI : nontrivial E := nontrivial_of_ne u 0 hu,
  have minor₀ := similarity_factor_sqrt_inv_times_cont_diff_at x psuedo_conf 
    ((D22 hf'.self_of_nhds).congr_of_eventually_eq Heven.symm),
  have minor₃ : ∀ᶠ x' in 𝓝 x, times_cont_diff_at ℝ 2 (fderiv ℝ f) x' := 
    hf'.mono (λ a ha, D22 $ ha.of_le triv₂),
  have minor₄ : ∀ᶠ x' in 𝓝 x, has_fderiv_at (λ y, similarity_factor_sqrt_inv $ psuedo_conf y) 
    (fderiv ℝ (λ y, similarity_factor_sqrt_inv $ psuedo_conf y) x') x' :=
    D21 (similarity_factor_sqrt_inv_times_cont_diff_at _ psuedo_conf $
    minor₃.self_of_nhds.congr_of_eventually_eq Heven.symm),
  rcases eventually_iff_exists_mem.mp hf' with ⟨s₁, hs₁, hy₁⟩,
  rcases eventually_iff_exists_mem.mp h with ⟨s₂, hs₂, hy₂⟩,
  rcases mem_nhds_iff.mp (inter_mem hs₁ hs₂) with ⟨t, ht, Ht₁, Ht₂⟩,
  have m₁ : fderiv ℝ _ _ w = (0 : F),
  { rw (GGG_eventually_eq hf Hf Heven Ht₂ Ht₁ hu hv huv 
    (λ y' hy', (hy₁ y' (ht hy').1).of_le triv₁) $ λ y' hy', hy₂ y' (ht hy').2).fderiv_eq,
    simp only [congr_arg, fderiv_const, pi.zero_apply, zero_apply] },
  have m₂ : fderiv ℝ _ _ v = (0 : F),
  { rw (GGG_eventually_eq hf Hf Heven Ht₂ Ht₁ hu hw huw
    (λ y' hy', (hy₁ y' (ht hy').1).of_le triv₁) $ λ y' hy', hy₂ y' (ht hy').2).fderiv_eq,
    simp only [congr_arg, fderiv_const, pi.zero_apply, zero_apply] },
  rw ← m₂ at m₁,
  have diff₁ := (apply ℝ ℝ u).differentiable_at.comp _ (D23 zero_lt_two minor₀),
  have diff₁' := (apply ℝ ℝ v).differentiable_at.comp _ (D23 zero_lt_two minor₀),
  have diff₁'' := (apply ℝ ℝ w).differentiable_at.comp _ (D23 zero_lt_two minor₀),
  have diff₂ := (apply ℝ F v).differentiable_at.comp _ 
    ((D22 hf'.self_of_nhds).differentiable_at triv₃),
  have diff₂' := (apply ℝ F u).differentiable_at.comp _ 
    ((D22 hf'.self_of_nhds).differentiable_at triv₃),
  have diff₂'' := (apply ℝ F w).differentiable_at.comp _ 
    ((D22 hf'.self_of_nhds).differentiable_at triv₃),
  have diff₃ := (apply ℝ F v).differentiable_at.comp _ 
    ((apply ℝ (E →L[ℝ] F) u).differentiable_at.comp _ $ D23 zero_lt_two $ D22 hf'.self_of_nhds),
  have diff₃' := (apply ℝ F w).differentiable_at.comp _ 
    ((apply ℝ (E →L[ℝ] F) u).differentiable_at.comp _ $ D23 zero_lt_two $ D22 hf'.self_of_nhds),
  have diff_mk₁ := diff₁.smul diff₂,
  have diff_mk₁' := diff₁.smul diff₂'',
  have diff_mk₂ := diff₁'.smul diff₂',
  have diff_mk₂' := diff₁''.smul diff₂',
  have diff_mk₃ := (minor₀.differentiable_at triv₃).smul diff₃,
  have diff_mk₃' := (minor₀.differentiable_at triv₃).smul diff₃',
  simp only [congr_arg, function.comp_app, apply_apply] at 
    diff_mk₁ diff_mk₁' diff_mk₂ diff_mk₂' diff_mk₃ diff_mk₃',
  have times₁ := hf'.mono (λ a ha, ha.of_le triv₂), 
  rw [fderiv_add (diff_mk₃.add diff_mk₂) diff_mk₁, fderiv_add diff_mk₃ diff_mk₂,
      fderiv_add (diff_mk₃'.add diff_mk₂') diff_mk₁', fderiv_add diff_mk₃' diff_mk₂'] at m₁,
  simp only [add_apply] at m₁,
  rw [J1 hf Hf Heven v w hu times₁, J1 hf Hf Heven u w hv times₁,
      J1 hf Hf Heven w v hu times₁, J1 hf Hf Heven u v hw times₁] at m₁,
  rw [J2 hf Hf Heven v w hu hf'.self_of_nhds, J2 hf Hf Heven w v hu hf'.self_of_nhds] at m₁,
  -- rw second_derivative_symmetric_of_eventually (D21 hf'.self_of_nhds) 
  --   (D23 zero_lt_three hf'.self_of_nhds).has_fderiv_at w u at m₁,
end

end tot_diff_eq

-- h = u
-- k = v
-- l = w