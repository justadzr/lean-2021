import linear_algebra.bilinear_form
import analysis.calculus.conformal
import data.matrix.notation
import analysis.calculus.times_cont_diff
import analysis.calculus.fderiv_symmetric

noncomputable theory

open finite_dimensional bilin_form
open_locale real_inner_product_space classical

section bilin_form_eq

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]
  [finite_dimensional ℝ E]

lemma bilin_form_sub_div_mul_eq_zero
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0)
  {v : E} (hv : v ≠ 0) (w : E) : B v w - B v v / ⟪v, v⟫ * ⟪v, w⟫ = 0 :=
begin
  let v' := ∥v∥⁻¹ • v,
  let s : set E := {v'},
  have triv₁ : ⟪v, v⟫ ≠ 0 := λ p, hv (inner_self_eq_zero.mp p),
  have triv₂ : ∥v∥ ≠ 0 := λ p, hv (norm_eq_zero.mp p),
  have triv₀ : v = ∥v∥ • v',
  { simp_rw [v', smul_smul, mul_inv_cancel triv₂, one_smul], },
  have minor₁ : orthonormal ℝ (coe : s → E) :=
  begin
    rw orthonormal_subtype_iff_ite,
    intros x hx y hy,
    simp only [s, set.mem_singleton_iff] at hx hy,
    rw ← hy at hx,
    simp_rw [if_pos hx, hx, hy, v', real_inner_smul_left,
             real_inner_smul_right, real_inner_self_eq_norm_sq],
    field_simp [triv₂],
  end,
  rcases exists_subset_is_orthonormal_basis minor₁ with ⟨u, H, b, hb₁, hb₂⟩,
  have triv₃ : v' ∈ u,
  { apply H, simp_rw [s], exact set.mem_singleton _, },
  have minor₂ : ∀ (i : u), (⟨v', triv₃⟩ : u) ≠ i → ⟪v', ↑i⟫ = 0,
  { intros i hi, let q := hb₁.2 hi, simp only [hb₂, subtype.coe_mk] at q, exact q, },
  have minor₃ : ∀ (i : u), (⟨v', triv₃⟩ : u) ≠ i → B v' ↑i = 0,
  { intros i hi, exact hB v' i (minor₂ i hi), },
  let L : E → ℝ := λ x, B v x - B v v / ⟪v, v⟫ * ⟪v, x⟫,
  have minor₄ : ∀ (i : u), L (b i) = 0 :=
  λ i, begin
    by_cases h : (⟨v', triv₃⟩ : u) = i,
    { simp only [L, hb₂, h.symm, subtype.coe_mk, v'],
      simp only [real_inner_smul_right, smul_right],
      field_simp [triv₁, triv₂],
      ring, },
    { simp only [L, hb₂],
      nth_rewrite 0 triv₀,
      nth_rewrite 5 triv₀,
      rw [real_inner_smul_left, smul_left, minor₂ i h, minor₃ i h],
      ring, },
  end,
  have key₁ : is_linear_map ℝ L :=
  { map_add := λ x y, by
    { simp only [L], simp only [add_right, inner_add_right], ring, },
    map_smul := λ s x, by
    { simp only [L], simp only [smul_right, real_inner_smul_right, smul_eq_mul], ring, }, },
  have key₂ : is_linear_map.mk' _ key₁ = 0 := b.ext minor₄,
  exact calc B v w - B v v / ⟪v, v⟫ * ⟪v, w⟫ = L w : rfl
    ... = (is_linear_map.mk' L key₁ : E → ℝ) w : by rw ← is_linear_map.mk'_apply key₁ w
    ... = (0 : E →ₗ[ℝ] ℝ) w : by rw key₂
    ... = 0 : linear_map.zero_apply w,
end

lemma sym_bilin_form_div_inner_self_const_aux
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0) (hB' : sym_bilin_form.is_sym B)
  {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : ⟪v, w⟫ ≠ 0) : B v v / ⟪v, v⟫ = B w w / ⟪w, w⟫ :=
begin
  let p := bilin_form_sub_div_mul_eq_zero hB hv w,
  let q := bilin_form_sub_div_mul_eq_zero hB hw v,
  rw [sym_bilin_form.sym hB', ← q, sub_eq_sub_iff_sub_eq_sub, sub_self] at p,
  let p' := p.symm,
  rw [sub_eq_zero, real_inner_comm v w] at p',
  exact mul_right_cancel' hvw p',
end

lemma sym_bilin_form_div_inner_self_const
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0) (hB' : sym_bilin_form.is_sym B)
  {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) : B v v / ⟪v, v⟫ = B w w / ⟪w, w⟫ :=
begin
  by_cases hvw : ⟪v, w⟫ ≠ 0,
  { exact sym_bilin_form_div_inner_self_const_aux hB hB' hv hw hvw, },
  { rw not_not at hvw,
    let u := v + w,
    have minor₁ : u ≠ 0 :=
    λ p, begin
      have : ⟪v, w⟫ < 0 :=
      calc ⟪v, w⟫ = ⟪v + w - w, w⟫ : by rw add_sub_cancel
        ... = ⟪u - w, w⟫ : by simp only [u]
        ... = ⟪u, w⟫ - ⟪w, w⟫ : by rw inner_sub_left
        ... = 0 - ⟪w, w⟫ : by rw [p, inner_zero_left]
        ... = - (∥w∥ * ∥w∥) : by rw [zero_sub, real_inner_self_eq_norm_sq, neg_mul_eq_neg_mul]
        ... < 0 : neg_lt_zero.mpr (mul_self_pos $ ne_of_gt $ norm_pos_iff.mpr hw),
      exact (ne_of_lt this) hvw,
    end,
    have minor₂ : ⟪v, u⟫ ≠ 0,
    { simp only [u, inner_add_right, hvw, add_zero], exact λ p, hv (inner_self_eq_zero.mp p), },
    have minor₃ : ⟪w, u⟫ ≠ 0,
    { simp only [u, inner_add_right, real_inner_comm, hvw, zero_add],
      exact λ p, hw (inner_self_eq_zero.mp p), },
    let p := sym_bilin_form_div_inner_self_const_aux hB hB' hv minor₁ minor₂,
    let q := sym_bilin_form_div_inner_self_const_aux hB hB' hw minor₁ minor₃,
    rw ← q at p,
    exact p, },
end

lemma sym_bilin_form_eq_const_mul_inner [nontrivial E]
  {B : bilin_form ℝ E} (hB : ∀ (u v : E), ⟪u, v⟫ = 0 → B u v = 0)
  (hB' : sym_bilin_form.is_sym B) :
  ∃ (r : ℝ), ∀ (v w : E), B v w = r * ⟪v, w⟫ :=
begin
  rcases exists_ne (0 : E) with ⟨v₀, hv₀⟩,
  let r := B v₀ v₀ / ⟪v₀, v₀⟫,
  refine ⟨r, λ v w, _⟩,
  by_cases h' : v = 0,
  { rw [h', inner_zero_left, hB 0 w (inner_zero_left), mul_zero], },
  { rw [← sub_eq_zero],
    simp only [r],
    rw sym_bilin_form_div_inner_self_const hB hB' hv₀ h',
    exact bilin_form_sub_div_mul_eq_zero hB h' w, },
end

/-- The scaling factor -/
def bilin_form_scale_factor [nontrivial E] {B : E → (bilin_form ℝ E)} 
  (hB : ∀ x u v, ⟪u, v⟫ = 0 → B x u v = 0) (hB' : ∀ x, sym_bilin_form.is_sym (B x)) (x : E) : ℝ :=
classical.some (sym_bilin_form_eq_const_mul_inner (hB x) $ hB' x)

lemma bilin_form_scale_factor_spec [nontrivial E] {B : E → (bilin_form ℝ E)} 
  (hB : ∀ x u v, ⟪u, v⟫ = 0 → B x u v = 0) (hB' : ∀ x, sym_bilin_form.is_sym (B x)) (x : E) :
  ∀ u v, B x u v = (bilin_form_scale_factor hB hB' x) * ⟪u, v⟫ :=
classical.some_spec (sym_bilin_form_eq_const_mul_inner (hB x) $ hB' x)

end bilin_form_eq

section fderiv_eval

/-- Evaluation map of a continuous linear map -/
def continuous_linear_map_eval_at {E : Type*} (𝕜 F : Type*) [normed_group E] [normed_group F] 
  [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (x : E) : 
  (E →L[𝕜] F) →ₗ[𝕜] F :=
{ to_fun := λ f, f x,
  map_add' := by simp,
  map_smul' := by simp }

namespace continuous_linear_map_eval_at

variables {E : Type*} (𝕜 F : Type*) [normed_group E] [normed_group F] 
  [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (x : E)

@[simp] lemma continuous_linear_map_eval_at_apply {f : E →L[𝕜] F} :
  (continuous_linear_map_eval_at 𝕜 F x) f = f x :=
rfl

lemma is_bounded_linear_eval_at : is_bounded_linear_map 𝕜 (continuous_linear_map_eval_at 𝕜 F x) :=
{ to_is_linear_map := (continuous_linear_map_eval_at 𝕜 F x).is_linear,
  bound := begin
    by_cases x = 0,
    { refine ⟨1, zero_lt_one, λ f, _⟩,
      simp only [h, one_mul, continuous_linear_map_eval_at_apply, 
                 f.map_zero, norm_zero, norm_nonneg] },
    { refine ⟨∥x∥, norm_pos_iff.mpr h, λ f, _⟩,
      simpa [continuous_linear_map_eval_at_apply, mul_comm] using f.le_op_norm x }
  end }

lemma coe_eval_at : ((is_bounded_linear_eval_at 𝕜 F x).to_continuous_linear_map : 
  (E →L[𝕜] F) →ₗ[𝕜] F) =  continuous_linear_map_eval_at 𝕜 F x :=
rfl

lemma times_cont_diff_top : times_cont_diff 𝕜 ⊤ (continuous_linear_map_eval_at 𝕜 F x) :=
(is_bounded_linear_eval_at 𝕜 F x).times_cont_diff

end continuous_linear_map_eval_at

open conformal_at

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]

def similarity_factor {f' : E → (E →L[ℝ] F)} {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) : ℝ :=
classical.some h

lemma similarity_factor_prop {f' : E → (E →L[ℝ] F)} {x : E}
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  0 < similarity_factor h ∧ ∀ u v, ⟪f' x u, f' x v⟫ = (similarity_factor h) * ⟪u, v⟫ :=
classical.some_spec h

lemma similarity_factor_times_cont_diff_at {f' : E → (E →L[ℝ] F)} {v : E} (hv : v ≠ 0) (x : E)
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) 
  {n : ℕ} (H : times_cont_diff_at ℝ n f' x) : 
  times_cont_diff_at ℝ n (λ x, similarity_factor $ h x) x :=
begin
  have minor₁ : ∥v∥ ≠ 0 := λ w, hv (norm_eq_zero.mp w),
  have minor₂ : ∀ x, similarity_factor (h x)= ∥f' x v∥ ^ 2 / ∥v∥ ^ 2 :=
  λ x, by rw [← mul_div_cancel (similarity_factor $ h x) (pow_ne_zero 2 minor₁),
              pow_two, ← real_inner_self_eq_norm_sq, ← (similarity_factor_prop $ h x).2,
              real_inner_self_eq_norm_sq, ← pow_two],
  have minor₃ : (λ x, similarity_factor $ h x) =
    λ x, ∥(λ y, ((continuous_linear_map_eval_at ℝ F v) ∘ f') y) x∥ ^ 2 / ∥v∥ ^ 2,
  { ext1 x,
    simp only [minor₂ x, continuous_linear_map_eval_at.continuous_linear_map_eval_at_apply,
               function.comp_app], },
  rw [minor₃],
  apply times_cont_diff_at.div_const,
  apply times_cont_diff_at.norm_sq,
  simp only [congr_arg],
  apply times_cont_diff_at.comp,
  { exact 
    ((continuous_linear_map_eval_at.times_cont_diff_top ℝ F v).of_le le_top).times_cont_diff_at },
  { exact H }
end

lemma similarity_factor_eq_conformal_factor {f : E → F} (h : conformal f) :
  (λ x, similarity_factor $ conformal_at_iff'.mp $ h.conformal_at x) = 
  λ x, (h.conformal_at x).conformal_factor_at :=
rfl

lemma conformal_factor_times_cont_diff {f : E → F} {v : E} (hv : v ≠ 0) {n : ℕ}
  (y : E) (h : conformal f) (h' : differentiable ℝ f) (H : times_cont_diff_at ℝ (n + 1) f y) :
  times_cont_diff_at ℝ n (λ x, (h.conformal_at x).conformal_factor_at) y :=
begin
  rcases times_cont_diff_at_succ_iff_has_fderiv_at.mp H with ⟨f', ⟨u, hu, hx⟩, hf'⟩,
  rw [← similarity_factor_eq_conformal_factor],
  refine similarity_factor_times_cont_diff_at hv y (λ x, conformal_at_iff'.mp $ h.conformal_at x) _,
  have : set.eq_on (fderiv ℝ f) f' u,
  { intros x hxu,
    exact h'.differentiable_at.has_fderiv_at.unique (hx x hxu) },
  refine hf'.congr_of_eventually_eq _,
  exact filter.eventually_eq_of_mem hu this
end

end fderiv_eval

section experiment

open conformal_at

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] {f' : E → (E →L[ℝ] F)}

def map_scale_factor_inv_sqrt {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) : ℝ :=
real.sqrt (similarity_factor h)⁻¹

lemma map_scale_factor_inv_sqrt_prop {x : E} 
  (h : ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) :
  map_scale_factor_inv_sqrt h ≠ 0 ∧ 
  ∀ u v, ⟪f' x u, f' x v⟫ = ((map_scale_factor_inv_sqrt h)⁻¹) ^ 2 * ⟪u, v⟫ :=
begin
  refine ⟨real.sqrt_ne_zero'.mpr (inv_pos.mpr (similarity_factor_prop h).1), λ u v, _⟩,
  simp only [(similarity_factor_prop h).2, map_scale_factor_inv_sqrt, real.sqrt_inv,
             inv_inv', real.sq_sqrt (le_of_lt (similarity_factor_prop h).1)]
end

lemma map_scale_factor_inv_sqrt_times_cont_diff_at {v : E} (hv : v ≠ 0) (x : E)
  (h : ∀ x, ∃ (c : ℝ), 0 < c ∧ ∀ u v, ⟪f' x u, f' x v⟫ = c * ⟪u, v⟫) 
  {n : ℕ} (H : times_cont_diff_at ℝ n f' x) :
  times_cont_diff_at ℝ n (λ x, map_scale_factor_inv_sqrt $ h x) x :=
begin
  simp only [map_scale_factor_inv_sqrt],
  have := ne_of_gt (similarity_factor_prop $ h x).1,
  refine times_cont_diff_at.sqrt _ (inv_ne_zero this),
  exact times_cont_diff_at.inv (similarity_factor_times_cont_diff_at hv x h H) this
end

end experiment

section linear_alg_prep

open conformal_at submodule set

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
open continuous_linear_map_eval_at submodule set
open_locale topological_space

variables {E : Type*} [inner_product_space ℝ E] {f : E → E}

lemma d1 {u v : E} : ![u, v] 0 = u := rfl
lemma d2 {u v : E} : fin.tail ![u, v] = λ i, v := 
by simp only [fin.tail, matrix.cons_val_succ, matrix.cons_fin_one, matrix.vec_empty]

lemma D'' {y : E} (hf : times_cont_diff_at ℝ 2 f y) :
  ∀ᶠ (x : E) in 𝓝 y, has_fderiv_at f (fderiv ℝ f x) x :=
begin
  have triv₁ : (1 : with_top ℕ) ≤ 2 := by { apply with_top.coe_le_coe.mpr, exact one_le_two },
  rcases times_cont_diff_at_succ_iff_has_fderiv_at.mp hf with ⟨f', ⟨s, hs, hxs⟩, hf'⟩,
  have minor₁ : ∀ (x : E), x ∈ s → differentiable_at ℝ f x := λ x hx, ⟨f' x, hxs x hx⟩,
  have minor₂ : ∀ (x : E), x ∈ s → has_fderiv_at f (fderiv ℝ f x) x := 
    λ x hx, (minor₁ x hx).has_fderiv_at,
  rw filter.eventually_iff_exists_mem,
  exact ⟨s, hs, minor₂⟩
end

lemma D'''' {y : E} (hf : times_cont_diff_at ℝ 2 f y) :
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

lemma D''' {y : E} (hf : times_cont_diff_at ℝ 2 f y) :
  differentiable_at ℝ (fderiv ℝ f) y :=
(D'''' hf).differentiable_at (le_of_eq rfl)



lemma DD' {f' : E → (E →L[ℝ] E)} {y u : E} (hf : ∀ᶠ (x : E) in 𝓝 y, has_fderiv_at f (f' x) x)
  (hf' : differentiable_at ℝ f' y) :
  fderiv ℝ (λ x, f' x u) y = fderiv ℝ f' y u :=
begin
  have : (λ x, f' x u) = λ x, ((continuous_linear_map_eval_at ℝ E u) ∘ f') x :=
    by simp only [function.comp_app, continuous_linear_map_eval_at_apply],
  simp only [this, congr_arg],
  rw fderiv.comp _ ((times_cont_diff_top ℝ E u).differentiable le_top).differentiable_at hf',
  rw (is_bounded_linear_eval_at ℝ E u).fderiv,
  ext1 v,
  simp only [continuous_linear_map.coe_comp', function.comp_app, 
             continuous_linear_map_eval_at_apply],
  rw [← continuous_linear_map.coe_coe, coe_eval_at, continuous_linear_map_eval_at_apply],
  exact second_derivative_symmetric_of_eventually hf hf'.has_fderiv_at _ _
end

lemma DD {y : E} (hf : times_cont_diff_at ℝ 2 f y) (u : E) :
  differentiable_at ℝ (λ x, fderiv ℝ f x u) y :=
begin
  have : (λ x, fderiv ℝ f x u) = λ x, ((continuous_linear_map_eval_at ℝ E u) ∘ fderiv ℝ f) x :=
    by simp only [function.comp_app, continuous_linear_map_eval_at_apply],
  rw [this],
  simp only [congr_arg],
  apply differentiable_at.comp,
  { refine (times_cont_diff.differentiable _ le_top).differentiable_at,
    exact times_cont_diff_top _ _ _ },
  { exact D''' hf }
end

lemma D' (u v w : E) {y : E} (hf : times_cont_diff_at ℝ 2 f y)  :
  fderiv ℝ (λ x, ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫) y w = 
  ⟪fderiv ℝ (fderiv ℝ f) y u w, fderiv ℝ f y v⟫ + 
  ⟪fderiv ℝ f y u, fderiv ℝ (fderiv ℝ f) y v w⟫ :=
begin
  rw [fderiv_inner_apply (DD hf _) (DD hf _)],
  simp only [congr_arg, DD' (D'' hf) (D''' hf), congr_arg, add_comm]
end

-- h = u, k = v, l = w

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
  rw [second_derivative_symmetric_of_eventually (D'' hf') (D''' hf').has_fderiv_at v u,
      second_derivative_symmetric_of_eventually (D'' hf') (D''' hf').has_fderiv_at w u] at m₂,
  rw [second_derivative_symmetric_of_eventually (D'' hf') (D''' hf').has_fderiv_at w v] at m₃,
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

lemma F'' {x : E} (hf : conformal f) (hf' : times_cont_diff_at ℝ 2 f x) 
  (h : function.surjective (fderiv ℝ f x)) {u v w : E} (huv : ⟪u, v⟫ = 0) :
  fderiv ℝ (fderiv ℝ f) x u v ∈ span ℝ ({fderiv ℝ f x u} ∪ {fderiv ℝ f x v} : set E) := 
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


end tot_diff_eq