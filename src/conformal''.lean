import tactic
import data.matrix.notation
import analysis.complex.basic
import geometry.manifold.charted_space
import analysis.normed_space.inner_product
import linear_algebra.matrix.to_linear_equiv
import geometry.euclidean.basic
import analysis.complex.isometry
import analysis.normed_space.finite_dimension

noncomputable theory

section conformality

def is_conformal_map {X Y : Type*}
[inner_product_space ℝ X] [inner_product_space ℝ Y] (f' : X →L[ℝ] Y) :=
∃ (c : ℝ) (hc : c ≠ 0) (lie : X ≃ₗᵢ[ℝ] Y), ⇑f' = (λ y, c • y) ∘ lie

def conformal_at
{X Y : Type*} [inner_product_space ℝ X] [inner_product_space ℝ Y]
(f : X → Y) (x : X) :=
∃ (f' : X →L[ℝ] Y), has_fderiv_at f f' x ∧ is_conformal_map f'


namespace conformal_at

variables {X Y Z : Type*}
  [inner_product_space ℝ X] [inner_product_space ℝ Y] [inner_product_space ℝ Z]

open linear_isometry_equiv continuous_linear_map

theorem differentiable_at {f : X → Y} {x : X} (h : conformal_at f x) :
differentiable_at ℝ f x := let ⟨_, h₁, _, _, _, _⟩ := h in h₁.differentiable_at

theorem id (x : X) : conformal_at id x :=
⟨id ℝ X, has_fderiv_at_id _, 1, one_ne_zero, refl ℝ X, by ext; simp⟩

theorem const_smul {c : ℝ} (h : c ≠ 0) (x : X) : conformal_at (λ (x': X), c • x') x :=
⟨c • continuous_linear_map.id ℝ X, has_fderiv_at.const_smul (has_fderiv_at_id x) c, c, h, refl ℝ X, by ext; simp⟩

theorem comp {f : X → Y} {g : Y → Z} {x : X} :
  conformal_at f x → conformal_at g (f x) → conformal_at (g ∘ f) x :=
begin
  rintro ⟨f', hf₁, cf, hcf, lief, hf₂⟩ ⟨g', hg₁, cg, hcg, lieg, hg₂⟩,
  exact ⟨g'.comp f', has_fderiv_at.comp x hg₁ hf₁, cg * cf, mul_ne_zero hcg hcf, lief.trans lieg,
    by { ext, simp [coe_comp' f' g', hf₂, hg₂, smul_smul cg cf] }⟩,
end

theorem _root_.conformal_at_iff {f : X → Y} {x : X} {f' : X ≃L[ℝ] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) :
conformal_at f x ↔ ∃ (c : ℝ) (hc : c > 0), ∀ (u v : X), inner (f' u) (f' v) = (c : ℝ) * (inner u v) :=
begin
  split,
  { rintros ⟨f₁, h₁, c₁, hc₁, lie, h₂⟩,
    refine ⟨c₁ * c₁, mul_self_pos hc₁, λ u v, _⟩,
    simp [← f'.coe_coe, ← f'.coe_def_rev, has_fderiv_at.unique h h₁, h₂, inner_map_map, real_inner_smul_left,
      real_inner_smul_right, mul_assoc] },
  { rintro ⟨c₁, hc₁, huv⟩,
    let c := real.sqrt c₁⁻¹,
    have hc : c ≠ 0 := λ w, by {simp only [c] at w;
      exact (real.sqrt_ne_zero'.mpr $ inv_pos.mpr hc₁) w},
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
    exact ⟨f'.to_continuous_linear_map, h, c⁻¹, inv_ne_zero hc, f₁.isometry_of_inner key, minor'⟩, },
end

def char_fun_at {f : X → Y} (x : X) {f' : X ≃L[ℝ] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) (H : conformal_at f x) : ℝ :=
by choose c hc huv using (conformal_at_iff h).mp H; exact c

theorem _root_.conformal_at_preserves_angle {f : X → Y} {x : X} {f' : X ≃L[ℝ] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) (H : conformal_at f x) (u v : X) :
  inner_product_geometry.angle (f' u) (f' v) = inner_product_geometry.angle u v :=
begin
  repeat { rw inner_product_geometry.angle },
  suffices new : inner (f' u) (f' v) / (∥f' u∥ * ∥f' v∥) = inner u v / (∥u∥ * ∥v∥),
  { rw new, },
  { rcases H with ⟨f₁, h₁, c₁, hc₁, lie, h₂⟩,
    have minor : ∥c₁∥ ≠ 0 := λ w, hc₁ (norm_eq_zero.mp w),
    have : f'.to_continuous_linear_map = f₁ := has_fderiv_at.unique h h₁,
    rw [← continuous_linear_equiv.coe_coe f', ← continuous_linear_equiv.coe_def_rev f'],
    repeat {rw inner_product_angle.def},
    rw [this, h₂],
    repeat {rw function.comp_apply},
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, linear_isometry_equiv.inner_map_map],
    repeat {rw [norm_smul, linear_isometry_equiv.norm_map]},
    rw [← mul_assoc],
    exact calc c₁ * c₁ * inner u v / (∥c₁∥ * ∥u∥ * ∥c₁∥ * ∥v∥)
            = c₁ * c₁ * inner u v / (∥c₁∥ * ∥c₁∥ * ∥u∥ * ∥v∥) : by simp only [mul_comm, mul_assoc]
        ... = c₁ * c₁ * inner u v / (abs c₁ * abs c₁ * ∥u∥ * ∥v∥) : by rw [real.norm_eq_abs]
        ... = c₁ * c₁ * inner u v / (c₁ * c₁ * ∥u∥ * ∥v∥) : by rw [← pow_two, ← sq_abs, pow_two]
        ... = c₁ * (c₁ * inner u v) / (c₁ * (c₁ * (∥u∥ * ∥v∥))) : by simp only [mul_assoc]
        ... = (c₁ * inner u v) / (c₁ * (∥u∥ * ∥v∥)) : by rw mul_div_mul_left _ _ hc₁
        ... = inner u v / (∥u∥ * ∥v∥) : by rw mul_div_mul_left _ _ hc₁, },
end

end conformal_at

def conformal
{X Y : Type*} [inner_product_space ℝ X] [inner_product_space ℝ Y]
(f : X → Y) := ∀ (x : X), conformal_at f x

namespace conformal

variables {X Y Z : Type*} 
  [inner_product_space ℝ X] [inner_product_space ℝ Y] [inner_product_space ℝ Z]

theorem differentiable {f : X → Y} (h : conformal f) :
differentiable ℝ f := λ x, (h x).differentiable_at

theorem id : conformal (id : X → X) := λ x, conformal_at.id x

theorem const_smul {c : ℝ} (h : c ≠ 0) :
conformal (λ (x : X), c • x) := λ x, conformal_at.const_smul h x

theorem comp {f : X → Y} {g : Y → Z} (hf : conformal f) (hg : conformal g) :
conformal (g ∘ f) := λ x, conformal_at.comp (hf x) (hg (f x))

end conformal

variables {E F G: Type*} 
  [inner_product_space ℝ E] [inner_product_space ℝ F] [inner_product_space ℝ G]

def conformal_on (f : E → F) (s : set E) := ∀ (x : E), x ∈ s → conformal_at f x

lemma conformal.conformal_on (f : E → F) (h : conformal f) :
conformal_on f set.univ := λ x hx, h x

namespace conformal_on

lemma conformal_at {f : E → F} {u : set E} (h : conformal_on f u) {x : E} (hx : x ∈ u) :
conformal_at f x := h x hx

lemma comp {f : E → E} {g :E → E}
{u v : set E} (hf : conformal_on f u) (hg : conformal_on g v) :
conformal_on (g ∘ f) (u ∩ f⁻¹' v) := λ x hx, (hf x hx.1).comp (hg (f x) (set.mem_preimage.mp hx.2))

lemma congr {f : E → E} {g :E → E}
{u : set E} (hu : is_open u) (h : ∀ (x : E), x ∈ u → g x = f x) (hf : conformal_on f u) :
conformal_on g u := λ x hx, let ⟨f', h₁, c, hc, lie, h₂⟩ := hf x hx in
begin
  have : has_fderiv_at g f' x :=
    by apply h₁.congr_of_eventually_eq; rw filter.eventually_eq_iff_exists_mem; exact ⟨u, hu.mem_nhds hx, h⟩,
  exact ⟨f', this, c, hc, lie, h₂⟩,
end

def conformal_pregroupoid : pregroupoid E :=
{ property := λ f u, conformal_on f u,
  comp := λ f g u v hf hg hu hv huv, hf.comp hg,
  id_mem := conformal.conformal_on id conformal.id,
  locality := λ f u hu h x hx, let ⟨v, h₁, h₂, h₃⟩ := h x hx in h₃ x ⟨hx, h₂⟩,
  congr := λ f g u hu h hf, conformal_on.congr hu h hf, }

def conformal_groupoid : structure_groupoid E := conformal_pregroupoid.groupoid

-- TODO : rename and polish
section complex_conformal

open complex linear_isometry_equiv continuous_linear_map

variables {f : ℂ → ℂ} {z : ℂ} {g : ℂ →L[ℝ] ℂ}

theorem quick0 (a : circle) : is_linear_map ℂ (rotation a) :=
{
  map_add := (rotation a).map_add,
  map_smul := λ s x, by simp only [rotation_apply, smul_eq_mul, mul_assoc, mul_comm],
}

-- Is the statement `is_linear_map ℂ g` the best way to say `g` is `ℂ`-linear?
lemma quick1 (hz : ⇑g ≠ λ x, (0 : ℂ)) :
is_linear_map ℂ g → is_conformal_map g :=
begin
  intro h,
  let c := ∥g 1∥,
  have minor₁ : ∀ (x : ℂ), x = x • 1 := λ x, by simp only [smul_eq_mul, mul_one],
  have minor₂ : g 1 ≠ 0 := λ w, let p : ⇑g = (λ x, (0 : ℂ)) := by funext; nth_rewrite 0 minor₁ x; 
    simp only [h.map_smul, w, smul_zero] in hz p,
  have minor₃ : complex.abs ((g 1) / c) = 1 := by simp only [complex.abs_div, abs_of_real]; 
    simp_rw [c]; simp only [norm_eq_abs, complex.abs_abs, div_self (abs_ne_zero.mpr minor₂)],
  have key : ⇑g = (λ x, c • x) ∘ (rotation ⟨(g 1) / c, (mem_circle_iff_abs _).mpr minor₃⟩) :=
  begin
    funext, simp only [function.comp_apply, rotation_apply],
    nth_rewrite 0 minor₁ x,
    simp only [c, h.map_smul],
    simp only [smul_eq_mul, set_like.coe_mk, smul_coe],
    rw [← mul_assoc], nth_rewrite 2 mul_comm, nth_rewrite 1 mul_assoc,
    rw [inv_mul_cancel (of_real_ne_zero.mpr $ ne_of_gt $ norm_pos_iff.mpr minor₂), mul_one, mul_comm],
  end,
  exact ⟨c, ne_of_gt (norm_pos_iff.mpr minor₂), (rotation ⟨(g 1) / c, (mem_circle_iff_abs _).mpr minor₃⟩), key⟩,
end

-- ℂ-antilinear or being the conjugate of a ℂ-linear map?
lemma quick2 (hz : ⇑g ≠ λ x, (0 : ℂ)) :
is_linear_map ℂ g  → is_conformal_map (conj_cle.to_continuous_linear_map.comp g) :=
begin
  intro h,
  rcases quick1 hz h with ⟨c, hc, lie, hg'⟩,
  simp only [continuous_linear_map.coe_restrict_scalars'] at hg',
  use [c, hc, lie.trans conj_lie],
  rw [continuous_linear_map.coe_comp', continuous_linear_equiv.coe_def_rev, 
      continuous_linear_equiv.coe_coe, hg'],
  funext, simp only [function.comp_app, conj_cle_apply],
  rw [← complex.conj_lie_apply, conj_lie.map_smul, linear_isometry_equiv.coe_trans],
end

-- ℂ-antilinear or being the conjugate of a ℂ-linear map?
lemma quick3 (h : is_conformal_map g) :
(is_linear_map ℂ g ∨ ∃ (g' : ℂ →L[ℂ] ℂ), ⇑g = conj ∘ g') ∧ ⇑g ≠ λ x, (0 : ℂ) :=
begin
  rcases h with ⟨c, hc, lie, hg⟩,
  split, swap,
  {
    intros w, suffices new : ∥g 1∥ = 0,
    {
      have : ∥g 1∥ = ∥c∥ :=
      begin
        rw function.funext_iff at hg,
        rw [hg 1, function.comp_app, norm_smul, lie.norm_map, norm_one, mul_one],
      end,
      rw this at new, exact hc (norm_eq_zero.mp new),
    },
    { rw [w], simp only [function.app], exact norm_zero, },
  },
  {
    rcases linear_isometry_complex lie with ⟨a, ha⟩,
    cases ha,
    {
      have : is_linear_map ℂ g :=
      {
        map_add := g.map_add,
        map_smul := λ c₁ x₁, by rw [hg, ha]; simp only [function.comp_app, rotation_apply, smul_eq_mul, smul_coe]; ring,
      },
      exact or.intro_left _ this,
    },
    {
      have : ∃ (g' : ℂ →L[ℂ] ℂ), ⇑g = conj ∘ g' :=
      begin
        let map := (conj c) • (is_linear_map.mk' (rotation $ a⁻¹) $ quick0 $ a⁻¹).to_continuous_linear_map,
        have : ⇑g = conj ∘ map :=
        begin
          funext, rw [hg, ha], simp only [function.comp_app, linear_isometry_equiv.coe_trans, conj_lie_apply, rotation_apply],
          simp only [smul_coe, smul_eq_mul, function.comp_app, continuous_linear_map.smul_apply, 
                     map, is_linear_map.mk'_apply, linear_map.coe_to_continuous_linear_map', rotation_apply,
                     conj.map_mul, coe_inv_circle_eq_conj, conj_conj],
        end,
        exact ⟨map, this⟩,
      end,
      exact or.intro_right _ this,
    },
  },
end

lemma quick_eq_fderiv (h : differentiable_at ℂ f z) :
(fderiv ℝ f z : ℂ → ℂ) = fderiv ℂ f z :=
begin
  have : (fderiv ℝ f z) = (fderiv ℂ f z).restrict_scalars ℝ := (h.restrict_scalars ℝ).has_fderiv_at.unique (h.has_fderiv_at.restrict_scalars ℝ),
  rw this, simp only [continuous_linear_map.coe_restrict_scalars'],
end

lemma quick_complex_linear (h : differentiable_at ℂ f z) :
is_linear_map ℂ (fderiv ℝ f z) :=
begin
  refine is_linear_map.mk (fderiv ℝ f z).map_add _,
  rw quick_eq_fderiv h, exact (fderiv ℂ f z).map_smul,
end

lemma quick_conj (z : ℂ) : has_fderiv_at conj conj_cle.to_continuous_linear_map z := conj_cle.has_fderiv_at
lemma quick_conj' (z : ℂ) : differentiable_at ℝ conj z := (quick_conj z).differentiable_at
lemma quick_conj'' (z : ℂ) : fderiv ℝ conj z = conj_cle.to_continuous_linear_map := (quick_conj z).fderiv
lemma quick_conj_comp_aux (z z' : ℂ) (h : differentiable_at ℝ f z) : (fderiv ℝ f z z').conj = fderiv ℝ (conj ∘ f) z z' :=
begin
  rw fderiv.comp z (quick_conj' $ f z) h,
  simp only [function.app, function.comp_app, continuous_linear_map.coe_comp'],
  rw [quick_conj'' (f z), continuous_linear_equiv.coe_def_rev, 
      continuous_linear_equiv.coe_apply, conj_cle_apply],
end
lemma quick_conj_comp (z : ℂ) (h : differentiable_at ℝ f z) : conj ∘ fderiv ℝ f z = fderiv ℝ (conj ∘ f) z := by funext; simp only [function.comp_app]; rw quick_conj_comp_aux z x h

lemma quick_smul_one (x : ℂ) : x = x • 1 := by simp only [smul_eq_mul, mul_one]

lemma quick_holomorph {f' : ℂ →L[ℝ] ℂ} {g' : ℂ →L[ℂ] ℂ} (h : has_fderiv_at f f' z) (h' : ⇑f' = g') :
has_fderiv_at f g' z :=
begin
  simp only [has_fderiv_at, has_fderiv_at_filter] at h ⊢,
  rw ← h', exact h,
end

-- Not sure if we need this lemma since eventually we will split it
theorem main_aux:
is_conformal_map g ↔ (is_linear_map ℂ g ∨ ∃ (g' : ℂ →L[ℂ] ℂ), ⇑g = conj ∘ g') ∧ ⇑g ≠ λ x, (0 : ℂ) :=
begin
  split,
  { exact quick3, },
  { 
    intros h, rcases h with ⟨h₁, h₂⟩, cases h₁,
    { exact quick1 h₂ h₁, },
    { 
      rcases h₁ with ⟨g', hg'⟩, 
      have minor₁ : g = conj_cle.to_continuous_linear_map.comp (g'.restrict_scalars ℝ) :=
      begin 
        rw continuous_linear_map.ext_iff, intro x,
        simp only [continuous_linear_map.coe_comp', continuous_linear_equiv.coe_def_rev, 
                   continuous_linear_equiv.coe_coe, function.comp_app,
                   conj_cle_apply, continuous_linear_map.coe_restrict_scalars'],
        rw hg',
      end,
      have minor₂ : is_linear_map ℂ (g'.restrict_scalars ℝ) := 
        by rw continuous_linear_map.coe_restrict_scalars'; exact g'.to_linear_map.is_linear,
      have minor₃ : (g'.restrict_scalars ℝ : ℂ → ℂ) ≠ λ x, (0 : ℂ) := λ w,
      begin
        rw continuous_linear_map.coe_restrict_scalars' at w,
        have : ⇑g = λ x, (0 : ℂ) := by funext; rw [hg', w]; simp only [function.comp_app, conj_eq_zero],
        exact h₂ this,
      end,
      exact minor₁.symm ▸ (quick2 minor₃ minor₂),
    },
  },
end
-- (iff_iff_implies_and_implies _ _).mpr (and.intro quick3 $ λ p, or.elim p.1 (quick1 p.2) (quick2 p.2))

theorem main (h : differentiable_at ℝ f z) :
((differentiable_at ℂ f z ∨ ∃ (g : ℂ → ℂ) (hg : differentiable_at ℂ g z), f = conj ∘ g) ∧ fderiv ℝ f z 1 ≠ 0) ↔ conformal_at f z :=
begin
  split,
  {
    intro H, rcases H with ⟨H₁, H₂⟩, 
    let f' := fderiv ℝ f z,
    have : ⇑f' ≠ λ x, (0 : ℂ) := λ w, by rw w at H₂; simp only [function.app] at H₂; exact H₂ rfl,
    cases H₁,
    { 
      rcases quick1 this (quick_complex_linear H₁) with ⟨c, hc, lie, h'⟩,
      exact ⟨f', h.has_fderiv_at, c, hc, lie, h'⟩,
    },
    { 
      rcases H₁ with ⟨g, hg, hfg⟩,
      have minor₁: ⇑f' = conj ∘ (fderiv ℂ g z) :=
      begin
        funext, simp only [function.comp_app],
        let q := quick_conj_comp_aux z x (hg.restrict_scalars ℝ),
        rw quick_eq_fderiv hg at q, simp only [f', hfg], rw q,
      end,
      have minor₂ : ⇑((fderiv ℂ g z).restrict_scalars ℝ) ≠ λ x, (0 : ℂ) := λ w,
      begin
        rw continuous_linear_map.coe_restrict_scalars' at w,
        have sub : ⇑f' = λ x, (0 : ℂ) := by funext; rw [minor₁, w]; simp only [function.comp_app, conj_eq_zero],
        exact this sub,
      end,
      rcases quick2 minor₂ (fderiv ℂ g z).to_linear_map.is_linear with ⟨c, hc, lie, h'⟩,
      simp only [continuous_linear_map.coe_comp', continuous_linear_equiv.coe_def_rev, 
                 continuous_linear_equiv.coe_coe, function.comp_app,
                 conj_cle_apply, continuous_linear_map.coe_restrict_scalars'] at h',
      have minor₃ : ⇑conj_cle = conj := by funext x; exact conj_cle_apply x,
      rw [minor₃, ← minor₁] at h',
      exact ⟨f', h.has_fderiv_at, c, hc, lie, h'⟩,
    },
  },
  {
    intros H, rcases H with ⟨f', hf', H'⟩,
    let minor := hf'.fderiv.symm,
    rcases quick3 H' with ⟨h₁, h₂⟩,
    cases h₁,
    {
      have : fderiv ℝ f z 1 ≠ 0 := λ w,
      begin
        rw minor at h₁ h₂,
        have : ⇑(fderiv ℝ f z) = λ (x : ℂ), (0 : ℂ) :=
        begin
          funext, rw quick_smul_one x, simp only [h₁.map_smul, w, smul_zero],
        end,
        exact h₂ this,
      end,
      exact ⟨or.intro_left _ ⟨(is_linear_map.mk' f' h₁).to_continuous_linear_map, hf'⟩, this⟩,
    },
    {
      rcases h₁ with ⟨g', hg'⟩, rw minor at h₂ hg',
      have minor' : ⇑g' = conj ∘ f' := by rw [minor, hg']; funext; simp only [function.comp_app, conj_conj],
      have : fderiv ℝ f z 1 ≠ 0 := λ w,
      begin
        have : ⇑(fderiv ℝ f z) = λ (x : ℂ), (0 : ℂ) :=
        begin
          funext, rw [quick_smul_one x, hg'], simp only [function.comp_app, g'.map_smul],
          simp only [smul_eq_mul, conj.map_mul], rw [← function.comp_app conj g' 1, ← hg', w, mul_zero],
        end,
        exact h₂ this,
      end,
      have key : ∃ (g : ℂ → ℂ) (hg : differentiable_at ℂ g z), f = conj ∘ g :=
      begin
        let g := conj ∘ f,
        have sub₁ : f = conj ∘ g := by funext; simp only [function.comp_app, conj_conj],
        let Hf := differentiable_at.comp z conj_cle.differentiable_at h,
        have sub₂ : (conj_cle : ℂ → ℂ) = conj := by funext; rw conj_cle_apply,
        rw sub₂ at Hf,
        let Hg' := Hf.has_fderiv_at,
        have sub₃ : ⇑(fderiv ℝ (⇑conj ∘ f) z) = g':= by rw [← quick_conj_comp z h, ← minor, ← minor'],
        exact ⟨g, ⟨g', quick_holomorph Hg' sub₃⟩, sub₁⟩,
      end,
      exact ⟨or.intro_right _ key, this⟩,
    },
  }
end
end complex_conformal

end conformality

/-!
## Trash code
-/
-- have minor₂ : g 1 ≠ 0 := λ w, let p : ⇑g = (λ x, (0 : ℂ)) := by funext; nth_rewrite 0 minor₁ x; 
--   rw [h 1 x, w, mul_zero] in hz p,
-- have minor₃ : complex.abs ((g 1) / c) = 1 := by simp only [complex.abs_div, abs_of_real]; 
--   simp_rw [c]; simp only [norm_eq_abs, complex.abs_abs, div_self (abs_ne_zero.mpr minor₂)],
-- have key : ⇑g = (λ x, c • x) ∘ (conj_lie.trans $ rotation ⟨(g 1) / c, (mem_circle_iff_abs _).mpr minor₃⟩) :=
-- begin
--   funext,
--   nth_rewrite 0 minor₁ x, rw h 1 x,
--   simp only [linear_isometry_equiv.coe_trans, function.comp_apply, 
--              rotation_apply, conj_lie_apply, set_like.coe_mk, smul_coe],
--   rw [← mul_assoc], nth_rewrite 2 mul_comm, nth_rewrite 1 mul_assoc,
--   rw [inv_mul_cancel (of_real_ne_zero.mpr $ ne_of_gt $ norm_pos_iff.mpr minor₂), mul_one, mul_comm],
-- end,
-- exact ⟨c, ne_of_gt (norm_pos_iff.mpr minor₂), (conj_lie.trans $ rotation ⟨(g 1) / c, (mem_circle_iff_abs _).mpr minor₃⟩), key⟩,

/-!
## Content
1. Some time-saving lemmas for rewrites.
2. Cauchy-Riemann for holomorphic functions.
3. Preparation for further uses of `fderiv ℝ f z`'s linearity
4. Cauchy-RIemann-like equations for antiholomorphic functions.
5. A baby version of the two dimensional Jacobian. The only purpose of defining this Jacobian is using
   it to construct a `continuous_linear_equiv` from a `continuous_linear_map`, which saves us some time
   by not computing its actual inverse.
6. More time-saving lemmas dealing with the inner product `inner : ℂ × ℂ → ℝ`.
7. The main result: holomorphic ∨ antiholomorphic + nonzero (real) derivative → `conformal_at`
8. A corollary.
-/

-- Time saving stuff

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

-- lemma quick_re (z : ℂ) : has_fderiv_at re re_clm z := re_clm.has_fderiv_at
-- lemma quick_re' (z : ℂ) : differentiable_at ℝ re z := (quick_re z).differentiable_at
-- lemma quick_re'' (z : ℂ) : fderiv ℝ re z = re_clm := (quick_re z).fderiv
-- lemma quick_re_comp (z z': ℂ) (h : differentiable_at ℝ f z) : (fderiv ℝ f z z').re = fderiv ℝ (re ∘ f) z z' :=
-- begin
--   rw fderiv.comp z (quick_re' $ f z) h,
--   simp only [function.app, function.comp_app, continuous_linear_map.coe_comp'],
--   rw [quick_re'' (f z), re_clm_apply],
-- end


-- lemma quick_im (z : ℂ) : has_fderiv_at im im_clm z := im_clm.has_fderiv_at
-- lemma quick_im' (z : ℂ) : differentiable_at ℝ im z := (quick_im z).differentiable_at
-- lemma quick_im'' (z : ℂ) : fderiv ℝ im z = im_clm := (quick_im z).fderiv
-- lemma quick_im_comp (z z': ℂ) (h : differentiable_at ℝ f z) : (fderiv ℝ f z z').im = fderiv ℝ (im ∘ f) z z' :=
-- begin
--   rw fderiv.comp z (quick_im' $ f z) h,
--   simp only [function.app, function.comp_app, continuous_linear_map.coe_comp'],
--   rw [quick_im'' (f z), im_clm_apply],
-- end

-- lemma quick_conj (z : ℂ) : has_fderiv_at conj conj_cle.to_continuous_linear_map z := conj_cle.has_fderiv_at
-- lemma quick_conj' (z : ℂ) : differentiable_at ℝ conj z := (quick_conj z).differentiable_at
-- lemma quick_conj'' (z : ℂ) : fderiv ℝ conj z = conj_cle.to_continuous_linear_map := (quick_conj z).fderiv
-- lemma quick_conj_comp (z z' : ℂ) (h : differentiable_at ℝ f z) : (fderiv ℝ f z z').conj = fderiv ℝ (conj ∘ f) z z' :=
-- begin
--   rw fderiv.comp z (quick_conj' $ f z) h,
--   simp only [function.app, function.comp_app, continuous_linear_map.coe_comp'],
--   rw [quick_conj'' (f z), continuous_linear_equiv.coe_def_rev, 
--       continuous_linear_equiv.coe_apply, conj_cle_apply],
-- end

-- lemma complex_fderiv_eq_real_fderiv (h : differentiable_at ℂ f z) :
-- (fderiv ℂ f z).restrict_scalars ℝ = fderiv ℝ f z := (h.has_fderiv_at.restrict_scalars ℝ).unique (h.restrict_scalars ℝ).has_fderiv_at

-- lemma coe_complex_fderiv_eq_coe_real_fderiv (h : differentiable_at ℂ f z) :
-- (fderiv ℂ f z : ℂ → ℂ) = (fderiv ℝ f z : ℂ → ℂ) := by rw ← complex_fderiv_eq_real_fderiv h; exact @continuous_linear_map.coe_restrict_scalars' _ _ _ _ _ _ _ _ _ _ ℝ _ _ _ _ (fderiv ℂ f z)

-- /-!
-- ## Important:
-- The following two lemmas are modified versions of Cauchy-Riemann equations written by [hrmacbeth](https://github.com/hrmacbeth) 
-- in the file `complex.basic` in the `complex-diff` branch of mathlib. Some theorems in that branch conflict with
-- the current mathlib, which contains the most essential `linear_isometry_equiv` we need.
-- -/

-- /-- First Cauchy-Riemann equation: for a complex-differentiable function `f`, the `x`-derivative of
-- `re ∘ f` is equal to the `y`-derivative of `im ∘ f`. -/
-- theorem fderiv_re_comp_eq_fderiv_im_comp (h : differentiable_at ℂ f z) :
--   fderiv ℝ (re ∘ f) z 1 = fderiv ℝ (im ∘ f) z I :=
-- begin
--   let hz := h.has_fderiv_at.restrict_scalars ℝ,
--   have hI : I = I • 1 := by simp,
--   simp only [continuous_linear_map.coe_comp', continuous_linear_map.coe_restrict_scalars', function.comp_app, 
--             ((quick_re $ f z).comp z hz).fderiv, ((quick_im $ f z).comp z hz).fderiv],
--   rw [hI, continuous_linear_map.map_smul],
--   simp,
-- end

-- /-- Second Cauchy-Riemann equation: for a complex-differentiable function `f`, the `x`-derivative of
-- `im ∘ f` is equal to the negative of the `y`-derivative of `re ∘ f`. -/
-- theorem fderiv_re_comp_eq_neg_fderiv_im_comp (h : differentiable_at ℂ f z) :
--   fderiv ℝ (re ∘ f) z I = - fderiv ℝ (im ∘ f) z 1 :=
-- begin
--   have hz := h.has_fderiv_at.restrict_scalars ℝ,
--   have hI : I = I • 1 := by simp,
--   simp only [continuous_linear_map.coe_comp', continuous_linear_map.coe_restrict_scalars', function.comp_app,
--             ((quick_re $ f z).comp z hz).fderiv, ((quick_im $ f z).comp z hz).fderiv],
--   rw [hI, continuous_linear_map.map_smul],
--   simp,
-- end

-- theorem fderiv_decomp_one (h : differentiable_at ℝ f z) :
-- fderiv ℝ f z 1 = fderiv ℝ (re ∘ f) z 1 + (fderiv ℝ (im ∘ f) z 1) * I :=
-- begin
--   have : fderiv ℝ f z 1 = (fderiv ℝ f z 1).re + (fderiv ℝ f z 1).im * I := 
--     by simp only [re_add_im],
--   rw [this, ← quick_re_comp z 1 h, ← quick_im_comp z 1 h],
-- end

-- theorem fderiv_decomp_I (h : differentiable_at ℝ f z) :
-- fderiv ℝ f z I = fderiv ℝ (re ∘ f) z I + (fderiv ℝ (im ∘ f) z I) * I :=
-- begin
--   have : fderiv ℝ f z I = (fderiv ℝ f z I).re + (fderiv ℝ f z I).im * I := 
--     by simp only [re_add_im],
--   rw [this, ← quick_re_comp z I h, ← quick_im_comp z I h],
-- end

-- theorem holomorph_fderiv_decomp_one (h : differentiable_at ℂ f z) :
-- fderiv ℂ f z 1 = fderiv ℝ (re ∘ f) z 1 + (fderiv ℝ (im ∘ f) z 1) * I :=
-- by rw coe_complex_fderiv_eq_coe_real_fderiv h; exact fderiv_decomp_one (h.restrict_scalars ℝ)

-- theorem holomorph_fderiv_decomp_I (h : differentiable_at ℂ f z) :
-- fderiv ℂ f z I = -fderiv ℝ (im ∘ f) z 1 + (fderiv ℝ (re ∘ f) z 1) * I := 
-- by rw [coe_complex_fderiv_eq_coe_real_fderiv h, fderiv_decomp_I (h.restrict_scalars ℝ), 
--        fderiv_re_comp_eq_fderiv_im_comp h, fderiv_re_comp_eq_neg_fderiv_im_comp h, of_real_neg]
-- --

-- theorem antiholomorph_fderiv_decomp_one
-- (h : differentiable_at ℝ f z) {g : ℂ → ℂ} 
-- (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- fderiv ℝ f z 1 = fderiv ℝ (re ∘ g) z 1 - (fderiv ℝ (im ∘ g) z 1) * I :=
-- begin
--   let hg' := hg.restrict_scalars ℝ,
--   nth_rewrite 0 Hg,
--   rw [← quick_conj_comp _ _ hg', fderiv_decomp_one hg'],
--   simp only [conj.map_add, conj_of_real, conj.map_mul, 
--              conj_I, mul_neg_eq_neg_mul_symm, sub_eq_add_neg],
-- end

-- theorem antiholomorph_fderiv_decomp_I
-- (h : differentiable_at ℝ f z) {g : ℂ → ℂ} 
-- (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- fderiv ℝ f z I = fderiv ℝ (re ∘ g) z I - (fderiv ℝ (im ∘ g) z I) * I :=
-- begin
--   let hg' := hg.restrict_scalars ℝ,
--   nth_rewrite 0 Hg,
--   rw [← quick_conj_comp _ _ hg', fderiv_decomp_I hg'],
--   simp only [conj.map_add, conj_of_real, conj.map_mul, 
--              conj_I, mul_neg_eq_neg_mul_symm, sub_eq_add_neg],
-- end

-- @[simp] lemma re_antiholomorph_fderiv_one_eq
-- (h : differentiable_at ℝ f z) {g : ℂ → ℂ} 
-- (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- fderiv ℝ (re ∘ f) z 1 = fderiv ℝ (re ∘ g) z 1 := let p := antiholomorph_fderiv_decomp_one h hg Hg in
-- begin
--   rw [fderiv_decomp_one h, complex.ext_iff] at p,
--   simp at p,
--   exact p.1,
-- end

-- @[simp] lemma im_antiholomorph_fderiv_one_eq
-- (h : differentiable_at ℝ f z) {g : ℂ → ℂ} 
-- (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- fderiv ℝ (im ∘ f) z 1 = - fderiv ℝ (im ∘ g) z 1 := let p := antiholomorph_fderiv_decomp_one h hg Hg in
-- begin
--   rw [fderiv_decomp_one h, complex.ext_iff] at p,
--   simp at p,
--   exact p.2,
-- end

-- @[simp] lemma re_antiholomorph_fderiv_I_eq
-- (h : differentiable_at ℝ f z) {g : ℂ → ℂ} 
-- (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- fderiv ℝ (re ∘ f) z I = fderiv ℝ (re ∘ g) z I := let p := antiholomorph_fderiv_decomp_I h hg Hg in
-- begin
--   rw [fderiv_decomp_I h, complex.ext_iff] at p,
--   simp at p,
--   exact p.1,
-- end

-- @[simp] lemma im_antiholomorph_fderiv_I_eq
-- (h : differentiable_at ℝ f z) {g : ℂ → ℂ} 
-- (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- fderiv ℝ (im ∘ f) z I = - fderiv ℝ (im ∘ g) z I := let p := antiholomorph_fderiv_decomp_I h hg Hg in
-- begin
--   rw [fderiv_decomp_I h, complex.ext_iff] at p,
--   simp at p,
--   exact p.2,
-- end

-- /-- For an anticomplex-differentiable function `f`, the `x`-derivative of
-- `re ∘ f` is equal to the negative of the `y`-derivative of `im ∘ f`. -/
-- theorem fderiv_re_comp_eq_neg_fderiv_im_comp'
-- (h : differentiable_at ℝ f z) {g : ℂ → ℂ} 
-- (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- fderiv ℝ (re ∘ f) z 1 = - fderiv ℝ (im ∘ f) z I :=
-- by rw [re_antiholomorph_fderiv_one_eq h hg Hg, fderiv_re_comp_eq_fderiv_im_comp hg, 
--        im_antiholomorph_fderiv_I_eq h hg Hg, neg_neg]
-- --

-- /-- For an anticomplex-differentiable function `f`, the `x`-derivative of
-- `im ∘ f` is equal to the `y`-derivative of `re ∘ f`. -/
-- theorem fderiv_re_comp_eq_fderiv_im_comp'
-- (h : differentiable_at ℝ f z) {g : ℂ → ℂ} 
-- (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- fderiv ℝ (re ∘ f) z I = fderiv ℝ (im ∘ f) z 1 :=
-- by rw [re_antiholomorph_fderiv_I_eq h hg Hg, fderiv_re_comp_eq_neg_fderiv_im_comp hg, 
--        im_antiholomorph_fderiv_one_eq h hg Hg]
-- --
-- -- Using the Jacobian to show that the differential is a `continuous_linear_equiv`. This is the only
-- -- purpose of defining this matrix since actually using the matrix involves extensive use of `finset`,
-- -- `sum` and `basis`, which is very painful even for the case of dimension two.
-- def complex_jacobian_at (h : differentiable_at ℝ f z) : matrix (fin 2) (fin 2) ℝ :=
-- ![![fderiv ℝ (re ∘ f) z 1, fderiv ℝ (re ∘ f) z I], ![fderiv ℝ (im ∘ f) z 1, fderiv ℝ (im ∘ f) z I]]

-- @[simp] theorem complex_jacobian_at.def (h : differentiable_at ℝ f z) :
-- complex_jacobian_at h = ![![fderiv ℝ (re ∘ f) z 1, fderiv ℝ (re ∘ f) z I], 
--                           ![fderiv ℝ (im ∘ f) z 1, fderiv ℝ (im ∘ f) z I]] := rfl

-- @[simp] theorem complex_jacobian_at_det_eq (h : differentiable_at ℝ f z) :
-- (complex_jacobian_at h).det = (fderiv ℝ (re ∘ f) z 1) * fderiv ℝ (im ∘ f) z I - (fderiv ℝ (re ∘ f) z I) * fderiv ℝ (im ∘ f) z 1 :=
-- begin
--   rw matrix.det_succ_row_zero, repeat {rw [fin.sum_univ_succ]}, simp_rw [fin.sum_univ_zero],
--   simp, rw ← sub_eq_add_neg _ _,
-- end

-- @[simp] theorem complex_jacobian_at_det_eq_holomorph (h : differentiable_at ℂ f z) :
-- (complex_jacobian_at $ h.restrict_scalars ℝ).det = (fderiv ℝ (re ∘ f) z 1) * fderiv ℝ (re ∘ f) z 1 + (fderiv ℝ (im ∘ f) z 1) * fderiv ℝ (im ∘ f) z 1 :=
-- let h' := complex_jacobian_at_det_eq (h.restrict_scalars ℝ) in by rw [← fderiv_re_comp_eq_fderiv_im_comp h, fderiv_re_comp_eq_neg_fderiv_im_comp h, ← neg_mul_eq_neg_mul, sub_neg_eq_add] at h'; exact h'

-- @[simp] theorem complex_jacobian_at_det_eq_antiholomorph (h : differentiable_at ℝ f z) {g : ℂ → ℂ} 
-- (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- (complex_jacobian_at $ h.restrict_scalars ℝ).det = -((fderiv ℝ (re ∘ f) z 1) * fderiv ℝ (re ∘ f) z 1 + (fderiv ℝ (im ∘ f) z 1) * fderiv ℝ (im ∘ f) z 1) :=
-- let h' := complex_jacobian_at_det_eq h in by
-- rw [fderiv_re_comp_eq_fderiv_im_comp' h hg Hg, 
--     eq_neg_of_eq_neg (fderiv_re_comp_eq_neg_fderiv_im_comp' h hg Hg), 
--     ← neg_mul_eq_mul_neg, sub_eq_add_neg, ← neg_add] at h'; 
-- exact h'

-- theorem real_fderiv_to_matrix (h : differentiable_at ℝ f z) : 
-- (linear_map.to_matrix basis_one_I basis_one_I) (fderiv ℝ f z) = complex_jacobian_at h :=
-- begin
--   ext,
--   rw linear_map.to_matrix_apply _ _ _ _ _,
--   simp only [coe_basis_one_I, coe_basis_one_I_repr],
--   fin_cases i,
--   { 
--     fin_cases j,
--     {
--       repeat {rw cvec_two_apply}, rw rvec_two_apply,
--       simp only [complex_jacobian_at, rmatrix_two_apply00],
--       exact quick_re_comp z 1 h,
--     },
--     {
--       repeat {rw cvec_two_apply'}, rw rvec_two_apply,
--       simp only [complex_jacobian_at, rmatrix_two_apply01],
--       exact quick_re_comp z I h,
--     },
--   },
--   { 
--     fin_cases j,
--     {
--       repeat {rw cvec_two_apply}, rw rvec_two_apply',
--       simp only [complex_jacobian_at, rmatrix_two_apply10],
--       exact quick_im_comp z 1 h,
--     },
--     {
--       repeat {rw cvec_two_apply}, rw rvec_two_apply',
--       simp only [complex_jacobian_at, rmatrix_two_apply11],
--       exact quick_im_comp z I h,
--     },
--   },
-- end

-- theorem complex_jacobian_det_eq_fderiv_norm_sq (h : differentiable_at ℂ f z) :
-- (complex_jacobian_at $ h.restrict_scalars ℝ).det = norm_sq (fderiv ℂ f z 1) :=
-- begin
--   let h' := h.restrict_scalars ℝ,
--   let p := complex_jacobian_at_det_eq_holomorph h,
--   rw [← quick_re_comp z 1 h', ← quick_im_comp z 1 h', ← coe_complex_fderiv_eq_coe_real_fderiv h] at p,
--   simp only [norm_sq_apply, re_add_im],
--   exact p,
-- end

-- theorem complex_jacobian_det_eq_neg_fderiv_norm_sq (h : differentiable_at ℝ f z) {g : ℂ → ℂ} 
-- (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- (complex_jacobian_at $ h.restrict_scalars ℝ).det = -norm_sq (fderiv ℂ g z 1) :=
-- begin
--   let hg' := hg.restrict_scalars ℝ,
--   let p := complex_jacobian_at_det_eq_antiholomorph h hg Hg,
--   rw [re_antiholomorph_fderiv_one_eq h hg Hg, im_antiholomorph_fderiv_one_eq h hg Hg, neg_mul_neg,
--       ← quick_re_comp z 1 hg', ← quick_im_comp z 1 hg', ← coe_complex_fderiv_eq_coe_real_fderiv hg] at p,
--   simp only [norm_sq_apply, re_add_im],
--   exact p,
-- end

-- theorem complex_jacobian_at_det_pos_iff_holomorph_fderiv_ne_zero (h : differentiable_at ℂ f z) :
-- (complex_jacobian_at $ h.restrict_scalars ℝ).det > 0 ↔ ¬ fderiv ℝ f z 1 = 0 :=
-- begin
--   split,
--   {
--     intros H, 
--     rw [complex_jacobian_det_eq_fderiv_norm_sq h, coe_complex_fderiv_eq_coe_real_fderiv h] at H, 
--     exact norm_sq_pos.mp H,
--   },
--   {
--     intros H,
--     let p := norm_sq_pos.mpr H,
--     rw [← coe_complex_fderiv_eq_coe_real_fderiv h, ← complex_jacobian_det_eq_fderiv_norm_sq h] at p,
--     exact p,
--   }
-- end

-- theorem complex_jacobian_at_det_neg_iff_antiholomorph_fderiv_ne_zero (h : differentiable_at ℝ f z)
-- {g : ℂ → ℂ} (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- (complex_jacobian_at $ h.restrict_scalars ℝ).det < 0 ↔ ¬ fderiv ℝ f z 1 = 0 :=
-- begin
--   split,
--   {
--     intros H w, rw [antiholomorph_fderiv_decomp_one h hg Hg, ext_iff] at w, 
--     rcases w with ⟨w₁, w₂⟩, 
--     rw [sub_re, zero_re, of_real_re] at w₁,
--     rw [sub_im, zero_im, of_real_im] at w₂,
--     rw [mul_re, of_real_re, of_real_im, I_re, I_im, mul_zero, zero_mul, zero_sub, sub_neg_eq_add, add_zero] at w₁,
--     rw [mul_im, of_real_re, of_real_im, I_re, I_im, mul_zero, mul_one, add_zero, zero_sub, neg_eq_zero] at w₂,
--     have : fderiv ℝ g z 1 = 0 := let p := fderiv_decomp_one (hg.restrict_scalars ℝ) in by rw [w₁, w₂, of_real_zero, zero_mul, zero_add] at p; exact p,
--     rw [complex_jacobian_det_eq_neg_fderiv_norm_sq h hg Hg] at H,
--     let H' := neg_lt_of_neg_lt H, rw [neg_zero, ← complex_jacobian_det_eq_fderiv_norm_sq hg] at H',
--     exact (complex_jacobian_at_det_pos_iff_holomorph_fderiv_ne_zero hg).mp H' this,
--   },
--   {
--     intros H,
--     rw [complex_jacobian_at_det_eq_antiholomorph h hg Hg, neg_lt, neg_zero],
--     have : ¬ (fderiv ℝ f z 1).re = 0 ∨ ¬ (fderiv ℝ f z 1).im = 0 :=
--     begin
--       by_contra w, rw [not_or_distrib, not_not, not_not] at w, rcases w with ⟨w₁, w₂⟩,
--       rw [fderiv_decomp_one h, ← quick_re_comp z 1 h, ← quick_im_comp z 1 h, w₁, w₂, of_real_zero, zero_add, zero_mul] at H,
--       show false, from H rfl,
--     end,
--     cases this with h₁ h₂,
--     {
--       exact calc  (fderiv ℝ (re ∘ f) z 1) * (fderiv ℝ (re ∘ f) z 1) + (fderiv ℝ (im ∘ f) z 1) * (fderiv ℝ (im ∘ f) z 1)
--                 = (fderiv ℝ (re ∘ f) z 1) ^ 2 +  (fderiv ℝ (im ∘ f) z 1) ^ 2 : by repeat {rw pow_two}
--             ... ≥ (fderiv ℝ (re ∘ f) z 1) ^ 2 + 0 : (add_le_add_iff_left _).mpr (sq_nonneg _)
--             ... = (fderiv ℝ f z 1).re ^ 2 : by rw [add_zero, ← quick_re_comp z 1 h]
--             ... > 0 : sq_pos_of_ne_zero _ h₁,
--     },
--     {
--       exact calc  (fderiv ℝ (re ∘ f) z 1) * (fderiv ℝ (re ∘ f) z 1) + (fderiv ℝ (im ∘ f) z 1) * (fderiv ℝ (im ∘ f) z 1)
--                 = (fderiv ℝ (re ∘ f) z 1) ^ 2 +  (fderiv ℝ (im ∘ f) z 1) ^ 2 : by repeat {rw pow_two}
--             ... ≥ 0 + (fderiv ℝ (im ∘ f) z 1) ^ 2 : (add_le_add_iff_right _).mpr (sq_nonneg _)
--             ... = (fderiv ℝ f z 1).im ^ 2 : by rw [zero_add, ← quick_im_comp z 1 h]
--             ... > 0 : sq_pos_of_ne_zero _ h₂,
--     },
--   },
-- end

-- /-!
-- I could only do this for holomorphic/antiholomorphic + nonzero Jacobian → conformal, but couldn't show
-- conformal + nonzero Jacobian → holomorphic ∨ antiholomorphic because Cauchy-Riemann → holomorphic
-- is not proved yet.
-- -/
 
-- lemma complex_smul (z : ℝ) : (z : ℂ) = z • (1 : ℂ) := by simp
-- lemma complex_smul_I (z : ℝ) : (z : ℂ) * I = z • I := by simp

-- theorem inner_fderiv_fderiv (u v : ℂ) :
-- (inner (fderiv ℝ f z u) (fderiv ℝ f z v) : ℝ) 
-- = (u.re * v.re) * (inner (fderiv ℝ f z 1) (fderiv ℝ f z 1)) + (u.re * v.im) * (inner (fderiv ℝ f z 1) (fderiv ℝ f z I))
-- + (u.im * v.re) * (inner (fderiv ℝ f z I) (fderiv ℝ f z 1)) + (u.im * v.im) * (inner (fderiv ℝ f z I) (fderiv ℝ f z I)) :=
-- calc (inner (fderiv ℝ f z u) (fderiv ℝ f z v) : ℝ) = inner (fderiv ℝ f z (u.re + u.im * I)) (fderiv ℝ f z (v.re + v.im * I)) : by simp only [re_add_im]
--   ... = (inner (fderiv ℝ f z (u.re : ℂ) + fderiv ℝ f z (u.im * I)) (fderiv ℝ f z (v.re : ℂ) + fderiv ℝ f z (v.im * I)) : ℝ) : by simp only [continuous_linear_map.map_add]
--   ... = inner (fderiv ℝ f z (u.re • 1) + fderiv ℝ f z (u.im • I)) (fderiv ℝ f z (v.re • 1) + fderiv ℝ f z (v.im • I)) : by repeat {rw [complex_smul, complex_smul_I]}
--   ... = inner (u.re • fderiv ℝ f z 1 + u.im • fderiv ℝ f z I) (v.re • fderiv ℝ f z 1 + v.im • fderiv ℝ f z I) : by repeat {rw [(fderiv ℝ f z).map_smul]}
--   ... = inner (u.re • fderiv ℝ f z 1) (v.re • fderiv ℝ f z 1 + v.im • fderiv ℝ f z I) + inner (u.im • fderiv ℝ f z I) (v.re • fderiv ℝ f z 1 + v.im • fderiv ℝ f z I) : by rw inner_add_left
--   ... = inner (u.re • fderiv ℝ f z 1) (v.re • fderiv ℝ f z 1) + inner (u.re • fderiv ℝ f z 1) (v.im • fderiv ℝ f z I) 
--       + inner (u.im • fderiv ℝ f z I) (v.re • fderiv ℝ f z 1) + inner (u.im • fderiv ℝ f z I) (v.im • fderiv ℝ f z I) : by simp only [inner_add_right, add_assoc]
--   ... = u.re * (v.re * inner (fderiv ℝ f z 1) (fderiv ℝ f z 1)) + u.re * (v.im * inner (fderiv ℝ f z 1) (fderiv ℝ f z I))
--       + u.im * (v.re * inner (fderiv ℝ f z I) (fderiv ℝ f z 1)) + u.im * (v.im * inner (fderiv ℝ f z I) (fderiv ℝ f z I)) : by repeat {rw [real_inner_smul_left]}; repeat {rw [real_inner_smul_right]}
--   ... = (u.re * v.re) * (inner (fderiv ℝ f z 1) (fderiv ℝ f z 1)) + (u.re * v.im) * (inner (fderiv ℝ f z 1) (fderiv ℝ f z I))
--       + (u.im * v.re) * (inner (fderiv ℝ f z I) (fderiv ℝ f z 1)) + (u.im * v.im) * (inner (fderiv ℝ f z I) (fderiv ℝ f z I)) : by simp only [mul_assoc]
-- --
-- lemma quick_inner_one_one (h : differentiable_at ℝ f z) :
-- (inner (fderiv ℝ f z 1) (fderiv ℝ f z 1) : ℝ) = (fderiv ℝ (re ∘ f) z 1) * fderiv ℝ (re ∘ f) z 1 + (fderiv ℝ (im ∘ f) z 1) * fderiv ℝ (im ∘ f) z 1 :=
-- begin
--   rw [real_inner_eq_re_inner, is_R_or_C.inner_apply],
--   rw fderiv_decomp_one h,
--   simp,
-- end

-- lemma quick_inner_one_I (h : differentiable_at ℂ f z) :
-- (inner (fderiv ℝ f z 1) (fderiv ℝ f z I) : ℝ) = 0 :=
-- begin
--   let h' := h.restrict_scalars ℝ,
--   rw [real_inner_eq_re_inner, is_R_or_C.inner_apply],
--   rw fderiv_decomp_one h',
--   simp,
--   rw [quick_re_comp z I h', quick_im_comp _ I h', 
--       fderiv_re_comp_eq_neg_fderiv_im_comp h, ← fderiv_re_comp_eq_fderiv_im_comp h],
--   simp only [mul_neg_eq_neg_mul_symm, mul_comm, add_left_neg],
-- end

-- lemma quick_inner_I_one (h : differentiable_at ℂ f z) :
-- (inner (fderiv ℝ f z I) (fderiv ℝ f z 1) : ℝ) = 0 :=
-- begin
--   let h' := h.restrict_scalars ℝ,
--   rw [real_inner_eq_re_inner, is_R_or_C.inner_apply],
--   rw fderiv_decomp_one h',
--   simp,
--   rw [quick_re_comp z I h', quick_im_comp _ I h', 
--       fderiv_re_comp_eq_neg_fderiv_im_comp h, ← fderiv_re_comp_eq_fderiv_im_comp h],
--   rw [← neg_mul_eq_neg_mul, mul_comm, add_left_neg],
-- end

-- lemma quick_inner_I_I (h : differentiable_at ℂ f z) :
-- (inner (fderiv ℝ f z I) (fderiv ℝ f z I) : ℝ) = (fderiv ℝ (re ∘ f) z 1) * fderiv ℝ (re ∘ f) z 1 + (fderiv ℝ (im ∘ f) z 1) * fderiv ℝ (im ∘ f) z 1 :=
-- begin
--   let h' := h.restrict_scalars ℝ,
--   rw [real_inner_eq_re_inner, is_R_or_C.inner_apply],
--   rw fderiv_decomp_I h',
--   simp,
--   rw [fderiv_re_comp_eq_neg_fderiv_im_comp h, ← fderiv_re_comp_eq_fderiv_im_comp h,
--       neg_mul_neg, add_comm],
-- end

-- lemma quick_inner_one_I' (h : differentiable_at ℝ f z)
-- {g : ℂ → ℂ} (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- (inner (fderiv ℝ f z 1) (fderiv ℝ f z I) : ℝ) = 0 :=
-- begin
--   rw [real_inner_eq_re_inner, is_R_or_C.inner_apply],
--   rw fderiv_decomp_one h,
--   simp,
--   rw [quick_re_comp z I h, quick_im_comp _ I h, 
--       fderiv_re_comp_eq_fderiv_im_comp' h hg Hg, eq_neg_iff_eq_neg.mp (fderiv_re_comp_eq_neg_fderiv_im_comp' h hg Hg)],
--   simp only [mul_neg_eq_neg_mul_symm, mul_comm, add_right_neg],
-- end

-- lemma quick_inner_I_one' (h : differentiable_at ℝ f z)
-- {g : ℂ → ℂ} (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- (inner (fderiv ℝ f z I) (fderiv ℝ f z 1) : ℝ) = 0 :=
-- begin
--   rw [real_inner_eq_re_inner, is_R_or_C.inner_apply],
--   rw fderiv_decomp_one h,
--   simp,
--   rw [quick_re_comp z I h, quick_im_comp _ I h, 
--       fderiv_re_comp_eq_fderiv_im_comp' h hg Hg, eq_neg_iff_eq_neg.mp (fderiv_re_comp_eq_neg_fderiv_im_comp' h hg Hg)],
--   simp only [mul_neg_eq_neg_mul_symm, mul_comm, add_right_neg],
-- end

-- lemma quick_inner_I_I' (h : differentiable_at ℝ f z)
-- {g : ℂ → ℂ} (hg : differentiable_at ℂ g z) (Hg : f = conj ∘ g) :
-- (inner (fderiv ℝ f z I) (fderiv ℝ f z I) : ℝ) = (fderiv ℝ (re ∘ f) z 1) * fderiv ℝ (re ∘ f) z 1 + (fderiv ℝ (im ∘ f) z 1) * fderiv ℝ (im ∘ f) z 1 :=
-- begin
--   rw [real_inner_eq_re_inner, is_R_or_C.inner_apply],
--   rw fderiv_decomp_I h,
--   simp,
--   rw [fderiv_re_comp_eq_neg_fderiv_im_comp' h hg Hg, ← fderiv_re_comp_eq_fderiv_im_comp' h hg Hg,
--       neg_mul_neg, add_comm],
-- end

-- lemma quick_inner_decomp (u v : ℂ) :
-- (u.re * v.re + u.im * v.im : ℝ) = inner u v := by rw [real_inner_eq_re_inner, is_R_or_C.inner_apply]; simp

-- theorem conformal_at_if_real_deriv_ne_zero_of_holomorph_or_antiholomorph
-- {f : ℂ → ℂ} {z : ℂ} (h : differentiable_at ℝ f z) (H : ¬ fderiv ℝ f z 1 = 0) :
-- (differentiable_at ℂ f z ∨ ∃ (g : ℂ → ℂ) (hg : differentiable_at ℂ g z), f = conj ∘ g) →
-- conformal_at f z := λ p,
-- begin
--   let M := (linear_map.to_matrix basis_one_I basis_one_I) (fderiv ℝ f z),
--   have : ¬ (complex_jacobian_at h).det = 0 :=
--   begin
--     cases p,
--     exact ne_of_gt ((complex_jacobian_at_det_pos_iff_holomorph_fderiv_ne_zero p).mpr H),
--     rcases p with ⟨g, hg, Hg⟩,
--     exact ne_of_lt ((complex_jacobian_at_det_neg_iff_antiholomorph_fderiv_ne_zero h hg Hg).mpr H),
--   end,
--   have H' : ¬ M.det = 0 := by rw (real_fderiv_to_matrix h).symm at this; exact this,
--   let F := matrix.to_linear_equiv basis_one_I M (is_unit.mk0 _ H'),
--   let f' := F.to_continuous_linear_equiv,
--   have step₁ : (f' : ℂ → ℂ) = (F : ℂ → ℂ) := rfl,
--   have step₂ : (F : ℂ → ℂ) = fderiv ℝ f z :=
--   begin
--     simp only [F, M],
--     rw [← linear_equiv.to_fun_eq_coe],
--     simp only [matrix.to_linear_equiv, matrix.to_lin_to_matrix],
--     trivial,
--   end,
--   have minor₁ : ⇑f' = fderiv ℝ f z := by rw [step₁, step₂],
--   have minor₂ : f'.to_continuous_linear_map = fderiv ℝ f z :=
--     continuous_linear_map.ext (λ x, by simp only [continuous_linear_equiv.coe_def_rev, continuous_linear_equiv.coe_apply]; rw minor₁),
--   have minor₃ : has_fderiv_at f f'.to_continuous_linear_map z := by rw minor₂; exact h.has_fderiv_at,
--   cases p,
--   {
--     let c := (complex_jacobian_at h).det,
--     have hc : c > 0 := (complex_jacobian_at_det_pos_iff_holomorph_fderiv_ne_zero p).mpr H,
--     rw conformal_at_iff minor₃,
--     use [c, hc], intros u v,
--     rw [minor₁, inner_fderiv_fderiv _ _, quick_inner_one_I p, quick_inner_I_one p, 
--         mul_zero, mul_zero, add_zero, add_zero, quick_inner_one_one h, quick_inner_I_I p,
--         ← complex_jacobian_at_det_eq_holomorph p, ← add_mul, quick_inner_decomp],
--     simp only [c, mul_comm],
--   },
--   {
--     rcases p with ⟨g, hg, Hg⟩,
--     let c := -(complex_jacobian_at h).det,
--     have hc : c > 0 := let q := 
--       (neg_lt_neg_iff.mpr $ (complex_jacobian_at_det_neg_iff_antiholomorph_fderiv_ne_zero h hg Hg).mpr H) 
--     in by rw neg_zero at q; exact q,
--     rw conformal_at_iff minor₃,
--     use [c, hc], intros u v,
--     rw [minor₁, inner_fderiv_fderiv _ _, quick_inner_one_I' h hg Hg, quick_inner_I_one' h hg Hg, 
--         mul_zero, mul_zero, add_zero, add_zero, quick_inner_one_one h, quick_inner_I_I' h hg Hg,
--         ← add_mul, quick_inner_decomp],
--     simp only [c, mul_comm],
--     rw [complex_jacobian_at_det_eq_antiholomorph h hg Hg, neg_neg],
--   },
-- end

-- theorem conformal_if_all_real_deriv_ne_zero_of_holomorph_or_antiholomorph
-- {f : ℂ → ℂ} (h : ∀ (x : ℂ), differentiable_at ℝ f x) (H : ∀ (x : ℂ), ¬ fderiv ℝ f x 1 = 0) :
-- (∀ (x : ℂ), (differentiable_at ℂ f x ∨ ∃ (g : ℂ → ℂ) (hg : differentiable_at ℂ g x), f = conj ∘ g)) →
-- conformal f := λ hf x, conformal_at_if_real_deriv_ne_zero_of_holomorph_or_antiholomorph (h x) (H x) (hf x)



