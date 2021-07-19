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

section conformal

def conformal_at 
{X Y : Type*} [inner_product_space ℝ X] [inner_product_space ℝ Y] 
(f : X → Y) (x : X) :=
∃ (f' : X →L[ℝ] Y) (c : ℝ) (hc : c ≠ 0) (lie : X ≃ₗᵢ[ℝ] Y),
has_fderiv_at f f' x ∧ ⇑f' = (λ y, c • y) ∘ lie

def conformal 
{X Y : Type*} [inner_product_space ℝ X] [inner_product_space ℝ Y]
(f : X → Y) := ∀ (x : X), conformal_at f x

variables {X Y : Type*} [inner_product_space ℝ X] [inner_product_space ℝ Y] 

theorem conformal_at.differentiable_at {f : X → Y} {x : X} (h : conformal_at f x) :
differentiable_at ℝ f x := let ⟨f', c, hc, lie, h₁, h₂⟩ := h in h₁.differentiable_at

theorem conformal.differentiable {f : X → Y} (h : conformal f) :
differentiable ℝ f := λ x, (h x).differentiable_at

theorem conformal_at.id (x : X) : conformal_at id x := 
⟨continuous_linear_map.id ℝ X, 1, one_ne_zero, linear_isometry_equiv.refl ℝ X, ⟨has_fderiv_at_id _, by ext; simp only [function.comp_app, linear_isometry_equiv.coe_refl, id, one_smul, continuous_linear_map.id_apply]⟩⟩

theorem conformal.id : conformal (id : X → X) := λ x, conformal_at.id x

theorem conformal_at.const_smul {c : ℝ} (h : c ≠ 0) (x : X) : conformal_at (λ (x': X), c • x') x :=
⟨c • continuous_linear_map.id ℝ X, c, h, linear_isometry_equiv.refl ℝ X, ⟨by apply has_fderiv_at.const_smul (has_fderiv_at_id x) c, by ext; simp only [linear_isometry_equiv.coe_refl, id, continuous_linear_map.id_apply, continuous_linear_map.smul_apply, function.comp_app]⟩⟩

theorem conformal.const_smul {c : ℝ} (h : c ≠ 0) : 
conformal (λ (x : X), c • x) := λ x, conformal_at.const_smul h x

variables {Z : Type*} [inner_product_space ℝ Z]

theorem conformal_at.comp {f : X → Y} {g : Y → Z} {x : X} 
(hf : conformal_at f x) (hg : conformal_at g (f x)) :
conformal_at (g ∘ f) x :=
begin
  rcases hf with ⟨f', cf, hcf, lief, hf₁, hf₂⟩,
  rcases hg with ⟨g', cg, hcg, lieg, hg₁, hg₂⟩,
  use [g'.comp f', cg * cf, mul_ne_zero hcg hcf, lief.trans lieg],
  exact ⟨has_fderiv_at.comp x hg₁ hf₁,
        by ext; rw [continuous_linear_map.coe_comp' f' g', hf₂, hg₂]; 
        simp [function.comp_app]; exact smul_smul cg cf _⟩,
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
    rcases h' with ⟨f₁, c₁, hc₁, lie, h₁, h₂⟩,
    use [c₁ ^ 2, sq_pos_of_ne_zero _ hc₁],
    intros u v,
    rw [← continuous_linear_equiv.coe_coe f', 
        ← continuous_linear_equiv.coe_def_rev f', has_fderiv_at.unique h h₁, h₂],
    simp only [function.comp_apply, real_inner_smul_left, real_inner_smul_right, 
               linear_isometry_equiv.inner_map_map],
    rw [← mul_assoc, pow_two],
  },
  {
    intros h',
    rcases h' with ⟨c₁, hc₁, huv⟩,
    let c := real.sqrt c₁⁻¹,
    have hc : c ≠ 0 := λ w, by simp only [c] at w; 
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
    exact ⟨f'.to_continuous_linear_map, c⁻¹, inv_ne_zero hc, f₁.isometry_of_inner key, ⟨h, minor'⟩⟩,
  },
end

def conformal_at.char_fun {f : X → Y} (x : X) {f' : X ≃L[ℝ] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) (H : conformal_at f x) : ℝ :=
by choose c hc huv using (conformal_at_iff h).mp H; exact c

theorem conformal_at_preserves_angle {f : X → Y} {x : X} {f' : X ≃L[ℝ] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) (H : conformal_at f x) :
∀ (u v : X), inner_product_geometry.angle (f' u) (f' v) = inner_product_geometry.angle u v :=
begin
  intros u v,
  repeat {rw inner_product_geometry.angle},
  suffices new : inner (f' u) (f' v) / (∥f' u∥ * ∥f' v∥) = inner u v / (∥u∥ * ∥v∥),
  { rw new, },
  {
    rcases H with ⟨f₁, c₁, hc₁, lie, h₁, h₂⟩,
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
        ... = inner u v / (∥u∥ * ∥v∥) : by rw mul_div_mul_left _ _ hc₁,                  
  },
end

end conformal

section conformal_groupoid

variables {E F G: Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] [inner_product_space ℝ G]

def conformal_on (f : E → F) (s : set E) := ∀ (x : E), x ∈ s → conformal_at f x

lemma conformal.conformal_on (f : E → F) (h : conformal f) :
conformal_on f set.univ := λ x hx, h x

lemma conformal_on.comp {f : E → E} {g :E → E}
{u v : set E} (hf : conformal_on f u) (hg : conformal_on g v) :
conformal_on (g ∘ f) (u ∩ f⁻¹' v) := λ x hx, (hf x hx.1).comp (hg (f x) (set.mem_preimage.mp hx.2))

lemma conformal_on.congr {f : E → E} {g :E → E}
{u : set E} (hu : is_open u) (h : ∀ (x : E), x ∈ u → g x = f x) (hf : conformal_on f u) :
conformal_on g u := λ x hx, let ⟨f', c, hc, lie, h₁, h₂⟩ := hf x hx in
begin
  have : has_fderiv_at g f' x :=
  begin
    apply h₁.congr_of_eventually_eq,
    rw filter.eventually_eq_iff_exists_mem,
    use [u, hu.mem_nhds hx],
    exact h,
  end,
  exact ⟨f', c, hc, lie, ⟨this, h₂⟩⟩,
end

def conformal_pregroupoid : pregroupoid E :=
{
  property := λ f u, conformal_on f u,
  comp := λ f g u v hf hg hu hv huv, hf.comp hg,
  id_mem := conformal.conformal_on id conformal.id,
  locality := λ f u hu h x hx, let ⟨v, h₁, h₂, h₃⟩ := h x hx in h₃ x ⟨hx, h₂⟩,
  congr := λ f g u hu h hf, conformal_on.congr hu h hf,
}

def conformal_groupoid : structure_groupoid E := conformal_pregroupoid.groupoid

end conformal_groupoid

-- TODO : rename and polish
section complex_conformal

open complex

variables {f : ℂ → ℂ} {z : ℂ} {g : ℂ →L[ℝ] ℂ}

theorem quick0 (a : circle) : is_linear_map ℂ (rotation a) :=
{
  map_add := (rotation a).map_add,
  map_smul := λ s x, by simp only [rotation_apply, smul_eq_mul, mul_assoc, mul_comm],
}

-- Is the statement `is_linear_map ℂ g` the best way to say `g` is `ℂ`-linear?
lemma quick1 (hz : ⇑g ≠ (λ x, (0 : ℂ))) :
is_linear_map ℂ g → ∃ (c : ℝ) (hc : c ≠ 0) (lie : ℂ ≃ₗᵢ[ℝ] ℂ), ⇑g = (λ y, c • y) ∘ lie :=
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
lemma quick2 (hz : ⇑g ≠ (λ x, (0 : ℂ))) :
(∃ (g' : ℂ →L[ℂ] ℂ), ⇑g = conj ∘ g')  → ∃ (c : ℝ) (hc : c ≠ 0) (lie : ℂ ≃ₗᵢ[ℝ] ℂ), ⇑g = (λ y, c • y) ∘ lie :=
begin
  intro h, rcases h with ⟨g', hg⟩,
  have : ⇑g' ≠ (λ x, (0 : ℂ)) := λ w,
  begin
    rw w at hg,
    have minor : ⇑g = (λ x, (0 : ℂ)) := by funext; rw hg; simp only [function.comp_app]; rw conj_eq_zero,
    exact hz minor,
  end,
  let p := g'.to_linear_map.is_linear,
  rw [continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe] at p,
  rcases @quick1 (g'.restrict_scalars ℝ) this p with ⟨c, hc, lie, hg'⟩,
  simp only [continuous_linear_map.coe_restrict_scalars'] at hg',
  use [c, hc, lie.trans conj_lie],
  rw [hg, hg'], funext, simp only [function.comp_app],
  rw [← complex.conj_lie_apply, conj_lie.map_smul, linear_isometry_equiv.coe_trans],
end

-- ℂ-antilinear or being the conjugate of a ℂ-linear map?
lemma quick3 (h : ∃ (c : ℝ) (hc : c ≠ 0) (lie : ℂ ≃ₗᵢ[ℝ] ℂ), ⇑g = (λ y, c • y) ∘ lie) :
(is_linear_map ℂ g ∨ ∃ (g' : ℂ →L[ℂ] ℂ), ⇑g = conj ∘ g') ∧ ⇑g ≠ (λ x, (0 : ℂ)) :=
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

-- Not sure if we need this lemma since eventually we will split it eventually
theorem main_aux:
(∃ (c : ℝ) (hc : c ≠ 0) (lie : ℂ ≃ₗᵢ[ℝ] ℂ), ⇑g = (λ y, c • y) ∘ lie) ↔ (is_linear_map ℂ g ∨ ∃ (g' : ℂ →L[ℂ] ℂ), ⇑g = conj ∘ g') ∧ ⇑g ≠ (λ x, (0 : ℂ)) :=
(iff_iff_implies_and_implies _ _).mpr (and.intro quick3 $ λ p, or.elim p.1 (quick1 p.2) (quick2 p.2))

theorem main (h : differentiable_at ℝ f z) :
((differentiable_at ℂ f z ∨ ∃ (g : ℂ → ℂ) (hg : differentiable_at ℂ g z), f = conj ∘ g) ∧ fderiv ℝ f z 1 ≠ 0) ↔ conformal_at f z :=
begin
  split,
  {
    intro H, rcases H with ⟨H₁, H₂⟩, 
    let f' := fderiv ℝ f z,
    have : ⇑f' ≠ (λ x, (0 : ℂ)) := λ w, by rw w at H₂; simp only [function.app] at H₂; exact H₂ rfl,
    cases H₁,
    { 
      rcases quick1 this (quick_complex_linear H₁) with ⟨c, hc, lie, h'⟩,
      exact ⟨f', c, hc, lie, ⟨h.has_fderiv_at, h'⟩⟩,
    },
    { 
      rcases H₁ with ⟨g, hg, hfg⟩,
      have  minor: ⇑f' = conj ∘ (fderiv ℂ g z) :=
      begin
        funext, simp only [function.comp_app],
        let q := quick_conj_comp_aux z x (hg.restrict_scalars ℝ),
        rw quick_eq_fderiv hg at q, simp only [f', hfg], rw q,
      end,
      rcases quick2 this ⟨fderiv ℂ g z, minor⟩ with ⟨c, hc, lie, h'⟩,
      exact ⟨f', c, hc, lie, ⟨h.has_fderiv_at, h'⟩⟩,
    },
  },
  {
    intros H, rcases H with ⟨f', c, hc, lie, hf', H'⟩,
    let minor := hf'.fderiv.symm,
    rcases quick3 ⟨c, hc, lie, H'⟩ with ⟨h₁, h₂⟩,
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