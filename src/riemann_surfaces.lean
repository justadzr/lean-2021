import tactic
import analysis.calculus.iterated_deriv
import topology.continuous_function.polynomial
import topology.separation
import topology.path_connected
import analysis.complex.basic
import analysis.calculus.tangent_cone
import analysis.normed_space.units
import analysis.asymptotics.asymptotic_equivalent
import analysis.analytic.basic
import geometry.manifold.algebra.smooth_functions
import geometry.manifold.local_invariant_properties
import linear_algebra.finite_dimensional
import analysis.normed_space.inner_product
import topology.metric_space.basic
import analysis.calculus.formal_multilinear_series
import group_theory.coset
import complex_analysis_prep

open set complex classical filter asymptotics continuous_linear_map set metric is_open differentiable
open_locale topological_space classical nnreal asymptotics filter ennreal unit_interval

noncomputable theory

/-
We immitate the existing definition of smooth manifolds to define Riemann_surfaces
-/

def holomorph_pregroupoid : pregroupoid ℂ :=
{
  property := λ f s, differentiable_on ℂ f s,
  comp := λ f g u v hf hg hu hv huv z hz,
  begin
    rw _root_.differentiable_on at hf hg,
    apply differentiable_within_at.comp',
    { have : f z ∈ v := mem_preimage.mp (mem_of_mem_inter_right hz), exact hg (f z) this, },
    { exact hf z (set.mem_of_mem_inter_left hz), },
  end,
  id_mem := differentiable_on_id,
  locality := λ f u hu hx, differentiable_on_of_locally_differentiable_on hx,
  congr := λ f g u hu hx hf, (differentiable_on_congr hx).mpr hf,
}

def biholomorph_groupoid : structure_groupoid ℂ :=
holomorph_pregroupoid.groupoid

lemma of_set_mem_biholomorph_groupoid {s : set ℂ} (h : is_open s) :
local_homeomorph.of_set s h ∈ biholomorph_groupoid :=
begin
  rw [biholomorph_groupoid, mem_groupoid_of_pregroupoid],
  simp,
  exact differentiable_on_id,
end

instance : closed_under_restriction biholomorph_groupoid :=
(closed_under_restriction_iff_id_le _).mpr
begin
  apply structure_groupoid.le_iff.mpr,
  rintros e ⟨s, hs, h⟩,
  apply biholomorph_groupoid.eq_on_source' _ _ _ h,
  exact of_set_mem_biholomorph_groupoid hs,
end

class riemann_surface 
(X : Type*) [topological_space X] [t2_space X] 
[connected_space X] [charted_space ℂ X]
extends has_groupoid X biholomorph_groupoid : Prop

theorem riemann_surface.mk'
(X : Type*) [topological_space X] [t2_space X] 
[connected_space X] [charted_space ℂ X] 
[cstructure : has_groupoid X biholomorph_groupoid] : riemann_surface X :=
{
  .. cstructure
}

theorem riemann_surface_of_cstructure
(X : Type*) [topological_space X] [t2_space X] 
[connected_space X] [charted_space ℂ X]
(h : ∀ (e e' : local_homeomorph X ℂ), e ∈ atlas ℂ X → e' ∈ atlas ℂ X → 
(differentiable_on ℂ ⇑(e.symm.trans e') (e.symm.trans e').to_local_equiv.source)) :
riemann_surface X :=
{
  compatible :=
  begin
    haveI : has_groupoid X biholomorph_groupoid := has_groupoid_of_pregroupoid _ h,
    apply structure_groupoid.compatible,
  end
}

instance biholomorph_groupoid_of_ℂ : has_groupoid ℂ biholomorph_groupoid := 
{
  compatible := λ e e' he he', begin
    rw charted_space_self_atlas at he he',
    simp [he, he', biholomorph_groupoid.id_mem],
  end
}

instance : riemann_surface ℂ :=
{
  .. biholomorph_groupoid_of_ℂ
}

def complex_plane : model_with_corners ℂ ℂ ℂ := by apply model_with_corners_self

example (f : ℂ → ℂ) (s : set ℂ) (h : is_open s) : holomorph_pregroupoid.property f s → differentiable_on ℂ f s :=
begin
  intros h,
  exact h,
end

lemma biholomorph_groupoid_eq : 
biholomorph_groupoid = times_cont_diff_groupoid ⊤ complex_plane :=
begin
  apply le_antisymm,
  {
    rw structure_groupoid.le_iff,
    intros e he,
    rw [biholomorph_groupoid, mem_groupoid_of_pregroupoid] at he,
    rw [times_cont_diff_groupoid, mem_groupoid_of_pregroupoid, complex_plane] at ⊢,
    simp,
    split,
    { apply (smooth_on_iff_holomorph_on e e.open_source).mp, exact he.1, }, 
    { apply (smooth_on_iff_holomorph_on e.symm e.open_target).mp, exact he.2, },
  },
  {rw structure_groupoid.le_iff,
    intros e he,
    rw [biholomorph_groupoid, mem_groupoid_of_pregroupoid] at ⊢,
    rw [times_cont_diff_groupoid, mem_groupoid_of_pregroupoid, complex_plane] at he,
    simp at he,
    split,
    { apply (smooth_on_iff_holomorph_on e e.open_source).mpr, exact he.1, }, 
    { apply (smooth_on_iff_holomorph_on e.symm e.open_target).mpr, exact he.2, },
  },
end

lemma riemann_surface.smooth_manifold
(X : Type*) [topological_space X] [t2_space X] 
[connected_space X] [charted_space ℂ X] [riemann_surface X] :
smooth_manifold_with_corners complex_plane X :=
{
    compatible := λ e e' he he',
    begin
       --- Very bad proof here
      have : e.symm.trans e' ∈ biholomorph_groupoid := begin
        apply structure_groupoid.compatible,
        exact he,
        exact he',
      end,
      apply structure_groupoid.le_iff.mp (le_antisymm_iff.mp biholomorph_groupoid_eq).1,
      exact this,
    end
}

lemma topological_space.opens.riemann_surface
{X : Type*} [topological_space X] [t2_space X] 
[connected_space X] [charted_space ℂ X] [riemann_surface X]
(Y : topological_space.opens X) [connected_space Y] :
@riemann_surface Y _ _ _ (topological_space.opens.charted_space Y) :=
{
  .. Y.has_groupoid biholomorph_groupoid
}

lemma two_points_open : ∀ (x : ℂ) (s : set ℂ) (H: is_open s), x ∈ s → (∃ y, y ∈ s ∧ ¬ y = x) :=
begin
  intros x s hs hx,
  have minor₁ : ¬ s = {x} := by_contra (λ h, (crowded_space.def ℂ) x $ (not_not.mp h) ▸ hs),
  have minor₂ : ¬ s ⊆ {x} := by_contra (λ h, minor₁ $ subset.antisymm (not_not.mp h) $ λ x' hx', (set.eq_of_mem_singleton hx').symm ▸ hx),
  rw ← nonempty_diff at minor₂,
  rcases minor₂ with ⟨a, ha⟩,
  use a,
  rw [mem_diff_singleton, ne.def] at ha,
  exact ha,
end

instance riemann_surface_crowded_space (X : Type*) [topological_space X] [t2_space X] 
[connected_space X] [charted_space ℂ X] [riemann_surface X] : 
crowded_space X :=
{
  is_crowded := begin
    have : ∀ (x : X), ∃ y, ¬ y = x := λ x,
    begin
      have : ∃ (y' : ℂ), y' ∈ (chart_at ℂ x).to_local_equiv.target ∧ ¬ y' = (chart_at ℂ x).to_local_equiv x :=
      begin
        rcases two_points_open (chart_at ℂ x x) 
                                (chart_at ℂ x).to_local_equiv.target 
                                (chart_at ℂ x).open_target (mem_chart_target ℂ x),
        use w,
        exact h,
      end,
      rcases this with ⟨y', hy'₁, hy'₂⟩,
      use (chart_at ℂ x).to_local_equiv.symm y',
      by_contra w,
      rw [← local_equiv.left_inv (chart_at ℂ x).to_local_equiv (mem_chart_source ℂ x), 
          local_equiv.left_inv (chart_at ℂ x).to_local_equiv (mem_chart_source ℂ x)] at w,
      have : (chart_at ℂ x).to_local_equiv x = y' := begin
        nth_rewrite 1 ← w,
        rw local_equiv.right_inv (chart_at ℂ x).to_local_equiv hy'₁,
      end,
      exact hy'₂ this.symm,
    end,
    exact t1_space_connected_with_two_points_is_crowded X this,
  end,
}

variables {X Y Z : Type*}
[topological_space X] [t2_space X] [connected_space X] [charted_space ℂ X] [riemann_surface X]
[topological_space Y] [t2_space Y] [connected_space Y] [charted_space ℂ Y] [riemann_surface Y]
[topological_space Z] [t2_space Z] [connected_space Z] [charted_space ℂ Z] [riemann_surface Z]

def fholomorph_on (f : X → ℂ) {s : set X} (h : is_open s) :=
continuous_on f s ∧
∀ (ϕ : local_homeomorph X ℂ),
ϕ ∈ atlas ℂ X → differentiable_on ℂ (f ∘ ϕ.symm) (ϕ '' (ϕ.to_local_equiv.source ∩ s))

@[simp] theorem fholomorph_on.mono {f : X → ℂ} {s s': set X} {hs: is_open s} {hs' : is_open s'}
(h : fholomorph_on f hs) (H : s' ⊆ s) : fholomorph_on f hs' :=
begin
  split,
  exact continuous_on.mono h.1 H,
  {
    intros ϕ hϕ,
    have : ϕ '' (ϕ.to_local_equiv.source ∩ s') ⊆ ϕ '' (ϕ.to_local_equiv.source ∩ s) := 
      λ x hx, let ⟨v, ⟨hv₁, hv₂⟩, hv₃⟩ := hx in ⟨v, ⟨hv₁, H hv₂⟩, hv₃⟩,
    exact differentiable_on.mono (h.2 ϕ hϕ) this,
  },
end

def mholomorph (f : X → Y) :=
continuous f ∧
∀ (ϕ : local_homeomorph X ℂ) (ψ : local_homeomorph Y ℂ), 
ϕ ∈ atlas ℂ X → ψ ∈ atlas ℂ Y →
differentiable_on ℂ (ψ ∘ f ∘ ϕ.symm) (ϕ '' (ϕ.to_local_equiv.source ∩ f⁻¹' ψ.to_local_equiv.source))

lemma mholomorph_of_fholomorph_on_univ {f : X → ℂ} (hf : fholomorph_on f is_open_univ) :
mholomorph f  := and.intro
  (continuous_iff_continuous_on_univ.mpr hf.1)
  (begin
    intros e e' he he',
    rw charted_space_self_atlas at he',
    rw he',
    simp,
    rw ← set.inter_univ e.to_local_equiv.source,
    exact hf.2 e he,
  end)
--
lemma fholomorph_on.continuous {f : X → ℂ} {s : set X} {h : is_open s} (H : fholomorph_on f h) : continuous_on f s := H.1
lemma mholomorph.continuous {f : X → Y} (h : mholomorph f) : continuous f := h.1

@[simp] theorem fholomorph_on_const {s : set X} (h : is_open s) (c : ℂ) :
fholomorph_on (λ (x : X), c) h:=
begin
  split,
  exact continuous_on_const,
  intros ϕ hϕ,
  rw function.const_comp,
  exact differentiable_on_const c,
end
@[simp] theorem  mholomorph_const (c : Y) :
mholomorph (λ (x : X), c) :=
begin
  split,
  exact continuous_const,
  intros e e' he he',
  rw [function.const_comp, function.comp_const],
  exact differentiable_on_const (e' c),
end

@[simp] theorem fholomorph_on.mul {f g : X → ℂ} {s : set X} {h : is_open s} 
(hf : fholomorph_on f h) (hg : fholomorph_on g h) : fholomorph_on (λ (x : X), (f x) * g x) h :=
and.intro (continuous_on.mul hf.1 hg.1) (λ ϕ hϕ, differentiable_on.mul (hf.2 ϕ hϕ) $ hg.2 ϕ hϕ)

@[simp] theorem fholomorph_on.add {f g : X → ℂ} {s : set X} {h : is_open s} 
(hf : fholomorph_on f h) (hg : fholomorph_on g h) : fholomorph_on (λ (x : X), (f x) + g x) h :=
and.intro (continuous_on.add hf.1 hg.1) (λ ϕ hϕ, differentiable_on.add (hf.2 ϕ hϕ) $ hg.2 ϕ hϕ)

@[simp] theorem fholomorph_on.neg {f: X → ℂ} {s : set X} {h : is_open s} 
(hf : fholomorph_on f h) : fholomorph_on (λ (x : X), - f x) h :=
begin
  let g : X → ℂ := λ x, -1,
  have minor₁ : fholomorph_on g h := fholomorph_on_const h (-1 : ℂ),
  have minor₂ : (λ (x : X), - f x) = (λ (x : X),  (g x) * f x) := by simp,
  exact minor₂.symm ▸ fholomorph_on.mul minor₁ hf,
end

-- do we need this?
@[simp] theorem mholomorph.comp {f : X → Y} {g : Y → Z}
(hf : mholomorph f) (hg : mholomorph g) : mholomorph (g ∘ f) :=
begin
  sorry,
end

variables (U : set X) [is_open U] [is_connected U]

theorem eq_on_local_disk_around_accumulation_pt
{f g : X → Y} (hf : mholomorph f) (hg : mholomorph g)
{G : set X} (hG : set.eq_on f g G)
{z : X} (key₁ : z ∈ G) (hz : accumulation_pt X G z) :
∃ (U : set X), z ∈ U ∧ is_open U ∧ set.eq_on f g U :=
begin
  have minor₁ : set.eq_on f g G := hG,
  have minor₂ : f z = g z := hG key₁,
  let ϕ : local_homeomorph X ℂ := chart_at ℂ z, 
  let ψ : local_homeomorph Y ℂ := chart_at ℂ (f z),
  let πf : ℂ → ℂ := ψ ∘ f ∘ ϕ.symm,
  let πg : ℂ → ℂ := ψ ∘ g ∘ ϕ.symm,
  let W : set X := f⁻¹' ψ.to_local_equiv.source ∩ g⁻¹' ψ.to_local_equiv.source,
  let W' : set X := ϕ.to_local_equiv.source ∩ W,
  let V : set ℂ := ϕ '' W',
  have zmemW' : z ∈ W' := 
    ⟨mem_chart_source ℂ z,
      ⟨mem_chart_source ℂ (f z), 
      (minor₂ ▸ mem_chart_source ℂ (f z) : g z ∈ (chart_at ℂ (f z)).to_local_equiv.source)⟩⟩,
  have openW' : is_open W' := 
    is_open.inter ϕ.open_source (is_open.inter (is_open.preimage hf.1 ψ.open_source) $ is_open.preimage hg.1 ψ.open_source),
  have openV : is_open V := 
    local_homeomorph.image_open_of_open ϕ openW' (set.inter_subset_left _ W),
  have nonemptyW' : W'.nonempty := ⟨z, zmemW'⟩,
  have nonemptyV : V.nonempty := set.nonempty.image ϕ nonemptyW',
  rw metric.is_open_iff at openV,
  rcases openV (ϕ z) (set.mem_image_of_mem ϕ zmemW') with ⟨ε, hε, hball⟩,
  let ϕball := ball (ϕ z) ε,
  have Vsubset : V ⊆ ϕ.to_local_equiv.target :=
  begin
    intros v hv,
    have : V = ϕ '' W' := rfl,
    rw this at hv,
    rw local_homeomorph.image_eq_target_inter_inv_preimage ϕ (set.inter_subset_left _ W) at hv,
    exact hv.1,
  end,
  have W'subsetf : W' ⊆ f⁻¹' ψ.to_local_equiv.source := set.subset.trans (set.inter_subset_right _ W) (set.inter_subset_left _ _),
  have W'subsetg : W' ⊆ g⁻¹' ψ.to_local_equiv.source := set.subset.trans (set.inter_subset_right _ W) (set.inter_subset_right _ _),
  have fW'subsetsource : f '' W' ⊆ ψ.to_local_equiv.source := by rw ← set.image_subset_iff at W'subsetf; exact W'subsetf,
  have gW'subsetsource : g '' W' ⊆ ψ.to_local_equiv.source := by rw ← set.image_subset_iff at W'subsetg; exact W'subsetg,
  --have openϕball : is_open ϕball := metric.is_open_ball, 
  have πfdiffon : differentiable_on ℂ πf (ϕ '' (ϕ.to_local_equiv.source ∩ f⁻¹' ψ.to_local_equiv.source)) :=
    hf.2 ϕ ψ (chart_mem_atlas ℂ z) (chart_mem_atlas ℂ (f z)),
  have πgdiffon : differentiable_on ℂ πg (ϕ '' (ϕ.to_local_equiv.source ∩ g⁻¹' ψ.to_local_equiv.source)) :=
    hg.2 ϕ ψ (chart_mem_atlas ℂ z) (chart_mem_atlas ℂ (f z)),
  have πfϕballsubset : ϕball ⊆ ϕ '' (ϕ.to_local_equiv.source ∩ f⁻¹' ψ.to_local_equiv.source) := 
    λ v hv, let ⟨v', hv'⟩ := hball hv in ⟨v', ⟨⟨hv'.1.1, hv'.1.2.1⟩, hv'.2⟩⟩,
  have πgϕballsubset : ϕball ⊆ ϕ '' (ϕ.to_local_equiv.source ∩ g⁻¹' ψ.to_local_equiv.source) := 
    λ v hv, let ⟨v', hv'⟩ := hball hv in ⟨v', ⟨⟨hv'.1.1, hv'.1.2.2⟩, hv'.2⟩⟩,
  have ϕballsubset : ϕball ⊆ ϕ.to_local_equiv.target := λ v hv, 
  begin
    rw local_homeomorph.image_eq_target_inter_inv_preimage ϕ (set.inter_subset_left _ _) at πfϕballsubset,
    exact (πfϕballsubset hv).1,
  end, 
  have subkeyπf : differentiable_on ℂ πf ϕball := differentiable_on.mono πfdiffon πfϕballsubset,
  have subkeyπg : differentiable_on ℂ πg ϕball := differentiable_on.mono πgdiffon πgϕballsubset,
  let superkeyset := ϕball,
  have superkeyopen : is_open superkeyset := metric.is_open_ball,
  have superkeyconnected : is_connected ϕball := 
    (is_open.is_connected_iff_is_path_connected metric.is_open_ball).mp 
          (convex.is_path_connected (convex_ball (ϕ z) ε) $ metric.nonempty_ball hε),
  have superkeymem : ϕ z ∈ superkeyset := metric.mem_ball_self hε,
  have superkeymem' : ϕ z ∈  ϕ '' (G ∩ ϕ.to_local_equiv.source) ∩ superkeyset := ⟨⟨z, ⟨⟨key₁, mem_chart_source ℂ z⟩, rfl⟩⟩, superkeymem⟩,
  have subkeyaccum : accumulation_pt ℂ (ϕ '' (G ∩ ϕ.to_local_equiv.source)) (ϕ z) := 
    accumulation_pt_local_homeomorph (accumulation_pt_open_inter ϕ.open_source (mem_chart_source ℂ z) hz) (mem_chart_source ℂ z),
  have superkeyaccum : accumulation_pt ℂ (ϕ '' (G ∩ ϕ.to_local_equiv.source) ∩ superkeyset) (ϕ z) := accumulation_pt_open_inter superkeyopen superkeymem subkeyaccum,
  -- have superkeyeq₁ : set.eq_on πf πg (ϕ '' (G ∩ ϕ.to_local_equiv.source)) :=
  have superkeyeq₁ : set.eq_on πf πg (ϕ '' (G ∩ ϕ.to_local_equiv.source) ∩ superkeyset) :=
  begin
    intros m hm,
    rcases hm with ⟨hm₁, hm₂⟩,
    have trivial₀ : ϕ (ϕ.symm m) = m := local_homeomorph.right_inv ϕ (ϕballsubset hm₂),
    have trivial₁ : ϕ.symm m ∈ ϕ.to_local_equiv.source := local_homeomorph.map_target ϕ (ϕballsubset hm₂),
    rw ← trivial₀ at hm₁,
    have trivial₂ : ϕ.symm m ∈ G := 
      ((set.inj_on.mem_image_iff ϕ.to_local_equiv.inj_on (set.inter_subset_right G ϕ.to_local_equiv.source) trivial₁).mp hm₁).1,
    exact calc πf m = (ψ ∘ f ∘ ϕ.symm) m : rfl
      --- no simp to make the code faster
        ... = ((ψ ∘ f) ∘ ϕ.symm) m : by rw (function.comp.assoc ψ f ϕ.symm).symm
        ... = (ψ ∘ f) (ϕ.symm m) : function.comp_app (ψ ∘ f) ϕ.symm m
        ... = ψ (f (ϕ.symm m)) : function.comp_app ψ f (ϕ.symm m)
        ... = ψ (g (ϕ.symm m)) : by rw hG trivial₂
        ... = (ψ ∘ g) (ϕ.symm m) : (function.comp_app ψ g (ϕ.symm m)).symm
        ... = ((ψ ∘ g) ∘ ϕ.symm) m : (function.comp_app (ψ ∘ g) ϕ.symm m).symm
        ... = (ψ ∘ g ∘ ϕ.symm) m : by rw (function.comp.assoc ψ g ϕ.symm)
        ... = πg m : rfl,
  end,
  have superkeyeq₂ : set.eq_on πf πg superkeyset :=
    identity_theorem superkeyopen superkeyconnected subkeyπf subkeyπg 
      (set.inter_subset_right (ϕ '' (G ∩ ϕ.to_local_equiv.source)) superkeyset) 
      superkeyeq₁ superkeymem' superkeyaccum,
  let U := ϕ.symm '' ϕball,
  have minor₃ : U = ϕ.to_local_equiv.source ∩ ϕ⁻¹' ϕball := 
  begin
    have : U = ϕ.symm '' ϕball := rfl,
    rw local_homeomorph.symm_image_eq_source_inter_preimage _ ϕballsubset at this,
    exact this, 
  end,
  have superkeymemU : z ∈ U := ⟨ϕ z, ⟨mem_ball_self hε, local_homeomorph.left_inv ϕ (mem_chart_source ℂ z)⟩⟩,
  have superkeyopenU : is_open U := 
  begin
    let q := local_homeomorph.preimage_open_of_open ϕ superkeyopen,
    rw (local_homeomorph.symm_image_eq_source_inter_preimage _ ϕballsubset).symm at q,
    exact q,
  end,
  have superkeyeqU : set.eq_on f g U :=
  begin
    intros m hm,
    rcases (set.mem_image _ ϕball _).mp hm with ⟨m', h₁, h₂⟩,
    rw minor₃ at hm,
    have trivial₀ : m ∈ ϕ.to_local_equiv.source := hm.1,
    have trivial₁ : m ∈ W' := 
    begin
      rcases hball hm.2 with ⟨m₁, hm₁, hm₁'⟩,
      let q := ϕ.to_local_equiv.inj_on ((set.inter_subset_left _ W) hm₁) trivial₀ hm₁',
      rw q at hm₁,
      exact hm₁,
    end,
    have trivial₂ : ϕ m ∈ ϕball := hm.2,
    exact calc f m = (ψ.symm) (ψ $ f m) : (local_homeomorph.left_inv ψ $ fW'subsetsource $ mem_image_of_mem f trivial₁).symm
      ... = (ψ.symm) (ψ $ f $ ϕ.symm $ ϕ m) : by nth_rewrite 0 ← local_homeomorph.left_inv ϕ trivial₀
      ... = (ψ.symm) (πf $ ϕ m) : by simp
      ... = (ψ.symm) (πg $ ϕ m) : by rw superkeyeq₂ trivial₂
      ... = (ψ.symm) (ψ $ g $ ϕ.symm $ ϕ m) : by simp
      ... = (ψ.symm) (ψ $ g m) : by rw local_homeomorph.left_inv ϕ trivial₀
      ... = g m : (local_homeomorph.left_inv ψ $ gW'subsetsource $ mem_image_of_mem g trivial₁)
  end,
  use U,
  exact ⟨superkeymemU, superkeyopenU, superkeyeqU⟩,
end

theorem nondiscrete_closure_of_eq_mholomorph
{f g : X → Y} (hf : mholomorph f) (hg : mholomorph g)
{G : set X} (key₁ : is_open G) (hG₂ : set.eq_on f g G)
{z : X} (hz : z ∈ closure G) :
∃ (U : set X), z ∈ U ∧ is_open U ∧ set.eq_on f g U :=
begin
    have : closure G = frontier G ∪ G := by rw [is_open.frontier_eq key₁, diff_union_of_subset subset_closure],
    by_cases p : z ∈ frontier G,
    { 
      have minor₁ : set.eq_on f g G := hG₂,
      have minor₂ : f z = g z := (set.eq_on.mono frontier_subset_closure $ set.eq_on.closure minor₁ hf.continuous hg.continuous) p,
      let ϕ : local_homeomorph X ℂ := chart_at ℂ z, 
      let ψ : local_homeomorph Y ℂ := chart_at ℂ (f z),
      let πf : ℂ → ℂ := ψ ∘ f ∘ ϕ.symm,
      let πg : ℂ → ℂ := ψ ∘ g ∘ ϕ.symm,
      let W : set X := f⁻¹' ψ.to_local_equiv.source ∩ g⁻¹' ψ.to_local_equiv.source,
      let W' : set X := ϕ.to_local_equiv.source ∩ W,
      let V : set ℂ := ϕ '' (G ∩ W'),
      have zmemW' : z ∈ W' := 
        ⟨mem_chart_source ℂ z,
          ⟨mem_chart_source ℂ (f z), 
          (minor₂ ▸ mem_chart_source ℂ (f z) : g z ∈ (chart_at ℂ (f z)).to_local_equiv.source)⟩⟩,
      have openW' : is_open W' := 
        is_open.inter ϕ.open_source (is_open.inter (is_open.preimage hf.1 ψ.open_source) $ is_open.preimage hg.1 ψ.open_source),
      have openpreV : is_open (G ∩ W') := is_open.inter key₁ openW',
      have openV : is_open V := 
        local_homeomorph.image_open_of_open ϕ openpreV (set.subset.trans (set.inter_subset_right G W') $ set.inter_subset_left _ W),
      have openϕW' : is_open (ϕ '' W') := local_homeomorph.image_open_of_open ϕ openW' (set.inter_subset_left _ W),
      have nonemptypreV : (G ∩ W').nonempty := 
      begin
        let p' := frontier_subset_closure p,
        rw _root_.mem_closure_iff at p',
        specialize p' W' openW' zmemW',
        rw set.inter_comm at p',
        exact p',
      end,
      have nonemptyV : V.nonempty := set.nonempty.image ϕ nonemptypreV,
      have memclosurepreV : z ∈ closure (G ∩ W') := mem_closure_inter (frontier_subset_closure p) openW' zmemW',
      have memclosureV : ϕ z ∈ closure V := mem_image_closure_mem_closure memclosurepreV (mem_chart_source ℂ z),
      rw metric.is_open_iff at openϕW',
      rcases openϕW' (ϕ z) (set.mem_image_of_mem ϕ zmemW') with ⟨ε, hε, hball⟩,
      let ϕball := ball (ϕ z) ε,
      have Vsubset : V ⊆ ϕ.to_local_equiv.target :=
      begin
        intros v hv,
        have : V = ϕ '' (G ∩ W') := rfl,
        rw this at hv,
        rw local_homeomorph.image_eq_target_inter_inv_preimage ϕ (set.subset.trans (set.inter_subset_right G W') (set.inter_subset_left _ W)) at hv,
        exact hv.1,
      end,
      have W'subsetf : W' ⊆ f⁻¹' ψ.to_local_equiv.source := set.subset.trans (set.inter_subset_right _ W) (set.inter_subset_left _ _),
      have W'subsetg : W' ⊆ g⁻¹' ψ.to_local_equiv.source := set.subset.trans (set.inter_subset_right _ W) (set.inter_subset_right _ _),
      have fW'subsetsource : f '' W' ⊆ ψ.to_local_equiv.source := by rw ← set.image_subset_iff at W'subsetf; exact W'subsetf,
      have gW'subsetsource : g '' W' ⊆ ψ.to_local_equiv.source := by rw ← set.image_subset_iff at W'subsetg; exact W'subsetg,
      have openϕball : is_open ϕball := metric.is_open_ball,
      have connectedϕball : is_connected ϕball := 
        (is_open.is_connected_iff_is_path_connected metric.is_open_ball).mp 
          (convex.is_path_connected (convex_ball (ϕ z) ε) $ metric.nonempty_ball hε),
      have πfdiffon : differentiable_on ℂ πf (ϕ '' (ϕ.to_local_equiv.source ∩ f⁻¹' ψ.to_local_equiv.source)) :=
        hf.2 ϕ ψ (chart_mem_atlas ℂ z) (chart_mem_atlas ℂ (f z)),
      have πgdiffon : differentiable_on ℂ πg (ϕ '' (ϕ.to_local_equiv.source ∩ g⁻¹' ψ.to_local_equiv.source)) :=
        hg.2 ϕ ψ (chart_mem_atlas ℂ z) (chart_mem_atlas ℂ (f z)),
      have πfϕballsubset : ϕball ⊆ ϕ '' (ϕ.to_local_equiv.source ∩ f⁻¹' ψ.to_local_equiv.source) := 
        λ v hv, let ⟨v', hv'⟩ := hball hv in ⟨v', ⟨⟨hv'.1.1, hv'.1.2.1⟩, hv'.2⟩⟩,
      have πgϕballsubset : ϕball ⊆ ϕ '' (ϕ.to_local_equiv.source ∩ g⁻¹' ψ.to_local_equiv.source) := 
        λ v hv, let ⟨v', hv'⟩ := hball hv in ⟨v', ⟨⟨hv'.1.1, hv'.1.2.2⟩, hv'.2⟩⟩,
      have ϕballsubset : ϕball ⊆ ϕ.to_local_equiv.target := λ v hv, 
      begin
        rw local_homeomorph.image_eq_target_inter_inv_preimage ϕ (set.inter_subset_left _ _) at πfϕballsubset,
        exact (πfϕballsubset hv).1,
      end, 
      have subkeyπf : differentiable_on ℂ πf ϕball := differentiable_on.mono πfdiffon πfϕballsubset,
      have subkeyπg : differentiable_on ℂ πg ϕball := differentiable_on.mono πgdiffon πgϕballsubset,
      let superkeyset := ϕball ∩ V,
      have superkeyopen : is_open superkeyset := is_open.inter metric.is_open_ball openV,
      have superkeynonempty : superkeyset.nonempty := 
      begin
        rw _root_.mem_closure_iff at memclosureV,
        exact memclosureV ϕball metric.is_open_ball (metric.mem_ball_self hε),
      end,
      have superkeyeq₁ : set.eq_on πf πg superkeyset :=
      begin
        intros m hm,
        rcases hm with ⟨hm₁, hm₂⟩,
        have trivial₀ : ϕ (ϕ.symm m) = m := local_homeomorph.right_inv ϕ (Vsubset hm₂),
        have trivial₁ : ϕ.symm m ∈ ϕ.source := local_homeomorph.map_target ϕ (Vsubset hm₂),
        rw ←trivial₀ at hm₂,
        have trivial₂ : ϕ.symm m ∈ G := 
          ((set.inj_on.mem_image_iff ϕ.to_local_equiv.inj_on (set.subset.trans (set.inter_subset_right G W') (set.inter_subset_left _ W)) trivial₁).mp hm₂).1,
        exact calc πf m = (ψ ∘ f ∘ ϕ.symm) m : rfl
        --- no simp to make the code faster
         ... = ((ψ ∘ f) ∘ ϕ.symm) m : by rw (function.comp.assoc ψ f ϕ.symm).symm
         ... = (ψ ∘ f) (ϕ.symm m) : function.comp_app (ψ ∘ f) ϕ.symm m
         ... = ψ (f (ϕ.symm m)) : function.comp_app ψ f (ϕ.symm m)
         ... = ψ (g (ϕ.symm m)) : by rw minor₁ trivial₂
         ... = (ψ ∘ g) (ϕ.symm m) : (function.comp_app ψ g (ϕ.symm m)).symm
         ... = ((ψ ∘ g) ∘ ϕ.symm) m : (function.comp_app (ψ ∘ g) ϕ.symm m).symm
         ... = (ψ ∘ g ∘ ϕ.symm) m : by rw (function.comp.assoc ψ g ϕ.symm)
         ... = πg m : rfl,
      end,
      have superkeyeq₂ : set.eq_on πf πg ϕball :=
        eq_of_eq_on_open openϕball connectedϕball subkeyπf subkeyπg superkeyopen superkeynonempty superkeyeq₁ (set.inter_subset_left _ V),
      let U := ϕ.symm '' ϕball,
      have minor₃ : U = ϕ.to_local_equiv.source ∩ ϕ⁻¹' ϕball := 
      begin
        have : U = ϕ.symm '' ϕball := rfl,
        rw local_homeomorph.symm_image_eq_source_inter_preimage _ ϕballsubset at this,
        exact this, 
      end,
      have superkeymemU : z ∈ U := ⟨ϕ z, ⟨mem_ball_self hε, local_homeomorph.left_inv ϕ (mem_chart_source ℂ z)⟩⟩,
      have superkeyopenU : is_open U := 
      begin
        let q := local_homeomorph.preimage_open_of_open ϕ openϕball,
        rw (local_homeomorph.symm_image_eq_source_inter_preimage _ ϕballsubset).symm at q,
        exact q,
      end,
      have superkeyeqU : set.eq_on f g U :=
      begin
        intros m hm,
        rcases (set.mem_image _ ϕball _).mp hm with ⟨m', h₁, h₂⟩,
        rw minor₃ at hm,
        have trivial₀ : m ∈ ϕ.to_local_equiv.source := hm.1,
        have trivial₁ : m ∈ W' := 
        begin
          rcases hball hm.2 with ⟨m₁, hm₁, hm₁'⟩,
          let q := ϕ.to_local_equiv.inj_on ((set.inter_subset_left _ W) hm₁) trivial₀ hm₁',
          rw q at hm₁,
          exact hm₁,
        end,
        have trivial₂ : ϕ m ∈ ϕball := hm.2,
        exact calc f m = (ψ.symm) (ψ $ f m) : (local_homeomorph.left_inv ψ $ fW'subsetsource $ mem_image_of_mem f trivial₁).symm
          ... = (ψ.symm) (ψ $ f $ ϕ.symm $ ϕ m) : by nth_rewrite 0 ← local_homeomorph.left_inv ϕ trivial₀
          ... = (ψ.symm) (πf $ ϕ m) : by simp
          ... = (ψ.symm) (πg $ ϕ m) : by rw superkeyeq₂ trivial₂
          ... = (ψ.symm) (ψ $ g $ ϕ.symm $ ϕ m) : by simp
          ... = (ψ.symm) (ψ $ g m) : by rw local_homeomorph.left_inv ϕ trivial₀
          ... = g m : (local_homeomorph.left_inv ψ $ gW'subsetsource $ mem_image_of_mem g trivial₁)
      end,
      use U,
      exact ⟨superkeymemU, superkeyopenU, superkeyeqU⟩,
    },  
    {
      rw [this, set.mem_union] at hz,
      have key : z ∈ G := or.resolve_left hz p,
      rcases (is_open_iff_forall_mem_open.mp key₁ z key) with ⟨U, hU₁, hU₂, hU₃⟩,
      exact ⟨U, hU₃, hU₂, set.eq_on.mono hU₁ hG₂⟩,
    }, 
end

theorem identity_theorem_of_mholomorph
{f g : X → Y} (hf : mholomorph f) (hg : mholomorph g)
{S : set X} (hS : set.eq_on f g S)
{s₀ : X} (hs₀ : s₀ ∈ S) (hs₀' : accumulation_pt X S s₀):
set.eq_on f g univ :=
begin
  let G : set X := {z : X | ∃ (U : set X), z ∈ U ∧ is_open U ∧ set.eq_on f g U},
  have key₁ : is_open G :=
  begin
    rw is_open_iff_forall_mem_open,
    intros x hx,
    rcases hx with ⟨U, hU₁, hU₂, hU₃⟩,
    have : U ⊆ G := λ u hu,
    begin
      rw is_open_iff_forall_mem_open at hU₂,
      rcases hU₂ u hu with ⟨t, ht₁, ht₂⟩,
      exact ⟨t, ht₂.2, ⟨ht₂.1, λ x hx, hU₃ (ht₁ hx)⟩⟩,
    end,
    exact ⟨U, this, ⟨hU₂, hU₁⟩⟩, 
  end,
  have : set.eq_on f g G := λ x hx, let ⟨U, h₁, h₂, h₃⟩ := hx in h₃ h₁,
  have key₂ : is_closed G:= 
    is_closed_of_closure_subset (λ z hz, let ⟨U, h₁, h₂, h₃⟩ := nondiscrete_closure_of_eq_mholomorph hf hg key₁ this hz in ⟨U, h₁, h₂, h₃⟩),
  have key₃ : G = ∅ ∨ G = univ := is_clopen_iff.mp ⟨key₁, key₂⟩,
  have key₄ : G.nonempty := let ⟨U, h₁, h₂, h₃⟩ := eq_on_local_disk_around_accumulation_pt hf hg hS hs₀ hs₀' in ⟨s₀, ⟨U, h₁, h₂, h₃⟩⟩,
  have superkey : G = univ := or.resolve_left key₃ (ne_empty_iff_nonempty.mpr key₄),
  rw ← superkey,
  exact this,
end

def shifted_chart_to_local_equiv (e : local_equiv X ℂ) (a : ℂ) : local_equiv X ℂ :=
{
  to_fun := λ x, e x + a,
  inv_fun := λ z, e.symm (z - a),
  source := e.source,
  target := {z | z - a ∈ e.target},
  map_source' := λ x hx, by simp; exact e.map_source' hx,
  map_target' := λ x hx, local_equiv.map_target e hx,
  left_inv' := λ x hx, 
  begin
    rw [add_sub_assoc _ a a, sub_self a, add_zero (e x)],
    exact e.left_inv' hx,
  end,
  right_inv' := λ x hx, 
  begin
    rw [← local_equiv.inv_fun_as_coe, ← local_equiv.to_fun_as_coe, e.right_inv' hx],
    ring,
  end,
}

lemma shifted_source (e : local_equiv X ℂ) (a : ℂ) : (shifted_chart_to_local_equiv e a).source = e.source := rfl
lemma shifted_target (e : local_equiv X ℂ) (a : ℂ) : (shifted_chart_to_local_equiv e a).target = {z | z - a ∈ e.target} := rfl
lemma shifted_to_fun (e : local_equiv X ℂ) (a : ℂ) : (shifted_chart_to_local_equiv e a).to_fun = λ x, e x + a := rfl
lemma shifted_inv_fun (e : local_equiv X ℂ) (a : ℂ) : (shifted_chart_to_local_equiv e a).inv_fun = λ x, e.symm (x - a) := rfl

def shifted_chart_to_local_homeomorph (e : local_homeomorph X ℂ) (a : ℂ) : local_homeomorph X ℂ :=
{
  to_local_equiv := shifted_chart_to_local_equiv e.to_local_equiv a,
  open_source := (shifted_source e.to_local_equiv a).symm ▸ e.open_source,
  open_target := 
  begin
    rw shifted_target e.to_local_equiv a,
    have : {z | z - a ∈ e.to_local_equiv.target} = (λ z, z + a) '' e.to_local_equiv.target :=
    begin
      ext,
      split,
      { intros hx, exact ⟨x - a, ⟨hx, by simp⟩⟩, },
      {
        intros hx, rcases hx with ⟨x', hx'⟩,
        simp at hx',
        rw ← hx'.2,
        simp,
        exact hx'.1,
      },
    end,
    rw this,
    exact is_open_map_add_right a e.to_local_equiv.target e.open_target,
  end,
  continuous_to_fun := 
  begin
    rw [shifted_to_fun e.to_local_equiv a, shifted_source e.to_local_equiv a, local_homeomorph.coe_coe e],
    exact continuous_on.add (e.continuous_to_fun) (continuous_on_const),
  end,
  continuous_inv_fun :=
  begin
    rw [shifted_inv_fun e.to_local_equiv a, shifted_target e.to_local_equiv a, local_homeomorph.coe_coe_symm e],
    have : {z | z - a ∈ e.to_local_equiv.target} = (λ z, z + a) '' e.to_local_equiv.target :=
    begin
      ext,
      split,
      { intros hx, exact ⟨x - a, ⟨hx, by simp⟩⟩, },
      {
        intros hx, rcases hx with ⟨x', hx'⟩,
        simp at hx',
        rw ← hx'.2,
        simp,
        exact hx'.1,
      },
    end,
    rw this,
    have minor : (λ x, e.symm (x - a)) = (e.symm ∘ (λ x, x - a)) := by simp,
    rw minor,
    have key : (λ (z : ℂ), z + a) '' e.to_local_equiv.target ⊆ (λ x, x - a)⁻¹' e.to_local_equiv.target :=
    begin
      intros x hx,
      rcases hx with ⟨x', hx'₁, hx'₂⟩,
      have : (λ x, x - a) x = x' :=
      calc (λ x, x - a) x = x - a : by simp
        ... = ((λ x, x + a) x') - a : by rw hx'₂
        ... = (x' + a) - a : by simp
        ... = x' : by ring,
      rw ← this at hx'₁,
      exact hx'₁,
    end,
    exact continuous_on.comp 
      (local_homeomorph.continuous_on_symm e) 
      (continuous_on.sub continuous_on_id continuous_on_const)
      key,
  end,
}

lemma shifted_h_to_e (e : local_homeomorph X ℂ) (a : ℂ) : (shifted_chart_to_local_homeomorph e a).to_local_equiv = shifted_chart_to_local_equiv e.to_local_equiv a := rfl 
lemma shifted_source' (e : local_homeomorph X ℂ) (a : ℂ) : (shifted_chart_to_local_homeomorph e a).to_local_equiv.source = e.to_local_equiv.source := rfl
lemma shifted_target' (e : local_homeomorph X ℂ) (a : ℂ) : (shifted_chart_to_local_homeomorph e a).to_local_equiv.target = {z | z - a ∈ e.to_local_equiv.target} := by rw shifted_h_to_e; refl
lemma shifted_to_fun' (e : local_homeomorph X ℂ) (a : ℂ) : (shifted_chart_to_local_homeomorph e a).to_local_equiv.to_fun = λ x, e x + a := rfl
lemma shifted_inv_fun' (e : local_homeomorph X ℂ) (a : ℂ) : (shifted_chart_to_local_homeomorph e a).to_local_equiv.inv_fun = λ x, e.symm (x - a) := rfl

theorem chart_at_origin_of_fun_at
{f : X → Y} (hf : continuous f) (a : X) :
∃ (ϕ : local_homeomorph X ℂ) (ψ : local_homeomorph Y ℂ),
a ∈ ϕ.to_local_equiv.source ∧ ϕ a = 0 ∧ 
f a ∈ ψ.to_local_equiv.source ∧ ψ (f a) = 0 ∧
f '' ϕ.to_local_equiv.source ⊆ ψ.to_local_equiv.source :=
sorry
-- begin
--   let ϕ₁ := chart_at ℂ a,
--   let ψ₁ := chart_at ℂ (f a),
--   let ϕ₂ := shifted_chart_to_local_homeomorph ϕ₁ (-ϕ₁ a),
--   have ϕ_obv : ϕ₂ = shifted_chart_to_local_homeomorph ϕ₁ (-ϕ₁ a) := rfl,
--   let ψ₂ := shifted_chart_to_local_homeomorph ψ₁ (-ψ₁ (f a)),
--   have ψ_obv : ψ₂ = shifted_chart_to_local_homeomorph ψ₁ (-ψ₁ (f a)) := rfl,
--   let ϕ₃ := ϕ₂.restr (f⁻¹' ψ₂.to_local_equiv.source),
--   have ϕ_obv' : ϕ₃ = ϕ₂.restr (f⁻¹' ψ₂.to_local_equiv.source) := rfl,
--   use [ϕ₃, ψ₂],
--   split,
--   { 
--     rw local_homeomorph.restr_source' ϕ₂ _, 
--     have trivial₀ : a ∈ f⁻¹' ψ₂.to_local_equiv.source := mem_chart_source ℂ (f a),
--     rw [ϕ_obv, shifted_source' ϕ₁ (-ϕ₁ a)],
--     exact ⟨mem_chart_source ℂ a, trivial₀⟩,
--     exact is_open.preimage hf ψ₂.open_source,
--   },
--   {
--     split,
--     {
--       exact calc ϕ₃ a = (ϕ₂.restr (f⁻¹' ψ₂.to_local_equiv.source)) a : by rw ϕ_obv'
--         ... = ϕ₂ a : by rw ϕ₂.restr_apply _
--         ... = shifted_chart_to_local_homeomorph ϕ₁ (-ϕ₁ a) a : by rw ϕ_obv
--         ... = (shifted_chart_to_local_homeomorph ϕ₁ (-ϕ₁ a)).to_local_equiv.to_fun a : by rw ← local_homeomorph.to_fun_eq_coe
--         ... = ϕ₁ a + (-ϕ₁ a) : by rw shifted_to_fun'
--         ... = 0 : by ring,
--     },
--     {
--       split,
--       {
--         rw [ψ_obv, shifted_source'],
--         exact mem_chart_source ℂ (f a),
--       },
--       {
--         split,
--         {
--           exact calc ψ₂ (f a) = (shifted_chart_to_local_homeomorph ψ₁ $ -ψ₁ (f a)) (f a) : by rw ψ_obv
--             ... = (shifted_chart_to_local_homeomorph ψ₁ $ -ψ₁ (f a)).to_local_equiv.to_fun (f a) : by rw ← local_homeomorph.to_fun_eq_coe
--             ... = ψ₁ (f a) + (-ψ₁ (f a)) : by rw shifted_to_fun'
--             ... = 0 : by ring,
--         },
--         {
--           intros v hv,
--           rw local_homeomorph.restr_source' _ _ (is_open.preimage hf ψ₂.open_source) at hv,
--           rcases hv with ⟨v', hv'⟩,
--           rw ← hv'.2,
--           exact hv'.1.2,
--         },
--       },
--     },
--   },
-- end

theorem local_behavior_of_mholomorph
{f : X → Y} (hf : mholomorph f) (a : X) 
(h_non_const : ∀ x, ∃ y, ¬ f x = f y):
∃ (ϕ : local_homeomorph X ℂ) (ψ : local_homeomorph Y ℂ),
a ∈ ϕ.to_local_equiv.source ∧ ϕ a = 0 ∧ 
f a ∈ ψ.to_local_equiv.source ∧ ψ (f a) = 0 ∧
f '' ϕ.to_local_equiv.source ⊆ ψ.to_local_equiv.source ∧
∃ (k : ℕ) (hk : k ≥ 1), ∀ (v : ℂ), v ∈ ϕ.to_local_equiv.target → 
(ψ ∘ f ∘ ϕ.symm) v = v ^ k :=
begin
  rcases chart_at_origin_of_fun_at hf.1 a with ⟨ϕ₁, ψ, h₁, h₂, h₃, h₄, h₅⟩,
  
end