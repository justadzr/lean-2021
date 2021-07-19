--- Will clean up these imports
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
import linear_algebra.finite_dimensional
import analysis.normed_space.inner_product
import topology.metric_space.basic
import topology.continuous_on
import analysis.calculus.formal_multilinear_series

open set complex classical filter asymptotics continuous_linear_map set metric is_open differentiable
open_locale topological_space classical nnreal asymptotics filter ennreal unit_interval

noncomputable theory

--- Some assumptions

theorem holomorph_analytic (f : ℂ → ℂ) (z : ℂ) : differentiable_at ℂ f z ↔ analytic_at ℂ f z :=
sorry

theorem smooth_within_at_iff_holomorph_within_at (f : ℂ → ℂ) {s : set ℂ} (h : is_open s) : ∀ (z : ℂ), (differentiable_within_at ℂ f s z ↔ times_cont_diff_within_at ℂ ⊤ f s z):=
sorry

theorem smooth_at_iff_holomorph_at (f : ℂ → ℂ) : ∀ (z : ℂ), (differentiable_at ℂ f z ↔ times_cont_diff_at ℂ ⊤ f z) :=
sorry

theorem smooth_on_iff_holomorph_on (f : ℂ → ℂ) {s : set ℂ} (h : is_open s) : differentiable_on ℂ f s ↔ times_cont_diff_on ℂ ⊤ f s := 
sorry

section accuml_pts

--- Need this?
--- def isolated_pt (X : Type*) [topological_space X] (U : set X) (z : X) : Prop :=
--- ∃ (V : set X), is_open V ∧ U ∩ (V \ {z}) = ∅

def accumulation_pt (X : Type*) [topological_space X] (U : set X) (z : X) : Prop :=
∀ (V : set X), V ∈ (𝓝 z) → ∃ (v : X), v ∈ U ∩ V ∧ ¬ v = z

lemma accumulation_pt_open_inter {X : Type*} [topological_space X] 
{U : set X} {U' : set X} {z : X}
(hU' : is_open U') (HU' : z ∈ U') (hz : accumulation_pt X U z) :
accumulation_pt X (U ∩ U') z := λ V hV,
  (set.inter_assoc U U' V).symm ▸ 
  (hz (U' ∩ V) $ _root_.mem_nhds_iff.mpr $ 
    let ⟨t, ht, ht₁, ht₂⟩ := _root_.mem_nhds_iff.mp hV in 
    ⟨U' ∩ t, ⟨set.inter_subset_inter_right U' ht, ⟨is_open.inter hU' ht₁, ⟨HU', ht₂⟩⟩⟩⟩)
--
lemma accumulation_pt_mem_closure {X : Type*} [topological_space X] 
{U : set X} {z : X} (hz : accumulation_pt X U z) :
z ∈ closure U :=
begin
  rw _root_.mem_closure_iff,
  intros o ho hxo,
  rcases hz o (is_open.mem_nhds ho hxo) with ⟨v, hv₁, hv₂⟩,
  use v,
  rw set.inter_comm at hv₁,
  exact hv₁,
end

end accuml_pts

section crowded_space

class crowded_space (X : Type*) [t : topological_space X] :=
(is_crowded : ∀ (x : X), ¬ t.is_open {x})

lemma crowded_space.def (X : Type*) [t : topological_space X] [cr : crowded_space X] : 
∀ (x : X), ¬ t.is_open {x} := cr.is_crowded

lemma mem_frontier (X : Type*) [t : topological_space X] {U : set X} {z : X} : 
z ∈ frontier U → ∀ (V : set X), V ∈ 𝓝 z → (V ∩ U ≠ ∅ ∧ V \ U ≠ ∅) :=
begin
  intros hz,
  rw frontier at hz,
  have h : ∀ (o : set X), is_open o → z ∈ o → (o ∩ U).nonempty := _root_.mem_closure_iff.mp (mem_of_mem_diff hz),
  have h' : ¬ (∃ (o : set X) (H : o ⊆ U), is_open o ∧ z ∈ o) := begin let p := not_mem_of_mem_diff hz, rw [mem_interior] at p, exact p end,
  simp at h',
  intros V hV,
  rcases _root_.mem_nhds_iff.mp hV with ⟨V', hV'₁, hV'₂, hV'₃⟩,
  split,
  { exact set.nonempty.ne_empty (set.nonempty.mono (set.inter_subset_inter_left _ hV'₁) $ h V' hV'₂ hV'₃), },
  {
    by_contra w,
    simp at w,
    rw [diff_eq_empty] at w,
    show false, from (h' V' (set.subset.trans hV'₁ w) hV'₂) hV'₃,
  },
end

lemma t1_space_connected_with_two_points_is_crowded (X : Type*) [t : topological_space X] [c : connected_space X] [haus : t1_space X]
(hX : ∀ (x : X), ∃ (y : X), ¬ y = x) : ∀ (x : X), ¬ t.is_open {x} :=
begin
  by_contra w,
  simp at w,
  rcases w with ⟨x, hx⟩,
  rcases hX x with ⟨y, hy⟩,
  have minor₁ : is_open {x}ᶜ := is_open_compl_singleton,
  have : set.nonempty {x}ᶜ := begin use y, rw [← ne.def, ← mem_compl_singleton_iff] at hy, exact hy, end,
  exact (ne_empty_iff_nonempty.mpr $ nonempty_inter hx (is_open_compl_singleton) (union_compl_self {x}) (set.singleton_nonempty x) this) (set.inter_compl_self {x}),
end

lemma accumulation_pt_of_mem_open_nondiscrete 
(X : Type*) [t : topological_space X] [cr : crowded_space X]
{U : set X} (hU : is_open U) {z : X} (hz : z ∈ U) :
accumulation_pt X U z := 
begin
  let ht := crowded_space.def X,
  intros V hV,
  rw is_open_iff_forall_mem_open at hU,
  rcases _root_.mem_nhds_iff.mp hV with ⟨V', hV'₁, hV'₂, hV'₃⟩,
  rcases hU z hz with ⟨U', hU'₁, hU'₂, hU'₃⟩,
  have : ¬ (U' ∩ V') = {z} := by_contra (λ h, ht z $ (not_not.mp h) ▸ is_open.inter hU'₂ hV'₂),
  rw set.ext_iff at this,
  simp at this,
  rcases this with ⟨v, hV⟩,
  use v,
  rw iff_iff_implies_and_implies at hV,
  cases not_and_distrib.mp hV,
  {
    simp at h,
    exact ⟨⟨hU'₁ h.1, hV'₁ h.2.1⟩, h.2.2⟩,
  },
  {
    simp at h,
    exfalso,
    exact h.2 (h.1.symm ▸ hU'₃) (h.1.symm ▸ hV'₃),
  },
end

lemma accumulation_pt_of_open_mem_frontier 
{X : Type*} [t : topological_space X] [cr : crowded_space X] {U : set X}
(hU : is_open U) {z : X} (hz : z ∈ frontier U) :
accumulation_pt X U z := if h : z ∈ U then accumulation_pt_of_mem_open_nondiscrete X hU h 
else begin
  rw accumulation_pt,
  intros V hV,
  let p := (mem_frontier X hz V hV).1,
  rcases set.nonempty_def.mp (set.ne_empty_iff_nonempty.mp p) with ⟨v, hv⟩,
  use v,
  have : ¬ v = z := begin
    by_contra w,
    rw ← w at h,
    exact h hv.2,
  end,
  rw set.inter_comm at hv,
  exact ⟨hv, this⟩,
end

instance complex_plane_crowded_space : crowded_space ℂ :=
{
  is_crowded := begin
    have : ∀ (x : ℂ), ∃ y, ¬ y = x :=
    begin
      intros x,
      by_cases (x = 0),
      {
        use 1, rw h, exact one_ne_zero,
      },
      {
        use 0, intros h', exact h h'.symm,
      },
    end,
    exact t1_space_connected_with_two_points_is_crowded ℂ this,
  end
}

end crowded_space

section accuml_pts_homeomorph

lemma mem_image_closure_mem_closure
{X : Type*} [topological_space X] {U : set X} {x : X} (hx : x ∈ closure U)
{Y : Type*} [topological_space Y] {e : local_homeomorph X Y} (he : x ∈ e.to_local_equiv.source) :
e x ∈ closure (e '' U) :=
begin
  rw _root_.mem_closure_iff at hx ⊢,
  intros o ho hxo,
  have : e.is_image (e⁻¹' o) o :=
  begin
    intros y hy,
    split,
    { intros h, exact h, },
    { intros h, exact set.mem_preimage.mp h },
  end,
  let o' := e.to_local_equiv.source ∩ e⁻¹' o,
  have subkey : x ∈ o' := ⟨he, hxo⟩,
  have key : is_open o' := (local_homeomorph.is_image.is_open_iff this).mpr (is_open.inter e.open_target ho),
  rcases hx o' key subkey with ⟨z, hz₁, hz₂⟩,
  rcases hz₁ with ⟨hz₁₁, hz₁₂⟩,
  use e z,
  exact ⟨hz₁₂, set.mem_image_of_mem e hz₂⟩,
end

lemma mem_closure_inter
{X : Type*} [topological_space X] {U : set X} {x : X} (hx : x ∈ closure U)
{U' : set X} (hU' : is_open U') (h : x ∈ U') :
x ∈ closure (U ∩ U') :=
begin
  rw _root_.mem_closure_iff at hx ⊢,
  intros o ho hxo,
  specialize hx (o ∩ U') (is_open.inter ho hU') ⟨hxo, h⟩,
  rw set.inter_assoc at hx,
  nth_rewrite 1 set.inter_comm at hx,
  exact hx,
end

lemma accumulation_pt_local_homeomorph 
{X : Type*} [topological_space X] {U : set X} {x : X} (hx : accumulation_pt X U x)
{Y : Type*} [topological_space Y] {e : local_homeomorph X Y} (he : x ∈ e.to_local_equiv.source) :
accumulation_pt Y (e '' U) (e x) :=
begin
  rw accumulation_pt at hx ⊢,
  intros V hV,
  rcases _root_.mem_nhds_iff.mp hV with ⟨V', hV'₁, hV'₂, hV'₃⟩,
  specialize hx (e.to_local_equiv.source ∩ e⁻¹' (V' ∩ e.to_local_equiv.target)),
  have : (e.to_local_equiv.source ∩ e⁻¹' (V' ∩ e.to_local_equiv.target)) ∈ 𝓝 x :=
  begin
    have minor : is_open (V' ∩ e.to_local_equiv.target) := is_open.inter hV'₂ e.open_target,
    have key : x ∈ (e⁻¹' (V' ∩ e.to_local_equiv.target)) := set.mem_preimage.mpr ⟨hV'₃, local_equiv.map_source _ he⟩,
    refine is_open.mem_nhds _ ⟨he, key⟩,
    apply local_homeomorph.preimage_open_of_open,
    exact is_open.inter hV'₂ e.open_target,
  end,
  rcases hx this with ⟨a, ha₁, ha₂⟩,
  rcases ha₁ with ⟨haa, hab⟩,
  let p := set.mem_image_of_mem e hab,
  use e a,
  split,
  {
    split, exact set.mem_image_of_mem e haa,
    nth_rewrite 1 set.inter_comm at p,
    rw [← local_homeomorph.coe_coe, 
        ← local_equiv.symm_image_target_inter_eq e.to_local_equiv V'] at p,
    have : set.left_inv_on ⇑(e.to_local_equiv) 
          ⇑(e.to_local_equiv.symm) e.to_local_equiv.target := 
    begin
      nth_rewrite 0 ← local_equiv.symm_symm e.to_local_equiv,
      rw [←local_homeomorph.symm_source, local_homeomorph.symm_to_local_equiv],
      exact local_equiv.left_inv_on e.to_local_equiv.symm,
    end,
    rw set.left_inv_on.image_image' this (set.inter_subset_left e.to_local_equiv.target V') at p,
    exact hV'₁ p.2,
  },
  rw set.mem_image at p,
  rcases p with ⟨b, hb⟩,
  rcases hb with ⟨left, right⟩,
  rcases left with ⟨hb₁, hb₂⟩,
  {
    intros w,
    have key : a = b := by rwa [eq_comm, ←local_homeomorph.coe_coe e, 
          set.inj_on.eq_iff (local_equiv.inj_on e.to_local_equiv) hab.1 hb₁] at right,
    rw ← right at w,
    rw [eq_comm, ←local_homeomorph.coe_coe e, 
        set.inj_on.eq_iff (local_equiv.inj_on e.to_local_equiv) he hb₁] at w,
    rw ← key at w,
    exact ha₂ (eq_comm.mp w),
  },
end

end accuml_pts_homeomorph

section complex_theorems

theorem identity_theorem
{f : ℂ → ℂ} {g : ℂ → ℂ}
{U : set ℂ} (hU₁ : is_open U) (hU₂ : is_connected U)
(hf : differentiable_on ℂ f U) (hg : differentiable_on ℂ g U)
{s₀ : ℂ} {S : set ℂ} (hS : S ⊆ U) (hS' : set.eq_on f g S)
(hs₀ : s₀ ∈ S) (hs₀' : accumulation_pt ℂ S s₀):
set.eq_on f g U :=
sorry

theorem eq_of_eq_on_open
{f : ℂ → ℂ} {g : ℂ → ℂ}
{U : set ℂ} (hU₁ : is_open U) (hU₂ : is_connected U)
(hf : differentiable_on ℂ f U) (hg : differentiable_on ℂ g U)
{V : set ℂ} (hV₁ : is_open V) (hV₂ : V.nonempty) (hV₃ : set.eq_on f g V) (hV₄ : V ⊆ U) :
set.eq_on f g U := let ⟨v, hv⟩ := hV₂ in 
identity_theorem hU₁ hU₂ hf hg hV₄ hV₃ hv $ accumulation_pt_of_mem_open_nondiscrete ℂ hV₁ hv

theorem open_mapping_complex
{f : ℂ → ℂ}
{U : set ℂ} (hU₁ : is_open U) (hU₂ : is_connected U)
(hf₁ : differentiable_on ℂ f U)
(hf₂ : ∃ (x y : ℂ), x ∈ U ∧ y ∈ U ∧ ¬ f x = f y) :
∀ (U' : set ℂ), U' ⊆ U → is_open U' → is_open (f '' U'):=
sorry

end complex_theorems

/-
  Trash codes. A bad attempt to prove the identity theorem only assuming some
  standard results
-/

/-
lemma nonvanishing_has_local_expansion
(ε : ℝ) {hε : ε > 0}
(f : ℂ → ℂ)
(w : ℂ)
{hf₁ : ∃ (z : ℂ), z ∈ ball w ε ∧ ¬f z = 0}
{hf₂ : ∀ (z : ℂ), z ∈ ball w ε  → analytic_at ℂ f z} {hf₂ : f w = 0}:
∃ (k : ℕ) (r : ℝ) (g : ℂ → ℂ),
k > 0 ∧ r ≤ ε ∧ 0 < r ∧
∀ (x : ℂ), x ∈ ball w r → f = (λ x, ((x - w) ^ k) * g x)
∧ ¬ g x = 0 ∧ analytic_at ℂ g x:=
sorry

-- I cannot prove the following theorem neatly. I tried to prove it with some disguting inductions,
-- but Lean's treatments of derivatives are not quite nice in this case. Maybe using g's expansion
-- would be easier. But again, that requires at least one induction.
lemma nonvanishing_iter_deriv_of_nonvanishing
(f : ℂ → ℂ)
(w : ℂ)
{hf : analytic_at ℂ f w}:
(∃ (k : ℕ),
¬ iterated_deriv k f w = 0)
↔ (∃ (ε : ℝ), 0 < ε ∧ (∀ (z : ℂ), z ∈ ball w ε → analytic_at ℂ f z) 
∧ (∃ (z : ℂ), z ∈ ball w ε ∧ ¬f z = 0)) := 
sorry

lemma nonvanishing_disk_of_continuous
(f : ℂ → ℂ)
(z : ℂ) {hf₁ : continuous_at f z} {hf₂ : ¬ f z = 0}:
∃ (ε : ℝ),
0 < ε ∧ ∀ (x : ℂ), x ∈ ball z ε → ¬ f x = 0 :=
begin
  have := hf₁,
  rw continuous_at_iff at this,
    let ε' := ∥f z∥ / 2,
    rw [← ne.def, ← norm_pos_iff] at hf₂,
    have hε' : 0 < ∥f z∥ / 2 := by linarith,
    rcases this ε' hε' with ⟨δ, hδ, h⟩,
    use min ε' δ,
    split,
    simp,
    exact ⟨hε', hδ⟩,
    {
      intros x hx,
      rw [mem_ball', dist_comm] at hx,
      have lt_δ : dist x z < δ := lt_of_lt_of_le hx (min_le_right _ _),
      specialize h lt_δ,
      rw [dist_eq_norm, norm_sub_rev] at h,
      have key : 0 < ∥f x∥ :=
        calc ∥f x∥ = ∥f z - (f z - f x)∥ : by simp
        ... ≥ ∥f z∥ - ∥f z - f x∥ : norm_sub_norm_le _ _
        ... ≥ ∥f z∥ - ε' : begin simp, apply le_of_lt, exact h, end
        ... ≥ ∥f z∥ - ∥f z∥ / 2 : begin simp, apply le_of_eq, rw ← norm_eq_abs, end
        ... = ∥f z∥ / 2 : by linarith
        ... > 0 : hε',
      rw [norm_pos_iff] at key,
      exact key,
    },
end

lemma is_open_nonvanishing_of_continuous
(f : ℂ → ℂ)
(U : set ℂ) {hU : is_open U}
{hf : ∀ (z : ℂ), z ∈ U → continuous_at f z} : 
is_open {z : ℂ | z ∈ U ∧ ¬ f z = 0} :=
begin
  rw metric.is_open_iff at *,
  dsimp,
  intros z hz,
  rcases hz with ⟨hz₁, hz₂⟩,
  specialize hU z hz₁,
  specialize hf z hz₁,
  rcases hU with ⟨δ, hδ₁, hδ₂⟩,
  rcases nonvanishing_disk_of_continuous f z with ⟨ε, hε₁, hε₂⟩,
  assumption',
  use min δ ε,
  split,
  simp at hδ₁,
  exact lt_min hδ₁ hε₁,
  rw subset_def,
  dsimp,
  intros x hx,
  have key₁ : x ∈ U := hδ₂ ((ball_subset_ball $ min_le_left δ ε) hx),
  have key₂ : ¬ f x = 0 := hε₂ x ((ball_subset_ball $ min_le_right δ ε) hx),
  exact ⟨key₁, key₂⟩,
end

lemma isolated_zeros_of_nonvanishing
(ε : ℝ) {hε : ε > 0}
(f : ℂ → ℂ)
(w : ℂ)
{hf₁ : ∃ (z : ℂ), z ∈ ball w ε ∧ ¬f z = 0} 
{hf₂ : ∀ (z : ℂ), z ∈ ball w ε  → analytic_at ℂ f z}:
∃ (r : ℝ),
r ≤ ε ∧ 0 < r ∧
∀ (x : ℂ), x ∈ ball w r → ¬ x - w = 0 → ¬ f x = 0:=
begin
  by_cases (f w = 0),
  -- the case where f w = 0; use f's local expansion around w
  {
    rcases nonvanishing_has_local_expansion ε f w with ⟨k, r, g, H⟩,
    rcases H with ⟨H₁, H₂, H₃, H₄⟩,
    use r,
    split,
    exact H₂,
    {
      split,
      exact H₃,
      {
        intros x hx₁ hx₂,
        by_contra h',
        specialize H₄ x hx₁,
        rcases H₄ with ⟨h₂₁, h₂₂, h₂₃⟩,
        rw h₂₁ at h',
        have key : (x - w) ^ k = 0 ∨ g x = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h',
        cases key with key₁ key₂,
        {
          rw [← complex.cpow_nat_cast, complex.cpow_eq_zero_iff] at key₁,
          exact hx₂ key₁.1,
        },
        {
          exact h₂₂ key₂,
        },
      },
    },
    assumption',
  },
  -- the case where f w ≠ 0; use the continuity of f at w
  {
    specialize hf₂ w (mem_ball_self hε),
    rcases nonvanishing_disk_of_continuous f w with ⟨r, hr⟩,
    assumption',
    use min r ε,
    split,
    exact min_le_right _ _,
    split,
    {
      simp,
      exact ⟨hr.1, hε⟩,
    },
    {
      intros x hx₁ hx₂,
      rw [mem_ball'] at hx₁,
      have key : dist w x < r := lt_of_lt_of_le hx₁ (min_le_left _ _),
      rw [← mem_ball'] at key,
      exact hr.2 x key,
    },
    exact analytic_at.continuous_at hf₂,
  },
end

def is_accumulation_point (U : set ℂ) (z : ℂ) : Prop :=
∀ (V : set ℂ), V ∈ (𝓝 z) → ∃ (v : ℂ), v ∈ U ∩ V ∧ ¬ v - z = 0

lemma vanishing_disk_of_accumulation_point
(U : set ℂ) {hU : is_open U}
(f : ℂ → ℂ) {hf : ∀ (z : ℂ), z ∈ U → analytic_at ℂ f z}
(s₀ : ℂ) 
{hs₀ : is_accumulation_point {s : ℂ | f s = 0 ∧ s ∈ U} s₀} 
{hs₀' : s₀ ∈ {s : ℂ | f s = 0 ∧ s ∈ U}}:
∃ (ε : ℝ), 0 < ε ∧ ball s₀ ε ⊆ U ∧
∀ (z : ℂ), z ∈ ball s₀ ε → f z = 0 :=
begin
  by_contra w,
  simp only [not_exists, not_and] at w,
  dsimp at hs₀',
  rw metric.is_open_iff at hU,
  specialize hU s₀ hs₀'.2,
  rcases hU with ⟨ε, hε₁, hε₂⟩,
  specialize w ε hε₁ hε₂,
  simp only [not_forall] at w,
  rcases w with ⟨z, hz₁, hz₂⟩,
  have hf₁ : ∃ (z : ℂ), z ∈ ball s₀ ε ∧ ¬f z = 0 := ⟨z, ⟨hz₁, hz₂⟩⟩,
  have hf₂ : ∀ (x : ℂ), x ∈ ball s₀ ε → analytic_at ℂ f x := λ x hx, hf x $ hε₂ hx,
  rcases isolated_zeros_of_nonvanishing ε f s₀ with ⟨r, hr₁, hr₂, hr₃⟩,
  assumption',
  have : ∃ (v : ℂ), v ∈ {s : ℂ | f s = 0 ∧ s ∈ U} ∩ (ball s₀ r) ∧ ¬ v - s₀ = 0 := 
    hs₀ (ball s₀ r) (ball_mem_nhds s₀ hr₂),
  rcases this with ⟨v, hv₁, hv₂⟩,
  dsimp at hv₁,
  show false, from (hr₃ v hv₁.2 hv₂) hv₁.1.1,
end

theorem vanishing_if_zeros_accumulate
(U : set ℂ) {hU₁ : is_open U} {hU₂ : is_connected U}
(f : ℂ → ℂ) {hf : ∀ (z : ℂ), z ∈ U → analytic_at ℂ f z}
(s₀ : ℂ)
{hs₀ : is_accumulation_point {s : ℂ | f s = 0 ∧ s ∈ U} s₀} 
{hs₀' : s₀ ∈ {s : ℂ | f s = 0 ∧ s ∈ U}}:
∀ (z : ℂ), z ∈ U → f z = 0:=
begin
  let U₁ : set ℂ := {z : ℂ | z ∈ U ∧ ∃ (r : ℝ), 0 < r ∧ ball z r ⊆ U ∧ ∀ (x : ℂ), x ∈ ball z r → f x = 0},
  let U₂ : set ℂ := {z : ℂ | z ∈ U ∧ ∃ (k : ℕ), ¬ iterated_deriv k f z = 0},
  have h₁ : U₁ ∪ U₂ = U :=
  begin
    ext,
    split,
    {
      intro h,
      dsimp at h,
      cases h with H₁ H₂,
      exact H₁.1,
      exact H₂.1,
    },
    {
      intro H,
      by_cases (x ∈ U₂),
      exact (mem_union_right U₁) h,
      {
        by_cases h' : f x = 0,
        {
          have key : is_accumulation_point {s : ℂ | f s = 0 ∧ s ∈ U} x ∧ x ∈ {s : ℂ | f s = 0 ∧ s ∈ U}:=
          begin
            by_contradiction w,
            rw not_and_distrib at w,
            cases w with w₁ w₂,
            {
              -- sorry,
              unfold is_accumulation_point at w₁,
              simp at w₁,
              rcases w₁ with ⟨U', hU₁', hU₂'⟩,
              rw metric.mem_nhds_iff at hU₁',
              rcases hU₁' with ⟨r, hr₁, hr₂⟩,
              let U'' : set ℂ := ball x r ∩ U,
              have key₁ : is_open U'' := is_open.inter metric.is_open_ball hU₁,
              rw metric.is_open_iff at key₁,
              specialize key₁ x (mem_inter (mem_ball_self hr₁) H),
              rcases key₁ with ⟨ε, hε₁, hε₂⟩,
              let x' : ℂ := x + ε / 2,
              have key₂ : x' ∈ ball x ε := 
              begin 
                simp,
                have : 0 ≤ ε / 2 := by linarith,
                exact calc dist x' x = ∥(x + ε / 2) - x∥ : by rw dist_eq_norm
                  ... = complex.abs ↑(ε / 2) : by simp
                  ... = ε / 2 : by rw complex.abs_of_nonneg this
                  ... < ε : by linarith,
              end,
              have key₃ : ¬ f x' = 0 :=
              begin
                by_contra w',
                have : x' ∈ U'' := hε₂ key₂,
                simp only [mem_inter_eq] at this,
                specialize hU₂' x' w' this.2 (hr₂ this.1),
                have key : ¬ x' - x = 0 := begin
                  simp,
                  exact ne_of_gt hε₁,
                end,
                show false, from key hU₂',
              end,
              have : ∃ (ε : ℝ), ε > 0 ∧ (∀ (z : ℂ), z ∈ ball x ε → analytic_at ℂ f z) ∧ ∃ (z : ℂ), z ∈ ball x ε ∧ ¬f z = 0 :=
              begin
                use ε,
                split,
                exact hε₁,
                split,
                intros z hz, 
                exact hf z (mem_of_mem_inter_right (hε₂ hz)),
                exact ⟨x', ⟨key₂, key₃⟩⟩,
              end,
              have key₄ : x ∈ U₂ :=
              begin
                dsimp,
                split,
                exact H,
                rcases iff.elim_right (nonvanishing_iter_deriv_of_nonvanishing f x) this with ⟨k, hk⟩,
                use k,
                exact hf x H,
              end, 
              show false, from h key₄,
            },
            {
              simp at w₂,
              show false, from (w₂ h') H,
            },
          end,
          rcases vanishing_disk_of_accumulation_point U f x with ⟨ε, hε₁, hε₂, hε₃⟩,
          assumption',
          have : x ∈ U₁ :=
          begin
            dsimp [U₁],
            split,
            exact H,
            {
              use ε,
              exact ⟨hε₁, ⟨hε₂, hε₃⟩⟩,
            },
          end,
          exact (mem_union_left U₂) this,
          exact key.1,
          exact key.2,
        },
        {
          have key₁ : ∃ (k : ℕ), ¬ iterated_deriv k f x = 0 := by use 0,
          have key₂ : x ∈ U₂ := begin
            simp,
            exact ⟨H, key₁⟩,
          end,
          exfalso,
          exact h key₂,
        },
      },
    },  
  end,
  have h₂ : U₁ ∩ U₂ = ∅ :=
  begin
    by_contra,
    rw [← ne.def, ne_empty_iff_nonempty, nonempty_def] at h,
    rcases h with ⟨x, hx⟩,
    dsimp at hx,
    rcases iff.elim_left (nonvanishing_iter_deriv_of_nonvanishing f x) hx.2.2 with ⟨ε, hε₁, hε₂, hε₃⟩,
    rcases isolated_zeros_of_nonvanishing ε f x with ⟨r, hr₁, hr₂, hr₃⟩,
    assumption',
    swap,
    exact hf x hx.1.1,
    rcases hx.1.2 with ⟨r', hr₁', hr₂', hr₃'⟩,
    let r'' : ℝ := min r r',
    have minor₁ : 0 < r'' := 
    begin
      rw lt_min_iff,
      exact ⟨hr₂, gt.lt hr₁'⟩,
    end,
    have minor₂ : ∃ (x' : ℂ), x' ∈ ball x r'' ∧ ¬ x' - x = 0 := 
    begin
      let x' : ℂ := x + r'' / 2,
      use x',
      split,
      simp only [metric.mem_ball],
      have : 0 ≤ r'' / 2 := by linarith,
      exact calc dist x' x = ∥(x + r'' / 2) - x∥ : by rw dist_eq_norm
        ... = complex.abs ↑(r'' / 2) : by simp
        ... = r'' / 2 : by rw complex.abs_of_nonneg this
        ... < r'' : by linarith,
      simp,
      exact ne_of_gt minor₁,
    end,
    rcases minor₂ with ⟨x', hx₁', hx₂'⟩,
    have key₁ : f x' = 0 := hr₃' x' ((ball_subset_ball (min_le_right r r')) hx₁'),
    have key₂ : ¬ f x' = 0 := hr₃ x' ((ball_subset_ball (min_le_left r r')) hx₁') hx₂',
    show false, from key₂ key₁,
  end,
  have h₃ : is_open U₁ :=
  begin
    rw metric.is_open_iff,
    intros x hx,
    dsimp at hx,
    rcases hx with ⟨hx₁, ε, hε₁, hε₂, hε₃⟩,
    use ε,
    split,
    exact hε₁,
    intros z hz,
    dsimp,
    split,
    exact hε₂ hz,
    have : ∃ (r : ℝ), (0 < r ∧ ball z r ⊆ U) ∧ ball z r ⊆ ball x ε :=
    begin
      have key : is_open (ball x ε) := is_open_ball,
      rw metric.is_open_iff at key,
      specialize key z hz,
      rcases key with ⟨r, hr₁, hr₂⟩,
      use r,
      split,
      exact ⟨hr₁, subset.trans hr₂ hε₂⟩,
      exact hr₂,
    end,
    rcases this with ⟨r, hr₁, hr₂⟩,
    use r,
    split,
    exact hr₁.1,
    split,
    exact hr₁.2,
    intros x' hx',
    exact hε₃ x' (hr₂ hx'),
  end,
  have h₄ : is_open U₂ :=
  begin
    sorry,   
  end,
  have h₅ : U₁.nonempty :=
  begin
    rw nonempty_def,
    use s₀,
    dsimp,
    simp at hs₀',
    split,
    exact hs₀'.2,
    rcases vanishing_disk_of_accumulation_point U f s₀ with ⟨ε, hε₁, hε₂, hε₃⟩,
    assumption',
    use ε,
    exact ⟨hε₁, ⟨hε₂, hε₃⟩⟩,
  end,
  have hfinal : U₁ = U :=
  begin
    have : is_preconnected U := is_connected.is_preconnected hU₂,
    rw is_preconnected_iff_subset_of_disjoint at this,
    specialize this U₁ U₂ h₃ h₄ (eq.subset (eq.symm h₁)),
    have minor : U ∩ (U₁ ∩ U₂) = ∅ := 
    begin
      rw h₂,
      simp,
    end,
    specialize this minor,
    cases this,
    {
      have minor' : U₁ ⊆ U :=
      begin
        let h := set.subset_union_left U₁ U₂,
        rw h₁ at h,
        exact h,
      end,
      exact has_subset.subset.antisymm minor' this,
    },
    {
      have minor₁ : U₁ ⊆ U :=
      begin
        let h := set.subset_union_left U₁ U₂,
        rw h₁ at h,
        exact h,
      end,
      have minor₂ : U₂ ⊆ U :=
      begin
        let h := set.subset_union_right U₁ U₂,
        rw h₁ at h,
        exact h,
      end,
      have minor₃ : U₂ = U := has_subset.subset.antisymm minor₂ this,
      have key : U₁ = ∅ :=
      begin
        rw [inter_comm, ← set.subset_empty_iff, ← set.diff_eq_self] at h₂,
        rw ← h₂,
        by_contra w,
        rw [← ne.def, set.ne_empty_iff_nonempty, set.nonempty_diff, minor₃] at w,
        show false, from w minor₁,
      end,
      rw [← set.not_nonempty_iff_eq_empty] at key,
      exfalso,
      exact key h₅,
    },
  end,
  intros z hz,
  have : z ∈ U₁ := (eq.subset (eq.symm hfinal)) hz,
  dsimp at this,
  rcases this.2 with ⟨r, hr₁, hr₂, hr₃⟩,
  specialize hr₃ z (mem_ball_self hr₁),
  exact hr₃,
end

theorem eq_if_eq_points_accumulate
(U : set ℂ) {hU₁ : is_open U} {hU₂ : is_connected U}
(f : ℂ → ℂ) {hf : ∀ (z : ℂ), z ∈ U → analytic_at ℂ f z}
(g : ℂ → ℂ) {hg : ∀ (z : ℂ), z ∈ U → analytic_at ℂ g z}
(s₀ : ℂ)
{hs₀ : is_accumulation_point {s : ℂ | f s = g s ∧ s ∈ U} s₀} 
{hs₀' : s₀ ∈ {s : ℂ | f s = g s ∧ s ∈ U}} :
∀ (z : ℂ), z ∈ U → f z = g z :=
begin
  let h : ℂ → ℂ := f - g,
  have minor : ∀ (z : ℂ), z ∈ U → analytic_at ℂ h z := λ z hz, analytic_at.sub (hf z hz) $ hg z hz,
  have key : {s : ℂ | f s = g s ∧ s ∈ U} = {s : ℂ | h s = 0 ∧ s ∈ U} :=
  begin
    ext,
    split,
    { 
      intros hx, 
      dsimp at hx, 
      simp, split,
      exact calc h x = (f - g) x : by refl
        ... = f x - g x : by simp
        ... = f x - f x : by rw ← hx.1
        ... = 0 : by ring,
      exact hx.2,
    },
    {
      intros hx, 
      dsimp at hx, 
      simp, split,
      exact calc f x = f x - g x + g x : by simp
        ... = (f - g) x + g x : by simp
        ... = h x + g x : by refl
        ... = 0 + g x : by rw hx.1
        ... = g x : by ring,
      exact hx.2,
    },
  end,
  rw key at hs₀ hs₀',
  intros z hz,
  have : h z = 0 := vanishing_if_zeros_accumulate U h s₀ z hz,
  assumption',
  exact calc f z = f z - g z + g z : by simp
        ... = (f - g) z + g z : by simp
        ... = h z + g z : by refl
        ... = 0 + g z : by rw this
        ... = g z : by ring,
end
-/
