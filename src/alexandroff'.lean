/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import topology.separation
import topology.opens

/-!
# The Alexandroff Compactification
We construct the Alexandroff compactification of an arbitrary topological space `X` and prove
some properties inherited from `X`.

## Main defintion
* `alexandroff`: the Alexandroff compactification
* `of`: the inclusion map defined by `option.some`. This map requires the argument
        `topological_space X`
* `infty`: the extra point

## Main results
* The topological structure of `alexandroff X`
* The connectedness of `alexandroff X` for noncompact, preconnected `X`
* `alexandroff X` is `T₁` for a T₁ space `X`
* `alexandroff X` is Hausdorff if `X` is locally compact and Hausdorff
-/

noncomputable theory
open set
open_locale classical topological_space filter

section option_topology

/-- The one-point extension of a topological space -/
@[reducible]
def one_point_extension (X : Type*) [topological_space X] :
  topological_space (option X) :=
{ is_open := λ s, if none ∈ s then is_compact (some⁻¹' s)ᶜ ∧ is_open (some⁻¹' s)
    else is_open (some⁻¹' s),
  is_open_univ := by simp,
  is_open_inter :=
  λ s t hs ht, begin
    split_ifs at hs ht with h h' h' h' h,
    { simpa [h, h', compl_inter] using and.intro (hs.1.union ht.1) (hs.2.inter ht.2) },
    { simpa [h, h'] using hs.inter ht.2 },
    { simpa [h, h'] using hs.2.inter ht },
    { simpa [h, h'] using hs.inter ht }
  end,
  is_open_sUnion :=
  λ S ht, begin
    suffices : is_open (some⁻¹' ⋃₀S),
    { split_ifs with h,
      { obtain ⟨(a : set (option X)), ha, ha'⟩ := mem_sUnion.mp h,
        specialize ht a ha,
        rw if_pos ha' at ht,
        refine ⟨compact_of_is_closed_subset ht.left this.is_closed_compl _, this⟩,
        rw [compl_subset_compl, preimage_subset_iff],
        intros y hy,
        refine ⟨a, ha, hy⟩ },
      { exact this } },
    rw is_open_iff_forall_mem_open,
    simp only [and_imp, exists_prop, mem_Union, preimage_sUnion, mem_preimage, exists_imp_distrib],
    intros y s hs hy,
    refine ⟨some⁻¹' s, subset_subset_Union _ (subset_subset_Union hs (subset.refl _)), _,
      mem_preimage.mpr hy⟩,
    specialize ht s hs,
    split_ifs at ht,
    { exact ht.right },
    { exact ht }
  end }

end option_topology

section basic

/-- The Alexandroff extension of an arbitrary topological space `X` -/
def alexandroff (X : Type*) [topological_space X] := option X

variables {X : Type*} [topological_space X]

/-- The embedding of `X` to its Alexandroff extension -/
def of : X → alexandroff X := some

/-- The range of the embedding -/
def range_of (X : Type*) [topological_space X] : set (alexandroff X) := of '' (univ : set X)

lemma of_apply {x : X} : of x = some x := rfl

lemma of_injective : function.injective (@of X _) :=
option.some_injective X

/-- The extra point in the extension -/
def infty : alexandroff X := none

local notation `∞` := infty

namespace alexandroff

instance : has_coe X (alexandroff X) := ⟨of⟩

instance : inhabited(alexandroff X) := ⟨∞⟩

@[norm_cast] 
lemma coe_eq_coe {x y : X} : (x : alexandroff X) = y ↔ x = y :=
of_injective.eq_iff

@[simp] lemma coe_ne_infty (x : X) : (x : alexandroff X) ≠ ∞  .
@[simp] lemma infity_ne_coe (x : X) : ∞ ≠ (x : alexandroff X) .
@[simp] lemma of_eq_coe {x : X} : (of x : alexandroff X) = x := rfl

@[elab_as_eliminator]
def rec_infty_of (C : alexandroff X → Sort*) (h₁ : C infty) (h₂ : Π (x : X), C x) :
  Π (z : alexandroff X), C z :=
option.rec h₁ h₂

@[simp] lemma ne_infty_iff_exists {x : alexandroff X} : 
  x ≠ infty ↔ ∃ (y : X), x = y :=
by { induction x using alexandroff.rec_infty_of; simp }

@[simp] lemma coe_mem_range_of (x : X) : (x : alexandroff X) ∈ (range_of X) :=
by simp [range_of]

lemma union_infty_eq_univ : (range_of X ∪ {∞}) = univ :=
begin
  refine le_antisymm (subset_univ _) (λ x hx, _),
  induction x using alexandroff.rec_infty_of; simp
end

@[simp] lemma infty_not_mem_range_of : ∞ ∉ range_of X :=
by simp [range_of]

@[simp] lemma not_mem_range_of_iff (x : alexandroff X) :
  x ∉ range_of X ↔ x = ∞ :=
by { induction x using alexandroff.rec_infty_of; simp }

@[simp] lemma infty_not_mem_image_of {s : set X} : ∞ ∉ of '' s :=
not_mem_subset (image_subset _ $ subset_univ _) infty_not_mem_range_of

lemma inter_infty_eq_empty : (range_of X) ∩ {∞} = ∅ :=
by { ext x, induction x using alexandroff.rec_infty_of; simp }

lemma of_preimage_infty : (of⁻¹' {∞} : set X) = ∅ :=
by { ext, simp }

end alexandroff

end basic

section topology
open alexandroff

variables {X : Type*} [topological_space X]

instance : topological_space (alexandroff X) := one_point_extension X

variables {s : set (alexandroff X)} {s' : set X}

@[simp] lemma is_open_alexandroff_iff_aux :
  is_open s ↔ if infty ∈ s then is_compact (of⁻¹' s)ᶜ ∧ is_open (of⁻¹' s)
  else is_open (of⁻¹' s) :=
iff.rfl

@[simp] lemma is_open_iff_of_mem' (h : infty ∈ s) :
  is_open s ↔ is_compact (of⁻¹' s)ᶜ ∧ is_open (of⁻¹' s) :=
by simp [h]

lemma is_open_iff_of_mem (h : infty ∈ s) :
  is_open s ↔ is_compact (of⁻¹' s)ᶜ ∧ is_closed (of⁻¹' s)ᶜ :=
by simp [h, is_closed_compl_iff]

@[simp] lemma is_open_iff_of_not_mem (h : infty ∉ s) :
  is_open s ↔ is_open (of⁻¹' s) :=
by simp [h]

lemma is_open_of_is_open (h : is_open s) :
  is_open (of⁻¹' s) :=
begin
  by_cases H : infty ∈ s,
  { simpa using ((is_open_iff_of_mem H).mp h).2 },
  { exact (is_open_iff_of_not_mem H).mp h }
end

end topology

section topological
open alexandroff

variables {X : Type*} [topological_space X]

@[continuity] lemma continuous_of : continuous (@of X _) :=
continuous_def.mpr (λ s hs, is_open_of_is_open hs)

def opens_of_compl {s : set X} (h : is_compact s ∧ is_closed s) :
  topological_space.opens (alexandroff X) :=
⟨(of '' s)ᶜ, by { rw [is_open_iff_of_mem ((mem_compl_iff _ _).mpr infty_not_mem_image_of),
  preimage_compl, compl_compl, of_injective.preimage_image _], exact h }⟩

lemma infty_mem_opens_of_compl {s : set X} (h : is_compact s ∧ is_closed s) :
  infty ∈ (opens_of_compl h : set (alexandroff X)) :=
by { simp only [opens_of_compl, topological_space.opens.coe_mk],
     exact mem_compl infty_not_mem_image_of }

lemma is_open_map_of : is_open_map (@of X _) :=
λ s hs, begin
  rw [← preimage_image_eq s of_injective] at hs,
  rwa is_open_iff_of_not_mem infty_not_mem_image_of
end

lemma is_open_range_of : is_open (@range_of X _) :=
is_open_map_of _ is_open_univ

instance : compact_space (alexandroff X) :=
{ compact_univ :=
  begin
    refine is_compact_of_finite_subcover (λ ι Z h H, _),
    simp only [univ_subset_iff] at H ⊢,
    rcases Union_eq_univ_iff.mp H infty with ⟨K, hK⟩,
    have minor₁ : is_compact (of⁻¹' Z K)ᶜ,
    { specialize h K, rw is_open_iff_of_mem hK at h, exact h.1 },
    let p : ι → set X := λ i, of⁻¹' Z i,
    have minor₂ : ∀ i, is_open (p i) := λ i, is_open_of_is_open (h i),
    have minor₃ : (of⁻¹' Z K)ᶜ ⊆ ⋃ i, p i :=
      by simp only [p, ← preimage_Union, H, preimage_univ, subset_univ],
    rcases is_compact_iff_finite_subcover.mp minor₁ p minor₂ minor₃ with ⟨ι', H'⟩,
    refine ⟨insert K ι', _⟩,
    rw ← preimage_compl at H',
    simp only [Union_eq_univ_iff],
    intros x,
    by_cases hx : x ∈ Z K,
    { exact ⟨K, mem_Union.mpr ⟨finset.mem_insert_self _ _, hx⟩⟩ },
    { have triv₁ : x ≠ infty := (ne_of_mem_of_not_mem hK hx).symm,
      rcases ne_infty_iff_exists.mp triv₁ with ⟨y, hy⟩,
      have triv₂ : (y : alexandroff X) ∈ {x} := mem_singleton_of_eq hy.symm,
      rw [← mem_compl_iff, ← singleton_subset_iff] at hx,
      have : of⁻¹' {x} ⊆ of⁻¹' (Z K)ᶜ := λ y hy, hx hy,
      have key : y ∈ ⋃ (i : ι) (H : i ∈ ι'), p i := this.trans H' (mem_preimage.mpr triv₂),
      rcases mem_bUnion_iff'.mp key with ⟨i, hi, hyi⟩,
      refine ⟨i, mem_Union.mpr ⟨finset.subset_insert _ ι' hi, _⟩⟩,
      simpa [hy] using hyi }
  end }

lemma dense_range_of (h : ¬ is_compact (univ : set X)) : dense (@range_of X _) :=
begin
  refine dense_iff_inter_open.mpr (λ s hs Hs, _),
  by_cases H : infty ∈ s,
  { rw is_open_iff_of_mem H at hs,
    have minor₁ : s ≠ {infty},
    { by_contra w,
      rw [not_not.mp w, of_preimage_infty, compl_empty] at hs,
      exact h hs.1 },
    have minor₂ : of⁻¹' s ≠ ∅,
    { by_contra w,
      rw [not_not, eq_empty_iff_forall_not_mem] at w,
      simp only [mem_preimage] at w,
      have : ∀ z ∈ s, z = infty := λ z hz,
        by_contra (λ w', let ⟨x, hx⟩ := ne_infty_iff_exists.mp w' in
          by rw hx at hz; exact (w x) hz),
      exact minor₁ (eq_singleton_iff_unique_mem.mpr ⟨H, this⟩) },
    rcases ne_empty_iff_nonempty.mp minor₂ with ⟨x, hx⟩,
    exact ⟨of x, hx, x, mem_univ _, rfl⟩ },
  { rcases Hs with ⟨z, hz⟩,
    rcases ne_infty_iff_exists.mp (ne_of_mem_of_not_mem hz H) with ⟨x, hx⟩,
    rw hx at hz,
    exact ⟨of x, hz, x, mem_univ _, rfl⟩ }
end

lemma connected_space_alexandroff [preconnected_space X] (h : ¬ is_compact (univ : set X)) :
  connected_space (alexandroff X) :=
{ is_preconnected_univ :=
  begin
    rw ← dense_iff_closure_eq.mp (dense_range_of h),
    exact is_preconnected.closure
      (is_preconnected_univ.image of continuous_of.continuous_on)
  end,
  to_nonempty := ⟨infty⟩ }

instance [t1_space X] : t1_space (alexandroff X) :=
{ t1 :=
  λ z, begin
    by_cases z = infty,
    { rw [h, ← is_open_compl_iff, compl_eq_univ_diff, ← union_infty_eq_univ,
          union_diff_cancel_right (subset.antisymm_iff.mp inter_infty_eq_empty).1],
      exact is_open_range_of },
    { rcases ne_infty_iff_exists.mp h with ⟨x, hx⟩,
      have minor₂ : (infty : alexandroff X) ∈ {z}ᶜ :=
        mem_compl (λ w, (ne.symm h) (mem_singleton_iff.mp w)),
      rw [← is_open_compl_iff, is_open_iff_of_mem minor₂],
      rw [preimage_compl, compl_compl, hx, ← of_eq_coe, 
          ← image_singleton, of_injective.preimage_image _],
      exact ⟨is_compact_singleton, is_closed_singleton⟩ }
  end }

instance [locally_compact_space X] [t2_space X] : t2_space (alexandroff X) :=
{ t2 :=
  λ x y hxy, begin
    have key : ∀ (z : alexandroff X), z ≠ infty →
      ∃ (u v : set (alexandroff X)), is_open u ∧ is_open v ∧ infty ∈ u ∧ z ∈ v ∧ u ∩ v = ∅ :=
    λ z h, begin
      rcases ne_infty_iff_exists.mp h with ⟨y', hy'⟩,
      rcases exists_open_with_compact_closure y' with ⟨u, hu, huy', Hu⟩,
      have minor₁ : _ ∧ is_closed (closure u) := ⟨Hu, is_closed_closure⟩,
      refine ⟨opens_of_compl minor₁, of '' u, _⟩,
      refine ⟨(opens_of_compl minor₁).2, is_open_map_of _ hu,
        infty_mem_opens_of_compl minor₁, ⟨y', huy', hy'.symm⟩, _⟩,
      simp only [opens_of_compl, topological_space.opens.coe_mk],
      have minor₂ : (of '' closure u)ᶜ ∩ of '' u ⊆ (of '' u)ᶜ ∩ of '' u,
      { apply inter_subset_inter_left,
        simp only [compl_subset_compl, image_subset _ (subset_closure)] },
      rw compl_inter_self at minor₂,
      exact eq_empty_of_subset_empty minor₂
    end,
    induction x using alexandroff.rec_infty_of; induction y using alexandroff.rec_infty_of,
    { simpa using hxy },
    { simpa using key y hxy.symm },
    { rcases key x hxy with ⟨u, v, hu, hv, hxu, hyv, huv⟩,
      exact ⟨v, u, hv, hu, hyv, hxu, (inter_comm u v) ▸ huv⟩ },
    { have hxy' : x ≠ y := λ w, hxy (coe_eq_coe.mpr w),
      rcases t2_separation hxy' with ⟨u, v, hu, hv, hxu, hyv, huv⟩,
      refine ⟨of '' u, of '' v, is_open_map_of _ hu, is_open_map_of _ hv,
        ⟨x, hxu, rfl⟩, ⟨y, hyv, rfl⟩, _⟩,
      simp only [image_inter of_injective, huv, image_empty], }
  end }

end topological