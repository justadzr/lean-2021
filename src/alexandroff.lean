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
* The topological structure of `alexandroff X`
* The connectedness of `alexandroff X` for noncompact, preconnected X
* `alexandroff X` is `T₁` for a T₁ space `X`
* `alexandroff X` is Hausdorff if `X` is locally compact and Hausdorff
-/

noncomputable theory
open filter set
open_locale classical topological_space filter

section basic

def alexandroff (X : Type*) [topological_space X] := option X

def of {X : Type*} [topological_space X] : X → alexandroff X := some

variables {X : Type*} [topological_space X]

lemma of_apply {x : X} : of x = some x := rfl

instance : has_coe X (alexandroff X) := ⟨of⟩

@[simp] lemma coe_some_eq_of {x : X} : (some x : alexandroff X) = x := rfl

@[simp] lemma coe_ne_none (x : X) : (x : alexandroff X) ≠ none  .

@[simp] lemma of_eq_coe {x : X} : of x = (x : alexandroff X) := rfl

def range_of (X : Type*) [topological_space X] : set (alexandroff X) := coe '' (univ : set X)

@[simp] lemma coe_mem_range_of (x : X) : (x : alexandroff X) ∈ (range_of X) :=
by simp [range_of]

lemma univ_eq_union_none : (range_of X ∪ {none}) = univ :=
begin
  refine le_antisymm (subset_univ _) _,
  rintro ⟨_|x⟩;
  simp
end

@[simp] lemma none_not_mem_range_of : none ∉ range_of X :=
by simp [range_of, ← coe_some_eq_of]

@[simp] lemma not_mem_range_of_iff (x : alexandroff X) :
  x ∉ range_of X ↔ x = none :=
by { cases x; simp }

@[simp] lemma none_not_mem_image_of {s : set X} : none ∉ of '' s :=
not_mem_subset (image_subset _ $ subset_univ _) none_not_mem_range_of

lemma inter_none_eq_empty : (range_of X) ∩ {none} = ∅ :=
by { ext ⟨_|x⟩; simp }

lemma of_preimage_none : (of⁻¹' {none} : set X) = ∅ :=
by { ext, simp }

instance : topological_space (alexandroff X)  :=
{ is_open := λ s, if none ∈ s then is_compact (of⁻¹' s)ᶜ ∧ is_open (of⁻¹' s)
    else is_open (of⁻¹' s),
  is_open_univ := by simp,
  is_open_inter :=
  λ s t hs ht, begin
    split_ifs at hs ht with h h' h' h' h,
    { simpa [h, h', compl_inter] using and.intro (hs.1.union ht.1) (hs.2.inter ht.2) },
    { simpa [h, h'] using hs.inter ht.right },
    { simpa [h, h'] using hs.2.inter ht },
    { simpa [h, h'] using hs.inter ht }
  end,
  is_open_sUnion :=
  λ S ht, begin
    suffices : is_open (of⁻¹' ⋃₀S),
    { split_ifs with h,
      { obtain ⟨(a : set (alexandroff X)), ha, ha'⟩ := mem_sUnion.mp h,
        specialize ht a ha,
        rw if_pos ha' at ht,
        refine ⟨compact_of_is_closed_subset ht.left this.is_closed_compl _, this⟩,
        rw [compl_subset_compl, preimage_subset_iff],
        intros y hy,
        refine ⟨a, ha, hy⟩ },
      { exact this } },
     rw is_open_iff_forall_mem_open,
     simp only [and_imp, exists_prop, mem_Union, preimage_sUnion, mem_preimage, of_eq_coe,
                exists_imp_distrib],
     intros y s hs hy,
     refine ⟨of ⁻¹' s, subset_subset_Union _ (subset_subset_Union hs (subset.refl _)), _,
        mem_preimage.mpr hy⟩,
     specialize ht s hs,
     split_ifs at ht,
     { exact ht.right },
     { exact ht }
  end }

variables {s : set (alexandroff X)} {s' : set X}

@[simp] lemma is_open_alexandroff_iff_aux :
  is_open s ↔ if none ∈ s then is_compact (of⁻¹' s)ᶜ ∧ is_open (of⁻¹' s)
  else is_open (of⁻¹' s) :=
iff.rfl

@[simp] lemma is_open_iff_of_mem' (h : none ∈ s) :
  is_open s ↔ is_compact (of⁻¹' s)ᶜ ∧ is_open (of⁻¹' s) :=
by simp [h]

lemma is_open_iff_of_mem (h : none ∈ s) :
  is_open s ↔ is_compact (of⁻¹' s)ᶜ ∧ is_closed (of⁻¹' s)ᶜ :=
by simp [h, is_closed_compl_iff]

@[simp] lemma is_open_iff_of_not_mem (h : none ∉ s) :
  is_open s ↔ is_open (of⁻¹' s) :=
by simp [h]

lemma is_open_of_is_open (h : is_open s) :
  is_open (of⁻¹' s) :=
begin
  by_cases H : none ∈ s,
  { simpa using ((is_open_iff_of_mem H).mp h).2, },
  { exact (is_open_iff_of_not_mem H).mp h, },
end

instance : compact_space (alexandroff X) :=
{ compact_univ :=
  begin
    refine is_compact_of_finite_subcover (λ ι Z h H, _),
    simp only [univ_subset_iff] at H ⊢,
    rcases Union_eq_univ_iff.mp H none with ⟨K, hK⟩,
    have minor₁ : is_compact (of⁻¹' Z K)ᶜ,
    { specialize h K, rw is_open_iff_of_mem hK at h, exact h.1, },
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
    { exact ⟨K, mem_Union.mpr ⟨finset.mem_insert_self _ _, hx⟩⟩, },
    { have triv₁ : x ≠ none := (ne_of_mem_of_not_mem hK hx).symm,
      rcases option.ne_none_iff_exists.mp triv₁ with ⟨y, hy⟩,
      have triv₂ : of y ∈ {x} := mem_singleton_of_eq hy,
      rw [← mem_compl_iff, ← singleton_subset_iff] at hx,
      have : of⁻¹' {x} ⊆ of⁻¹' (Z K)ᶜ := λ y hy, hx hy,
      have key : y ∈ ⋃ (i : ι) (H : i ∈ ι'), p i := this.trans H' (mem_preimage.mpr triv₂),
      rcases mem_bUnion_iff'.mp key with ⟨i, hi, hyi⟩,
      rw [mem_preimage, of_apply, hy] at hyi,
      exact ⟨i, mem_Union.mpr ⟨finset.subset_insert _ ι' hi, hyi⟩⟩, },
  end }

end basic

section topological

variables {X : Type*} [topological_space X]

lemma of_injective : function.injective (@of X _) :=
option.some_injective X

@[continuity] lemma continuous_of : continuous (@of X _) :=
continuous_def.mpr (λ s hs, is_open_of_is_open hs)

def opens_of_compl {s : set X} (h : is_compact s ∧ is_closed s) :
  topological_space.opens (alexandroff X) :=
⟨(of '' s)ᶜ, by { rw [is_open_iff_of_mem ((mem_compl_iff _ _).mpr none_not_mem_image_of),
  preimage_compl, compl_compl, of_injective.preimage_image _], exact h, }⟩

lemma none_mem_opens_of_compl {s : set X} (h : is_compact s ∧ is_closed s) :
  none ∈ (opens_of_compl h : set (alexandroff X)) :=
by { simp only [opens_of_compl, topological_space.opens.coe_mk],
     exact mem_compl none_not_mem_image_of, }

lemma is_open_map_of : is_open_map (@of X _) :=
λ s hs, begin
  rw [← preimage_image_eq s of_injective] at hs,
  rw is_open_iff_of_not_mem none_not_mem_image_of,
  exact hs,
end

lemma is_open_range_of : is_open (@range_of X _) :=
is_open_map_of _ is_open_univ

lemma dense_set_self (h : ¬ is_compact (univ : set X)) : dense (@range_of X _) :=
begin
  refine dense_iff_inter_open.mpr (λ s hs Hs, _),
  by_cases H : none ∈ s,
  { rw is_open_iff_of_mem H at hs,
    have minor₁ : s ≠ {none},
    { by_contra w,
      rw [not_not.mp w, of_preimage_none, compl_empty] at hs,
      exact h hs.1, },
    have minor₂ : of⁻¹' s ≠ ∅,
    { by_contra w,
      rw [not_not, eq_empty_iff_forall_not_mem] at w,
      simp only [mem_preimage] at w,
      have : ∀ z ∈ s, z = none := λ z hz,
        by_contra (λ w', let ⟨x, hx⟩ := option.ne_none_iff_exists'.mp w' in
          by rw hx at hz; exact (w x) hz),
      exact minor₁ (eq_singleton_iff_unique_mem.mpr ⟨H, this⟩), },
    rcases ne_empty_iff_nonempty.mp minor₂ with ⟨x, hx⟩,
    exact ⟨of x, hx, x, mem_univ _, rfl⟩, },
  { rcases Hs with ⟨z, hz⟩,
    rcases option.ne_none_iff_exists'.mp (ne_of_mem_of_not_mem hz H) with ⟨x, hx⟩,
    rw hx at hz,
    exact ⟨of x, hz, x, mem_univ _, rfl⟩, },
end

instance [preconnected_space X] (h : ¬ is_compact (univ : set X)) :
  connected_space (alexandroff X) :=
{ is_preconnected_univ :=
  begin
    rw ← dense_iff_closure_eq.mp (dense_set_self h),
    exact is_preconnected.closure
      (is_preconnected_univ.image of continuous_of.continuous_on),
  end,
  to_nonempty := ⟨none⟩, }

instance [t1_space X] : t1_space (alexandroff X) :=
{ t1 :=
  λ z, begin
    by_cases z = none,
    { rw [h, ← is_open_compl_iff, compl_eq_univ_diff, ← univ_eq_union_none,
          union_diff_cancel_right (subset.antisymm_iff.mp inter_none_eq_empty).1],
      exact is_open_range_of, },
    { rcases option.ne_none_iff_exists.mp h with ⟨x, hx⟩,
      have minor₂ : (none : alexandroff X) ∈ {z}ᶜ :=
        mem_compl (λ w, (ne.symm h) (mem_singleton_iff.mp w)),
      rw [← is_open_compl_iff, is_open_iff_of_mem minor₂],
      simp only [preimage_compl, compl_compl, ← hx, of,
                 ← image_singleton, (option.some_injective X).preimage_image _],
      exact ⟨is_compact_singleton, is_closed_singleton⟩, },
  end, }

instance [locally_compact_space X] [t2_space X] : t2_space (alexandroff X) :=
{ t2 :=
  λ x y hxy, begin
    have key : ∀ (x y : alexandroff X), x = none → y ≠ none →
      ∃ (u v : set (alexandroff X)), is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
    λ x y h₁ h₂, begin
      rcases option.ne_none_iff_exists.mp h₂ with ⟨y', hy'⟩,
      rcases exists_open_with_compact_closure y' with ⟨u, hu, huy', Hu⟩,
      have minor₁ : _ ∧ is_closed (closure u) := ⟨Hu, is_closed_closure⟩,
      refine ⟨opens_of_compl minor₁, of '' u, _⟩,
      rw h₁,
      refine ⟨(opens_of_compl minor₁).2, is_open_map_of _ hu,
        none_mem_opens_of_compl minor₁, ⟨y', huy', hy'⟩, _⟩,
      simp only [opens_of_compl, topological_space.opens.coe_mk],
      have minor₂ : (of '' closure u)ᶜ ∩ of '' u ⊆ (of '' u)ᶜ ∩ of '' u,
      { apply inter_subset_inter_left,
        simp only [compl_subset_compl, image_subset _ (subset_closure)], },
      rw compl_inter_self at minor₂,
      exact eq_empty_of_subset_empty minor₂,
    end,
    by_cases h₁ : x = none; by_cases h₂ : y = none,
    { exfalso,
      rw [h₁, h₂] at hxy,
      exact hxy rfl, },
    { rcases key x y h₁ h₂ with ⟨u, v, huv⟩,
      exact ⟨u, v, huv⟩, },
    { rcases key y x h₂ h₁ with ⟨u, v, hu, hv, yv, xu, huv⟩,
      rw inter_comm at huv,
      exact ⟨v, u, hv, hu, xu, yv, huv⟩, },
    { rcases option.ne_none_iff_exists.mp h₁ with ⟨x', hx'⟩,
      rcases option.ne_none_iff_exists.mp h₂ with ⟨y', hy'⟩,
      rw [← hx', ← hy'] at hxy,
      have hxy' := of_injective.ne_iff.mp hxy,
      rcases t2_separation hxy' with ⟨u, v, hu, hv, xu, yv, huv⟩,
      refine ⟨of '' u, of '' v, is_open_map_of _ hu, is_open_map_of _ hv,
        ⟨x', xu, hx'⟩, ⟨y', yv, hy'⟩, _⟩,
      simp only [image_inter of_injective, huv, image_empty], },
  end, }

end topological
