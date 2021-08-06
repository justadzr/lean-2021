import topology.separation
import topology.opens
import tactic

noncomputable theory

open_locale classical topological_space filter

open filter set

section basic

def alexandroff (X : Type*) [topological_space X] := option X

def of_base {X : Type*} [topological_space X] : X → alexandroff X := some

variables {X : Type*} [topological_space X]

@[simp] lemma of_base_eq_some {x : X} : of_base x = some x := rfl

def set_base : set (alexandroff X) := of_base '' univ

lemma univ_eq_union_none : (set_base ∪ {none} : set (alexandroff X)) = univ :=
begin
  rw eq_univ_iff_forall,
  intro z,
  by_cases z = none,
  { rw h,
    exact or.intro_right _ (mem_singleton _), },
  { rcases option.ne_none_iff_exists.mp h with ⟨x, hx⟩,
    exact or.intro_left _ ⟨x, mem_univ _, hx⟩, },
end

lemma inter_none_eq_empty : (set_base : set (alexandroff X)) ∩ {none} = ∅ :=
begin
  by_contra w,
  rcases ne_empty_iff_nonempty.mp w with ⟨z, hz⟩,
  rcases hz.1 with ⟨x, hx, Hx⟩,
  rw mem_singleton_iff.mp hz.2 at Hx,
  convert Hx,
  simp only [option.is_none_none, of_base, option.is_none_some],
end

lemma not_mem_of_base_image (s' : set X) : none ∉ (of_base '' s') :=
begin
  by_contra,
  rcases (mem_image _ _ _).mp h with ⟨x, hx, Hx⟩,
  convert Hx,
  simp only [option.is_none_none, of_base, option.is_none_some],
end

lemma of_base_preimage_none : (of_base⁻¹' {none} : set X) = ∅ :=
begin
  by_contra,
  rcases ne_empty_iff_nonempty.mp h with ⟨x, hx⟩,
  have : none ∈ (of_base '' {x}),
  { rw mem_image, exact ⟨x, mem_singleton _, hx⟩, },
  exact not_mem_of_base_image {x} this,
end

instance : topological_space (alexandroff X)  :=
{ is_open := λ s, if none ∈ s then is_compact (some⁻¹' s)ᶜ ∧ is_closed (some⁻¹' s)ᶜ 
    else is_open (some⁻¹' s),
  is_open_univ := 
  begin
    rw [if_pos (mem_univ _), preimage_univ, compl_univ], 
    exact ⟨is_compact_empty, is_closed_empty⟩,
  end,
  is_open_inter := 
  λ s t hs ht, begin
    split_ifs,
    { cases h with hs₁ ht₁,
      rw if_pos at hs ht; [skip, exact hs₁, exact ht₁],
      rw [preimage_inter, compl_inter],
      exact ⟨hs.1.union ht.1, hs.2.union ht.2⟩, },
    { rw [mem_inter_iff, not_and_distrib] at h,
      rw preimage_inter,
      cases h with hs₂ ht₂,
      { rw if_neg hs₂ at hs,
        by_cases H : none ∈ t,
        { rw [if_pos H, is_closed_compl_iff] at ht,
          exact hs.inter ht.2, },
        { rw [if_neg H] at ht,
          exact hs.inter ht, }, },
      { rw if_neg ht₂ at ht,
        by_cases H : none ∈ s,
        { rw [if_pos H, is_closed_compl_iff] at hs,
          exact hs.2.inter ht, },
        { rw [if_neg H] at hs,
          exact hs.inter ht, }, }, },
  end,
  is_open_sUnion := 
  λ S ht, begin
    split_ifs,
    { rcases mem_sUnion.mp h with ⟨a, ha, Ha⟩,
      have minor₁ : is_compact (some⁻¹' a)ᶜ ∧ is_closed (some⁻¹' a)ᶜ,
      { convert ht a ha, rw if_pos Ha, },
      have minor₂ : (some⁻¹' ⋃₀S)ᶜ ⊆ (some⁻¹' a)ᶜ := compl_subset_compl.mpr (λ x hx, ⟨a, ha, hx⟩),
      suffices p : is_closed (some⁻¹' ⋃₀S)ᶜ,
      { exact ⟨compact_of_is_closed_subset minor₁.1 p minor₂, p⟩, },
      have triv : S = {t | t ∈ S ∧ none ∈ t} ∪ {t | t ∈ S ∧ none ∉ t},
      { ext1,
        simp only [← set_of_or, mem_set_of_eq, exists_prop, ← and_or_distrib_left, and_true],
        split,
        { intros h, exact ⟨h, classical.em _⟩, },
        { intros h, exact h.1, }, },
      rw [← preimage_compl, triv, sUnion_union, compl_union, preimage_inter, 
          compl_sUnion, preimage_compl, preimage_sUnion, sInter_eq_bInter, preimage_bInter],
      have minor₃ : ∀ t' ∈ {t | t ∈ S ∧ none ∉ t}, is_open (some⁻¹' t'),
      { intros s hs, convert ht s hs.1, rw if_neg hs.2, },
      have key₁ : is_closed (⋃ t ∈ {t | t ∈ S ∧ none ∉ t}, some ⁻¹' t)ᶜ,
      { refine is_open.is_closed_compl _, exact is_open_bUnion minor₃, },
      have minor₄ : ∀ t' ∈ {t | t ∈ S ∧ none ∈ t}, is_closed (some⁻¹' t')ᶜ,
      { intros s hs, specialize ht s hs.1, rw if_pos hs.2 at ht, exact ht.2, },
      have key₂ : is_closed (⋂ t ∈ compl '' {t | t ∈ S ∧ none ∈ t}, some ⁻¹' t),
      { refine is_closed_bInter (λ s' hs', _), 
        rcases hs' with ⟨s, hs, Hs⟩, 
        exact Hs ▸ (minor₄ s hs), },
      exact key₂.inter key₁, },
    { rw preimage_sUnion,
      have minor : ∀ t, t ∈ S → none ∉ t :=
        λ s hs, set.not_mem_of_not_mem_sUnion h hs,
      have key : ∀ t, t ∈ S → is_open (some⁻¹' t),
      { intros s hs, specialize ht s hs, rw if_neg (minor s hs) at ht, exact ht, },
      exact is_open_bUnion key, },
  end, }

variables {s : set (alexandroff X)} {s' : set X}

lemma is_open_alexandroff_iff_aux :
  is_open s ↔ if none ∈ s then is_compact (of_base⁻¹' s)ᶜ ∧ is_closed (of_base⁻¹' s)ᶜ
  else is_open (of_base⁻¹' s) :=
iff.rfl

lemma is_open_iff_of_mem (h : none ∈ s) :
  is_open s ↔ is_compact (of_base⁻¹' s)ᶜ ∧ is_closed (of_base⁻¹' s)ᶜ :=
by rw [is_open_alexandroff_iff_aux, if_pos h]

lemma is_open_iff_of_mem' (h : none ∈ s) :
  is_open s ↔ is_compact (of_base⁻¹' s)ᶜ ∧ is_open (of_base⁻¹' s) :=
by rw [is_open_iff_of_mem h, is_closed_compl_iff]

lemma is_open_iff_of_not_mem (h : none ∉ s) :
  is_open s ↔ is_open (of_base⁻¹' s) :=
by rw [is_open_alexandroff_iff_aux, if_neg h] 

lemma is_open_of_is_open (h : is_open s) :
  is_open (of_base⁻¹' s) :=
begin
  by_cases H : none ∈ s,
  { convert ((is_open_iff_of_mem H).mp h).2.is_open_compl, rw compl_compl, },
  { exact (is_open_iff_of_not_mem H).mp h, },
end

instance : compact_space (alexandroff X) := 
{ compact_univ := 
  begin
    refine is_compact_of_finite_subcover (λ ι Z h H, _),
    simp only [univ_subset_iff] at H ⊢,
    rcases Union_eq_univ_iff.mp H none with ⟨K, hK⟩,
    have minor₁ : is_compact (of_base⁻¹' Z K)ᶜ,
    { specialize h K, rw is_open_iff_of_mem hK at h, exact h.1, },
    let p : ι → set X := λ i, of_base⁻¹' Z i,
    have minor₂ : ∀ i, is_open (p i) := λ i, is_open_of_is_open (h i),
    have minor₃ : (of_base⁻¹' Z K)ᶜ ⊆ ⋃ i, p i :=
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
      have triv₂ : of_base y ∈ {x} := mem_singleton_of_eq hy,  
      rw [← mem_compl_iff, ← singleton_subset_iff] at hx,
      have : of_base⁻¹' {x} ⊆ of_base⁻¹' (Z K)ᶜ := λ y hy, hx hy,
      have key : y ∈ ⋃ (i : ι) (H : i ∈ ι'), p i := this.trans H' (mem_preimage.mpr triv₂),
      rcases mem_bUnion_iff'.mp key with ⟨i, hi, hyi⟩,
      rw [mem_preimage, of_base_eq_some, hy] at hyi,
      exact ⟨i, mem_Union.mpr ⟨finset.subset_insert _ ι' hi, hyi⟩⟩, }, 
  end }

end basic

section topological

variables {X : Type*} [topological_space X]

lemma of_base_injective : function.injective (@of_base X _) :=
option.some_injective X

@[continuity] lemma continuous_of_base : continuous (@of_base X _) :=
continuous_def.mpr (λ s hs, is_open_of_is_open hs)

def opens_of_compl {s : set X} (h : is_compact s ∧ is_closed s) : 
  topological_space.opens (alexandroff X) :=
⟨(of_base '' s)ᶜ, 
  by { rw [is_open_iff_of_mem ((mem_compl_iff _ _).mpr $ not_mem_of_base_image _), 
      preimage_compl, compl_compl, of_base_injective.preimage_image _], exact h, }⟩

lemma none_mem_opens_of_compl {s : set X} (h : is_compact s ∧ is_closed s) :
  none ∈ (opens_of_compl h : set (alexandroff X)) :=
by { simp only [opens_of_compl, topological_space.opens.coe_mk], 
     exact mem_compl (not_mem_of_base_image _), }

lemma is_open_map_of_base : is_open_map (@of_base X _) :=
λ s hs, begin
  rw [← preimage_image_eq s of_base_injective] at hs,
  rw is_open_iff_of_not_mem (not_mem_of_base_image s),
  exact hs,
end

lemma is_open_set_base : is_open (@set_base X _) :=
is_open_map_of_base _ is_open_univ 

lemma dense_set_self (h : ¬ is_compact (univ : set X)) : dense (@set_base X _) :=
begin
  refine dense_iff_inter_open.mpr (λ s hs Hs, _),
  by_cases H : none ∈ s,
  { rw is_open_iff_of_mem H at hs,
    have minor₁ : s ≠ {none},
    { by_contra w,
      rw [not_not.mp w, of_base_preimage_none, compl_empty] at hs,
      exact h hs.1, },
    have minor₂ : of_base⁻¹' s ≠ ∅,
    { by_contra w, 
      rw [not_not, eq_empty_iff_forall_not_mem] at w,
      simp only [mem_preimage] at w,
      have : ∀ z ∈ s, z = none := λ z hz, 
        by_contra (λ w', let ⟨x, hx⟩ := option.ne_none_iff_exists'.mp w' in 
          by rw hx at hz; exact (w x) hz), 
      exact minor₁ (eq_singleton_iff_unique_mem.mpr ⟨H, this⟩), },
    rcases ne_empty_iff_nonempty.mp minor₂ with ⟨x, hx⟩,
    exact ⟨of_base x, hx, x, mem_univ _, rfl⟩, },
  { rcases Hs with ⟨z, hz⟩,
    rcases option.ne_none_iff_exists'.mp (ne_of_mem_of_not_mem hz H) with ⟨x, hx⟩,
    rw hx at hz,
    exact ⟨of_base x, hz, x, mem_univ _, rfl⟩, },
end

instance [preconnected_space X] (h : ¬ is_compact (univ : set X)) : 
  connected_space (alexandroff X) :=
{ is_preconnected_univ := 
  begin
    rw ← dense_iff_closure_eq.mp (dense_set_self h),
    exact is_preconnected.closure 
      (is_preconnected_univ.image of_base continuous_of_base.continuous_on),
  end,
  to_nonempty := ⟨none⟩, }

instance [t1_space X] : t1_space (alexandroff X) :=
{ t1 :=
  λ z, begin
    by_cases z = none,
    { rw [h, ← is_open_compl_iff, compl_eq_univ_diff, ← univ_eq_union_none, 
          union_diff_cancel_right (subset.antisymm_iff.mp inter_none_eq_empty).1],
      exact is_open_set_base, },
    { rcases option.ne_none_iff_exists.mp h with ⟨x, hx⟩,
      have minor₂ : (none : alexandroff X) ∈ {z}ᶜ := 
        mem_compl (λ w, (ne.symm h) (mem_singleton_iff.mp w)),
      rw [← is_open_compl_iff, is_open_iff_of_mem minor₂],
      simp only [preimage_compl, compl_compl, ← hx, of_base, 
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
      refine ⟨opens_of_compl minor₁, of_base '' u, _⟩,
      rw h₁,
      refine ⟨(opens_of_compl minor₁).2, is_open_map_of_base _ hu, 
        none_mem_opens_of_compl minor₁, ⟨y', huy', hy'⟩, _⟩,
      simp only [opens_of_compl, topological_space.opens.coe_mk],
      have minor₂ : (of_base '' closure u)ᶜ ∩ of_base '' u ⊆ (of_base '' u)ᶜ ∩ of_base '' u,
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
      have hxy' := of_base_injective.ne_iff.mp hxy,
      rcases t2_separation hxy' with ⟨u, v, hu, hv, xu, yv, huv⟩,
      refine ⟨of_base '' u, of_base '' v, is_open_map_of_base _ hu, is_open_map_of_base _ hv, 
        ⟨x', xu, hx'⟩, ⟨y', yv, hy'⟩, _⟩,
      simp only [image_inter of_base_injective, huv, image_empty], },    
  end, }

end topological
