import topology.subset_properties
import tactic

noncomputable theory

open_locale classical topological_space filter

open filter set

section basic

def alexandroff (X : Type*) [topological_space X] := option X

def of_base {X : Type*} [topological_space X] : X → alexandroff X := some

variables {X : Type*} [topological_space X]

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

variables {s : set (alexandroff X)}

lemma is_open_alexandroff_iff_aux :
  is_open s ↔ if none ∈ s then is_compact (some⁻¹' s)ᶜ ∧ is_closed (some⁻¹' s)ᶜ
  else is_open (some⁻¹' s) :=
iff.rfl

lemma is_open_iff_of_mem (h : none ∈ s) :
  is_open s ↔ is_compact (some⁻¹' s)ᶜ ∧ is_closed (some⁻¹' s)ᶜ :=
by rw [is_open_alexandroff_iff_aux, if_pos h]

lemma is_open_iff_of_mem' (h : none ∈ s) :
  is_open s ↔ is_compact (some⁻¹' s)ᶜ ∧ is_open (some⁻¹' s) :=
by rw [is_open_iff_of_mem h, is_closed_compl_iff]

lemma is_open_iff_of_not_mem (h : none ∉ s) :
  is_open s ↔ is_open (some⁻¹' s) :=
by rw [is_open_alexandroff_iff_aux, if_neg h] 

lemma is_open_of_is_open (h : is_open s) :
  is_open (some⁻¹' s) :=
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
    have minor₁ : is_compact (some⁻¹' Z K)ᶜ,
    { specialize h K, rw is_open_iff_of_mem hK at h, exact h.1, },
    let p : ι → set X := λ i, some⁻¹' Z i,
    have minor₂ : ∀ i, is_open (p i) := λ i, is_open_of_is_open (h i),
    have minor₃ : (some⁻¹' Z K)ᶜ ⊆ ⋃ i, p i :=
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
      have triv₂ : some y ∈ {x} := mem_singleton_of_eq hy,  
      rw [← mem_compl_iff, ← singleton_subset_iff] at hx,
      have : some⁻¹' {x} ⊆ some⁻¹' (Z K)ᶜ := λ y hy, hx hy,
      have key : y ∈ ⋃ (i : ι) (H : i ∈ ι'), p i := this.trans H' (mem_preimage.mpr triv₂),
      rcases mem_bUnion_iff'.mp key with ⟨i, hi, hyi⟩,
      rw [mem_preimage, hy] at hyi,
      exact ⟨i, mem_Union.mpr ⟨finset.subset_insert _ ι' hi, hyi⟩⟩, }, 
  end }

end basic

section topological

variables {X : Type*} [topological_space X]

@[continuity] lemma continuous_of_base : continuous (@of_base X _) :=
continuous_def.mpr (λ s hs, is_open_of_is_open hs)

def set_self : set (alexandroff X) := of_base '' univ

lemma set_self.dense : dense (@set_self X _) :=
begin
  
end

end topological
