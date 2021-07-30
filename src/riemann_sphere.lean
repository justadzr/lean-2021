import riemann_surfaces

noncomputable theory
open_locale classical

inductive rsphere
| of_complex (z : ℂ) : rsphere
| infinity : rsphere

namespace rsphere

protected def add : rsphere → rsphere → rsphere
| (of_complex z) (of_complex z') := of_complex (z + z')
| infinity z := infinity
| z infinity := infinity

protected def mul : rsphere → rsphere → rsphere
| (of_complex z) (of_complex z') := of_complex (z * z')
| infinity z := of_complex 0
| z infinity := of_complex 0

protected def inv : rsphere → rsphere
| (of_complex z) := of_complex z⁻¹
| infinity := of_complex 0

protected def neg : rsphere → rsphere
| (of_complex z) := of_complex (-z)
| infinity := infinity

def is_complex : rsphere → bool
| (of_complex z) := tt
| infinity := ff

def is_infinity : rsphere → bool
| (of_complex _) := ff
| infinity := tt

def get_or_else : rsphere → ℂ → ℂ
| (of_complex x) _ := x
| infinity x := x

def get : ∀ {z : rsphere}, z.is_complex → ℂ
| (of_complex x) h := x
| infinity h := false.rec _ $ bool.ff_ne_tt h

lemma is_complex_iff_exists {z : rsphere} :
  is_complex z ↔ ∃ (x : ℂ), z = of_complex x :=
by cases z; simp [is_complex]; exact ⟨_, rfl⟩

@[simp] lemma is_infinity_infinity : is_infinity infinity = tt := rfl
@[simp] lemma is_infinity_of_complex {z : ℂ} : is_infinity (of_complex z) = ff := rfl
@[simp] lemma is_complex_infinity : is_complex infinity = ff := rfl
@[simp] lemma is_complex_of_complex {z : ℂ} : is_complex (of_complex z) = tt := rfl
@[simp] lemma not_is_complex {z : rsphere} : z.is_complex = tt ↔ z.is_infinity = ff :=
by cases z; simp

end rsphere

open rsphere

instance : has_one rsphere := ⟨of_complex 1⟩
instance : has_zero rsphere := ⟨of_complex 0⟩
instance : has_add rsphere := ⟨rsphere.add⟩
instance : has_mul rsphere := ⟨rsphere.mul⟩
instance : has_inv rsphere := ⟨rsphere.inv⟩
instance : has_neg rsphere := ⟨rsphere.neg⟩
instance : has_coe ℂ rsphere := ⟨λ z, of_complex z⟩
instance : inhabited rsphere := ⟨0⟩

lemma coe_eq (z z' : ℂ) : (z : rsphere) = z' ↔ z = z'  :=
⟨of_complex.inj, λ h, by rw h⟩

namespace rsphere

lemma coe_def {z : ℂ} : ↑z = of_complex z := rfl

lemma ne_infinity_iff_is_complex {z : rsphere} :
  z ≠ infinity ↔ z.is_complex :=
by cases z; simp

lemma ne_infinity_iff_exists {z : rsphere} :
  z ≠ infinity ↔ ∃ (x : ℂ), z = of_complex x :=
by cases z; simp

lemma ne_infinity_iff_exists' {z : rsphere} :
  z ≠ infinity ↔ ∃ (x : ℂ), z = ↑x :=
by cases z; simp [coe_def]

end rsphere

-- lemma eq_complex_of_is_complex : 
--   ∀ {z : rsphere} (h : z.is_complex), z = of_complex (get h)
-- | (of_complex x) h := rfl

-- lemma eq_infinity_of_is_infinity :
--   ∀ {z : rsphere} (h : z.is_infinity), z = infinity
-- | infinity h := rfl

-- lemma is_infinity_iff_eq_infinity {z : rsphere} :
--   z.is_infinity ↔ z = infinity :=
-- ⟨λ h, eq_infinity_of_is_infinity h, λ e, e.symm ▸ rfl⟩

-- lemma of_complex_ne_infinity (z : ℂ) : 
--   of_complex z ≠ infinity :=
-- λ h, rsphere.no_confusion h

open rsphere

def set_of_complex {s : set rsphere} (h : infinity ∉ s) : set ℂ :=
{z : ℂ | ↑z ∈ s}

def Set_of_complex {S : set (set rsphere)} 
  (h : ∀ (t : set rsphere), t ∈ S → infinity ∉ t) : set (set ℂ) :=
{s : set ℂ | ∃ (s' : set rsphere) (hs' : s' ∈ S), set_of_complex (h s' hs') = s}

lemma mem_coe_mem_set_of_complex {s : set rsphere} 
  (h : infinity ∉ s) {z : ℂ} :
↑z ∈ s ↔ z ∈ set_of_complex h := iff.rfl

lemma set_of_complex_inter {s t : set rsphere} 
  (hs : infinity ∉ s) (ht : infinity ∉ t) (hst : infinity ∉ s ∩ t) :
  (set_of_complex hs) ∩ (set_of_complex ht) = set_of_complex hst :=
by unfold set_of_complex; ext1; simp

lemma set_of_complex_inter_comm {s t : set rsphere} 
  (hst : infinity ∉ s ∩ t) (hts : infinity ∉ t ∩ s) : 
  set_of_complex hst = set_of_complex hts :=
by unfold set_of_complex; rw set.inter_comm

lemma set_of_complex_sUnion {S : set (set rsphere)} 
  (hS : infinity ∉ ⋃₀S) (ht : ∀ (t : set rsphere), t ∈ S → infinity ∉ t) : 
  set_of_complex hS = ⋃₀(Set_of_complex ht)  :=
begin
  ext1 z,
  split,
  { rintros ⟨s', hs', Hs'⟩,
    simp only [Set_of_complex],
    let p := ht s' hs',
    refine ⟨set_of_complex p, _, (mem_coe_mem_set_of_complex p).mp Hs'⟩,
    exact ⟨s', hs', rfl⟩, },
  { rintros ⟨s', hs', Hs'⟩,
    rcases hs' with ⟨a, ha, Ha⟩,
    simp only [set_of_complex, set.mem_set_of_eq, set.mem_sUnion],
    rw ← Ha at Hs',
    rw ← mem_coe_mem_set_of_complex at Hs',
    exact ⟨a, ha, Hs'⟩, },
end

lemma is_open_sUnion_Set_of_complex {S : set (set rsphere)}
  (ht : ∀ (t : set rsphere), t ∈ S → infinity ∉ t) 
  (Ht : ∀ (t : set rsphere) (ht' : t ∈ S), is_open (set_of_complex $ ht t ht')) :
  is_open ⋃₀(Set_of_complex ht) :=
begin
  refine is_open_sUnion (λ s' hs', _),
  rcases hs' with ⟨a, ha, Ha⟩,
  specialize Ht a ha,
  rw Ha at Ht,
  exact Ht,
end

def set_to_rsphere (s : set ℂ) : set rsphere :=
{z : rsphere | ∃ (z' : ℂ) (H : z' ∈ s), z = ↑z'}

lemma set_to_rsphere_injective (s t : set ℂ) :
  set_to_rsphere s = set_to_rsphere t ↔ s = t :=
begin
  split,
  { intros h, 
    ext1 z',
    split,
    { intros h',
      have : ↑z' ∈ set_to_rsphere s := ⟨z', h', rfl⟩, 
      rw h at this, 
      rcases this with ⟨z'', hz'', hzz''⟩, 
      rw coe_eq at hzz'',
      rw hzz'',
      exact hz'', },
    { intros h',
      have : ↑z' ∈ set_to_rsphere t := ⟨z', h', rfl⟩,
      rw ← h at this, 
      rcases this with ⟨z'', hz'', hzz''⟩, 
      rw coe_eq at hzz'',
      rw hzz'',
      exact hz'', }, },
  { intros h, rw h, },
end

lemma set_to_rsphere_inter (s t : set ℂ) :
  set_to_rsphere s ∩ set_to_rsphere t = set_to_rsphere (s ∩ t) :=
begin
  unfold set_to_rsphere,
  ext1 z,
  split,
  { intros h, 
    rcases h.1 with ⟨z', hs, hzz'⟩, 
    rcases h.2 with ⟨z'', ht, hzz''⟩, 
    rw [hzz', coe_eq] at hzz'',
    rw ← hzz'' at ht,
    exact ⟨z', ⟨hs, ht⟩, hzz'⟩, },
  { rintros ⟨z', hst, hzz'⟩,
    exact ⟨⟨z', hst.1, hzz'⟩, z', hst.2, hzz'⟩, },
end

lemma of_complex_to_rsphere_eq_self {s : set rsphere} (h : infinity ∉ s) :
  set_to_rsphere (set_of_complex h) = s :=
begin
  ext1 z,
  split,
  { rintros ⟨z', hz', hzz'⟩,
    rw hzz',
    exact hz', },
  { intros h',
    rcases ne_infinity_iff_exists'.mp (ne_of_mem_of_not_mem h' h) with ⟨z', hzz'⟩,
    rw hzz' at h',
    exact ⟨z', h', hzz'⟩, },
end

lemma infinity_not_mem_set_to_rpshere (s : set ℂ) :
  infinity ∉ set_to_rsphere s :=
λ w, begin
  simp only [set_to_rsphere, set.mem_set_of_eq] at w,
  rcases w with ⟨z', hz', hinfz'⟩,
  exact (ne_infinity_iff_exists'.mpr ⟨z', hinfz'⟩) rfl,
end

lemma set_of_complex_to_rsphere (s : set ℂ):
  set_of_complex (infinity_not_mem_set_to_rpshere s) = s :=
begin
  ext1 z,
  simp only [set_of_complex, set_to_rsphere, set.mem_set_of_eq],
  split,
  { rintros ⟨z', hz', hzz'⟩, rw coe_eq at hzz', rw hzz', exact hz', },
  { intros h, exact ⟨z, h, rfl⟩, },
end

lemma subset_to_rsphere_subset {s t : set ℂ} (h : s ⊆ t) :
  set_to_rsphere s ⊆ set_to_rsphere t :=
λ x hx, begin
  simp only [set_to_rsphere, set.mem_set_of_eq] at hx,
  rcases hx with ⟨z', hz', hxz'⟩,
  exact ⟨z', h hz', hxz'⟩, 
end

lemma coe_mem_set_to_rsphere {z : ℂ} {s : set ℂ} :
  ↑z ∈ set_to_rsphere s ↔ z ∈ s :=
begin
  split,
  { intros hz,
    simp only [set_to_rsphere, set.mem_set_of_eq] at hz,
    rcases hz with ⟨z', hz', hzz'⟩,
    rw coe_eq at hzz',
    exact hzz'.symm ▸ hz', },
  { intros hz,
    exact ⟨z, hz, rfl⟩, }
end

def compl_of_infinity {s : set rsphere} (h : infinity ∈ s) : set ℂ :=
{z : ℂ | ↑z ∉ s}

def Compl_of_infinity {S : set (set rsphere)}
  (h : ∀ (t : set rsphere), t ∈ S → infinity ∈ t) : set (set ℂ) :=
{s : set ℂ | ∃ (s' : set rsphere) (hs' : s' ∈ S), compl_of_infinity (h s' hs') = s}

lemma set_to_rsphere_compl_of_infinity_eq {s : set rsphere} (h : infinity ∈ s) :
  set_to_rsphere (compl_of_infinity h) = sᶜ :=
begin
  ext1 z,
  simp only [set_to_rsphere, compl_of_infinity, set.mem_set_of_eq],
  split,
  { rintros ⟨z', hz', hzz'⟩, 
    rw [set.mem_set_of_eq, ← set.mem_compl_iff, ← hzz'] at hz',
    exact hz' },
  { intros h',
    rw set.mem_compl_iff at h',
    have : z ≠ infinity,
    { intros w, rw ← w at h, exact h' h, },
    rcases ne_infinity_iff_exists'.mp this with ⟨z', hz'⟩,
    rw hz' at h',
    exact ⟨z', h', hz'⟩, },
end

lemma compl_of_infinity_sInter {S : set (set rsphere)} 
  (hS : infinity ∈ ⋃₀S) (ht : ∀ (t : set rsphere), t ∈ S → infinity ∈ t) :
  compl_of_infinity hS = ⋂₀(Compl_of_infinity ht) :=
begin
  ext1 z,
  split,
  { intros h t ht',
    rcases ht' with ⟨s', hs', Hs'⟩,
    simp only [compl_of_infinity] at h,
    rw [set.mem_set_of_eq, ← set.mem_compl_iff, set.compl_sUnion, set.mem_sInter] at h,
    have key : set_to_rsphere t = s'ᶜ,
    { rw ← Hs', exact set_to_rsphere_compl_of_infinity_eq (ht s' hs'), },
    specialize h (set_to_rsphere t) ((set.mem_image compl S _).mpr ⟨s', hs', key.symm⟩),
    exact coe_mem_set_to_rsphere.mp h, },
  { intros h,
    rw [set.mem_sInter, Compl_of_infinity] at h,
    rw [compl_of_infinity, set.mem_set_of_eq, ← set.mem_compl_iff, 
        set.compl_sUnion, set.mem_sInter],
    intros t ht',
    rcases ht' with ⟨s', hs', Hs'⟩,
    have minor : infinity ∉ t,
    { intros w, rw [← Hs', set.mem_compl_iff] at w, exact w (ht s' hs'), },
    let t' := set_of_complex minor,
    have key : ∃ (t'' : set rsphere) (ht'' : t'' ∈ S), compl_of_infinity (ht t'' ht'') = t',
    { rw [← set_to_rsphere_compl_of_infinity_eq (ht s' hs'), 
          ← of_complex_to_rsphere_eq_self minor, set_to_rsphere_injective] at Hs',
      exact ⟨s', hs', Hs'⟩, },
    specialize h t' key,
    exact (mem_coe_mem_set_of_complex _).mpr h, }
end

def exists_of_compl_of_infinity {s : set rsphere} 
  (h : infinity ∈ s) (H : is_compact $ compl_of_infinity h) :
  ∃ (K : set ℂ) (hc : is_compact K), s = set_to_rsphere Kᶜ ∪ { infinity } :=
begin
  let K := compl_of_infinity h,
  have : set_to_rsphere Kᶜ = s \ {infinity} :=
  begin
    ext1 z,
    split,
    { rintros ⟨z', hz', hzz'⟩,
      simp only [K, compl_of_infinity, set.compl_set_of, not_not, set.mem_set_of_eq] at hz',
      have key₁ : z ∈ s := hzz'.symm ▸ hz',
      have key₂ : z ≠ infinity := ne_infinity_iff_exists'.mpr ⟨z', hzz'⟩,
      exact ⟨key₁, key₂⟩, },
    { intros h',
      have minor : z ≠ infinity := h'.2,
      rcases ne_infinity_iff_exists'.mp minor with ⟨z', hzz'⟩,
      have key : z' ∈ Kᶜ,
      { simp only [K, compl_of_infinity, set.compl_set_of, not_not, set.mem_set_of_eq],
        exact hzz' ▸ h'.1, },
      exact ⟨z', key, hzz'⟩, },
  end,
  refine ⟨K, H, _⟩,
  rw [this, set.diff_union_self, set.union_singleton, set.insert_eq_of_mem h],
end

lemma compl_of_univ : compl_of_infinity (set.mem_univ infinity) = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  intros x,
  by_contra w,
  exact w (set.mem_univ $ of_complex x),
end

lemma is_compact_sInter_Set_of_complex {S : set (set rsphere)}
  (h : infinity ∈ ⋃₀S)
  (ht : ∀ (t : set rsphere), t ∈ S → infinity ∈ t)
  (Ht : ∀ (t : set rsphere) (ht' : t ∈ S), is_compact (compl_of_infinity $ ht t ht')) :
  is_compact ⋂₀(Compl_of_infinity ht) :=
begin
  rcases set.mem_sUnion.mp h with ⟨t₀, ht₀, hinft₀⟩,
  have minor₁ : is_compact (compl_of_infinity hinft₀) := Ht t₀ ht₀,
  have minor₂ : ∀ (t : set ℂ) (ht' : t ∈ Compl_of_infinity ht), is_closed t :=
    λ t ht', let ⟨a, ha, hat⟩ := ht' in hat ▸ (Ht a ha).is_closed,
  have minor₃ : compl_of_infinity hinft₀ ∈ Compl_of_infinity ht := ⟨t₀, ht₀, rfl⟩,
  have minor₄ : ⋂₀(Compl_of_infinity ht) ⊆ compl_of_infinity hinft₀ := 
    set.sInter_subset_of_mem minor₃,
  have key : is_closed ⋂₀(Compl_of_infinity ht) := is_closed_sInter minor₂,
  exact compact_of_is_closed_subset minor₁ key minor₄,
end

lemma is_compact_union_compact {s t : set rsphere}
  (hs : infinity ∈ s) (ht : infinity ∈ t) (hst : infinity ∈ s ∩ t)
  (Hs : is_compact (compl_of_infinity hs)) (Ht : is_compact (compl_of_infinity ht)) :
  is_compact (compl_of_infinity hst) :=
begin
  rcases exists_of_compl_of_infinity hs Hs with ⟨Ks, hks, h₁⟩,
  rcases exists_of_compl_of_infinity ht Ht with ⟨Kt, hkt, h₂⟩,
  have : compl_of_infinity hst = Ks ∪ Kt :=
  begin
    ext1 z,
    simp only [compl_of_infinity, set.mem_set_of_eq],
    split,
    { intros h,
      let p := ne_infinity_iff_exists'.mpr ⟨z, rfl⟩,
      have minor₁ : ↑z ∉ set_to_rsphere Ksᶜ ∩ set_to_rsphere Ktᶜ :=
      λ w, begin
        have sub : ↑z ∈ s ∩ t,
        { rw [h₁, h₂], exact set.inter_subset_inter (set.subset_union_left _ _) 
          (set.subset_union_left _ _) w, },
        exact h sub,
      end,
      rw set_to_rsphere_inter at minor₁,
      have key : z ∉ Ksᶜ ∩ Ktᶜ,
      { rw ← coe_mem_set_to_rsphere, exact minor₁, },
      rw [← set.compl_union, ← set.mem_compl_iff, compl_compl] at key,
      exact key, },
    { intros h,
      rw set.mem_union_eq at h,
      cases h with u₁ u₂,
      { have : ↑z ∉ s :=
        λ w, begin
          rw [h₁, set.union_singleton] at w,
          let q := coe_mem_set_to_rsphere.mp (set.mem_of_mem_insert_of_ne w $ 
            ne_infinity_iff_exists'.mpr ⟨z, rfl⟩),
          exact q u₁,
        end,
        intros w,
        exact this w.1, },
      { have : ↑z ∉ t := 
        λ w, begin
          rw [h₂, set.union_singleton] at w,
          let q := coe_mem_set_to_rsphere.mp (set.mem_of_mem_insert_of_ne w $ 
            ne_infinity_iff_exists'.mpr ⟨z, rfl⟩),
          exact q u₂,
        end,
        intros w,
        exact this w.2, }, },
  end,
  rw this,
  exact hks.union hkt,
end

lemma is_open_union_mixed {s t : set rsphere} 
  (hs : infinity ∉ s) (ht : infinity ∈ t) (hst : infinity ∉ s ∩ t) 
  (Hs : is_open (set_of_complex hs)) (Ht : is_compact (compl_of_infinity ht)) :
  is_open (set_of_complex hst) :=
begin
  rcases exists_of_compl_of_infinity ht Ht with ⟨K, hk, H⟩,
  have minor₁ : infinity ∉ s ∩ set_to_rsphere Kᶜ := λ w, hs w.1,
  have key₁ : set_of_complex hst = set_of_complex minor₁,
  { ext1 z,
    split,
    { intros h,
      simp only [set_of_complex, set.mem_set_of_eq] at h ⊢,
      simp only [set.union_singleton] at H,
      rw H at h,
      let p := ne_infinity_iff_exists'.mpr ⟨z, rfl⟩,
      exact ⟨h.1, set.mem_of_mem_insert_of_ne h.2 p⟩, },
    { intros h,
      simp only [set_of_complex, set.mem_set_of_eq] at h ⊢,
      rw H,
      exact ⟨h.1, (set.subset_union_left _ _) h.2⟩, }, },
  rw [key₁, ← set_of_complex_inter],
  have minor₂ : infinity ∉ set_to_rsphere Kᶜ := infinity_not_mem_set_to_rpshere Kᶜ,
  let key₂ : is_closed K := hk.is_closed,
  rw set_of_complex_to_rsphere Kᶜ,
  rw ← is_open_compl_iff at key₂,
  exact is_open.inter Hs key₂,
end

lemma sUnion_separate {X : Type*} (S : set (set X)) (p : set X → Prop) :
  ⋃₀S = ⋃₀{s : set X | s ∈ S ∧ p s} ∪ ⋃₀{s : set X | s ∈ S ∧ ¬ p s} :=
begin
  ext1,
  split,
  { rintros ⟨a, ha, hxa⟩, 
    by_cases h : p a, 
    exact set.mem_union_left _ ⟨a, ⟨ha, h⟩, hxa⟩,
    exact set.mem_union_right _ ⟨a, ⟨ha, h⟩, hxa⟩, },
  { intros h,
    rw set.mem_union at h,
    cases h,
    { rcases h with ⟨a, ⟨ha, q⟩, hxa⟩, exact ⟨a, ha, hxa⟩, },
    { rcases h with ⟨a, ⟨ha, q⟩, hxa⟩, exact ⟨a, ha, hxa⟩, }, },
end

lemma compl_of_infinity_sUnion_separate {S : set (set rsphere)} (h : infinity ∈ ⋃₀S)
  (H : infinity ∈ ⋃₀{s : set rsphere | s ∈ S ∧ infinity ∈ s})
  (H' : infinity ∉ ⋃₀{s : set rsphere | s ∈ S ∧ infinity ∉ s}) :
  compl_of_infinity h = compl_of_infinity H ∩ (set_of_complex H')ᶜ :=
begin
  simp only [compl_of_infinity, set_of_complex],
  rw [set.compl_set_of, sUnion_separate S (λ t, infinity ∈ t)],
  ext1 z,
  simp only [set.mem_set_of_eq, set.mem_inter_iff, set.mem_union, not_or_distrib],
end

lemma is_compact_sUnion_compl {S : set (set rsphere)} (h : infinity ∈ ⋃₀S)
  (ht : ∀ (t : set rsphere), t ∈ S → infinity ∈ t)
  (Ht : ∀ (t : set rsphere) (ht' : t ∈ S), is_compact (compl_of_infinity $ ht t ht')) :
  is_compact (compl_of_infinity h) :=
by { rw compl_of_infinity_sInter, exact is_compact_sInter_Set_of_complex h ht Ht, }

instance : topological_space rsphere :=
{ is_open := λ s, if h : infinity ∉ s then (is_open $ set_of_complex h)
    else (is_compact $ compl_of_infinity $ not_not.mp h),
  is_open_univ :=
  begin
    have : ¬ infinity ∉ set.univ,
    { rw not_not, exact set.mem_univ infinity, },
    rw dif_neg,
    { rw compl_of_univ,
      exact is_compact_empty, },
    { exact this, },
  end,
  is_open_inter :=
  λ s t hs ht, begin
    by_cases h₁ : infinity ∉ s,
    { have : infinity ∉ s ∩ t := λ w, h₁ w.1,
      by_cases h₂ : infinity ∉ t,
      { rw dif_pos at hs ht ⊢,
        rw ← set_of_complex_inter h₁ h₂ this,
        exact is_open.inter hs ht, },
      { rw dif_pos h₁ at hs,
        rw dif_neg h₂ at ht,
        rw not_not at h₂,
        rw dif_pos this,
        exact is_open_union_mixed h₁ h₂ this hs ht, }, },
    { by_cases h₂ : infinity ∉ t,
      { have minor₁ : infinity ∉ s ∩ t := λ w, h₂ w.2,
        have minor₂ : infinity ∉ t ∩ s := λ w, h₂ w.1,
        rw dif_neg h₁ at hs,
        rw dif_pos h₂ at ht,
        rw dif_pos minor₁,
        rw not_not at h₁,
        rw set_of_complex_inter_comm minor₁ minor₂,
        exact is_open_union_mixed h₂ h₁ minor₂ ht hs, },
      { have minor₁ : ¬ infinity ∉ s ∩ t,
        { rw not_not, exact ⟨not_not.mp h₁, not_not.mp h₂⟩, },
        rw dif_neg h₁ at hs,
        rw dif_neg h₂ at ht,
        rw dif_neg minor₁,
        rw not_not at h₁ h₂ minor₁,
        exact is_compact_union_compact h₁ h₂ ⟨h₁, h₂⟩ hs ht, }, },
  end,
  is_open_sUnion :=
  λ S T, begin
    by_cases h : infinity ∉ ⋃₀S,
    { rw dif_pos h,
      have minor : ∀ (t : set rsphere), t ∈ S → infinity ∉ t := 
        λ t ht, set.not_mem_of_not_mem_sUnion h ht,
      have key : ∀ (t : set rsphere) (ht : t ∈ S), is_open (set_of_complex $ minor t ht),
      { intros t ht, specialize T t ht, rw dif_pos (minor t ht) at T, exact T, },
      rw set_of_complex_sUnion,
      exact is_open_sUnion_Set_of_complex minor key, },
    { rw dif_neg h,
      rw not_not at h,
      rcases h with ⟨a, ha, hinfa⟩,
      have H : infinity ∈ ⋃₀{s : set rsphere | s ∈ S ∧ infinity ∈ s} := ⟨a, ⟨ha, hinfa⟩, hinfa⟩,
      have H' : infinity ∉ ⋃₀{s : set rsphere | s ∈ S ∧ infinity ∉ s} := λ w, 
        let ⟨b, ⟨h₁, h₂⟩, hinfb⟩ := w in h₂ hinfb,
      rw compl_of_infinity_sUnion_separate (not_not.mp h) H H',
      have minor₁ : ∀ (t : set rsphere), 
        t ∈ {s : set rsphere | s ∈ S ∧ infinity ∉ s} → infinity ∉ t := λ t ht, ht.2,
      have minor₂ : ∀ (t : set rsphere)
        (ht : t ∈ {s : set rsphere | s ∈ S ∧ infinity ∉ s}), is_open (set_of_complex ht.2) :=
      λ t ht, by { specialize T t ht.1, rw dif_pos ht.2 at T, exact T, },
      rw set_of_complex_sUnion,
      have key₁ : is_closed (⋃₀Set_of_complex minor₁)ᶜ := 
        (is_open_sUnion_Set_of_complex minor₁ minor₂).is_closed_compl,
      have minor₃ : ∀ (t : set rsphere),
        t ∈ {s : set rsphere | s ∈ S ∧ infinity ∈ s} → infinity ∈ t := λ t ht, ht.2,
      have minor₄ : ∀ (t : set rsphere)
        (ht : t ∈ {s : set rsphere | s ∈ S ∧ infinity ∈ s}), is_compact (compl_of_infinity ht.2) :=
      λ t ht, by {specialize T t ht.1, rw dif_neg (not_not.mpr ht.2) at T, exact T, }, 
      have key₂ : is_compact (compl_of_infinity H) := is_compact_sUnion_compl H minor₃ minor₄,
      exact key₂.inter_right key₁, },
  end, }

lemma is_open_rsphere_iff {s : set rsphere} :
  is_open s ↔ 
  if h : infinity ∉ s then (is_open $ set_of_complex h) 
  else (is_compact $ compl_of_infinity $ not_not.mp h) := 
iff.rfl

instance : connected_space rsphere :=
{
  is_preconnected_univ := 
  λ u v hu hv hsuv hsu hsv, begin
    rw set.univ_inter at hsu hsv,
    rw is_open_rsphere_iff at hu hv,
  end,
}