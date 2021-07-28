import riemann_surfaces

noncomputable theory
open_locale classical

section rsphere

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

end rsphere

open rsphere

instance : has_one rsphere := ⟨of_complex 1⟩
instance : has_zero rsphere := ⟨of_complex 0⟩
instance : has_add rsphere := ⟨rsphere.add⟩
instance : has_mul rsphere := ⟨rsphere.mul⟩
instance : has_inv rsphere := ⟨rsphere.inv⟩
instance : has_neg rsphere := ⟨rsphere.neg⟩

def set_of_complex {s : set rsphere} (h : infinity ∉ s) : set ℂ :=
{z : ℂ | of_complex z ∈ s}

def compl_of_infinity {s : set rsphere} (h : infinity ∈ s) : set ℂ :=
{z : ℂ | of_complex z ∉ s}

instance : topological_space rsphere :=
{
  is_open := λ s, if h : infinity ∉ s then (is_open $ set_of_complex h) 
    else (is_compact $ compl_of_infinity $ not_not.mp h),
}

end rsphere