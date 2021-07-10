--- Will clean up these imports
import tactic
import analysis.calculus.iterated_deriv
import topology.continuous_function.polynomial
import topology.separation
import analysis.convex.topology
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
import analysis.calculus.formal_multilinear_series
import complex_analysis_prep
import riemann_surfaces

open set complex classical filter asymptotics continuous_linear_map set metric is_open differentiable
open_locale topological_space classical nnreal asymptotics filter ennreal unit_interval

noncomputable theory

def uhalf_plane : set ℂ := {z : ℂ | z.im > 0}

localized "notation `ℍ` := uhalf_plane" in uhalf_plane

namespace upper_half_plane

@[simp] theorem uhalf_plane.is_open : is_open ℍ :=
begin
  have : ℍ = complex.im⁻¹' Ioi 0 := set.ext (λ z, iff.intro (λ hz, mem_preimage.mp hz) $ λ hz, hz),
  exact is_open.preimage complex.continuous_im is_open_Ioi,
end


@[simp] theorem uhalf_plane.nonempty : set.nonempty ℍ :=
begin
  rw set.nonempty_def,
  use complex.I,
   --- Very bad proof here
  have : complex.I.im > 0 :=  by rw complex.I_im; exact zero_lt_one, 
  exact this,
end

@[simp] theorem uhalf_plane.convex : convex ℍ :=
begin
  rw convex_iff_forall_pos,
  intros x y hx hy a b ha hb hab,
  simp,
  exact calc (↑a * x + ↑b * y).im = (↑a * x).im + (↑b * y).im : by simp
    ... = a * x.im + b * y.im : by repeat {rw of_real_mul_im}
    ... > 0 + b * y.im : add_lt_add_of_lt_of_le (mul_pos ha hx) $ le_refl $ b * y.im
    ... > 0 + 0 : add_lt_add_of_le_of_lt (le_refl 0) $ mul_pos hb hy
    ... = 0 : by ring,
end

theorem uhalf_plane.is_path_connected : is_path_connected ℍ :=
convex.is_path_connected uhalf_plane.convex uhalf_plane.nonempty

@[simp] theorem uhalf_plane.is_connected : is_connected ℍ := (is_open.is_connected_iff_is_path_connected uhalf_plane.is_open).mp uhalf_plane.is_path_connected

instance uhalf_plane_connected : connected_space ℍ := is_connected_iff_connected_space.mp uhalf_plane.is_connected

instance uhalf_plane_charted : charted_space ℂ ℍ := topological_space.opens.charted_space ⟨ℍ, uhalf_plane.is_open⟩ 

instance uhalf_plane_riemann_surface : riemann_surface ℍ := topological_space.opens.riemann_surface ⟨ℍ, uhalf_plane.is_open⟩

--- The ℍ here is the coersed subtype ↥ℍ

end upper_half_plane

namespace rsphere

def prersphere := ℂ ⊕ ℂ

def rsphere_gluing : setoid prersphere :=
{
  r := λ a b, (a = b) ∨ ((a.get_left.iget * b.get_right.iget = 1) ∨ (a.get_right.iget * b.get_left.iget = 1)),
  iseqv :=
  begin
    split,
    exact λ x, or.intro_left _ rfl,
    split,
    {
      intros a b hab, cases hab,
      exact or.intro_left _ hab.symm,
      cases hab,
      { rw mul_comm at hab, exact or.intro_right _ (or.intro_right _ hab), },
      { rw mul_comm at hab, exact or.intro_right _ (or.intro_left _ hab), },
    },
    {
      intros a b c hab hbc,
      cases hab,
      {
        cases hbc,
        exact or.intro_left _ (hab.symm ▸ hbc),
        cases hbc,
        exact or.intro_right _ (or.intro_left _ $ hab.symm ▸ hbc),
        exact or.intro_right _ (or.intro_right _ $ hab.symm ▸ hbc),
      },
      {
        cases hab,
        {
          cases hbc,
          exact or.intro_right _ (or.intro_left _ $ hbc ▸ hab),
          cases hbc,
          {
            sorry,
          },
          {
            sorry,
          },
        },
        {
          sorry,
        },
      },
    },
  end,
}

def rsphere := quotient rsphere_gluing

instance : 

end rsphere

namespace extended_upper_half_plane

inductive uhalf_and_cusps
| of_complex (z : ℂ) (hz : 0 < z.im) : uhalf_and_cusps
| of_rational (r : ℚ) : uhalf_and_cusps
| of_infinity : uhalf_and_cusps

/-
  TODO:
  has_one has_zero has_add has_mul topological_sapce
-/

end extended_upper_half_plane

namespace ctorus

def clattice {ω : fin 2 → ℂ} (h : linear_independent ℝ ω) : set ℂ := 
{z : ℂ | ∃ (m n : ℤ), z = (m : ℂ) * (ω 0) + (n : ℂ) * (ω 1)}

theorem clattice.add_subgroup {ω : fin 2 → ℂ} (h : linear_independent ℝ ω) : 
  add_subgroup ℂ :=
{
  carrier := clattice h,
  zero_mem' :=
  --- Very bad proof here. WHY is this proof so slow?
  begin
    have : ∃ (m n : ℤ), (0 : ℂ) = (m : ℂ) * (ω 0) + (n : ℂ) * (ω 1) := begin
      repeat {use 0},
      rw [int.cast_zero, zero_mul, zero_mul, zero_add],
    end,
    exact this,
  end,
  add_mem' :=
  begin
    intros a b ha hb,
    rcases ha with ⟨na, ma, ha'⟩,
    rcases hb with ⟨nb, mb, hb'⟩,
    use (na + nb),
    use (ma + mb),
    exact calc a + b = ↑na * ω 0 + ↑ma * ω 1 + (↑nb * ω 0 + ↑mb * ω 1) : by rw [ha', hb']
      ... = (↑na + ↑nb) * ω 0 + (↑ma + ↑mb) * ω 1 : by ring
      ... = ↑(na + nb) * ω 0 + ↑(ma + mb) * ω 1 : by repeat {rw ← int.cast_add},
  end,
  neg_mem' :=
  begin
    intros z hz,
    rcases hz with ⟨n, m, hz'⟩,
    use (-n),
    use (-m),
    rw [hz', neg_add],
    simp only [int.cast_neg, neg_mul_eq_neg_mul],    
  end
}

def ctorus {ω : fin 2 → ℂ} (h : linear_independent ℝ ω) : Type* := 
quotient_add_group.quotient (clattice.add_subgroup h)

instance {ω : fin 2 → ℂ} (h : linear_independent ℝ ω) : topological_space (ctorus h) :=
quotient_add_group.quotient.topological_space _

/-
TODO: riemann_surface ctorus
-/

end ctorus