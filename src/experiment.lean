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
import analysis.calculus.formal_multilinear_series

open set complex classical filter asymptotics continuous_linear_map set metric is_open differentiable
open_locale topological_space classical nnreal asymptotics filter ennreal -- unit_interval

noncomputable theory
--variables (α : Type*) (p : α → Prop)

structure point (α : Type*) :=
mk :: (x : α) (y : α) (z : α)

structure rgb_val :=
(red : nat) (green : nat) (blue : nat)

class red_green_point (α : Type*) extends point α, rgb_val

def p   : point nat := {x := 10, y := 10, z := 20}
def color : rgb_val := {red := 1, green := 2, blue := 3}
def rgp : red_green_point ℕ :=
{..p, ..color}

example : rgp.x   = 10 := rfl
example : rgp.red = 1 := rfl

variables {m n : with_top ℕ} {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H]
(I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M]

lemma times_cont_diff_groupoid_lle1 (h : m ≤ n) :
  times_cont_diff_groupoid n I ≤ times_cont_diff_groupoid m I :=
begin
  rw [times_cont_diff_groupoid, times_cont_diff_groupoid],
  apply groupoid_of_pregroupoid_le,
  assume f s hfs,
  exact times_cont_diff_on.of_le hfs h
end

-- example (f : ℂ → ℂ) {s : set ℂ} (h : is_open s) : 
-- differentiable_on ℂ f s → (∀ (z : ℂ), z ∈ s → differentiable_at ℂ f z):=
-- begin
--   rw _root_.differentiable_on,
--   intros h z hz,
--   specialize h z hz,
--   rw differentiable_within_at at h,
--   rcases h with ⟨f', hf⟩, 
--   rw has_fderiv_within_at at hf,
--   rw _root_.differentiable_at,
--   use f',
--   rw has_fderiv_at,
--   rw has_fderiv_at_filter at hf,
--   sorry,
-- end