import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

private local instance terminalMetricLowerBoundC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem metric_inner_lower_bound_of_ricci_upper_interior
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {a b eps : ℝ} (hab : a ≤ b) {U : Set M}
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hRic : ∀ s ∈ Ioo a b, ∀ x ∈ U, ∀ v : TangentSpace I x,
      S.ricciAt s x (vec2 v v) ≤ eps * (S.base.metric s).inner x v v)
    {x : M} (hx : x ∈ U) (v : TangentSpace I x) :
    Real.exp (-(2 * eps * (b - a))) * (S.base.metric a).inner x v v ≤
      (S.base.metric b).inner x v v := by
  have hcont : ContinuousOn (fun s : ℝ => (S.base.metric s).inner x v v)
      D.carrier := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hS.smoothMetric.metricTensor_cont.eval_continuous
      (P := {s : ℝ // s ∈ D.carrier}) (τ := Subtype.val) (b := fun _ => x)
      continuous_subtype_val (fun p => p.2) continuous_const
      (v := fun i _ => vec2 v v i) (fun _ => continuous_const)
  have hexpcont : Continuous (fun s : ℝ => Real.exp (2 * eps * (s - a))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
  have hexpderiv (s : ℝ) :
      HasDerivAt (fun r : ℝ => Real.exp (2 * eps * (r - a)))
        (Real.exp (2 * eps * (s - a)) * (2 * eps)) s := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id s).sub_const a).const_mul (2 * eps)).exp
  have hmono : MonotoneOn
      (fun s : ℝ => Real.exp (2 * eps * (s - a)) * (S.base.metric s).inner x v v)
      (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (f' := fun s => Real.exp (2 * eps * (s - a)) *
        (2 * eps * (S.base.metric s).inner x v v - 2 * S.ricciAt s x (vec2 v v)))
      (hexpcont.continuousOn.mul (hcont.mono hslab))
    · intro s hs
      have hs' : s ∈ Ioo a b := by simpa only [interior_Icc] using hs
      have hmetric := metricDerivAt (I := I) S hS ⟨s, hreg hs'⟩ x v v
      change HasDerivAt (fun u : ℝ => (S.base.metric u).inner x v v)
        ((-2 : ℝ) * S.ricciAt s x (vec2 v v)) s at hmetric
      have hprod := (hexpderiv s).mul hmetric
      have hcoeff :
          (Real.exp (2 * eps * (s - a)) * (2 * eps)) *
              (S.base.metric s).inner x v v +
            Real.exp (2 * eps * (s - a)) * ((-2 : ℝ) * S.ricciAt s x (vec2 v v)) =
          Real.exp (2 * eps * (s - a)) *
            (2 * eps * (S.base.metric s).inner x v v -
              2 * S.ricciAt s x (vec2 v v)) := by ring
      rw [hcoeff] at hprod
      exact hprod.hasDerivWithinAt
    · intro s hs
      have hs' : s ∈ Ioo a b := by simpa only [interior_Icc] using hs
      apply mul_nonneg (Real.exp_pos _).le
      have hupper := hRic s hs' x hx v
      linarith
  have hbound : (S.base.metric a).inner x v v ≤
      Real.exp (2 * eps * (b - a)) * (S.base.metric b).inner x v v := by
    simpa only [sub_self, mul_zero, Real.exp_zero, one_mul] using
      hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  calc
    Real.exp (-(2 * eps * (b - a))) * (S.base.metric a).inner x v v ≤
        Real.exp (-(2 * eps * (b - a))) *
          (Real.exp (2 * eps * (b - a)) * (S.base.metric b).inner x v v) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = (S.base.metric b).inner x v v := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [neg_add_cancel, Real.exp_zero, one_mul]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
