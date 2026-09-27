import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

private local instance ricciLowerMetricComparisonC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem metric_inner_le_exp_mul_of_ricci_lower_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) {a b δ : ℝ} (hab : a ≤ b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular) (x : M)
    (u : TangentSpace I x)
    (hRic : ∀ q ∈ Ioo a b, -δ * (S.base.metric q).inner x u u ≤ S.ricciAt q x (vec2 u u)) :
    (S.base.metric b).inner x u u ≤ Real.exp (2 * δ * (b - a)) * (S.base.metric a).inner x u u := by
  have hcont : ContinuousOn (fun s : ℝ => (S.base.metric s).inner x u u) D.carrier := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hS.smoothMetric.metricTensor_cont.eval_continuous
      (P := {s : ℝ // s ∈ D.carrier}) (τ := Subtype.val) (b := fun _ => x)
      continuous_subtype_val (fun p => p.2) continuous_const
      (v := fun i _ => vec2 u u i) (fun _ => continuous_const)
  have hexpcont : Continuous (fun s : ℝ => Real.exp (-(2 * δ * (s - a)))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const)).neg
  have hexpderiv (s : ℝ) :
      HasDerivAt (fun r : ℝ => Real.exp (-(2 * δ * (r - a))))
        (Real.exp (-(2 * δ * (s - a))) * (-(2 * δ))) s := by
    have h := (((hasDerivAt_id s).sub_const a).const_mul (2 * δ)).neg.exp
    simpa only [id_eq, mul_one, Pi.neg_apply] using h
  have hanti : AntitoneOn
      (fun s : ℝ => Real.exp (-(2 * δ * (s - a))) * (S.base.metric s).inner x u u)
      (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (f' := fun s => Real.exp (-(2 * δ * (s - a))) *
        (-(2 * δ) * (S.base.metric s).inner x u u - 2 * S.ricciAt s x (vec2 u u)))
      (hexpcont.continuousOn.mul (hcont.mono hslab))
    · intro s hs
      have hs' : s ∈ Ioo a b := by simpa only [interior_Icc] using hs
      have hmetric := metricDerivAt (I := I) S hS ⟨s, hreg hs'⟩ x u u
      change HasDerivAt (fun r : ℝ => (S.base.metric r).inner x u u)
        ((-2 : ℝ) * S.ricciAt s x (vec2 u u)) s at hmetric
      have hprod := (hexpderiv s).mul hmetric
      have hcoeff :
          (Real.exp (-(2 * δ * (s - a))) * (-(2 * δ))) * (S.base.metric s).inner x u u +
            Real.exp (-(2 * δ * (s - a))) * ((-2 : ℝ) * S.ricciAt s x (vec2 u u)) =
          Real.exp (-(2 * δ * (s - a))) *
            (-(2 * δ) * (S.base.metric s).inner x u u - 2 * S.ricciAt s x (vec2 u u)) := by
        ring
      rw [hcoeff] at hprod
      exact hprod.hasDerivWithinAt
    · intro s hs
      have hs' : s ∈ Ioo a b := by simpa only [interior_Icc] using hs
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hlower := hRic s hs'
      linarith
  have hbound := hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul] at hbound
  calc
    (S.base.metric b).inner x u u =
        Real.exp (2 * δ * (b - a)) *
          (Real.exp (-(2 * δ * (b - a))) * (S.base.metric b).inner x u u) := by
      rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (2 * δ * (b - a)) * (S.base.metric a).inner x u u :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le

end DifferentialGeometry.PDE.RicciFlow

end
