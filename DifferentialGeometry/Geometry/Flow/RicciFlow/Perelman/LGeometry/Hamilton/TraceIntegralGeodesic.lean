import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.TraceIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.Basic
set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem integral_lHamSq_mul_eq_of_geodesic
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (alpha : ℝ → M) {a l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hgeo : IsLRegularizedGeodesicOn S T alpha (Ioo l r))
    (hcont : ContinuousOn (lRegularizedLagrangian S T alpha) (Icc l r))
    (hHam : IntervalIntegrable (lHamSq S T alpha) volume l r) :
    4 * (∫ s in l..r, ((s - a) / s) ^ 2 * lHamSq S T alpha s) =
      (∫ s in l..r, (1 - a ^ 2 / s ^ 2) * lRegularizedLagrangian S T alpha s) -
        (((r - a) ^ 2 / r) * lRegularizedLagrangian S T alpha r -
          ((l - a) ^ 2 / l) * lRegularizedLagrangian S T alpha l) := by
  let L := lRegularizedLagrangian S T alpha
  let q : ℝ → ℝ := fun s => ((s - a) / s) ^ 2
  have hnonzero (s : ℝ) (hs : s ∈ Icc l r) : s ≠ 0 := (hl.trans_le hs.1).ne'
  have hL : ContinuousOn L (Icc l r) := hcont
  have hq : ContinuousOn q (Icc l r) :=
    ((continuousOn_id.sub continuousOn_const).div continuousOn_id hnonzero).pow 2
  have hc : ContinuousOn (fun s : ℝ => 1 - a ^ 2 / s ^ 2) (Icc l r) :=
    continuousOn_const.sub (continuousOn_const.div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero 2 (hnonzero s hs)))
  have hLagInt : IntervalIntegrable L volume l r := hL.intervalIntegrable_of_Icc hlr
  have hweightedLag : IntervalIntegrable (fun s => (1 - a ^ 2 / s ^ 2) * L s)
      volume l r :=
    hLagInt.continuousOn_mul (by simpa only [uIcc_of_le hlr] using hc)
  have hweightedHam : IntervalIntegrable (fun s => q s * lHamSq S T alpha s)
      volume l r :=
    hHam.continuousOn_mul (by simpa only [uIcc_of_le hlr] using hq)
  have hcurve : IsLRegularizedCurveOn S T alpha (Ioo l r) (alpha 0)
      ((1 / 2 : ℝ) • lVelocity (I := I) alpha 0) := by
    refine ⟨rfl, ?_, hgeo⟩
    rw [two_smul, ← add_smul]
    norm_num
  have hderiv (s : ℝ) (hs : s ∈ Ioo l r) :
      HasDerivAt (fun t => q t * (t * L t))
        ((1 - a ^ 2 / s ^ 2) * L s - 4 * (q s * lHamSq S T alpha s)) s := by
    have hs0 := hnonzero s (Ioo_subset_Icc_self hs)
    have hqd : HasDerivAt q (2 * ((s - a) / s) * (a / s ^ 2)) s := by
      have hh := (((hasDerivAt_id s).sub_const a).div (hasDerivAt_id s) hs0).pow 2
      change HasDerivAt q _ s at hh
      apply hh.congr_deriv
      simp only [Pi.div_apply, id_eq, mul_one, one_mul]
      ring
    have he := lLagMul_deriv S hS T hcurve hs
    have hp := hqd.mul he
    apply hp.congr_deriv
    dsimp only [L, q]
    field_simp [hs0]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr
    (hq.mul (continuousOn_id.mul hL)) hderiv
    (hweightedLag.sub (hweightedHam.const_mul 4))
  rw [intervalIntegral.integral_sub hweightedLag (hweightedHam.const_mul 4),
    intervalIntegral.integral_const_mul] at hFTC
  have hend (s : ℝ) (hs0 : s ≠ 0) : q s * (s * L s) = ((s - a) ^ 2 / s) * L s := by
    dsimp only [q]
    field_simp [hs0]
  change (∫ s in l..r, (1 - a ^ 2 / s ^ 2) * L s) -
    4 * (∫ s in l..r, q s * lHamSq S T alpha s) = q r * (r * L r) - q l * (l * L l) at hFTC
  rw [hend r (hnonzero r ⟨hlr, le_rfl⟩), hend l hl.ne'] at hFTC
  change 4 * (∫ s in l..r, q s * lHamSq S T alpha s) = _
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman
