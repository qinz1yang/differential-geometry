import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapRecordsCompat_S58
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SliceKernelInputs_S53
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapScalarLowerAbs_S53
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapInitScalar_S53
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroCapScale_S44
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LateLinkedWitness_S48
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LapRJet_S52
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PreparedCapWindowUniform_S54

/-!
# CH12-S58, group 2: `hZC_S58` (hZC v2 verbatim)

Order of the argument (R3, D-R3-13): (0) scale facts from `CompatibleUpgradedCapRecords_S58` +
`recent_cutoff_smallness`: `neckRadius(s.time)⁻² ≤ C₀ q`, `1 ≤ a₀ q`, `s.time ≤ 2 t_j` -- these use
only the age window `≤ θ/q` on the record (no cap window, no `h ≳ ρ`); (1) the r-uniform kernel
(S54) at N = 2 gives `R ≥ q/4` at `y` (via `cap_scalar_lower`), at N = max 2 K the jets; (2) only then
`R(y) ≤ C0 ρ⁻²` (Z0) gives `q ≤ 4 C0 ρ⁻²`, i.e. `h_j ≳ ρ`, and the jets at scale `ρ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

private local instance sigmaCompactWindow_S58 (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

/-- `cap_scalar_lower_S53` with the target manifold of `L` in an arbitrary universe. -/
theorem cap_scalar_lower_S58 {M : Type} {N : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N] [T2Space N]
    (c : ℝ) (hc : 0 < c)
    (hlap : ∀ (N : Type) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
      [IsManifold ThreeModel ∞ N] [T2Space N]
      {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := N) D),
      IsSolutionOn (I := ThreeModel) S →
      ∀ (t : ℝ) (x : N), t ∈ D.carrier →
        |laplacianAt (I := ThreeModel) (flowG (I := ThreeModel) S) t (S.scalar t) x| ≤
          c * Real.sqrt (DifferentialGeometry.CheegerGromovCompactness.curvDerivNormSq
            (I := ThreeModel) 2 (S.base.metric t) x))
    (B T q : ℝ) (hT : 0 ≤ T) (hq : 0 < q)
    (S : SolutionOn (I := ThreeModel) (M := M) (RealTimeInterval.closed 0 T hT))
    (hS : IsSolutionOn (I := ThreeModel) S) (z : M)
    (hinit : 1 / 2 ≤ S.scalar 0 z)
    (hB : ∀ t ∈ Icc 0 T, CheegerGromovCompactness.curvDerivNormSq (I := ThreeModel) 2
        (S.base.metric t) z ≤ B)
    (L : SmoothRiemannianMetric ThreeModel N) (f : M → N)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) (hinj : Function.Injective f)
    (hfinal : ∀ y (v w : TangentSpace ThreeModel y), (S.base.metric T).inner y v w =
      q * L.inner (f y) (mfderiv ThreeModel ThreeModel f y v) (mfderiv ThreeModel ThreeModel f y w)) :
    c * Real.sqrt B * T ≤ 1 / 4 → q / 4 ≤ metricScalarAt L (f z) := by
  intro hsmall
  have hode := scalar_ge_of_lapR_S53 c B T hT S hS z
    (fun t ht => hlap M S hS t z ht) hB hc.le
  have hscal : S.scalar T z = metricScalarAt L (f z) / q := by
    change metricScalarAt (S.base.metric T) z = _
    exact scalar_eq_of_scaled_inner_local_S53 _ L f hf hinj hq hfinal z
  have h4 : 1 / 4 ≤ metricScalarAt L (f z) / q := by linarith
  have := (le_div_iff₀ hq).mp h4
  linarith

theorem one_le_transitionEnd_S58 : 1 ≤ StandardCap.transitionEnd := by
  unfold StandardCap.transitionEnd StandardCap.transitionStart
  have h2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : 3 / 2 < Real.pi / Real.sqrt 2 := by
    rw [lt_div_iff₀ h0]; nlinarith [Real.pi_gt_three]
  linarith

end GC.LongTime.Ch12
