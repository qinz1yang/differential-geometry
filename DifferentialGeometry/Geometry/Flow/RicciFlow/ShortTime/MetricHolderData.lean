import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.MetricWkpData
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.HolderNorm
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

/-!
# Uniform low-order Holder data for metric families

The uniform short-time theorem assumes only covariant bounds through order
three.  In the POU-weighted Euclidean chart model this is nevertheless enough
for a uniform `C^{2,1/2}` bound.  The reason is elementary: the third Frechet
derivative bounds the derivative of the second Frechet derivative, hence the
second derivative is globally Lipschitz.  The same second derivative is
globally bounded.  Interpolating those exponent-zero and exponent-one bounds
gives global exponent-`1/2` Holder control, not merely control on the compact
chart carrier.

This is the data-side producer for the dimension-generic parabolic Holder
route.  It does not use a high Sobolev norm and it does not use ellipticity.
-/

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff NNReal ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance iterFDerivTargetNormedAddCommGroup (m : ℕ) :
    NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin m => EuclN) ℝ) :=
  ContinuousMultilinearMap.normedAddCommGroup

private local instance iterFDerivTargetNormedSpace (m : ℕ) :
    NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin m => EuclN) ℝ) :=
  ContinuousMultilinearMap.normedSpace

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- A global bound on the next Frechet derivative makes an iterated Frechet
derivative Lipschitz. -/
private theorem iterFDeriv_lip
    {m : ℕ} {u : EuclN → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {C : ℝ} (hC : 0 ≤ C)
    (hnext : ∀ x : EuclN, ‖iteratedFDeriv ℝ (m + 1) u x‖ ≤ C) :
    LipschitzWith ⟨C, hC⟩ (iteratedFDeriv ℝ m u) := by
  let f : EuclN →
      ContinuousMultilinearMap ℝ (fun _ : Fin m => EuclN) ℝ :=
    iteratedFDeriv ℝ m u
  letI : NormedAddCommGroup
      (EuclN →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin m => EuclN) ℝ) :=
    @ContinuousLinearMap.toNormedAddCommGroup
      ℝ ℝ EuclN
      (ContinuousMultilinearMap ℝ (fun _ : Fin m => EuclN) ℝ)
      _ (iterFDerivTargetNormedAddCommGroup m) _ _ _
      (iterFDerivTargetNormedSpace m) (RingHom.id ℝ) _
  refine @lipschitzWith_of_nnnorm_fderiv_le
    ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin m => EuclN) ℝ)
    _ _ (iterFDerivTargetNormedAddCommGroup m)
    (iterFDerivTargetNormedSpace m) EuclN _ _ f ⟨C, hC⟩ ?_ ?_
  · exact hu.differentiable_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m))
  · intro x
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, NNReal.coe_mk]
    dsimp only [f]
    rw [norm_fderiv_iteratedFDeriv]
    exact hnext x

omit [BoundarylessManifold I M] in
/-- Uniform intrinsic metric bounds through order three give simultaneous
uniform `C^2` size and global exponent-`1/2` Holder control of the second Frechet
derivative of every active POU-weighted metric-difference component.

Both constants are chosen before the family index.  The Holder constant is
also independent of the active chart and of the two covariant component
indices. -/
theorem metricDiff_c2half
    {ι : Type*}
    (gBase : SmoothRiemannianMetric I M)
    (gSeq : ι → SmoothRiemannianMetric I M)
    (B : ℝ)
    (hbdd : ∀ k : ι, ∀ q : ℕ, q ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ q (gSeq k) gBase B) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ Cα : ℝ≥0,
      ∀ (α : M), α ∈ chartAtlasPOU_finset (I := I) (M := M) →
        ∀ (k : ι) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)),
          (∀ j : ℕ, j ≤ 2 → ∀ y : EuclN,
            ‖iteratedFDeriv ℝ j
              (tensorChartComp (I := I) (M := M) gBase 0 2
                (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k))
                α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) y‖ ≤ C₀) ∧
          HolderWith Cα (1 / 2 : ℝ≥0)
            (iteratedFDeriv ℝ 2
              (tensorChartComp (I := I) (M := M) gBase 0 2
                (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k))
                α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)) := by
  classical
  obtain ⟨Cjet, hCjet, hjet⟩ :=
    metricDiff_comp_jet (I := I) (M := M) gBase gSeq B hbdd
  let Cα : ℝ≥0 := 2 * ⟨Cjet, hCjet⟩
  refine ⟨Cjet, hCjet, Cα, ?_⟩
  intro α _hα k Jdx
  let u : EuclN → ℝ :=
    tensorChartComp (I := I) (M := M) gBase 0 2
      (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k))
      α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    dsimp only [u]
    exact tensorChartComp_contDiff (I := I) (M := M) gBase 0 2
      (metricDifferenceCcTensor (I := I) (M := M) gBase (gSeq k))
      α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx
  have hlip : LipschitzWith ⟨Cjet, hCjet⟩ (iteratedFDeriv ℝ 2 u) := by
    refine iterFDeriv_lip hu hCjet ?_
    intro y
    simpa only [u] using hjet α k Jdx 3 (by omega) y
  refine ⟨?_, ?_⟩
  · intro j hj y
    simpa only [u] using hjet α k Jdx j (hj.trans (by omega)) y
  · have h2 : ∀ y : EuclN, ‖iteratedFDeriv ℝ 2 u y‖ ≤ Cjet := by
      intro y
      simpa only [u] using hjet α k Jdx 2 (by omega) y
    have hzero : HolderWith Cα 0 (iteratedFDeriv ℝ 2 u) := by
      intro x y
      simp only [NNReal.coe_zero, ENNReal.rpow_zero, mul_one, edist_dist,
        ENNReal.ofReal_le_coe]
      rw [dist_eq_norm]
      calc
        ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖
            ≤ ‖iteratedFDeriv ℝ 2 u x‖ + ‖iteratedFDeriv ℝ 2 u y‖ :=
          norm_sub_le _ _
        _ ≤ Cjet + Cjet := add_le_add (h2 x) (h2 y)
        _ = (Cα : ℝ) := by simp [Cα]; ring
    have hmono : ⟨Cjet, hCjet⟩ ≤ Cα := by
      dsimp only [Cα]
      nlinarith
    have hone : HolderWith Cα 1 (iteratedFDeriv ℝ 2 u) :=
      hlip.holderWith.mono hmono
    have hhalf0 : (0 : ℝ≥0) ≤ 1 / 2 := by norm_num
    have hhalf1 : (1 / 2 : ℝ≥0) ≤ 1 := by norm_num
    simpa using hzero.of_le_of_le hone hhalf0 hhalf1

end DifferentialGeometry.PDE.RicciFlow
