import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothEmbedInj
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PartialForcingFixedPoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckRealizedSolutionFamily
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

/-!
# Low-regularity dense Ricci--DeTurck nonlinearity

This file starts the dimension-three replacement for the supercritical
Sobolev nonlinearity construction.  Its first bridge is algebraic: the smooth
spectral embedding is injective, so the smooth Ricci--DeTurck nonlinearity is
independent of the chosen representative without any high-order estimate.
-/

noncomputable section

open Bundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M]

/-- The rank-two smooth spectral embedding used by the Ricci--DeTurck
nonlinearity is injective at every real order. -/
theorem smoothHs_inj (g : SmoothRiemannianMetric I M) (σ : ℝ) :
    Function.Injective (smoothCcToTensorHs (I := I) (M := M) g σ) := by
  intro S T hST
  apply ccToHs_injective (I := I) (M := M) g 2 σ
  apply tensorHs.ext
  funext i
  have hi := congrArg (fun u => u.coeff i) hST
  simpa only [ccTensorToHs_coeff, smoothCcToTensorHs_coeff] using hi

/-- Equal smooth spectral representatives give the same smooth
Ricci--DeTurck nonlinearity at every order.  No supercritical Sobolev
hypothesis is needed: injectivity first identifies the smooth tensors, and
metric realization is independent of the fibre-bound witness. -/
theorem smoothN_wd
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTT' : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') :
    deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T hδ_lt hδ =
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ' := by
  have hT : T = T' :=
    smoothHs_inj (I := I) (M := M) g₀ ((a : ℝ) + 2) hTT'
  subst T'
  have hg :
      tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ =
        tensorSectionRealizeMetric (I := I) g₀ T hδ'_lt hδ' := by
    apply smoothRiemannianMetric_ext_inner
    intro x v w
    rw [tensorSectionRealizeMetric_inner, tensorSectionRealizeMetric_inner]
  have hrem :
      deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ =
        deTurckSmoothRemainder (I := I) g₀ g_bg T hδ'_lt hδ' := by
    apply SmoothCcTensor.ext
    change
      (deTurckRHSSection (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection -
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection =
        (deTurckRHSSection (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ T hδ'_lt hδ')).toSection -
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection
    rw [hg]
  apply tensorHs.ext
  funext i
  rw [deTurckSmoothN_coeff, deTurckSmoothN_coeff, hrem]

/-- Smooth spectral rank-two tensors which remain in the lower `H2` state
ball, viewed as a subset of that state-ball subtype. -/
def smoothCore (g₀ : SmoothRiemannianMetric I M) (R : ℝ) :
    Set (lowerState (I := I) (M := M) g₀ 1 R) :=
  lowerCore
    (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)))
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)) R

/-- The smooth part of a positive lower `H2` state ball is dense in the
strong `H3` topology of the state subtype. -/
theorem smoothCore_dense (g₀ : SmoothRiemannianMetric I M)
    {R : ℝ} (hR : 0 < R) : Dense (smoothCore (I := I) (M := M) g₀ R) := by
  exact dense_lowerCore
    (smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2))
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)) hR

/-- The chosen smooth representative of a point in the smooth state core. -/
def coreRep (g₀ : SmoothRiemannianMetric I M) {R : ℝ}
    (x : smoothCore (I := I) (M := M) g₀ R) : SmoothCcTensor g₀ 0 2 :=
  Classical.choose x.property

theorem coreRep_spec (g₀ : SmoothRiemannianMetric I M) {R : ℝ}
    (x : smoothCore (I := I) (M := M) g₀ R) :
    smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) (coreRep g₀ x) =
      (x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) :=
  Classical.choose_spec x.property

/-- Symmetrizing a smooth representative of a state-core point preserves its
lower `H2` radius. -/
theorem coreSymm_h2 (g₀ : SmoothRiemannianMetric I M) {R : ℝ}
    (x : smoothCore (I := I) (M := M) g₀ R) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
      (ccTensor02Symm (I := I) (M := M) g₀ (coreRep g₀ x))‖ ≤ R := by
  have hsymm := norm_smoothCcToTensorHs_symmS_le
    (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) (coreRep g₀ x)
  have hincl := tensorHsInclusion_smoothCcToTensorHs
    (I := I) (M := M) g₀
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith) (coreRep g₀ x)
  have hxR :
      ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith) (x.1.1)‖ ≤ R :=
    x.1.2
  calc
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
        (ccTensor02Symm (I := I) (M := M) g₀ (coreRep g₀ x))‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
          (coreRep g₀ x)‖ := hsymm
    _ = ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
          (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
            (coreRep g₀ x))‖ := by
      rw [hincl]
    _ = ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith) (x.1.1)‖ := by
      rw [coreRep_spec]
    _ ≤ R := hxR

/-- The genuine smooth Ricci--DeTurck nonlinearity on the smooth part of a
lower state ball, with realization supplied exactly from that lower ball. -/
def coreN (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ} (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    smoothCore (I := I) (M := M) g₀ R →
      tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ) :=
  fun x => deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg (1 : ℕ)
    (ccTensor02Symm (I := I) (M := M) g₀ (coreRep g₀ x)) hδ
    (hreal _ (coreSymm_h2 (I := I) (M := M) g₀ x))

end DifferentialGeometry.PDE.RicciFlow

end
