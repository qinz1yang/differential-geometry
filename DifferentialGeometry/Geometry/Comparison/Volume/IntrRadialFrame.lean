import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound

set_option linter.unusedSectionVars false

/-!
# Parallel frame along the intrinsic radial geodesic, at every scale

`exists_radialFrame` (`RadialGronwall.lean`) produces a parallel orthonormal
frame along the chart-based `radialCurve`, but its `C²` input is only
satisfiable below `expMapC2Radius` — the analytic cap of the Route B frontier.
This file provides the un-capped replacement along the *intrinsic* geodesic:
`intrinsicGeodesic` is globally `C^∞` in time
(`intrinsicGeodesic_contMDiff`, `Exponential/IntrinsicSmooth.lean`), so the
generic parallel-transport engine `exists_parallel_frame` (`PerpFrame.lean`)
applies on `[0, b]` for **every** `b > 0` and **every** launch vector — no
smallness hypothesis.

## Main result

* `exists_intrFrame` — a full parallel `g`-orthonormal frame along
  `intrinsicGeodesic g hEnorm p v` on `[0, b]`, in the same four-clause shape
  as `exists_radialFrame` (card bridge, chart-representation
  differentiability, parallelism, orthonormality).
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [T2Space (TangentBundle I M)]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **Parallel orthonormal frame along the intrinsic radial geodesic, at every
scale.**  Un-capped analogue of `exists_radialFrame`: the interval `[0, b]` and
the launch vector `v` are arbitrary. -/
lemma exists_intrFrame
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) {b : ℝ} (hb : 0 < b) :
    ∃ F : Fin (Module.finrank ℝ
        (TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p v 0))) →
        ∀ t : ℝ, TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p v t),
      (∀ t ∈ Icc (0 : ℝ) b,
        Fintype.card (Fin (Module.finrank ℝ
            (TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p v 0)))) =
          Module.finrank ℝ
            (TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p v t))) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        DifferentiableAt ℝ
          (chartRepAt (I := I) (intrinsicGeodesic (I := I) g hEnorm p v)
            (F i) t) t) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) b,
        covDerivAlong (I := I) g (intrinsicGeodesic (I := I) g hEnorm p v)
          (F i) t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) b, ∀ i j,
        g.inner (intrinsicGeodesic (I := I) g hEnorm p v t) (F i t) (F j t) =
          if i = j then (1 : ℝ) else 0) := by
  classical
  have hsm : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞)
      (intrinsicGeodesic (I := I) g hEnorm p v) :=
    (intrinsicGeodesic_contMDiff (I := I) g hEnorm p v).of_le
      (by exact_mod_cast le_top)
  obtain ⟨basis, hON0⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis
      (I := I) g (intrinsicGeodesic (I := I) g hEnorm p v 0)
  obtain ⟨F, _hF0, hFdiff, hFpar, hFON⟩ :=
    exists_parallel_frame (I := I) g (intrinsicGeodesic (I := I) g hEnorm p v)
      (N := 2) (by norm_num) hsm hb basis hON0
  refine ⟨F, ?_, hFdiff, hFpar, hFON⟩
  intro t ht
  simp only [Fintype.card_fin]
  rfl

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
