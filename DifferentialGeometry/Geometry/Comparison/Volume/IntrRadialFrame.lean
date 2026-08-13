import DifferentialGeometry.Geometry.Exponential.IntrinsicSmooth
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
open DifferentialGeometry.Geometry.Curvature

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
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [T2Space (TangentBundle I M)]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [T2Space (TangentBundle I M)]
  [ConnectedSpace M] in
lemma exists_intrFrame
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
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
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis
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
