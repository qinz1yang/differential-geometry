import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.TopOrderPairingDecomposition

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem riemannC2_eq_kernel
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (qA qB : Fin 4 → Equiv.Perm (Fin 4))
    (hq : IsFramePairPartner qA qB) (s : ℝ) :
    riemannPalatiniDecompositionC2Family
        (I := I) (M := M) g T hδ hδZ qA qB s =
      s • curvatureDecompositionKernelCoeffField (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g
          (symmS (I := I) (M := M) g T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g
          (symmS (I := I) (M := M) g T))
        (qA 0) (qA 1) (qA 2) (qA 3) := by
  have h0 := curvatureDecompositionMonomialCoeffField_unitValue_pair_eq_symmS
    (I := I) (M := M) g
    (metricPerturbationPath (I := I) g T 0 hδ hδZ s) T (qA 0)
  have h1 := curvatureDecompositionMonomialCoeffField_unitValue_pair_eq_symmS
    (I := I) (M := M) g
    (metricPerturbationPath (I := I) g T 0 hδ hδZ s) T (qA 1)
  have h2 := curvatureDecompositionMonomialCoeffField_unitValue_pair_eq_symmS
    (I := I) (M := M) g
    (metricPerturbationPath (I := I) g T 0 hδ hδZ s) T (qA 2)
  have h3 := curvatureDecompositionMonomialCoeffField_unitValue_pair_eq_symmS
    (I := I) (M := M) g
    (metricPerturbationPath (I := I) g T 0 hδ hδZ s) T (qA 3)
  rw [riemannPalatiniDecompositionC2Family, hq 0, hq 1, hq 2, hq 3]
  simp only [Equiv.Perm.mul_def, curvatureDecompositionKernelCoeffField,
    curvatureActionKernelCoeffField]
  rw [← h0, ← h1, ← h2, ← h3]
  module

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
