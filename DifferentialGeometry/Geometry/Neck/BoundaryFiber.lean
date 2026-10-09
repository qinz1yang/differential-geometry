import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Geometry.Boundary.ChartCrossSection

noncomputable section
open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Neck

open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem cylindricalChart.exists_boundaryLevel_sphere_parametrization
    {E H W F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [hI : HasSmoothBoundary E H I] [IsManifold I ∞ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]
    (C : cylindricalChart J (M := M))
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (t : ℝ) (hsection : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t) ∈ C.domain)
    (u : W → ℝ) (a b : ℝ) (hab : a ≠ b) (hu : Continuous u)
    (hboundary : ∀ w, I.IsBoundaryPoint w → u w = a ∨ u w = b)
    (himage : ι '' {w : W | I.IsBoundaryPoint w ∧ u w = a} =
      range (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦
        (C.chart ⟨(p, t), hsection p⟩ : M))) :
    ∃ η : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, hI.boundaryI⟯
        boundaryLevel u a b hab hu hboundary,
      ∀ p, ι (η p).1.1 = (C.chart ⟨(p, t), hsection p⟩ : M) :=
  exists_boundaryLevel_diffeomorph_of_product_chart ι hι hemb hinj hdim
    C.domain C.target C.chart t hsection u a b hab hu hboundary himage

end DifferentialGeometry.Geometry.Neck
