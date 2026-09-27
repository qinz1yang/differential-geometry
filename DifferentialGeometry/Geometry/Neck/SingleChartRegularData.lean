import DifferentialGeometry.Geometry.Neck.AxialSubmersion
import DifferentialGeometry.Geometry.Neck.RegularEndpoints

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Boundary DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Neck

theorem cylindricalChart.exists_regular_data_of_boundary_sections
    {E H W : Type} {F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [hI : HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [PreconnectedSpace W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]
    (C : cylindricalChart J (M := M))
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (htarget : ∀ w, ι w ∈ C.target) (t₀ t₁ τ c : ℝ) (hτ : τ = 1 ∨ τ = -1)
    (S₀ S₁ : Set W) (hboundary : I.boundary W = S₀ ∪ S₁)
    (hsection₀ : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t₀) ∈ C.domain)
    (hsection₁ : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t₁) ∈ C.domain)
    (himage₀ : ι '' S₀ = range (fun p ↦ (C.chart ⟨(p, t₀), hsection₀ p⟩ : M)))
    (himage₁ : ι '' S₁ = range (fun p ↦ (C.chart ⟨(p, t₁), hsection₁ p⟩ : M)))
    (r : ℝ) (hr : 0 < r)
    (hcollar : ∀ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) s,
      s ∈ Icc 0 r → (p, t₀ + τ * s) ∈ C.domain)
    (hinward : ∀ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) s (hs : s ∈ Icc 0 r),
      (C.chart ⟨(p, t₀ + τ * s), hcollar p s hs⟩ : M) ∈ range ι) :
    let u := fun w ↦ τ * C.axial (ι w) + c
    let a := τ * (Real.sqrt C.scale)⁻¹ * t₀ + c
    let b := τ * (Real.sqrt C.scale)⁻¹ * t₁ + c
    ∃ (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hab : a < b)
      (hbdy : ∀ w, I.IsBoundaryPoint w → u w = a ∨ u w = b),
      RegularIntervalDatum I u a b ∧
      u ⁻¹' ({a} : Set ℝ) = S₀ ∧ u ⁻¹' ({b} : Set ℝ) = S₁ ∧
      ∃ η : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, hI.boundaryI⟯
          boundaryLevel u a b hab.ne hu.continuous hbdy,
        ∀ p, ι (η p).1.1 = (C.chart ⟨(p, t₀), hsection₀ p⟩ : M) := by
  have hsurj (w : W) : Function.Surjective (mfderiv I J ι w) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (mfderiv I J ι w).toLinearMap)).mp (hinj w)
  have hτne : τ ≠ 0 := by rcases hτ with rfl | rfl <;> norm_num
  obtain ⟨hu, hreg⟩ := C.contMDiff_and_mvfderiv_affine_axial_ne_zero ι hι hsurj htarget τ c hτne
  refine ⟨hu, ?_⟩
  exact exists_regular_endpoints_of_extreme_neck_sections ι hι hemb hinj hdim
    C C t₀ t₁ τ τ c c hτ S₀ S₁ hboundary hsection₀ hsection₁ himage₀ himage₁
    (fun w ↦ τ * C.axial (ι w) + c) hu hreg
    (Eventually.of_forall (fun _ ↦ rfl)) (Eventually.of_forall (fun _ ↦ rfl)) r hr hcollar hinward

end DifferentialGeometry.Geometry.Neck
