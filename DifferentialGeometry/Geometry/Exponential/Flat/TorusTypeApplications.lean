import DifferentialGeometry.Geometry.Exponential.Flat.TorusType

/-!
# SF4(c): consumers

* Lattice translations are periods of the cover of a compact flat surface.
* A compact connected orientable smooth flat surface is homeomorphic to `ℝ/ℤ × ℝ/ℤ`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Connection Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The periodic cover of a compact flat surface is invariant under every lattice translation. -/
theorem exists_periodic_cover_add_zsmul_of_flat (hdim : Module.finrank ℝ E = 2) [CompactSpace M]
    [ConnectedSpace M] (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0) :
    ∃ (cov : E → M) (v₁ v₂ : E), Surjective cov ∧ LinearIndependent ℝ ![v₁, v₂] ∧
      ∀ (y : E) (m n : ℤ), cov (y + (m • v₁ + n • v₂)) = cov y := by
  obtain ⟨cov, v₁, v₂, -, -, hsurj, hli, hfib⟩ := exists_periodic_cover_of_flat hdim o g hEnorm hR
  refine ⟨cov, v₁, v₂, hsurj, hli, fun y m n => ((hfib y _).mpr ⟨m, n, ?_⟩).symm⟩
  abel

/-- A compact connected orientable smooth flat surface is homeomorphic to `ℝ/ℤ × ℝ/ℤ`. -/
theorem nonempty_homeomorph_addCircle_prod_of_flat (hdim : Module.finrank ℝ E = 2)
    [CompactSpace M] [ConnectedSpace M] (o : DifferentialGeometry.ManifoldOrientation I M 2)
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hR : ∀ x (X Y Z : TangentSpace I x), riemannOp (LeviCivita (I := I) g) x X Y Z = 0) :
    Nonempty (M ≃ₜ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  obtain ⟨Φ⟩ := nonempty_diffeomorph_addCircle_prod_of_flat hdim o g hEnorm hR
  exact ⟨Φ.toHomeomorph⟩

end DifferentialGeometry.Geometry.Riemannian.Exponential
