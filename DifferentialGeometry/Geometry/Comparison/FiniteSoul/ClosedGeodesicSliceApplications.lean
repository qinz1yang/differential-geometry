import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicSlice
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicCircle

/-!
# Consumers of BASE-1a (lane CMS3-SLICE, group G4)

* the frozen interface `exists_closedGeodesic_of_slice_dim_one` VERBATIM (with its instance
  `[NeZero (Module.finrank ℝ E)]`), as an `example` applying the proved form;
* `exists_homeomorph_addCircle_of_slice_dim_one`: a compact connected one-dimensional totally geodesic
  `C^r` slice is homeomorphic to a circle `AddCircle ℓ`, through the closed geodesic (with CMS-S's SA1).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- The frozen interface BASE-1a, verbatim (`FiniteSoulThreeInterfaces.lean` §9). -/
example [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hconn : IsConnected S)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) 1 S) (htg : IsTotallyGeodesicFinite g S) :
    ∃ (p : TangentBundle I M) (ℓ : ℝ), 0 < ℓ ∧ g.inner p.proj p.snd p.snd = 1 ∧
      g.geodesicFlow p ℓ = p ∧ InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ) ∧
      S = range (fun t => (g.geodesicFlow p t).proj) :=
  exists_closedGeodesic_of_slice_dim_one g hr hnorm hSc hconn hS htg

/-- **A compact connected one-dimensional totally geodesic slice is a circle.** -/
theorem exists_homeomorph_addCircle_of_slice_dim_one
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hconn : IsConnected S)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) 1 S) (htg : IsTotallyGeodesicFinite g S) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ Nonempty (AddCircle ℓ ≃ₜ S) := by
  obtain ⟨p, ℓ, hℓ, hp, hper, hinj, hrange⟩ :=
    exists_closedGeodesic_of_slice_dim_one g hr hnorm hSc hconn hS htg
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  obtain ⟨e, -⟩ := exists_homeomorph_addCircle_range_geodesicFlow g hr hnorm hp hper hinj
  exact ⟨ℓ, hℓ, ⟨e.trans (Homeomorph.setCongr hrange.symm)⟩⟩

end DifferentialGeometry.Geometry.FiniteSoul
