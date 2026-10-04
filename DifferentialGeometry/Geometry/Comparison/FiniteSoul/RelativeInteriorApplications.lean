import DifferentialGeometry.Geometry.Comparison.FiniteSoul.RelativeInteriorSpec

/-!
# Consumers of S3-SLICE (lane CMS3-SLICE, group G3)

* the frozen interface `maxSliceLocusOfOrder_spec` VERBATIM (with its hypothesis `IsClosed C`), as an
  `example` applying the proved form;
* `isClosed_relBoundaryOfOrder`: the relative boundary of a closed totally convex set is closed (input
  of the REL kernel: the distance to the relative boundary);
* `closure_maxSliceLocusOfOrder`: the relative interior is dense, `closure relint = closure C`;
* `maxSliceDimOfOrder_eq_finrank_iff`: full relative dimension iff nonempty interior.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
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

/-- The frozen interface S3-SLICE, verbatim (`build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean`
§5), from the proved form (which does not need `IsClosed C`). -/
example
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (_hCcl : IsClosed C) (hCne : C.Nonempty) (hconv : IsTotallyConvexFinite g C) :
    (maxSliceLocusOfOrder I (r : ℕ∞ω) C).Nonempty ∧
      maxSliceDimOfOrder I (r : ℕ∞ω) C ≤ Module.finrank ℝ E ∧
      IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) C)
        (maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      IsTotallyGeodesicFinite g (maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      C ⊆ closure (maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      (∀ x ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        C ∩ U ⊆ maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      (∀ (p : TangentBundle I M) (a b : ℝ), (∀ t ∈ Icc a b, (g.geodesicFlow p t).proj ∈ C) →
        ∀ s ∈ Icc a b, (g.geodesicFlow p s).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C →
          ∀ t ∈ Ioo a b, (g.geodesicFlow p t).proj ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) ∧
      (maxSliceDimOfOrder I (r : ℕ∞ω) C = Module.finrank ℝ E →
        maxSliceLocusOfOrder I (r : ℕ∞ω) C = interior C) :=
  maxSliceLocusOfOrder_spec g hr hnorm hCne hconv

/-- The relative boundary of a closed totally convex set is closed. -/
theorem isClosed_relBoundaryOfOrder
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCcl : IsClosed C) (hconv : IsTotallyConvexFinite g C) :
    IsClosed (relBoundaryOfOrder I (r : ℕ∞ω) C) := by
  obtain ⟨O, hO, hCO⟩ := exists_isOpen_inter_eq_maxSliceLocusOfOrder g hr hnorm hconv
  have heq : relBoundaryOfOrder I (r : ℕ∞ω) C = C ∩ Oᶜ := by
    ext x
    constructor
    · rintro ⟨hxC, hxN⟩
      refine ⟨hxC, fun hxO => hxN ?_⟩
      rw [← hCO]
      exact ⟨hxC, hxO⟩
    · rintro ⟨hxC, hxO⟩
      refine ⟨hxC, fun hxN => hxO ?_⟩
      rw [← hCO] at hxN
      exact hxN.2
  rw [heq]
  exact hCcl.inter hO.isClosed_compl

/-- The relative interior is dense in `C`. -/
theorem closure_maxSliceLocusOfOrder
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCne : C.Nonempty) (hconv : IsTotallyConvexFinite g C) :
    closure (maxSliceLocusOfOrder I (r : ℕ∞ω) C) = closure C :=
  Subset.antisymm (closure_mono maxSliceLocusOfOrder_subset)
    (closure_minimal (subset_closure_maxSliceLocusOfOrder g hr hnorm hCne hconv) isClosed_closure)

/-- Full relative dimension iff nonempty interior. -/
theorem maxSliceDimOfOrder_eq_finrank_iff
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hCne : C.Nonempty) (hconv : IsTotallyConvexFinite g C) :
    maxSliceDimOfOrder I (r : ℕ∞ω) C = Module.finrank ℝ E ↔ (interior C).Nonempty := by
  constructor
  · intro hd
    rw [← maxSliceLocusOfOrder_eq_interior g hr hnorm hconv hd]
    exact maxSliceLocusOfOrder_nonempty hCne
  · intro hint
    exact le_antisymm (maxSliceDimOfOrder_le C)
      (le_maxSliceDimOfOrder ⟨interior C, hint, interior_subset,
        IsEmbeddedSliceOfOrder.of_isOpen isOpen_interior⟩)

end DifferentialGeometry.Geometry.FiniteSoul
