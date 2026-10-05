import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleSeamSides

/-!
# FC42 normalization, packet N4 (a): the bad vertex set and the measure `μ`

Review 40 §1.4 and item 1 of its dispositions: the recursion of FC42 runs on
`μ(D) = sphereSeamCount + badVertexCount`, where a vertex is BAD if it is not a ball and owns a
partitioned face with a sphere model. Lane ASM-NRM (frozen text
`build-logs/scratch/ASM-NRM/Targets.lean`).

* `badVertexSet`: the finite set whose cardinality is the built `badVertexCount`
  (`card_badVertexSet`), with its membership criterion;
* `sphereMeasure`: `μ`; `sphereMeasure_eq_zero_iff`;
* `exists_mem_badVertexSet`: a positive bad count gives a bad vertex;
* `isBall_of_sphereMeasure_eq_zero`: the built terminal B5 at `μ = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

open Classical in
/-- **N4.** The bad vertices (review 40 §1.4): not a ball, owner of a partitioned sphere face. -/
def badVertexSet : Finset (Fin D.vertexCount) :=
  Finset.univ.filter fun k : Fin D.vertexCount =>
    ¬ (D.vertex k).IsBall ∧
      ∃ f, D.faceOwner f = k ∧ D.faceKind f = .partitioned ∧
        ∃ e : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl e

/-- The cardinality of the bad vertex set is the built `badVertexCount`. -/
theorem card_badVertexSet : D.badVertexSet.card = D.badVertexCount := by
  classical
  unfold badVertexSet badVertexCount
  congr 1

/-- **N4.** The induction measure `μ(D) = sphereSeamCount + badVertexCount`. -/
def sphereMeasure : ℕ :=
  D.sphereSeamCount + D.badVertexCount

section Iff

variable {D}

theorem mem_badVertexSet_iff {k : Fin D.vertexCount} :
    k ∈ D.badVertexSet ↔ ¬ (D.vertex k).IsBall ∧
      ∃ f, D.faceOwner f = k ∧ D.faceKind f = .partitioned ∧
        ∃ e : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl e := by
  classical
  unfold badVertexSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem sphereMeasure_eq_zero_iff :
    D.sphereMeasure = 0 ↔ D.sphereSeamCount = 0 ∧ D.badVertexCount = 0 := by
  unfold sphereMeasure
  omega

end Iff

/-- A positive bad count gives a bad vertex. -/
theorem exists_mem_badVertexSet (h : 0 < D.badVertexCount) : ∃ k, k ∈ D.badVertexSet := by
  rw [← D.card_badVertexSet] at h
  exact Finset.card_pos.mp h

/-- **N4, terminal binding**: at `μ = 0` every partitioned sphere face is owned by a ball (the built
terminal B5). -/
theorem isBall_of_sphereMeasure_eq_zero (hμ : D.sphereMeasure = 0) (f : Fin D.faceCount)
    (hf : D.faceKind f = .partitioned)
    (hS : ∃ e : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl e) :
    (D.vertex (D.faceOwner f)).IsBall :=
  D.partitionedSphereFace_ball_of_badVertexCount_eq_zero (sphereMeasure_eq_zero_iff.mp hμ).2 f hf hS

end DecompositionCertificate

end GC.GraphManifold.Assembly
