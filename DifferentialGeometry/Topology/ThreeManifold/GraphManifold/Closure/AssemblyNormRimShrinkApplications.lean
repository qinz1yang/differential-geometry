import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormRimShrink
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleSeamSidesApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SphereCertificate

/-!
# Consumers of packets N1 and N4 (a): support preparation and the measure

* `exists_shrinkRims_avoiding_interior`: the form used by the internal sphere operations N2 / N3 —
  a compact set of ambient interior points of a vertex image (inside `W.interior`) avoids every rim
  chart target of a shrunk certificate with the same measure, the same cornered region, and the
  rim-product clause transported (N1 main + the rim-circle lemma).
* `nonempty_cyclePartition_shrinkRims`: the shrunk certificate feeds lane ASM-CYC3's cycle partition
  (H2) verbatim — its statements are for an arbitrary certificate; at `μ = 0` the shrink keeps
  `μ = 0`.
* The concrete inhabitant `standardSphereCertificate` (two hemisphere balls of `S³`, one sphere
  seam): no bad vertex, `μ = 1`, and the same for any shrink of it.
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

/-- **N1 for the internal sphere operations.** A compact set of ambient interior points of a vertex
image inside `W.interior` avoids every rim chart target of some shrink of `D`, which has the same
measure and cornered region and inherits the rim-product clause. -/
theorem exists_shrinkRims_avoiding_interior {k : Fin D.vertexCount} {K : Set W.Carrier}
    (hKc : IsCompact K) (hK : K ⊆ interior (D.vertex k).image ∩ W.interior) :
    ∃ (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2),
      (∀ h b, Disjoint ((D.shrinkRims ε hε hε1).rimChart h b).target K) ∧
      (D.shrinkRims ε hε hε1).sphereMeasure = D.sphereMeasure ∧
      (D.shrinkRims ε hε hε1).circ.region = D.circ.region ∧
      (D.RimProduct → (D.shrinkRims ε hε hε1).RimProduct) := by
  obtain ⟨ε, hε, hε1, hdisj⟩ :=
    D.exists_shrinkRims_disjoint hKc fun h b => D.disjoint_rimCircle_of_subset_interior hK h b
  exact ⟨ε, hε, hε1, hdisj, D.sphereMeasure_shrinkRims ε hε hε1, D.region_shrinkRims ε hε hε1,
    fun hD => RimProduct.shrinkRims ε hε hε1 hD⟩

/-- **The shrunk certificate feeds the cycle partition** (ASM-CYC3, H2) when `μ = 0`. -/
theorem nonempty_cyclePartition_shrinkRims (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hμ : D.sphereMeasure = 0) : Nonempty (D.shrinkRims ε hε hε1).CyclePartition := by
  have h0 := sphereMeasure_eq_zero_iff.mp ((D.sphereMeasure_shrinkRims ε hε hε1).trans hμ)
  exact (D.shrinkRims ε hε hε1).nonempty_cyclePartition_of_badVertexCount_eq_zero h0.1 h0.2

end DecompositionCertificate

/-! ## The concrete inhabitant -/

theorem badVertexSet_standardSphereCertificate :
    standardSphereCertificate.{u}.badVertexSet = ∅ := by
  ext k
  simp only [Finset.notMem_empty, iff_false]
  intro hk
  apply (DecompositionCertificate.mem_badVertexSet_iff.mp hk).1
  fin_cases k
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem sphereMeasure_standardSphereCertificate :
    standardSphereCertificate.{u}.sphereMeasure = 1 := by
  rw [DecompositionCertificate.sphereMeasure, ← DecompositionCertificate.card_badVertexSet,
    badVertexSet_standardSphereCertificate]
  rfl

theorem sphereMeasure_shrinkRims_standardSphereCertificate (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    (standardSphereCertificate.{u}.shrinkRims ε hε hε1).sphereMeasure = 1 :=
  (standardSphereCertificate.{u}.sphereMeasure_shrinkRims ε hε hε1).trans
    sphereMeasure_standardSphereCertificate

end GC.GraphManifold.Assembly
