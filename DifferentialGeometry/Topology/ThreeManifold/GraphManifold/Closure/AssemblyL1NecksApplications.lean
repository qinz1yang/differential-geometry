import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Necks

/-!
# Chapter-14 assembly, item L1, G3b: consumers of the necks (T1′)

Lane ASM-L1e3, group G2 (consumer of `AssemblyL1NecksRim` and `AssemblyL1Necks`).

* `BallHandleCycle.exists_necks_centre_mem`: under the rim-product clause, the centre of every
  neck lies on the end disk where the handle meets the ball, and the closed neck boxes have
  pairwise disjoint images.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The centres of the necks of T1′ lie in ball ∩ handle; the closed neck boxes have pairwise
disjoint images. -/
theorem BallHandleCycle.exists_necks_centre_mem {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (hprod : C.RimProduct) (hint : ∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ N : Fin C.len → Bool → PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
        (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞,
      (∀ k b, N k b 0 ∈ range (C.ball (rimBall C.len k b)).map ∩ range (C.handle k).map) ∧
      ∀ k b k' b', (k, b) ≠ (k', b') →
        Disjoint (N k b '' closedNeckDomain ε) (N k' b' '' closedNeckDomain ε) := by
  obtain ⟨ε, hε, -, N, hsrc, hdisj, hball, hhandle, -⟩ := C.exists_necks_of_rimProduct hprod hint
  have hbox : (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ closedNeckDomain ε := by
    refine ⟨?_, ?_⟩
    · change ‖(0 : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 + 2 * ε
      rw [norm_zero]
      linarith
    · change |(0 : ℝ)| ≤ 2 * ε
      rw [abs_zero]
      linarith
  have himg : ∀ k b, N k b '' closedNeckDomain ε ⊆ (N k b).target := fun k b =>
    image_subset_iff.mpr fun q hq => (N k b).map_source (hsrc k b hq)
  refine ⟨ε, hε, N, fun k b => ⟨(hball k b (hsrc k b hbox)).mpr le_rfl,
    (hhandle k b (hsrc k b hbox)).mpr ⟨le_rfl, ?_⟩⟩, fun k b k' b' hne =>
      (hdisj k b k' b' hne).mono (himg k b) (himg k' b')⟩
  change ‖(0 : EuclideanSpace ℝ (Fin 2))‖ ≤ 1
  rw [norm_zero]
  exact zero_le_one

end GC.GraphManifold.Assembly
