import DifferentialGeometry.Topology.Handle.RoundedHalfBallDisk
import DifferentialGeometry.Topology.Handle.BallPairComparison

open Set Metric
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable (m : ℕ)

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨by simp⟩

theorem exists_diffeomorph_roundedHalfBall_comparison
    (c : PartialDiffeomorph (𝓡 ((m + 1) + 1)) (𝓡 ((m + 1) + 1))
      (EuclideanSpace ℝ (Fin ((m + 1) + 1))) (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ∞)
    (D : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin ((m + 1) + 1))))
    (v : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    {B : Set (EuclideanSpace ℝ (Fin ((m + 1) + 1)))} {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / 2)
    (hD : D '' closedBall 0 1 = B)
    (hc : c.toOpenPartialHomeomorph.IsImage
      {z | DifferentialGeometry.Topology.Handle.roundedHalfBallFunction (m + 1) ε 0 z ≤ 0} B)
    (hK : (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)).symm ''
      (closedBall 0 1 ×ˢ {(0 : ℝ)}) ⊆ c.source)
    (hstrip : {p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 × (ℝ × ℝ) |
      0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆
      ((c.symm.toOpenPartialHomeomorph.trans
        (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)).toHomeomorph.toOpenPartialHomeomorph).trans
          (OpenPartialHomeomorph.halfBallCorner 1 v)).target) :
    ∃ Q : (EuclideanSpace ℝ (Fin ((m + 1) + 1))) ≃ₘ[ℝ] (EuclideanSpace ℝ (Fin ((m + 1) + 1))),
      Q '' {z | DifferentialGeometry.Topology.Handle.roundedHalfBallFunction (m + 1) ε 0 z ≤ 0} = B ∧
      ∃ V, IsOpen V ∧
        (fun x : EuclideanSpace ℝ (Fin (m + 1)) => (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)).symm
          (DifferentialGeometry.Topology.Handle.halfBallRounding 1 ε (x, 0))) '' closedBall 0 1 ⊆ V ∧
        V ⊆ c.source ∧ EqOn Q c V := by
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)
  let e := OpenPartialHomeomorph.halfBallCorner 1 v
  let d := (c.symm.toOpenPartialHomeomorph.trans L.toHomeomorph.toOpenPartialHomeomorph).trans e
  have hsource (x : EuclideanSpace ℝ (Fin (m + 1))) (hx : x ∈ closedBall 0 1) :
      L.symm (DifferentialGeometry.Topology.Handle.halfBallRounding 1 ε (x, 0)) ∈ c.source := by
    have hraw : L.symm (x, 0) ∈ c.source := hK ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
    by_cases hx0 : x = 0
    · subst x
      simpa only [DifferentialGeometry.Topology.Handle.halfBallRounding_zero_fst] using hraw
    · have hxs : (x, (0 : ℝ)) ∈ e.source := hx0
      have hdt : e (x, 0) ∈ d.target := by
        refine ⟨e.map_source hxs, ?_⟩
        change (True ∧ L.symm (e.symm (e (x, 0))) ∈ c.source)
        rwa [e.left_inv hxs, true_and]
      have hq : 0 ≤ (e (x, 0)).2.1 ∧ 0 ≤ (e (x, 0)).2.2 := by
        have hn := mem_closedBall_zero_iff.mp hx
        change 0 ≤ 1 ^ 2 - ‖x‖ ^ 2 - 0 ^ 2 ∧ 0 ≤ (0 : ℝ)
        exact ⟨by nlinarith [norm_nonneg x], le_rfl⟩
      have hnew := d.smoothAbsQuadrantMap_coordinate_mem_target hε hstrip hdt hq
      have hnewsource : L.symm (e.symm ((e (x, 0)).1,
          Real.smoothAbs.quadrantMap ε (e (x, 0)).2)) ∈ c.source := hnew.2.2
      have heq := DifferentialGeometry.Topology.Handle.halfBallRounding_halfBallCorner_symm
        1 ε v (e.map_source hxs)
      change DifferentialGeometry.Topology.Handle.halfBallRounding 1 ε (e.symm (e (x, 0))) =
        e.symm ((e (x, 0)).1, Real.smoothAbs.quadrantMap ε (e (x, 0)).2) at heq
      rw [e.left_inv hxs] at heq
      rwa [← heq] at hnewsource
  obtain ⟨D₀, ψ, hD₀, _, hψs, hψ⟩ :=
    DifferentialGeometry.Topology.Handle.exists_partialDiffeomorph_roundedHalfBall_disk (m + 1) hε hsmall
  obtain ⟨Q, hQ, V, hV, hKV, hVc, hQV⟩ :=
    c.exists_diffeomorph_eqOn_neighborhood_of_boundary_disk m D₀ D hD₀ hD hc ψ hψs (by
      intro x hx
      rw [hψ x (hψs hx)]
      exact hsource x hx)
  refine ⟨Q, hQ, V, hV, ?_, hVc, hQV⟩
  rintro z ⟨x, hx, rfl⟩
  apply hKV
  refine ⟨(ψ x).val, ⟨ψ x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
  exact hψ x (hψs hx)

end PartialDiffeomorph
