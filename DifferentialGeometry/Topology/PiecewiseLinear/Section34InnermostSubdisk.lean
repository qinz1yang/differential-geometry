import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnermostDisk
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_disk_in_disk_sdiff_boundary {S D J : Set E}
    (hS : IsPLSphere 2 S) {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDS : D ⊆ S)
    (hJ : IsPLSphere 1 J) (hJD : J ⊆ D \ r '' stdSimplexBoundary 2) :
    ∃ (Q : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q ∧
      Q ⊆ D \ r '' stdSimplexBoundary 2 ∧ q '' stdSimplexBoundary 2 = J := by
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hbdD : r '' stdSimplexBoundary 2 ⊆ D := by
    rw [← hr.image_eq]
    exact image_mono fun _ hx => hx.1
  have hbdJ : Disjoint (r '' stdSimplexBoundary 2) J :=
    disjoint_left.mpr fun x hx hy => (hJD hy).2 hx
  obtain ⟨Q, q, hq, hQS, hdis, hqJ⟩ :=
    hS.exists_isPLBall_with_boundary_disjoint_of_isPreconnected
      hr.isPLSphere_image_stdSimplexBoundary.isConnected.isPreconnected
      (hbdD.trans hDS) hJ ((hJD.trans sdiff_subset).trans hDS) hbdJ
  have hQ : IsPLBall 2 Q := ⟨q, hq⟩
  have hJQ : J ⊆ Q := by
    rw [← hqJ, ← hq.image_eq]
    exact image_mono fun _ hx => hx.1
  have hcover : Q ⊆ D ∪ closure (S \ D) := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hQS hx, hxD⟩)
  have hinter : D ∩ closure (S \ D) = r '' stdSimplexBoundary 2 :=
    hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hr hDS
  have havoid : Q ∩ (D ∩ closure (S \ D)) = ∅ := by
    rw [hinter]
    exact hdis.symm.inter_eq
  have hQD : Q ⊆ D := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hQ.isConnected.isPreconnected
        D (closure (S \ D)) hD.isPolyhedron.isClosed isClosed_closure hcover havoid with h | h
    · exact h
    · obtain ⟨x, hx⟩ := hJ.nonempty
      exact ((hJD hx).2 (hinter.subset ⟨(hJD hx).1, h (hJQ hx)⟩)).elim
  exact ⟨Q, q, hq, fun x hx => ⟨hQD hx, fun hxB => disjoint_left.mp hdis hxB hx⟩, hqJ⟩

theorem IsPLSphere.exists_innermost_subdisk {S D : Set E} (hS : IsPLSphere 2 S)
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDS : D ⊆ S) {ι : Type*} [Finite ι] [Nonempty ι] {J : ι → Set E}
    (hJ : ∀ i, IsPLSphere 1 (J i))
    (hJD : ∀ i, J i ⊆ D \ r '' stdSimplexBoundary 2)
    (hdisj : Pairwise fun i j => Disjoint (J i) (J j)) :
    ∃ (i : ι) (Q : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q ∧
      Q ⊆ D \ r '' stdSimplexBoundary 2 ∧ q '' stdSimplexBoundary 2 = J i ∧
      ∀ j, j ≠ i → Disjoint Q (J j) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨Q, q, hq, hQD, hqJ⟩ := hS.exists_disk_in_disk_sdiff_boundary hr hDS (hJ i) (hJD i)
  exact hS.exists_innermost_disk_subset (sdiff_subset.trans hDS) hJ
    (fun j => ((hJD j).trans sdiff_subset).trans hDS) hdisj ⟨i, Q, q, hq, hQD, hqJ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
