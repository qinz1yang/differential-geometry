import DifferentialGeometry.Topology.PiecewiseLinear.PLCellMarkerMove
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_marked_pierced_cell_pair_covering_compact {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C₀ C₁ O G : Set M}
    (h₀ : IsPolyhedralBall (n := 3) 3 C₀) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (hD : IsPolyhedralBall (n := 3) 2 (C₀ ∩ C₁))
    (hD₀ : C₀ ∩ C₁ ⊆ frontier C₀) (hD₁ : C₀ ∩ C₁ ⊆ frontier C₁)
    (hO : IsOpen O) (hDO : C₀ ∩ C₁ ⊆ O) (hG : IsCompact G)
    (hGC : G ⊆ interior (C₀ ∪ C₁)) {p₀ p₁ : M}
    (hp₀ : p₀ ∈ C₀ ∩ C₁) (hp₁ : p₁ ∈ C₀ ∩ C₁)
    (hp₀I : p₀ ∈ interior (C₀ ∪ C₁)) (hp₁I : p₁ ∈ interior (C₀ ∪ C₁))
    (hne : p₀ ≠ p₁) :
    ∃ A B : Set M, IsPLCellOn 3 A (frontier A) ∧ IsPLCellOn 3 B (frontier B) ∧
      p₀ ∈ interior A ∧ p₀ ∉ B ∧ p₁ ∈ interior B ∧ p₁ ∉ A ∧
      (interior A ∩ interior B).Nonempty ∧
      IsPolyhedralSphere (n := 3) 1 (frontier A ∩ frontier B) ∧
      frontier A ∩ frontier B ⊆ C₀ ∩ C₁ ∧ A ∩ B ⊆ O ∧ A ∪ B ⊆ C₀ ∪ C₁ ∧
      G ⊆ interior A ∪ interior B ∧ A \ O = C₀ \ O ∧ B \ O = C₁ \ O := by
  let H := G ∪ {p₀, p₁}
  have hH : IsCompact H := hG.union (isCompact_singleton.insert p₀)
  have hHC : H ⊆ interior (C₀ ∪ C₁) := by
    refine union_subset hGC ?_
    intro x hx
    rcases hx with rfl | hx
    · exact hp₀I
    · exact (mem_singleton_iff.mp hx).symm ▸ hp₁I
  obtain ⟨A, B, hA, hB, hn, hs, hm, hl, hab, hcover, hAd, hBd, hroutes⟩ :=
    exists_pierced_cell_pair_covering_compact h₀ h₁ hD hD₀ hD₁ hO hDO hH hHC
  have hp₀H : p₀ ∈ H := Or.inr (Or.inl rfl)
  have hp₁H : p₁ ∈ H := Or.inr (Or.inr rfl)
  obtain ⟨K₀, K₁, q₀, q₁, hK₀, hK₁, hc₀, hc₁, hdisj, hp₀K, hq₀K, hp₁K, hq₁K,
    hsub₀, hsub₁, hq₀B, hq₁A⟩ := hroutes p₀ ⟨hp₀H, hp₀⟩ p₁ ⟨hp₁H, hp₁⟩ hne
  obtain ⟨A', B', hA', hB', hp₀A', hp₀B', hp₁B', hp₁A', hu, hi, hf, hdA, hdB, hn'⟩ :=
    exists_marked_cell_pair_of_disjoint_connected_routes hA hB hO hK₀ hK₁ hc₀ hc₁ hdisj
      hsub₀ hsub₁ hp₀K hq₀K hq₀B hp₁K hq₁K hq₁A
  refine ⟨A', B', hA', hB', hp₀A', hp₀B', hp₁B', hp₁A', hn'.mpr hn,
    hf.symm ▸ hs, hf.subset.trans hm, ?_, hu.subset.trans hab,
    (subset_union_left.trans hcover).trans hi.symm.subset, hdA.trans hAd, hdB.trans hBd⟩
  intro x hx
  by_contra hxO
  exact hxO (hl ⟨(hdA.subset ⟨hx.1, hxO⟩).1, (hdB.subset ⟨hx.2, hxO⟩).1⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
