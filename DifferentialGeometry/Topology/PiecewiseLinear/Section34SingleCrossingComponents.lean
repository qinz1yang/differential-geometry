import DifferentialGeometry.Topology.PiecewiseLinear.Section34SingleTraceSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingOutsideDensity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.mem_closure_annulus_sides_of_chart_crossing {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B X Xb A A₀ A₁ : Set M} (hS : IsPLCellOn 3 S B) (hX : IsPLCellOn 3 X Xb)
    (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B) {x : M}
    (hxA : x ∈ A) (hxX : x ∈ Xb) (hxends : x ∉ A₀ ∪ A₁)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hxc : x ∈ c.source)
    (hcross : HasPLCrossingAt (c '' (A ∩ c.source)) (c '' (Xb ∩ c.source)) (c x)) :
    x ∈ closure (A ∩ interior X) ∧ x ∈ closure (A \ X) := by
  have hreg : closure (interior X) = X := by
    rw [← hX.sdiff_boundary_eq_interior]
    exact hX.closure_sdiff_boundary
  have hball := fun N hN => hS.exists_ball_chart_in_annulus hA hAB hxA hxends (N := N) hN
  have hfront : x ∈ frontier X := hX.boundary_eq_frontier ▸ hxX
  have hcross' := hX.boundary_eq_frontier ▸ hcross
  have hxcl : x ∈ closure (interior X) := hreg.symm ▸ hX.boundary_subset hxX
  obtain ⟨V, -, -, -, hV⟩ := exists_connected_inside_slice_of_chart_crossing
    hX.isCompact.isClosed hxcl c hxc hcross' hball
  obtain ⟨W, -, -, -, hW⟩ := exists_connected_outside_slice_of_chart_crossing
    hX.isCompact.isClosed hreg c hxc hcross' hfront hball
  exact ⟨closure_mono inter_subset_left hV, closure_mono inter_subset_left hW⟩

theorem IsPLCellOn.isConnected_annulus_sides_of_single_crossing {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B X Xb A A₀ A₁ J : Set M} (hS : IsPLCellOn 3 S B) (hX : IsPLCellOn 3 X Xb)
    (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B)
    (hJ : IsPolyhedralSphere (n := 3) 1 J) (hends : Disjoint J (A₀ ∪ A₁))
    (htrace : A ∩ Xb = J)
    (hcross : ∀ x ∈ J, ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      x ∈ c.source ∧
        HasPLCrossingAt (c '' (A ∩ c.source)) (c '' (Xb ∩ c.source)) (c x)) :
    IsConnected (A ∩ X) ∧ IsConnected (A \ X) := by
  have hcl : ∀ x ∈ J, x ∈ closure (A ∩ interior X) ∧ x ∈ closure (A \ X) := by
    intro x hx
    obtain ⟨c, hxc, hcross⟩ := hcross x hx
    exact hS.mem_closure_annulus_sides_of_chart_crossing hX hA hAB
      (htrace.superset hx).1 (htrace.superset hx).2
      (fun h => disjoint_left.mp hends hx h) c hxc hcross
  have hne : J.Nonempty := by
    obtain ⟨T, hT⟩ := hJ
    exact T.piece.bijOn.image_eq ▸ hT.nonempty.image T.piece.map
  obtain ⟨x, hx⟩ := hne
  have hpos := closure_nonempty_iff.mp ⟨x, (hcl x hx).1⟩
  have hneg := closure_nonempty_iff.mp ⟨x, (hcl x hx).2⟩
  apply hS.isConnected_annulus_sides_of_single_circle hA hAB hJ
    (htrace.symm.subset.trans inter_subset_left) hends hX.isCompact.isClosed
    (hX.boundary_eq_frontier ▸ htrace) hpos hneg
  exact fun x hx => (hcl x hx).1

theorem IsPLCellOn.component_conditions_of_single_crossing {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B X Xb A A₀ A₁ J : Set M} (hS : IsPLCellOn 3 S B) (hX : IsPLCellOn 3 X Xb)
    (hA : IsAnnulusOn A A₀ A₁) (hAB : A ⊆ B)
    (hJ : IsPolyhedralSphere (n := 3) 1 J) (hends : Disjoint J (A₀ ∪ A₁))
    (htrace : A ∩ Xb = J)
    (hcross : ∀ x ∈ J, ∃ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      x ∈ c.source ∧
        HasPLCrossingAt (c '' (A ∩ c.source)) (c '' (Xb ∩ c.source)) (c x)) (T : Set M) :
    (∃ a ∈ A ∩ X, ∀ z ∈ A ∩ X, z ∉ T → z ∈ connectedComponentIn (A ∩ X) a) ∧
      ∃ b ∈ A \ X, ∀ z ∈ A \ X, z ∉ T → z ∈ connectedComponentIn (A \ X) b := by
  obtain ⟨hin, hout⟩ := hS.isConnected_annulus_sides_of_single_crossing
    hX hA hAB hJ hends htrace hcross
  obtain ⟨a, ha⟩ := hin.nonempty
  obtain ⟨b, hb⟩ := hout.nonempty
  exact ⟨⟨a, ha, fun _ hz _ => hin.isPreconnected.subset_connectedComponentIn ha Subset.rfl hz⟩,
    ⟨b, hb, fun _ hz _ => hout.isPreconnected.subset_connectedComponentIn hb Subset.rfl hz⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
