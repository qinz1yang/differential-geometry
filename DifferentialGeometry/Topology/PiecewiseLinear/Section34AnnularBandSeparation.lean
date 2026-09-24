import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularRegionGerms
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandComponents

open Set Topology

namespace DifferentialGeometry.Topology

theorem closure_subset_of_same_interior_side
    {X : Type*} [TopologicalSpace X] {R A O V : Set X} {x : X}
    (hR : IsClosed R) (hRA : R ⊆ A) (hxR : x ∈ closure (interior R))
    (hxO : x ∈ closure O) (hV : V ∈ 𝓝 x)
    (hVconn : IsPreconnected (V ∩ interior A))
    (hfront : V ∩ frontier R ⊆ frontier A)
    (hO : IsPreconnected O) (hOA : O ⊆ interior A) (hdis : Disjoint O (frontier R)) :
    closure O ⊆ R := by
  have hgerm := inter_interior_eq_of_subset_of_local_frontier_subset hRA hxR hV hVconn hfront
  obtain ⟨y, hyV, hyO⟩ := mem_closure_iff_nhds.mp hxO V hV
  have hyR : y ∈ interior R := (hgerm.superset ⟨hyV, hOA hyO⟩).2
  have hsub := subset_interior_of_isPreconnected_of_disjoint_frontier hO hdis ⟨y, hyO, hyR⟩
  exact closure_minimal (hsub.trans interior_subset) hR

theorem closure_subset_of_same_exterior_side
    {X : Type*} [TopologicalSpace X] {R A O V : Set X} {x : X}
    (hR : IsClosed R) (hA : closure (interior A) = A) (hRA : R ∩ A ⊆ frontier A)
    (hxR : x ∈ closure (interior R)) (hxO : x ∈ closure O) (hV : V ∈ 𝓝 x)
    (hVconn : IsPreconnected (V ∩ Aᶜ)) (hfront : V ∩ frontier R ⊆ frontier A)
    (hO : IsPreconnected O) (hOA : O ⊆ Aᶜ) (hdis : Disjoint O (frontier R)) :
    closure O ⊆ R := by
  have hgerm := inter_interior_eq_compl_of_local_frontier_subset hA hRA hxR hV hVconn hfront
  obtain ⟨y, hyV, hyO⟩ := mem_closure_iff_nhds.mp hxO V hV
  have hyR : y ∈ interior R := (hgerm.superset ⟨hyV, hOA hyO⟩).2
  have hsub := subset_interior_of_isPreconnected_of_disjoint_frontier hO hdis ⟨y, hyO, hyR⟩
  exact closure_minimal (hsub.trans interior_subset) hR

namespace PiecewiseLinear

theorem IsPLCellOn.disjoint_lateral_bands_of_disjoint_ends
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B T : Set M}
    (hS : IsPLCellOn 3 S B) {f g : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfi : InjOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hgi : InjOn g (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hfB : f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ B)
    (hgB : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ B)
    (hfT : f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      f '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ T)
    (hgT : g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      g '' (stdSimplexBoundary 2 ×ˢ {1}) ⊆ T)
    (hfempty : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) T)
    (hgempty : Disjoint (g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) T)
    (hends : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪
      f '' (stdSimplexBoundary 2 ×ˢ {1}))
      (g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪ g '' (stdSimplexBoundary 2 ×ˢ {1}))) :
    Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
      (g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) := by
  let F := f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
  let G := g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
  let O := f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
  let V := g '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)
  let J := f '' (stdSimplexBoundary 2 ×ˢ {0}) ∪ f '' (stdSimplexBoundary 2 ×ˢ {1})
  let K := g '' (stdSimplexBoundary 2 ×ˢ {0}) ∪ g '' (stdSimplexBoundary 2 ×ˢ {1})
  have hO : O = F \ J := image_lateral_open_eq_sdiff_ends hfi
  have hV : V = G \ K := image_lateral_open_eq_sdiff_ends hgi
  have hJsub : J ⊆ F := union_subset (image_mono (prod_mono_right (by simp)))
    (image_mono (prod_mono_right (by simp)))
  refine disjoint_left.mpr fun x hxF hxG => ?_
  have hxJ : x ∉ J := by
    intro hxJ
    by_cases hxK : x ∈ K
    · exact disjoint_left.mp hends hxJ hxK
    · exact disjoint_left.mp hgempty (hV.superset ⟨hxG, hxK⟩) (hfT hxJ)
  have hxK : x ∉ K := fun hxK =>
    disjoint_left.mp hfempty (hO.superset ⟨hxF, hxJ⟩) (hgT hxK)
  have hxO : x ∈ O := hO.superset ⟨hxF, hxJ⟩
  have hxV : x ∈ V := hV.superset ⟨hxG, hxK⟩
  have heq : O = V :=
    (hS.connectedComponentIn_eq_lateral_band Subset.rfl hf hfi hfB hfT hfempty hxO).1.symm.trans
      (hS.connectedComponentIn_eq_lateral_band Subset.rfl hg hgi hgB hgT hgempty hxV).1
  have hFG : F = G := (closure_image_lateral_open hf).symm.trans
    ((congrArg closure heq).trans (closure_image_lateral_open hg))
  have hJK : J ⊆ K := by
    intro y hyJ
    by_contra hyK
    have hyV : y ∈ V := hV.superset ⟨hFG.subset (hJsub hyJ), hyK⟩
    exact (hO.subset (heq.symm ▸ hyV)).2 hyJ
  obtain ⟨y, hy⟩ :=
    (isAnnulusOn_stdSimplex_lateral.image_of_continuousOn_injOn hf hfi).ends_nonempty.1
  exact disjoint_left.mp hends (Or.inl hy) (hJK (Or.inl hy))

theorem image_lateral_subset_of_same_side
    {M : Type*} [TopologicalSpace M] [T2Space M] {R A V : Set M} {x : M}
    {f : (Fin 3 → ℝ) × ℝ → M}
    (hf : ContinuousOn f (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hR : IsClosed R) (hA : closure (interior A) = A)
    (hxR : x ∈ closure (interior R))
    (hxf : x ∈ f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
    (hV : V ∈ 𝓝 x) (hin : IsPreconnected (V ∩ interior A))
    (hout : IsPreconnected (V ∩ Aᶜ)) (hfront : V ∩ frontier R ⊆ frontier A)
    (hdis : Disjoint (f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1)) (frontier R))
    (hside : (R ⊆ A ∧ f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ interior A) ∨
      (R ∩ A ⊆ frontier A ∧ f '' (stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1) ⊆ Aᶜ)) :
    f '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ R := by
  have hclosure := closure_image_lateral_open hf
  have hconn := ((isConnected_stdSimplexBoundary 0).prod
    (isConnected_Ioo (zero_lt_one : (0 : ℝ) < 1))).image f
      (hf.mono (prod_mono_right Ioo_subset_Icc_self))
  rw [← hclosure] at hxf ⊢
  rcases hside with ⟨hRA, hOA⟩ | ⟨hRA, hOA⟩
  · exact closure_subset_of_same_interior_side hR hRA hxR hxf hV hin hfront
      hconn.isPreconnected hOA hdis
  · exact closure_subset_of_same_exterior_side hR hA hRA hxR hxf hV hout hfront
      hconn.isPreconnected hOA hdis

end PiecewiseLinear

end DifferentialGeometry.Topology
