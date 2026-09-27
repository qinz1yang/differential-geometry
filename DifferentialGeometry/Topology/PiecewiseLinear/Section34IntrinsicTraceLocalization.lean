/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicFaceCycle

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
open Classical in
theorem Section34CutFrame.exists_vertex_ball_of_connected_subset_faceTorus
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3) {A : Set M₂} (hA : IsConnected A)
    (hAT : A ⊆ section34FaceTorus (section34VertexBallImage src f₁) s)
    (hAE : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      Disjoint A (section34SplitDiskImage src f₁ e)) :
    ∃ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 ∧
      A ⊆ section34VertexBallImage src f₁ w := by
  let I := {w : Section34VertexIndex 𝒦 𝒦' // Section34Incident w.1 s.1}
  let _ : Finite I := (finite_setOf_section34Incident_graphIndex hcut.2.1
    (graphSkeletonSpace 𝒦) 1 s.2.1).to_subtype
  have hV : ∀ w, IsClosed (section34VertexBallImage src f₁ w) :=
    fun w => (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed
  obtain ⟨p, hp⟩ := hA.nonempty
  obtain ⟨w, hws, hpw⟩ := mem_section34FaceTorus_iff.mp (hAT hp)
  let O := ⋃ v : I, ⋃ (_ : v.1 ≠ w), section34VertexBallImage src f₁ v.1
  have hO : IsClosed O := isClosed_iUnion_of_finite fun v =>
    isClosed_iUnion_of_finite fun _ => hV v
  have hcover : A ⊆ section34VertexBallImage src f₁ w ∪ O := by
    intro x hx
    obtain ⟨v, hvs, hxv⟩ := mem_section34FaceTorus_iff.mp (hAT hx)
    by_cases hvw : v = w
    · exact Or.inl (hvw ▸ hxv)
    · exact Or.inr (mem_iUnion₂.mpr ⟨⟨v, hvs⟩, hvw, hxv⟩)
  have hdis : A ∩ (section34VertexBallImage src f₁ w ∩ O) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxA, hxw, hxO⟩
    obtain ⟨v, hvw, hxv⟩ := mem_iUnion₂.mp hxO
    obtain ⟨e, hxe⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn hvw hxv hxw
    exact disjoint_left.mp (hAE e) hxA hxe
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hA.isPreconnected
      (section34VertexBallImage src f₁ w) O (hV w) hO hcover hdis with hw | ho
  · exact ⟨w, hws, hw⟩
  · exact (notMem_empty p (hdis ▸ ⟨hp, hpw, ho hp⟩)).elim

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.exists_vertex_boundary_of_model_arc_avoiding_split_disks
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3) {P B : Set E3} {u : E3 → M₂}
    (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    {η : ℝ → E3} (hη : IsPLHomeomorphOn η (Icc 0 1) B) (hBP : B ⊆ P)
    (hBN : B ⊆ u ⁻¹' frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hBE : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      Disjoint (B \ {η 0, η 1}) (u ⁻¹' section34SplitDiskImage src f₁ e)) :
    ∃ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 ∧
      B ⊆ u ⁻¹' section34VertexBallImage srcBd f₁ w := by
  have hA : IsConnected (u '' (B \ {η 0, η 1})) :=
    (hη.isConnected_sdiff_endpoints zero_lt_one).image u
      (hu.continuousOn.mono (sdiff_subset.trans hBP))
  have hAT : u '' (B \ {η 0, η 1}) ⊆
      section34FaceTorus (section34VertexBallImage src f₁) s := by
    rw [← hUP]
    exact image_mono (sdiff_subset.trans hBP)
  have hAE : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      Disjoint (u '' (B \ {η 0, η 1})) (section34SplitDiskImage src f₁ e) := by
    intro e
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxe
    exact disjoint_left.mp (hBE e) hx hxe
  obtain ⟨w, hws, hw⟩ :=
    hcut.exists_vertex_ball_of_connected_subset_faceTorus hf₁ s hA hAT hAE
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hBcl : u '' B ⊆ closure (u '' (B \ {η 0, η 1})) := by
    calc
      u '' B = u '' closure (B \ {η 0, η 1}) := by
        rw [hη.closure_sdiff_endpoints zero_lt_one]
      _ ⊆ closure (u '' (B \ {η 0, η 1})) := ContinuousOn.image_closure (by
        rw [hη.closure_sdiff_endpoints zero_lt_one]
        exact hu.continuousOn.mono hBP)
  have hBW : u '' B ⊆ section34VertexBallImage src f₁ w :=
    hBcl.trans (closure_minimal hw hV.isCompact.isClosed)
  refine ⟨w, hws, ?_⟩
  rw [hV.boundary_eq_frontier]
  exact fun x hx => ⟨subset_closure (hBW ⟨x, hx, rfl⟩), fun hi =>
    (hBN hx).2 (interior_mono (subset_iUnion _ w) hi)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
