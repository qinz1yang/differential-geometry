/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellEnlargement
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import Mathlib.Geometry.Manifold.Metrizable

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_section34_chart_local_enlargements
    {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
    {M₁ M₂ : Type*} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [HasGroupoid M₁ (plGroupoid 3)]
    [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
    {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    (hU : IsOpen U) (hcont : ContinuousOn h U)
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hQ : ∀ w, h '' src (.vertexBall w) ⊆ interior (Q w))
    (hchart : ∀ w : Section34VertexIndex 𝒦 𝒦', ∃ c ∈ (plGroupoid 3).maximalAtlas M₂,
      h '' src (.vertexBall w) ⊆ c.source) :
    ∃ Cc : Section34VertexIndex 𝒦 𝒦' → Set M₁,
      (∀ w, IsPLCellOn 3 (Cc w) (frontier (Cc w))) ∧
      (∀ w, src (.vertexBall w) ⊆ interior (Cc w)) ∧ (∀ w, Cc w ⊆ U) ∧
      (∀ w, h '' Cc w ⊆ interior (Q w)) ∧
      (∀ w, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, h '' Cc w ⊆ c.source) ∧
      ∀ x ∈ U, ∃ V ∈ 𝓝 x, {w | (Cc w ∩ V).Nonempty}.Finite := by
  have : LocallyCompactSpace M₁ :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M₁
  have : TopologicalSpace.MetrizableSpace M₁ :=
    Manifold.metrizableSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) M₁
  choose c hc hsrcchart using hchart
  obtain ⟨-, -, -, hcell, -, -, -, hLF, hcover, -⟩ := hframe
  have hsrcU : ∀ l, src l ⊆ U := fun l => (subset_iUnion src l).trans hcover.subset
  let F : Section34CutLabelOf 𝒦 𝒦' → Set U := fun l => Subtype.val ⁻¹' src l
  have hFLF : LocallyFinite F := by
    intro x
    obtain ⟨V, hV, hfin⟩ := hLF x x.2
    refine ⟨Subtype.val ⁻¹' V, continuous_subtype_val.continuousAt hV, hfin.subset ?_⟩
    rintro l ⟨y, hyl, hyV⟩
    exact ⟨y, hyl, hyV⟩
  have hvertexLF : LocallyFinite fun w : Section34VertexIndex 𝒦 𝒦' =>
      (Subtype.val : U → M₁) ⁻¹' src (.vertexBall w) :=
    hFLF.comp_injective fun _ _ heq => Section34Label.vertexBall.inj heq
  let A : Section34VertexIndex 𝒦 𝒦' → Set U := fun w =>
    (U.domRestrict h) ⁻¹' (interior (Q w) ∩ (c w).source)
  have hA : ∀ w, IsOpen (A w) := fun w =>
    (isOpen_interior.inter (c w).open_source).preimage hcont.domRestrict
  have hCO (w) : src (.vertexBall w) ⊆ Subtype.val '' A w := by
    intro x hx
    exact ⟨⟨x, hsrcU _ hx⟩, ⟨hQ w ⟨x, hx, rfl⟩, hsrcchart w ⟨x, hx, rfl⟩⟩, rfl⟩
  obtain ⟨Cc, hCc, hsrcCc, hCcA, hCcLF⟩ := exists_locallyFinite_isPLCellOn_enlargements hU
    (fun w => hcell (.vertexBall w)) (fun w => hsrcU (.vertexBall w)) hvertexLF
    (fun w => hU.isOpenMap_subtype_val _ (hA w)) hCO
  refine ⟨Cc, hCc, hsrcCc, fun w => (hCcA w).trans inter_subset_left, ?_, ?_, ?_⟩
  · rintro w y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (hCcA w hx).2
    exact hz.1
  · refine fun w => ⟨c w, hc w, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (hCcA w hx).2
    exact hz.2
  · intro x hx
    obtain ⟨V, hV, hfin⟩ := hCcLF ⟨x, hx⟩
    obtain ⟨N, hN, hNV⟩ := (mem_nhds_subtype U ⟨x, hx⟩ V).mp hV
    refine ⟨N ∩ U, Filter.inter_mem hN (hU.mem_nhds hx), hfin.subset ?_⟩
    rintro w ⟨y, hy, hyN, hyU⟩
    exact ⟨⟨y, hyU⟩, hy, hNV hyN⟩

end DifferentialGeometry.Topology.PiecewiseLinear
