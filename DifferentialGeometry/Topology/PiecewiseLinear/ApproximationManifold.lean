import DifferentialGeometry.Topology.PiecewiseLinear.Approximation
import DifferentialGeometry.Topology.PiecewiseLinear.Manifold

open Set Topology TopologicalSpace
open scoped Manifold

namespace DifferentialGeometry.Topology.Manifold.AtlasOn

variable {H X : Type*} [TopologicalSpace H] [TopologicalSpace X] {G : StructureGroupoid H}

@[instance_reducible] noncomputable def subtypeChartedSpace (s : Opens X)
    (A : AtlasOn G (s : Set X)) :
    ChartedSpace H s where
  atlas := ⋃ x : s, {(A.exists_mem_source x.1 x.2).choose.subtypeRestr ⟨x⟩}
  chartAt x := (A.exists_mem_source x.1 x.2).choose.subtypeRestr ⟨x⟩
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact (A.exists_mem_source x.1 x.2).choose_spec.2
  chart_mem_atlas x := by
    simp only [mem_iUnion, mem_singleton_iff]
    exact ⟨x, rfl⟩

theorem subtypeChartedSpace_hasGroupoid [ClosedUnderRestriction G] (s : Opens X)
    (A : AtlasOn G (s : Set X)) :
    letI := A.subtypeChartedSpace s
    HasGroupoid s G := by
  let _ := A.subtypeChartedSpace s
  constructor
  rintro e e' ⟨_, ⟨x, hc⟩, he⟩ ⟨_, ⟨x', hc'⟩, he'⟩
  rw [hc.symm, mem_singleton_iff] at he
  rw [hc'.symm, mem_singleton_iff] at he'
  rw [he, he']
  refine G.mem_of_eqOnSource ?_
    (OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr (s := s) _ _ _)
  apply closedUnderRestriction'
  · exact A.compatible _ (A.exists_mem_source x.1 x.2).choose_spec.1 _
      (A.exists_mem_source x'.1 x'.2).choose_spec.1
  · exact OpenPartialHomeomorph.isOpen_inter_preimage_symm _ s.2

theorem subtypeRestr_mem_maximalAtlas [ClosedUnderRestriction G] (s : Opens X)
    (A : AtlasOn G (s : Set X)) (hs : Nonempty s) {e : OpenPartialHomeomorph X H}
    (he : e ∈ A.charts) :
    letI := A.subtypeChartedSpace s
    e.subtypeRestr hs ∈ G.maximalAtlas s := by
  let _ := A.subtypeChartedSpace s
  rintro e' ⟨_, ⟨x, hc⟩, he'⟩
  rw [hc.symm, mem_singleton_iff] at he'
  rw [he']
  have hx := (A.exists_mem_source x.1 x.2).choose_spec.1
  constructor
  · refine G.mem_of_eqOnSource ?_
      (OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr (s := s) _ _ _)
    exact closedUnderRestriction' (A.compatible _ he _ hx)
      (OpenPartialHomeomorph.isOpen_inter_preimage_symm _ s.2)
  · refine G.mem_of_eqOnSource ?_
      (OpenPartialHomeomorph.subtypeRestr_symm_trans_subtypeRestr (s := s) _ _ _)
    exact closedUnderRestriction' (A.compatible _ hx _ he)
      (OpenPartialHomeomorph.isOpen_inter_preimage_symm _ s.2)

end DifferentialGeometry.Topology.Manifold.AtlasOn

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.Manifold (AtlasOn)

universe u

variable {n : ℕ}

theorem openPartialHomeomorphSubtypeCoe_symm_apply {X : Type*} [TopologicalSpace X]
    (s : Opens X) (hs : Nonempty s) {x : X} (hx : x ∈ s) :
    (s.openPartialHomeomorphSubtypeCoe hs).symm x = ⟨x, hx⟩ := by
  have h := (s.openPartialHomeomorphSubtypeCoe hs).left_inv (x := ⟨x, hx⟩) (by simp)
  simpa using h

theorem plApproximation_of_plApproximationManifold (h : PLApproximationManifold.{u} n) :
    PLApproximation.{u} n := by
  intro X₁ X₂ _ _ _ _ _ O₁ O₂ A B g hgs hgt φ hφ hφpos
  classical
  by_cases hne : O₁.Nonempty
  swap
  · have hO₁ : O₁ = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨g, hgs, hgt, fun x hx => absurd ⟨x, hx⟩ hne, fun e he e' he' => ?_⟩
    have hempty : (e.symm ≫ₕ g ≫ₕ e').source = ∅ := by
      ext y
      simp only [mem_empty_iff_false, iff_false]
      intro hy
      have hy1 : e.symm y ∈ e.source := e.map_target hy.1
      have hy2 : e.symm y ∈ O₁ := A.source_subset e he hy1
      rw [hO₁] at hy2
      exact hy2
    refine (plGroupoid n).mem_of_eqOnSource (ofSet_mem_plGroupoid isOpen_empty) ⟨hempty, ?_⟩
    intro y hy
    rw [hempty] at hy
    exact absurd hy (notMem_empty y)
  obtain ⟨x₀, hx₀⟩ := hne
  have hO₁ : IsOpen O₁ := hgs ▸ g.open_source
  have hO₂ : IsOpen O₂ := hgt ▸ g.open_target
  let S₁ : Opens X₁ := ⟨O₁, hO₁⟩
  let S₂ : Opens X₂ := ⟨O₂, hO₂⟩
  have hS₁ : Nonempty S₁ := ⟨⟨x₀, hx₀⟩⟩
  have hS₂ : Nonempty S₂ := ⟨⟨g x₀, by
    have : g x₀ ∈ g.target := g.map_source (by rw [hgs]; exact hx₀)
    rw [hgt] at this
    exact this⟩⟩
  let C₁ : ChartedSpace (EuclideanSpace ℝ (Fin n)) S₁ := A.subtypeChartedSpace S₁
  let C₂ : ChartedSpace (EuclideanSpace ℝ (Fin n)) S₂ := B.subtypeChartedSpace S₂
  have hG₁ : HasGroupoid S₁ (plGroupoid n) := A.subtypeChartedSpace_hasGroupoid S₁
  have hG₂ : HasGroupoid S₂ (plGroupoid n) := B.subtypeChartedSpace_hasGroupoid S₂
  let g' : S₁ ≃ₜ S₂ := (Homeomorph.setCongr hgs.symm).trans
    (g.toHomeomorphSourceTarget.trans (Homeomorph.setCongr hgt))
  have hg' : ∀ x : S₁, ((g' x : S₂) : X₂) = g x := fun _ => rfl
  let φ' : S₁ → ℝ := fun x => φ x.1
  have hφ' : Continuous φ' := continuousOn_iff_continuous_domRestrict.mp hφ
  have hφ'pos : ∀ x : S₁, 0 < φ' x := fun x => hφpos x.1 x.2
  obtain ⟨f, hf, hfdist⟩ := h g' φ' hφ' hφ'pos
  let c₁ := S₁.openPartialHomeomorphSubtypeCoe hS₁
  let c₂ := S₂.openPartialHomeomorphSubtypeCoe hS₂
  let f' : OpenPartialHomeomorph X₁ X₂ := c₁.symm.trans (f.toOpenPartialHomeomorph.trans c₂)
  have hc₁symm : ∀ x (hx : x ∈ O₁), c₁.symm x = ⟨x, hx⟩ := fun x hx =>
    openPartialHomeomorphSubtypeCoe_symm_apply S₁ hS₁ hx
  have hf'val : ∀ x (hx : x ∈ O₁), f' x = (f ⟨x, hx⟩ : X₂) := by
    intro x hx
    change c₂ (f (c₁.symm x)) = _
    rw [hc₁symm x hx]
    rfl
  have hf's : f'.source = O₁ := by
    have h1 : (f.toOpenPartialHomeomorph.trans c₂).source = univ := by
      rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
        Opens.openPartialHomeomorphSubtypeCoe_source, preimage_univ, univ_inter]
    change (c₁.symm.trans _).source = O₁
    rw [OpenPartialHomeomorph.trans_source, h1, preimage_univ, inter_univ,
      OpenPartialHomeomorph.symm_source, Opens.openPartialHomeomorphSubtypeCoe_target]
    rfl
  have hf't : f'.target = O₂ := by
    have h1 : (f.toOpenPartialHomeomorph.trans c₂).target = O₂ := by
      rw [OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
        Opens.openPartialHomeomorphSubtypeCoe_target, preimage_univ, inter_univ]
      rfl
    change (c₁.symm.trans _).target = O₂
    rw [OpenPartialHomeomorph.trans_target, h1, OpenPartialHomeomorph.symm_target,
      Opens.openPartialHomeomorphSubtypeCoe_source, preimage_univ, inter_univ]
  refine ⟨f', hf's, hf't, ?_, ?_⟩
  · intro x hx
    rw [hf'val x hx]
    have hd := hfdist ⟨x, hx⟩
    rw [Subtype.dist_eq, hg'] at hd
    exact hd
  · intro e he e' he'
    apply mem_plGroupoid_of_isPiecewiseAffineOn
    intro y hy
    have hy1 : y ∈ e.target := hy.1
    have hx : e.symm y ∈ e.source := e.map_target hy1
    have hxO : e.symm y ∈ O₁ := A.source_subset e he hx
    have hfx : f' (e.symm y) ∈ e'.source := hy.2.2
    have hmax₁ := A.subtypeRestr_mem_maximalAtlas S₁ hS₁ he
    have hmax₂ := B.subtypeRestr_mem_maximalAtlas S₂ hS₂ he'
    have hp : (⟨e.symm y, hxO⟩ : S₁) ∈ (e.subtypeRestr hS₁).source := by
      rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact hx
    have hfp : f ⟨e.symm y, hxO⟩ ∈ (e'.subtypeRestr hS₂).source := by
      rw [OpenPartialHomeomorph.subtypeRestr_source]
      change (f ⟨e.symm y, hxO⟩ : X₂) ∈ e'.source
      rw [← hf'val _ hxO]
      exact hfx
    obtain ⟨-, hPA⟩ := (isPLAt_iff_of_mem_maximalAtlas hmax₁ hp hmax₂ hfp).mp (hf ⟨e.symm y, hxO⟩)
    have hey : (e.subtypeRestr hS₁) ⟨e.symm y, hxO⟩ = y := by
      change e (e.symm y) = y
      exact e.right_inv hy1
    rw [hey] at hPA
    have hPA' := hPA.inter_of_mem_nhds ((e.symm ≫ₕ f' ≫ₕ e').open_source.mem_nhds hy)
    rw [univ_inter] at hPA'
    refine hPA'.congr ?_
    intro z hz
    have hz1 : z ∈ e.target := hz.1
    have hzO : e.symm z ∈ O₁ := A.source_subset e he (e.map_target hz1)
    change e' (f' (e.symm z)) = e' (f (c₁.symm (e.symm z)) : X₂)
    rw [hf'val _ hzO, hc₁symm _ hzO]

end DifferentialGeometry.Topology.PiecewiseLinear
