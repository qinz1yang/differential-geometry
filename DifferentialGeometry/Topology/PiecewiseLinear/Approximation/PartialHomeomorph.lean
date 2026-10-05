import DifferentialGeometry.Topology.Manifold.PartialAtlas.Subtype
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.Homeomorph

open Set Topology TopologicalSpace
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

private theorem openPartialHomeomorphSubtypeCoe_symm_apply {X : Type*} [TopologicalSpace X]
    (s : Opens X) (hs : Nonempty s) {x : X} (hx : x ∈ s) :
    (s.openPartialHomeomorphSubtypeCoe hs).symm x = ⟨x, hx⟩ := by
  have h := (s.openPartialHomeomorphSubtypeCoe hs).left_inv (x := ⟨x, hx⟩) (by simp)
  simpa using h

theorem exists_openPartialHomeomorph_mem_plGroupoid_dist_lt_zero
    {X₁ X₂ : Type u} [TopologicalSpace X₁]
    [MetricSpace X₂] {O₁ : Set X₁} {O₂ : Set X₂}
    (A : DifferentialGeometry.Topology.Manifold.AtlasOn (plGroupoid 0) O₁)
    (B : DifferentialGeometry.Topology.Manifold.AtlasOn (plGroupoid 0) O₂)
    (g : OpenPartialHomeomorph X₁ X₂) (hgs : g.source = O₁) (hgt : g.target = O₂)
    (φ : X₁ → ℝ) (hφpos : ∀ x ∈ O₁, 0 < φ x) :
    ∃ f : OpenPartialHomeomorph X₁ X₂, f.source = O₁ ∧ f.target = O₂ ∧
      (∀ x ∈ O₁, dist (f x) (g x) < φ x) ∧
      ∀ e ∈ A.charts, ∀ e' ∈ B.charts, e.symm ≫ₕ f ≫ₕ e' ∈ plGroupoid 0 := by
  have hsub : Subsingleton (EuclideanSpace ℝ (Fin 0)) :=
    (WithLp.equiv 2 (Fin 0 → ℝ)).subsingleton
  exact ⟨g, hgs, hgt, fun x hx => by simpa using hφpos x hx, fun e _ e' _ =>
    mem_plGroupoid_of_isPiecewiseAffineOn (isPiecewiseAffineOn_of_subsingleton _ _)⟩

theorem exists_openPartialHomeomorph_mem_plGroupoid_dist_lt_three
    {X₁ X₂ : Type u} [TopologicalSpace X₁] [T2Space X₁] [SecondCountableTopology X₁]
    [MetricSpace X₂] [SecondCountableTopology X₂] {O₁ : Set X₁} {O₂ : Set X₂}
    (A : DifferentialGeometry.Topology.Manifold.AtlasOn (plGroupoid 3) O₁)
    (B : DifferentialGeometry.Topology.Manifold.AtlasOn (plGroupoid 3) O₂)
    (g : OpenPartialHomeomorph X₁ X₂) (hgs : g.source = O₁) (hgt : g.target = O₂)
    (φ : X₁ → ℝ) (hφ : ContinuousOn φ O₁) (hφpos : ∀ x ∈ O₁, 0 < φ x) :
    ∃ f : OpenPartialHomeomorph X₁ X₂, f.source = O₁ ∧ f.target = O₂ ∧
      (∀ x ∈ O₁, dist (f x) (g x) < φ x) ∧
      ∀ e ∈ A.charts, ∀ e' ∈ B.charts, e.symm ≫ₕ f ≫ₕ e' ∈ plGroupoid 3 := by
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
    refine (plGroupoid 3).mem_of_eqOnSource (ofSet_mem_plGroupoid isOpen_empty) ⟨hempty, ?_⟩
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
  let C₁ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) S₁ := A.subtypeChartedSpace S₁
  let C₂ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) S₂ := B.subtypeChartedSpace S₂
  have hG₁ : HasGroupoid S₁ (plGroupoid 3) := A.subtypeChartedSpace_hasGroupoid S₁
  have hG₂ : HasGroupoid S₂ (plGroupoid 3) := B.subtypeChartedSpace_hasGroupoid S₂
  let g' : S₁ ≃ₜ S₂ := (Homeomorph.setCongr hgs.symm).trans
    (g.toHomeomorphSourceTarget.trans (Homeomorph.setCongr hgt))
  have hg' : ∀ x : S₁, ((g' x : S₂) : X₂) = g x := fun _ => rfl
  let φ' : S₁ → ℝ := fun x => φ x.1
  have hφ' : Continuous φ' := continuousOn_iff_continuous_domRestrict.mp hφ
  have hφ'pos : ∀ x : S₁, 0 < φ' x := fun x => hφpos x.1 x.2
  obtain ⟨f, hf, hfdist⟩ := exists_homeomorph_isPL_dist_lt_three g' φ' hφ' hφ'pos
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
