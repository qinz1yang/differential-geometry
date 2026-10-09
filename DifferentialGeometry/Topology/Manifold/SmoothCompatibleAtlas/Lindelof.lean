import DifferentialGeometry.Topology.Manifold.SmoothCompatibleAtlas.Countable
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_smoothCompatibleAtlas_of_lindelof
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [ChartedSpace E X] [LindelofSpace X]
    {r : ℕ} [IsManifold 𝓘(ℝ, E) r X] (hr : 1 ≤ r) :
    ∃ s : Set X, s.Countable ∧
      (∀ x : X, ∃ i : s, x ∈ (chartAt E (i : X)).source) ∧
      ∃ (A : SmoothCompatibleAtlas E X s) (κ : s → E ≃ₜ E),
        (∀ i, (A.chart i).source = (chartAt E (i : X)).source ∧
          (A.chart i).target = (chartAt E (i : X)).target) ∧
        (∀ i, A.chart i = (chartAt E (i : X)).trans (κ i).toOpenPartialHomeomorph) ∧
        (∀ i, ContDiff ℝ r (κ i) ∧ ContDiff ℝ r (κ i).symm) ∧
        (∀ (i : s) x, x ∉ (chartAt E (i : X)).target → κ i x = x ∧ (κ i).symm x = x) ∧
        (∀ i x, 0 < (fderiv ℝ (κ i) x).det) ∧
        A.IsCompatible (chartAt E : X → OpenPartialHomeomorph X E) r := by
  obtain ⟨s, hs, hcover⟩ := LindelofSpace.elim_nhds_subcover
    (fun x : X => (chartAt E x).source) (chart_source_mem_nhds E)
  let : Countable s := hs.to_subtype
  have hcover' : ∀ x : X, ∃ i : s, x ∈ (chartAt E (i : X)).source := by
    intro x
    have hx : x ∈ ⋃ y ∈ s, (chartAt E y).source := by
      rw [hcover]
      exact mem_univ x
    obtain ⟨y, hy⟩ := mem_iUnion.mp hx
    obtain ⟨hys, hxy⟩ := mem_iUnion.mp hy
    exact ⟨⟨y, hys⟩, hxy⟩
  have htrans (x y : X) :
      ContDiffOn ℝ r ((chartAt E x).symm.trans (chartAt E y))
        ((chartAt E x).symm.trans (chartAt E y)).source := by
    exact (contMDiffOn_of_mem_contDiffGroupoid
      (IsManifold.compatible_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := (r : ℕ∞ω)) x)
        (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := (r : ℕ∞ω)) y))).contDiffOn
  obtain ⟨A, hst, _, κ, hchart, hreg, hfix, hdet⟩ :=
    exists_smoothCompatibleAtlas hr (fun i : s => chartAt E (i : X)) hcover'
      (fun i j => htrans i j)
  refine ⟨s, hs, hcover', A, κ, hst, hchart, hreg, hfix, hdet, ?_⟩
  intro x i
  rw [hchart i]
  exact ⟨contDiffOn_symm_trans_trans_homeomorph (chartAt E x) (chartAt E (i : X))
      (κ i) (htrans x i) (hreg i).1,
    contDiffOn_trans_homeomorph_symm_trans (chartAt E (i : X)) (chartAt E x)
      (κ i) (htrans i x) (hreg i).2⟩

end DifferentialGeometry.Topology.Manifold
