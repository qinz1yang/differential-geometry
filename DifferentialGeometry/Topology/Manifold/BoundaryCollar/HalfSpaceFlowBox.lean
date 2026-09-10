import DifferentialGeometry.Topology.Manifold.BoundaryCollar.PositiveFlowBox
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.EuclideanFlow
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Extension

open Set Function Manifold Filter
open scoped Topology ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.BoundaryCollar

theorem exists_inward_halfSpace_flowBox
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {U : Set (ℝ × E)} (hU : IsOpen U) {z : E} (hz : (0, z) ∈ U)
    {f : ℝ × E → ℝ × E}
    (hf : ContDiffOn ℝ ∞ f ((Ici (0 : ℝ) ×ˢ (univ : Set E)) ∩ U))
    (hpos : 0 < (f (0, z)).1) :
    ∃ Φ : (ℝ × E) × ℝ → ℝ × E, ContDiff ℝ ∞ Φ ∧
      (∀ x, Φ (x, 0) = x) ∧
      (∀ x s t, Φ (Φ (x, s), t) = Φ (x, s + t)) ∧
      (∀ t, Injective (fun x => Φ (x, t))) ∧
      ∃ e : PartialDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) 1,
        (0, z) ∈ e.source ∧ (e : ℝ × E → ℝ × E) = (fun p => Φ ((0, p.2), p.1)) ∧
        e.target ⊆ U ∧
        (∀ p ∈ e.source, 0 ≤ (e p).1 ↔ 0 ≤ p.1) ∧
        (∀ p ∈ e.source, (e p).1 = 0 ↔ p.1 = 0) ∧
        ∀ p ∈ e.source, ∀ t ∈ Icc (0 : ℝ) p.1,
          Φ ((0, p.2), t) ∈ U ∧ 0 ≤ (Φ ((0, p.2), t)).1 ∧
          HasDerivAt (fun s => Φ ((0, p.2), s)) (f (Φ ((0, p.2), t))) t := by
  obtain ⟨g, hg, hgK, hgf⟩ := exists_contDiff_halfSpace_extension hU hz hf
  obtain ⟨Φ, hΦ, hzero, hadd, hinj, hder⟩ := exists_complete_smooth_flow g hg hgK
  have hgpos : 0 < (g (0, z)).1 := by
    rw [hgf.eq_of_nhdsWithin (by simp)]
    exact hpos
  obtain ⟨A, hA, hAgf⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hgf
  obtain ⟨e, he, heq, htarget, hhalf, hboundary, hpath⟩ :=
    exists_positive_flowBox_of_flow hΦ hzero hg.continuous hder hgpos
      (inter_mem (hU.mem_nhds hz) hA)
  refine ⟨Φ, hΦ, hzero, hadd, hinj, e, he, heq,
    fun y hy => (htarget hy).1, hhalf, hboundary, ?_⟩
  intro p hp t ht
  have hh := hpath p hp t ht
  refine ⟨hh.1.1, hh.2, ?_⟩
  rw [← hAgf ⟨hh.1.2, hh.2, mem_univ _⟩]
  exact hder (0, p.2) t

end Poincare.Manifold.BoundaryCollar
