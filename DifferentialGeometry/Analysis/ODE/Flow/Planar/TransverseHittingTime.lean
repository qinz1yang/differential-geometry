import DifferentialGeometry.Analysis.Calculus.Inverse.ParameterizedInverse

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace Poincare.Analysis

theorem exists_contDiffOn_transverse_hittingTime
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {V S : Set E} (hV : IsOpen V) (hSV : S ⊆ V) {h : E × ℝ → ℝ} {c : E → ℝ}
    (hh : ContDiffOn ℝ ∞ h (V ×ˢ univ)) (hc : ContDiffOn ℝ ∞ c S)
    (hcross : ∀ p ∈ S, ∃! t : ℝ, h (p, t) = c p)
    (htransverse : ∀ p ∈ S, ∀ t, h (p, t) = c p → fderiv ℝ h (p, t) (0, 1) ≠ 0) :
    ∃ τ : E → ℝ, ContDiffOn ℝ ∞ τ S ∧
      (∀ p ∈ S, h (p, τ p) = c p) ∧
      ∀ p ∈ S, ∀ t, h (p, t) = c p → t = τ p := by
  classical
  let τ : E → ℝ := fun p ↦ if hp : p ∈ S then (hcross p hp).exists.choose else 0
  have hroot (p : E) (hp : p ∈ S) : h (p, τ p) = c p := by
    simpa only [τ, dif_pos hp] using (hcross p hp).exists.choose_spec
  have huniq (p : E) (hp : p ∈ S) (t : ℝ) (ht : h (p, t) = c p) : t = τ p :=
    (hcross p hp).unique ht (hroot p hp)
  refine ⟨τ, ?_, hroot, huniq⟩
  intro p hp
  obtain ⟨e, hep, _, _, hei, he, hparam⟩ := exists_localInverse_preserving_parameter hh
    (hV.prod isOpen_univ) (show (p, τ p) ∈ V ×ˢ univ from ⟨hSV hp, mem_univ _⟩)
    (htransverse p hp (τ p) (hroot p hp))
  have heq : e (p, τ p) = (p, c p) := by rw [he, hroot p hp]
  have ht : (p, c p) ∈ e.target := heq ▸ e.map_source hep
  have hgraph : ContDiffWithinAt ℝ ∞ (fun q ↦ (q, c q)) S p :=
    contDiffWithinAt_id.prodMk (hc p hp)
  have hnear : ∀ᶠ q in 𝓝[S] p, (q, c q) ∈ e.target :=
    hgraph.continuousWithinAt.preimage_mem_nhdsWithin (e.open_target.mem_nhds ht)
  have hagree : τ =ᶠ[𝓝[S] p] fun q ↦ (e.symm (q, c q)).2 := by
    filter_upwards [hnear, self_mem_nhdsWithin] with q hq hqV
    have hqparam := hparam (q, c q) hq
    have hpair : (q, (e.symm (q, c q)).2) = e.symm (q, c q) :=
      Prod.ext hqparam.1.symm rfl
    exact (huniq q hqV _ ((congrArg h hpair).trans hqparam.2)).symm
  have hat : τ p = (e.symm (p, c p)).2 := hagree.eq_of_nhdsWithin hp
  have hs := ((hei.contDiffAt (e.open_target.mem_nhds ht)).snd).comp_contDiffWithinAt p hgraph
  exact hs.congr_of_eventuallyEq hagree hat

end Poincare.Analysis
