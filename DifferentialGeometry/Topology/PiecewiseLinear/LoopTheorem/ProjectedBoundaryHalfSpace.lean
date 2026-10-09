/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem subset_interior_or_compl_of_avoids_frontier
    {X : Type*} [TopologicalSpace X] {C P : Set X} (hC : IsClosed C)
    (hP : IsPreconnected P) (havoid : ∀ x ∈ P, x ∉ frontier C) :
    P ⊆ interior C ∨ P ⊆ Cᶜ := by
  by_cases hsub : P ⊆ interior C
  · exact Or.inl hsub
  right
  obtain ⟨a, ha, hai⟩ := not_subset.mp hsub
  have hac : a ∈ Cᶜ := fun hac => havoid a ha ⟨subset_closure hac, hai⟩
  have hcover : P ⊆ interior C ∪ Cᶜ := by
    intro z hz
    by_cases hzc : z ∈ C
    · left
      by_contra hzi
      exact havoid z hz ⟨subset_closure hzc, hzi⟩
    · exact Or.inr hzc
  intro b hb hbc
  have hbi : b ∈ interior C := by
    by_contra hbi
    exact havoid b hb ⟨subset_closure hbc, hbi⟩
  obtain ⟨z, -, hzi, hzc⟩ := hP (interior C) Cᶜ isOpen_interior hC.isOpen_compl
    hcover ⟨b, hb, hbi⟩ ⟨a, ha, hac⟩
  exact hzc (interior_subset hzi)

private theorem exists_halfSpace_chart_of_frontier_chart
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {C : Set X} (hC : closure (interior C) = C) {y : X} (hy : y ∈ frontier C)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas X) (hye : y ∈ e.source)
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hBd : ∀ z ∈ e.source, z ∈ frontier C ↔ ℓ (e z) = 0) :
    ∃ (e' : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
      (a : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
      e' ∈ (plGroupoid 3).maximalAtlas X ∧ a ≠ 0 ∧ y ∈ e'.source ∧
      (∀ z ∈ e'.source, z ∈ C ↔ 0 ≤ a (e' z)) ∧
      ∀ z ∈ e'.source, z ∈ frontier C ↔ a (e' z) = 0 := by
  have hclosed : IsClosed C := hC ▸ isClosed_closure
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hye)
  let O := e.source ∩ e ⁻¹' Metric.ball (e y) r
  have hO : IsOpen O := e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hyO : y ∈ O := ⟨hye, Metric.mem_ball_self hr⟩
  let P := e.symm '' (Metric.ball (e y) r ∩ {z | 0 < ℓ z})
  let N := e.symm '' (Metric.ball (e y) r ∩ {z | ℓ z < 0})
  have hP : IsPreconnected P :=
    ((convex_ball (e y) r).inter (convex_halfSpace_gt ℓ.isLinear 0)).isPreconnected.image e.symm
      (e.continuousOn_symm.mono (fun _ hz => hball hz.1))
  have hN : IsPreconnected N :=
    ((convex_ball (e y) r).inter (convex_halfSpace_lt ℓ.isLinear 0)).isPreconnected.image e.symm
      (e.continuousOn_symm.mono (fun _ hz => hball hz.1))
  have hPavoid : ∀ z ∈ P, z ∉ frontier C := by
    rintro z ⟨w, ⟨hw, hpos⟩, rfl⟩ hz
    have h := (hBd (e.symm w) (e.map_target (hball hw))).mp hz
    rw [e.right_inv (hball hw)] at h
    exact hpos.ne' h
  have hNavoid : ∀ z ∈ N, z ∉ frontier C := by
    rintro z ⟨w, ⟨hw, hneg⟩, rfl⟩ hz
    have h := (hBd (e.symm w) (e.map_target (hball hw))).mp hz
    rw [e.right_inv (hball hw)] at h
    exact hneg.ne h
  have hpos (z : X) (hz : z ∈ O) (hl : 0 < ℓ (e z)) : z ∈ P :=
    ⟨e z, ⟨hz.2, hl⟩, e.left_inv hz.1⟩
  have hneg (z : X) (hz : z ∈ O) (hl : ℓ (e z) < 0) : z ∈ N :=
    ⟨e z, ⟨hz.2, hl⟩, e.left_inv hz.1⟩
  have hcover (z : X) (hz : z ∈ O) (hzB : z ∉ frontier C) : z ∈ P ∨ z ∈ N := by
    have hne : ℓ (e z) ≠ 0 := fun h => hzB ((hBd z hz.1).mpr h)
    rcases lt_or_gt_of_ne hne with hn | hp
    · exact Or.inr (hneg z hz hn)
    · exact Or.inl (hpos z hz hp)
  have hyint : y ∈ closure (interior C) := hC.symm ▸ hclosed.frontier_subset hy
  have hyout : y ∈ closure Cᶜ := by
    rw [frontier_eq_closure_inter_closure] at hy
    exact hy.2
  obtain ⟨u, huO, hui⟩ := (mem_closure_iff_nhds.mp hyint) O (hO.mem_nhds hyO)
  obtain ⟨v, hvO, hvc⟩ := (mem_closure_iff_nhds.mp hyout) O (hO.mem_nhds hyO)
  have huPN := hcover u huO (fun huB => huB.2 hui)
  have hvPN := hcover v hvO (fun hvB => hvc (hclosed.frontier_subset hvB))
  have hfinish (a : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (ha : a ≠ 0)
      (haBd : ∀ z ∈ e.source, z ∈ frontier C ↔ a (e z) = 0)
      (haPos : ∀ z ∈ O, 0 < a (e z) → z ∈ interior C)
      (haNeg : ∀ z ∈ O, a (e z) < 0 → z ∉ C) :
      ∃ (e' : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
        (a : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        e' ∈ (plGroupoid 3).maximalAtlas X ∧ a ≠ 0 ∧ y ∈ e'.source ∧
        (∀ z ∈ e'.source, z ∈ C ↔ 0 ≤ a (e' z)) ∧
        ∀ z ∈ e'.source, z ∈ frontier C ↔ a (e' z) = 0 := by
    let e' := e.restr O
    have hsrc : e'.source ⊆ O := fun _ hz => interior_subset hz.2
    refine ⟨e', a, restr_mem_maximalAtlas (G := plGroupoid 3) he hO, ha,
      ⟨hye, hO.interior_eq.symm ▸ hyO⟩, ?_, fun z hz => haBd z hz.1⟩
    intro z hz
    change z ∈ C ↔ 0 ≤ a (e z)
    rcases lt_trichotomy (a (e z)) 0 with hn | heq | hp
    · exact ⟨fun hzC => (haNeg z (hsrc hz) hn hzC).elim, fun hge => (not_lt_of_ge hge hn).elim⟩
    · exact iff_of_true (hclosed.frontier_subset ((haBd z hz.1).mpr heq)) heq.ge
    · exact iff_of_true (interior_subset (haPos z (hsrc hz) hp)) hp.le
  rcases subset_interior_or_compl_of_avoids_frontier hclosed hP hPavoid with hPi | hPc <;>
    rcases subset_interior_or_compl_of_avoids_frontier hclosed hN hNavoid with hNi | hNc
  · exact (hvc (interior_subset (hvPN.elim (fun h => hPi h) (fun h => hNi h)))).elim
  · exact hfinish ℓ hℓ hBd (fun z hz hl => hPi (hpos z hz hl))
      (fun z hz hl => hNc (hneg z hz hl))
  · apply hfinish (-ℓ) (neg_ne_zero.mpr hℓ)
    · intro z hz
      simpa only [LinearMap.neg_apply, neg_eq_zero] using hBd z hz
    · intro z hz hl
      have hn : ℓ (e z) < 0 := by simpa only [LinearMap.neg_apply, neg_pos] using hl
      exact hNi (hneg z hz hn)
    · intro z hz hl
      have hp : 0 < ℓ (e z) := by simpa only [LinearMap.neg_apply, neg_lt_zero] using hl
      exact hPc (hpos z hz hp)
  · exact (huPN.elim (fun h => hPc h) (fun h => hNc h) (interior_subset hui)).elim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_halfSpace_chart_glued₂_space_in_double
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (p : K.space) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    ∀ y ∈ frontier C,
      ∃ (e : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
        (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        e ∈ (plGroupoid 3).maximalAtlas (double 3 K).space ∧ ℓ ≠ 0 ∧ y ∈ e.source ∧
        (∀ z ∈ e.source, z ∈ C ↔ 0 ≤ ℓ (e z)) ∧
        ∀ z ∈ e.source, z ∈ frontier C ↔ ℓ (e z) = 0 := by
  classical
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K hK)
  let ι := simplicialMap K (glueEmbed₂ (boundaryComplex 3 K) id)
  let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
  change ∀ y ∈ frontier C, _
  intro y hy
  obtain ⟨hC, -⟩ := exists_bicollar_glued₂_space_in_double K hK p
  obtain ⟨e, ℓ, he, hℓ, hye, hBd⟩ := exists_boundary_chart_glued₂_space_in_double K hK p y hy
  exact exists_halfSpace_chart_of_frontier_chart hC.closure_interior hy e he hye ℓ hℓ hBd

end DifferentialGeometry.Topology.PiecewiseLinear
