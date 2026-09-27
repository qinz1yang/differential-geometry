/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConeFanCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.CarrierPerturbation
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleRelBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_pos_forall_exists_vertex_image_subset_openStar
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces] {f : ℝ × ℝ → F}
    (hf : ContinuousOn f stdCone) (hmap : MapsTo f stdCone L.space) :
    ∃ d > 0, ∀ p ∈ stdCone, ∃ v : F, {v} ∈ L.faces ∧
      ∀ z ∈ stdCone, dist z p < d → f z ∈ openStar L v := by
  classical
  choose V hVopen hVeq using fun w : {w : F // {w} ∈ L.faces} =>
    continuousOn_iff'.mp hf (avoidingUnion L w.1)ᶜ (isClosed_avoidingUnion L w.1).isOpen_compl
  obtain ⟨d, hd, hdsub⟩ := lebesgue_number_lemma_of_metric isHPolytope_stdCone.isCompact hVopen
    (by
      intro x hx
      obtain ⟨w, hw, hxw⟩ := exists_vertex_mem_openStar L (hmap hx)
      refine mem_iUnion.mpr ⟨⟨w, hw⟩, ?_⟩
      have hx' : x ∈ f ⁻¹' (avoidingUnion L w)ᶜ ∩ stdCone := ⟨hxw.2, hx⟩
      rw [hVeq ⟨w, hw⟩] at hx'
      exact hx'.1)
  refine ⟨d, hd, ?_⟩
  intro p hp
  obtain ⟨⟨w, hw⟩, hball⟩ := hdsub p hp
  refine ⟨w, hw, ?_⟩
  intro z hz hzd
  refine ⟨hmap hz, ?_⟩
  have hzV : z ∈ V ⟨w, hw⟩ ∩ stdCone := ⟨hball (Metric.mem_ball.mpr hzd), hz⟩
  rw [← hVeq ⟨w, hw⟩] at hzV
  exact hzV.1

theorem eq_of_mem_openStar_of_vertex {L : Geometry.SimplicialComplex ℝ F} {v y : F}
    (hy : y ∈ L.vertices) (hv : y ∈ openStar L v) : v = y := by
  have hmem := mem_carrierFace_of_mem_openStar L hv
  rw [carrierFace_eq_singleton hy] at hmem
  exact Finset.mem_singleton.mp hmem

theorem exists_pos_forall_exists_isPiecewiseAffineOn_stdCone_mapsTo_of_vertex_boundary
    {L : Geometry.SimplicialComplex ℝ F} [Finite L.faces] {f : ℝ × ℝ → F}
    (hf : ContinuousOn f stdCone) (hmap : MapsTo f stdCone L.space) :
    ∃ δ > 0, ∀ (M N : ℕ) (u σ : ℕ → ℝ),
      u 0 = 0 → u (M + 1) = 1 → (∀ j ≤ M, u j < u (j + 1)) → (∀ j ≤ M, u (j + 1) - u j < δ) →
      σ 0 = 0 → σ (N + 1) = 1 → (∀ k ≤ N, σ k < σ (k + 1)) → (∀ k ≤ N, σ (k + 1) - σ k < δ) →
      (∀ j ≤ M + 1, f (1 - u j, u j) ∈ L.vertices) →
      (∀ k ≤ N + 1, f (σ k, 0) ∈ L.vertices) →
      (∀ k ≤ N + 1, f (0, σ k) ∈ L.vertices) →
      ∃ Ψ : ℝ × ℝ → F, IsPiecewiseAffineOn Ψ stdCone ∧
        (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
          Ψ (t, 0) = AffineMap.lineMap (f (σ k, 0)) (f (σ (k + 1), 0))
            ((t - σ k) / (σ (k + 1) - σ k))) ∧
        (∀ k ≤ N, ∀ t ∈ Icc (σ k) (σ (k + 1)),
          Ψ (0, t) = AffineMap.lineMap (f (0, σ k)) (f (0, σ (k + 1)))
            ((t - σ k) / (σ (k + 1) - σ k))) ∧
        (∀ j ≤ M, ∀ r ∈ Icc (u j) (u (j + 1)),
          Ψ (1 - r, r) = AffineMap.lineMap (f (1 - u j, u j)) (f (1 - u (j + 1), u (j + 1)))
            ((r - u j) / (u (j + 1) - u j))) ∧
        (∀ z ∈ stdCone, Ψ z ∈ convexHull ℝ (carrierFace L (f z))) ∧
        MapsTo Ψ stdCone L.space := by
  classical
  obtain ⟨d, hd, hcover⟩ := exists_pos_forall_exists_vertex_image_subset_openStar hf hmap
  have hchoice : ∀ p : ℝ × ℝ, ∃ v : F, p ∈ stdCone →
      ∀ z ∈ stdCone, dist z p < d → f z ∈ openStar L v := by
    intro p
    by_cases hp : p ∈ stdCone
    · obtain ⟨v, -, hvz⟩ := hcover p hp
      exact ⟨v, fun _ => hvz⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose g hg using hchoice
  refine ⟨d / 4, by linarith, ?_⟩
  intro M N u σ hu0 huM humono humesh hσ0 hσN hσmono hσmesh hvH hv₁ hv₂
  have huchain := le_of_chain (fun j hj => (humono j hj).le)
  have hσchain := le_of_chain (fun k hk => (hσmono k hk).le)
  have hunn : ∀ j ≤ M + 1, 0 ≤ u j := by
    intro j hj
    have h := huchain j hj 0 (Nat.zero_le _)
    rwa [hu0] at h
  have hule : ∀ j ≤ M + 1, u j ≤ 1 := by
    intro j hj
    have h := huchain (M + 1) le_rfl j hj
    rwa [huM] at h
  have hσnn : ∀ k ≤ N + 1, 0 ≤ σ k := by
    intro k hk
    have h := hσchain k hk 0 (Nat.zero_le _)
    rwa [hσ0] at h
  have hσle : ∀ k ≤ N + 1, σ k ≤ 1 := by
    intro k hk
    have h := hσchain (N + 1) le_rfl k hk
    rwa [hσN] at h
  set p : ℕ → ℕ → ℝ × ℝ := fun a b => (σ a * (1 - u b), σ a * u b) with hpdef
  have hpval : ∀ a b : ℕ, p a b = ((σ a * (1 - u b), σ a * u b) : ℝ × ℝ) := fun _ _ => rfl
  have hpmem : ∀ a ≤ N + 1, ∀ b ≤ M + 1, p a b ∈ stdCone := by
    intro a ha b hb
    exact stdConeSector_subset_stdCone _ _
      (mem_stdConeSector_smul_left le_rfl (hunn b hb) (hule b hb) ⟨hσnn a ha, hσle a ha⟩)
  set w : ℕ → ℕ → F := fun a b => g (p a b) with hwdef
  have hwval : ∀ a b : ℕ, w a b = g (p a b) := fun _ _ => rfl
  have hvertex : ∀ a ≤ N + 1, ∀ b ≤ M + 1, f (p a b) ∈ L.vertices → w a b = f (p a b) := by
    intro a ha b hb hv
    refine eq_of_mem_openStar_of_vertex hv ?_
    rw [hwval]
    refine hg (p a b) (hpmem a ha b hb) _ (hpmem a ha b hb) ?_
    rw [dist_self]
    exact hd
  have hw0 : ∀ j, w 0 j = w 0 0 := by
    intro j
    rw [hwval, hwval, hpval, hpval, hσ0]
    norm_num
  have hstar : ∀ k ≤ N, ∀ j ≤ M, ∀ z ∈ stdCone, σ k ≤ z.1 + z.2 → z.1 + z.2 ≤ σ (k + 1) →
      z ∈ stdConeSector (u j) (u (j + 1)) →
      f z ∈ openStar L (w k j) ∧ f z ∈ openStar L (w k (j + 1)) ∧
        f z ∈ openStar L (w (k + 1) j) ∧ f z ∈ openStar L (w (k + 1) (j + 1)) := by
    intro k hk j hj z hz h1 h2 hsec
    have hcell : ∀ a b : ℕ, a ≤ N + 1 → b ≤ M + 1 → σ a ∈ Icc (σ k) (σ (k + 1)) →
        u b ∈ Icc (u j) (u (j + 1)) → f z ∈ openStar L (w a b) := by
      intro a b ha hb hσa hub
      rw [hwval]
      refine hg (p a b) (hpmem a ha b hb) z hz ?_
      have hdist := dist_cellCorner_le hsec h1 h2 hσa hub (hunn j (by omega))
        (hule (j + 1) (by omega))
      have e1 := hσmesh k hk
      have e2 := humesh j hj
      rw [dist_comm, hpval]
      linarith
    exact ⟨hcell k j (by omega) (by omega) ⟨le_rfl, (hσmono k hk).le⟩
        ⟨le_rfl, (humono j hj).le⟩,
      hcell k (j + 1) (by omega) (by omega) ⟨le_rfl, (hσmono k hk).le⟩
        ⟨(humono j hj).le, le_rfl⟩,
      hcell (k + 1) j (by omega) (by omega) ⟨(hσmono k hk).le, le_rfl⟩
        ⟨le_rfl, (humono j hj).le⟩,
      hcell (k + 1) (j + 1) (by omega) (by omega) ⟨(hσmono k hk).le, le_rfl⟩
        ⟨(humono j hj).le, le_rfl⟩⟩
  obtain ⟨Ψ, hPA, -, hray₁, hray₂, houter, hcarrier, hmapsto⟩ :=
    exists_isPiecewiseAffineOn_stdCone_fan_carrierFace f w hu0 huM humono hσ0 hσN hσmono hw0 hstar
  have hwleg₁ : ∀ k ≤ N + 1, w k 0 = f (σ k, 0) := by
    intro k hk
    have hpt : p k 0 = ((σ k, 0) : ℝ × ℝ) := by
      rw [hpval, hu0]
      norm_num
    have := hvertex k hk 0 (by omega) (by rw [hpt]; exact hv₁ k hk)
    rw [this, hpt]
  have hwleg₂ : ∀ k ≤ N + 1, w k (M + 1) = f (0, σ k) := by
    intro k hk
    have hpt : p k (M + 1) = ((0, σ k) : ℝ × ℝ) := by
      rw [hpval, huM]
      norm_num
    have := hvertex k hk (M + 1) (by omega) (by rw [hpt]; exact hv₂ k hk)
    rw [this, hpt]
  have hwhyp : ∀ j ≤ M + 1, w (N + 1) j = f (1 - u j, u j) := by
    intro j hj
    have hpt : p (N + 1) j = ((1 - u j, u j) : ℝ × ℝ) := by
      rw [hpval, hσN]
      norm_num
    have := hvertex (N + 1) (by omega) j hj (by rw [hpt]; exact hvH j hj)
    rw [this, hpt]
  refine ⟨Ψ, hPA, ?_, ?_, ?_, hcarrier, hmapsto⟩
  · intro k hk t ht
    have hpt : ((t * (1 - u 0), t * u 0) : ℝ × ℝ) = (t, 0) := by
      rw [hu0]
      norm_num
    rw [← hpt, hray₁ k hk t ht, hwleg₁ k (by omega), hwleg₁ (k + 1) (by omega)]
  · intro k hk t ht
    have hpt : ((t * (1 - u (M + 1)), t * u (M + 1)) : ℝ × ℝ) = (0, t) := by
      rw [huM]
      norm_num
    rw [← hpt, hray₂ k hk t ht, hwleg₂ k (by omega), hwleg₂ (k + 1) (by omega)]
  · intro j hj r hr
    rw [houter j hj r hr, hwhyp j (by omega), hwhyp (j + 1) (by omega)]

end DifferentialGeometry.Topology.PiecewiseLinear
