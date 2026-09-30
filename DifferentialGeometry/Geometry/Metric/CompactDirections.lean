import DifferentialGeometry.Geometry.Metric.DirectionPackingShortening
import DifferentialGeometry.Topology.MetricSpace.FiniteNets

set_option autoImplicit false

open Set Metric Filter Topology

namespace Metric

theorem compactSpace_spaceOfDirections_of_uniform_scaled_nets
    {X : Type*} [MetricSpace X] (q : X) [HasAnglesAt q]
    (hnet : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ S : ℝ, 0 < S ∧
      ∀ s : ℝ, 0 < s → s < S → ∃ T : Finset X, T.card ≤ N ∧
        ∀ x ∈ closedBall q s, ∃ y ∈ T, dist x y < ε * s) :
    CompactSpace (SpaceOfDirections q) := by
  classical
  have htb : TotallyBounded (univ : Set (SpaceOfDirections q)) := by
    apply Metric.totallyBounded_iff.mpr
    intro δ hδ
    obtain ⟨N, S, hS, hcover⟩ := hnet (δ / Real.pi / 4) (by positivity)
    have hpack (A : Finset (SpaceOfDirections q))
        (_hA : (A : Set (SpaceOfDirections q)) ⊆ univ)
        (hAsep : (A : Set (SpaceOfDirections q)).Pairwise (fun x y => δ ≤ dist x y)) :
        A.card ≤ N := by
      obtain ⟨σ, s, hs, hsS, _, _, hrad, hsep⟩ :=
        exists_common_shortening_of_separated_directions hδ hS (fun i : A => i.val)
          (fun i j hij => hAsep i.property j.property (fun h => hij (Subtype.ext h)))
      obtain ⟨T, hTcard, hTnet⟩ := hcover s hs hsS
      let f : A → X := fun i => (σ i).path s
      have hf : Function.Injective f := by
        intro i j hij
        by_contra hne
        have hd := hsep i j hne
        change δ / Real.pi * s < dist (f i) (f j) at hd
        rw [hij, dist_self] at hd
        exact (not_lt_of_ge (mul_pos (div_pos hδ Real.pi_pos) hs).le) hd
      let B : Finset X := Finset.univ.image f
      have hBcard : B.card = A.card := by
        simp only [B, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_coe]
      have hBsep : (B : Set X).Pairwise (fun x y => δ / Real.pi * s ≤ dist x y) := by
        intro x hx y hy hxy
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
        exact (hsep i j (fun h => hxy (congrArg f h))).le
      have hBnet : ∀ x ∈ B, ∃ y ∈ T, dist x y ≤ δ / Real.pi / 4 * s := by
        intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨y, hy, hxy⟩ := hTnet (f i) (by
          change dist (f i) q ≤ s
          rw [dist_comm, hrad i])
        exact ⟨y, hy, hxy.le⟩
      have hgap : 2 * (δ / Real.pi / 4 * s) < δ / Real.pi * s := by
        nlinarith [mul_pos (div_pos hδ Real.pi_pos) hs]
      have hcard := card_le_card_of_separated_net B T hgap hBsep hBnet
      rw [hBcard] at hcard
      exact hcard.trans hTcard
    obtain ⟨A, _, _, hAnet⟩ := exists_finset_net_card_le_of_packing hδ N hpack
    refine ⟨A, A.finite_toSet, ?_⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hAnet x hx
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, hxy⟩⟩
  exact ⟨htb.isCompact_of_isComplete isComplete_univ⟩

end Metric
