import DifferentialGeometry.Topology.ThreeManifold.SmoothSchoenflies
import DifferentialGeometry.Topology.Diffeomorph.SphereGermExtension
import DifferentialGeometry.Topology.Connected.BallComplement
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Embedding.Sphere

/-!
# Ball filling of a smooth shell in `ℝ³`

Lane N2e (helper of N2d, route A′ of the side data). A partial diffeomorphism `F` of `ℝ³` defined
near the unit sphere, whose image sphere `F '' S²` is the frontier of a bounded open connected set
`U` with `F` sending the inside of the sphere into `U` and the outside away from `closure U`,
extends near the sphere to a global diffeomorphism `G` of `ℝ³` carrying the unit ball onto `U`
(`exists_ballFill_of_shell`).

Proof: the smooth Schoenflies theorem `smooth_schoenflies_three` applied to `F ∘ coe` gives `Φ`
with `Φ '' S² = F '' S²`; a bounded open connected set with frontier the unit sphere is the unit
ball (`eq_ball_of_frontier_eq_sphere`), so `U = Φ '' ball`; the partial diffeomorphism
`Φ⁻¹ ∘ F` preserves the sphere and its outside, so the sphere germ extension theorem
`exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph_of_compl_ball`
(Smale's isotopy on the sphere and a collar isotopy) gives a diffeomorphism `D` preserving the
closed ball and equal to `Φ⁻¹ ∘ F` near the sphere; `G := Φ ∘ D`.
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.Seifert.SplitTube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private local instance ballFillFact : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem eq_ball_of_frontier_eq_sphere {W : Set E3} (hW : IsOpen W)
    (hbd : Bornology.IsBounded W) (hconn : IsPreconnected W) (hne : W.Nonempty)
    (hfront : frontier W = sphere (0 : E3) 1) : W = ball 0 1 := by
  have hcl : ∀ C : Set E3, Disjoint C (sphere 0 1) → closure W ∩ C ⊆ W := by
    rintro C hC x ⟨hxW, hxC⟩
    rw [closure_eq_self_union_frontier, hfront] at hxW
    rcases hxW with h | h
    · exact h
    · exact absurd h (hC.notMem_of_mem_left hxC)
  have hWS : W ⊆ ball 0 1 ∪ (closedBall 0 1)ᶜ := by
    intro x hx
    have hxs : x ∉ sphere (0 : E3) 1 := by
      rw [← hfront]
      intro h
      have := hW.inter_frontier_eq
      exact this.subset ⟨hx, h⟩
    rcases lt_trichotomy ‖x‖ 1 with h | h | h
    · exact Or.inl (mem_ball_zero_iff.mpr h)
    · exact absurd (mem_sphere_zero_iff_norm.mpr h) hxs
    · exact Or.inr (fun hc => absurd (mem_closedBall_zero_iff.mp hc) (not_le.mpr h))
  rcases hconn.subset_or_subset isOpen_ball isClosed_closedBall.isOpen_compl
      (disjoint_compl_right.mono_right (compl_subset_compl.mpr ball_subset_closedBall) |>.mono_left
        le_rfl) hWS with h | h
  · refine Subset.antisymm h ?_
    refine (convex_ball (0 : E3) 1).isPreconnected.subset_of_closure_inter_subset hW ?_ ?_
    · obtain ⟨x, hx⟩ := hne
      exact ⟨x, h hx, hx⟩
    · refine hcl _ ?_
      rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
      rintro x ⟨hb, hs⟩
      exact (ne_of_lt (mem_ball_zero_iff.mp hb)) (mem_sphere_zero_iff_norm.mp hs)
  · exfalso
    have hrank : 1 < Module.rank ℝ E3 := by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      norm_num
    have hsub : (closedBall (0 : E3) 1)ᶜ ⊆ W := by
      refine (isPathConnected_compl_closedBall hrank (0 : E3) 1).isConnected.isPreconnected
        |>.subset_of_closure_inter_subset hW ?_ ?_
      · obtain ⟨x, hx⟩ := hne
        exact ⟨x, h hx, hx⟩
      · refine hcl _ ?_
        rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
        rintro x ⟨hb, hs⟩
        exact hb (sphere_subset_closedBall hs)
    have hall : Bornology.IsBounded (univ : Set E3) := by
      rw [← union_compl_self (closedBall (0 : E3) 1)]
      exact (isBounded_closedBall).union (hbd.subset hsub)
    exact NormedSpace.unbounded_univ ℝ E3 hall

theorem isSmoothEmbedding_partialDiffeomorph_comp_coe
    (F : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (hS : sphere (0 : E3) 1 ⊆ F.source) :
    IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun z : sphere (0 : E3) 1 => F z) := by
  let O : TopologicalSpace.Opens E3 := ⟨F.source, F.open_source⟩
  have hloc : IsLocalDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞ (fun x : O => F x) :=
    isLocalDiffeomorph_restrict_open O (fun x => F.isLocalDiffeomorphAt _ _ _ x.2)
  have hinj : Injective (fun x : O => F x) := fun x y h => Subtype.ext (F.injOn x.2 y.2 h)
  have hFO := Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective hloc hinj
  let c : sphere (0 : E3) 1 → O := fun z => ⟨z, hS z.2⟩
  have hc : IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ c :=
    Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡 2) 𝓘(ℝ, E3) O c
      (isSmoothEmbedding_coe_sphere (E := E3) (n := 2))
  exact hFO.comp hc (by simp)

open DifferentialGeometry.Topology.Manifold in
theorem exists_ballFill_of_shell (F : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (hS : sphere (0 : E3) 1 ⊆ F.source) {U : Set E3} (hU : IsOpen U)
    (hbd : Bornology.IsBounded U) (hconn : IsPreconnected U) (hfront : frontier U = F '' sphere 0 1)
    (hin : ∀ x ∈ F.source, ‖x‖ < 1 → F x ∈ U) (hout : ∀ x ∈ F.source, 1 < ‖x‖ → F x ∉ closure U) :
    ∃ G : E3 ≃ₘ[ℝ] E3, G '' ball 0 1 = U ∧ G '' closedBall 0 1 = closure U ∧
      ∃ V : Set E3, IsOpen V ∧ sphere (0 : E3) 1 ⊆ V ∧ V ⊆ F.source ∧ EqOn G F V := by
  obtain ⟨Φ, hΦ⟩ := ThreeManifold.smooth_schoenflies_three (fun z => F z)
    (isSmoothEmbedding_partialDiffeomorph_comp_coe F hS)
  have hΦS : Φ '' sphere 0 1 = F '' sphere 0 1 := by
    rw [hΦ]
    ext y
    simp
  have hne : (Φ.symm '' U).Nonempty := by
    have hp : (EuclideanSpace.single 0 1 : E3) ∈ sphere (0 : E3) 1 := by simp
    have hcl : (EuclideanSpace.single 0 1 : E3) ∈ closure (ball (0 : E3) 1) := by
      rw [closure_ball _ one_ne_zero]
      exact sphere_subset_closedBall hp
    obtain ⟨x, hxs, hxb⟩ := mem_closure_iff_nhds.mp hcl F.source
      (F.open_source.mem_nhds (hS hp))
    exact ⟨_, mem_image_of_mem _ (hin x hxs (mem_ball_zero_iff.mp hxb))⟩
  have hW : Φ.symm '' U = ball 0 1 := by
    refine eq_ball_of_frontier_eq_sphere (Φ.symm.toHomeomorph.isOpenMap U hU) ?_
      (hconn.image _ Φ.symm.continuous.continuousOn) hne ?_
    · exact ((hbd.isCompact_closure.image Φ.symm.continuous).isBounded).subset
        (image_mono subset_closure)
    · rw [← Diffeomorph.coe_toHomeomorph, ← Homeomorph.image_frontier,
        Diffeomorph.coe_toHomeomorph, hfront, ← hΦS, Diffeomorph.symm_image_image]
  have hUΦ : U = Φ '' ball 0 1 := by
    rw [← hW, Diffeomorph.image_symm_image]
  have hclU : closure U = Φ '' closedBall 0 1 := by
    rw [hUΦ, ← closure_ball (0 : E3) one_ne_zero, ← Diffeomorph.coe_toHomeomorph,
      Homeomorph.image_closure]
  let A := F.trans Φ.symm.toPartialDiffeomorph
  have hAsource : A.source = F.source := by
    ext x
    change (x ∈ F.source ∧ F x ∈ (univ : Set E3)) ↔ x ∈ F.source
    exact ⟨And.left, fun hx => ⟨hx, mem_univ _⟩⟩
  have hAS : A '' sphere 0 1 = sphere 0 1 := by
    change (Φ.symm ∘ F) '' _ = _
    rw [image_comp, ← hΦS, Diffeomorph.symm_image_image]
  have hAmap : MapsTo A ((ball 0 1)ᶜ ∩ A.source) (ball 0 1)ᶜ := by
    rintro x ⟨hx, hxs⟩
    rw [hAsource] at hxs
    have hx1 : 1 ≤ ‖x‖ := not_lt.mp fun h => hx (mem_ball_zero_iff.mpr h)
    rcases hx1.lt_or_eq with h | h
    · intro hAx
      apply hout x hxs h
      rw [hclU]
      exact ⟨A x, ball_subset_closedBall hAx, Φ.apply_symm_apply _⟩
    · have hAx : A x ∈ sphere (0 : E3) 1 :=
        hAS ▸ mem_image_of_mem A (mem_sphere_zero_iff_norm.mpr h.symm)
      exact fun hb => (ne_of_lt (mem_ball_zero_iff.mp hb)) (mem_sphere_zero_iff_norm.mp hAx)
  obtain ⟨D, hDball, V, hV, hSV, hVA, hDA⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_sphere_preserving_partialDiffeomorph_of_compl_ball
      A (hAsource ▸ hS) hAS hAmap
  have hDb : D '' ball 0 1 = ball 0 1 := by
    have h := D.toHomeomorph.image_interior (closedBall (0 : E3) 1)
    rw [Diffeomorph.coe_toHomeomorph, hDball, interior_closedBall _ one_ne_zero] at h
    exact h
  refine ⟨D.trans Φ, ?_, ?_, V, hV, hSV, hVA.trans hAsource.le, ?_⟩
  · rw [Diffeomorph.coe_trans, image_comp, hDb, hUΦ]
  · rw [Diffeomorph.coe_trans, image_comp, hDball, hclU]
  · intro x hx
    change Φ (D x) = F x
    rw [hDA hx]
    exact Φ.apply_symm_apply (F x)

end GC.Seifert.SplitTube
