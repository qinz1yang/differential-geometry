import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeWiringComponent

/-!
A common positive shrink of every old torus collar avoids a compact interior fibre tube.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem fibreCollarHalfLift_continuous : Continuous halfSpaceOneLift := by
  have he : halfSpaceOneLift = fun t : ℝ =>
      halfSpaceOneHomeomorph.symm ⟨max 0 t, le_max_left 0 t⟩ :=
    funext halfSpaceOneLift_eq
  rw [he]
  exact halfSpaceOneHomeomorph.symm.continuous.comp
    ((continuous_const.max continuous_id).subtype_mk (fun t => le_max_left 0 t))

private theorem fibreCollar_avoid_width {C : CompactCarrier.{u}}
    (c : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hc : c.source = halfCollarSource)
    (hb : ∀ t, C.model.IsBoundaryPoint (c (t, halfZero))) {K : Set C.Carrier} (hK : IsCompact K)
    (hKI : K ⊆ C.interior) :
    ∃ ε > (0 : ℝ), ∀ t s, 0 ≤ s → s < ε → c (t, halfSpaceOneLift s) ∉ K := by
  let A : Set (Torus × EuclideanHalfSpace 1) :=
    c.source ∩ c ⁻¹' Kᶜ
  have hA : IsOpen A :=
    c.contMDiffOn.continuousOn.isOpen_inter_preimage
      c.open_source hK.isClosed.isOpen_compl
  let f : Torus × ℝ → Torus × EuclideanHalfSpace 1 :=
    fun p => (p.1, halfSpaceOneLift p.2)
  have hf : Continuous f := continuous_fst.prodMk
    (fibreCollarHalfLift_continuous.comp continuous_snd)
  have hz : (univ : Set Torus) ×ˢ ({0} : Set ℝ) ⊆ f ⁻¹' A := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    have he : halfSpaceOneLift 0 = halfZero := by
      exact halfSpaceOneLift_coord halfZero
    refine ⟨?_, ?_⟩
    · change (t, halfSpaceOneLift 0) ∈ c.source
      rw [he, hc]
      exact zero_mem_halfCollarSource t
    · change c (t, halfSpaceOneLift 0) ∉ K
      rw [he]
      intro hk
      exact (C.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp
        (hKI hk) (hb t)
  obtain ⟨V, W, hV, hW, hUV, hZW, hVW⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton (hA.preimage hf) hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW 0 (hZW rfl)
  refine ⟨ε, hε, fun t s hs hse => ?_⟩
  have hm : (t, s) ∈ f ⁻¹' A := hVW ⟨hUV (mem_univ t), hball (by
    simpa [Real.dist_eq, abs_of_nonneg hs] using hse)⟩
  exact hm.2

theorem exists_shrinkHalfCollars_avoiding_compact {C : CompactCarrier.{u}}
    {ι : Type*} [Finite ι]
    (c : ι → PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hc : ∀ i, (c i).source = halfCollarSource)
    (hb : ∀ i t, C.model.IsBoundaryPoint (c i (t, halfZero))) {K : Set C.Carrier} (hK : IsCompact K)
    (hKI : K ⊆ C.interior) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧
      ∀ i p, p ∈ halfCollarSource → shrinkHalfCollar hδ (c i) p ∉ K := by
  choose ε hε hav using fun i => fibreCollar_avoid_width (c i) (hc i) (hb i) hK hKI
  obtain ⟨m, hm, hme⟩ := Wiring.exists_pos_le_of_finite ε hε
  let δ := min m 1
  have hδ : 0 < δ := lt_min hm one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  refine ⟨δ, hδ, hδ1, fun i p hp => ?_⟩
  change c i (p.1, halfSpaceScale hδ p.2) ∉ K
  have hs : 0 ≤ δ * p.2.val 0 := mul_nonneg hδ.le p.2.property
  have hlt : δ * p.2.val 0 < ε i :=
    (mul_lt_of_lt_one_right hδ hp).trans_le ((min_le_left m 1).trans (hme i))
  have he : halfSpaceOneLift (δ * p.2.val 0) = halfSpaceScale hδ p.2 := by
    rw [← halfSpaceScale_coord hδ p.2]
    exact halfSpaceOneLift_coord _
  rw [← he]
  exact hav i p.1 _ hs hlt

theorem BoundaryTori.exists_shrink_avoiding_compact {C : CompactCarrier.{u}} {n : ℕ}
    (E : BoundaryTori C n) {K : Set C.Carrier} (hK : IsCompact K)
    (hKI : K ⊆ C.interior) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
      ∀ i p, p ∈ halfCollarSource → (E.shrink hδ hδ1).collar i p ∉ K := by
  obtain ⟨δ, hδ, hδ1, h⟩ :=
    exists_shrinkHalfCollars_avoiding_compact E.collar E.source_eq E.boundary_zero hK hKI
  exact ⟨δ, hδ, hδ1, h⟩

end GC.GraphManifold
