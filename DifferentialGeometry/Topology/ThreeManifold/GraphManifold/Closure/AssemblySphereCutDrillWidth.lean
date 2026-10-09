import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreSeparatedWidth
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreCollarAvoidance

/-!
# Chapter-14 assembly, L2-relative DRILL (a): one collar width for a drilled presentation with ports

Lane ASM-L2b, row DRILL (relative fibre drilling; handback `build-logs/worker-ASM-L2.md` §2(a)).
The closed drilling `RawGraphPresentation.exists_rawFibreExcision` (`Closure/RawFibreExcision.lean:39`)
shrinks only the pairing collars (`exists_fibreSeparatedWidth`, `Closure/FibreSeparatedWidth.lean:45`)
because a closed carrier has no ports. With ports, the external collars of the cut carrier and of
the carrier itself must avoid the drilled tube as well; this file gives ONE width `δ` for all of
them, so that the retained ports are reparametrized by the same recorded shrinking
`p ↦ (p.1, δ • p.2)`.

* `halfSpaceScale_comp`, `shrinkHalfCollar_apply_of_le`: shrinking by a smaller width factors
  through shrinking by a larger one.
* `isCompact_image_closedRadius`: the closed radius-two tube of a regular fibre tube is compact.
* `exists_fibreRelativeWidth`: the common width.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- Two half-space scalings compose to the scaling by the product. -/
theorem halfSpaceScale_comp {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') (s : EuclideanHalfSpace 1) :
    halfSpaceScale hδ (halfSpaceScale hδ' s) = halfSpaceScale (mul_pos hδ hδ') s := by
  change DifferentialGeometry.Topology.Manifold.halfSpaceOneLift (δ * (halfSpaceScale hδ' s).1 0) =
    DifferentialGeometry.Topology.Manifold.halfSpaceOneLift ((δ * δ') * s.1 0)
  rw [halfSpaceScale_coord, mul_assoc]

/-- Shrinking a half collar by a smaller width factors through the shrinking by a larger width. -/
theorem shrinkHalfCollar_apply_of_le {N : Type*} [TopologicalSpace N] {H : Type*}
    [TopologicalSpace H] {J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H} [ChartedSpace H N]
    {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ')
    (c : PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞)
    (p : Torus × EuclideanHalfSpace 1) :
    shrinkHalfCollar hδ' c p =
      shrinkHalfCollar hδ c (p.1, halfSpaceScale (div_pos hδ' hδ) p.2) := by
  rw [shrinkHalfCollar_apply, shrinkHalfCollar_apply, halfSpaceScale_comp]
  have hm : δ * (δ' / δ) = δ' := by field_simp
  congr 2
  change DifferentialGeometry.Topology.Manifold.halfSpaceOneLift (δ' * p.2.1 0) = DifferentialGeometry.Topology.Manifold.halfSpaceOneLift ((δ * (δ' / δ)) * p.2.1 0)
  rw [hm]

/-- The closed radius-two tube of a regular fibre tube is compact. -/
theorem isCompact_image_closedRadius {N : Type*} [TopologicalSpace N] {H : Type*}
    [TopologicalSpace H] {J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H} [ChartedSpace H N]
    (ψ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) J (PlaneLift.{u} × Circle) N ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ ψ.source) :
    IsCompact (ψ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2}) := by
  have hc : IsCompact {z : PlaneLift.{u} | ‖z.down‖ ≤ 2} := by
    have he : {z : PlaneLift.{u} | ‖z.down‖ ≤ 2} =
        (Homeomorph.ulift.symm : ℂ ≃ₜ PlaneLift.{u}) '' Metric.closedBall 0 2 := by
      ext z
      rcases z with ⟨z⟩
      simp [Metric.mem_closedBall, dist_zero_right, Homeomorph.ulift]
    rw [he]
    exact (isCompact_closedBall (0 : ℂ) 2).image Homeomorph.ulift.symm.continuous
  have hp : IsCompact {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
    have he : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} =
        {z : PlaneLift.{u} | ‖z.down‖ ≤ 2} ×ˢ univ := by ext p; simp
    rw [he]
    exact hc.prod isCompact_univ
  exact hp.image_of_continuousOn (ψ.contMDiffOn.continuousOn.mono
    (fun p hp => h3 (by change ‖p.1.down‖ ≤ 2 at hp; change ‖p.1.down‖ ≤ 3; linarith)))

/-- Pointwise avoidance by a shrunk collar passes to every smaller width. -/
theorem shrinkHalfCollar_notMem_of_le {N : Type*} [TopologicalSpace N] {H : Type*}
    [TopologicalSpace H] {J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H} [ChartedSpace H N]
    {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ') (hδδ' : δ' ≤ δ)
    (c : PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞) {K : Set N}
    (hav : ∀ p, p ∈ halfCollarSource → shrinkHalfCollar hδ c p ∉ K)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    shrinkHalfCollar hδ' c p ∉ K := by
  rw [shrinkHalfCollar_apply_of_le hδ hδ' c p]
  apply hav
  exact halfSpaceScale_mem (div_pos hδ' hδ) ((div_le_one hδ).mpr hδδ') hp

/-- The target of a shrunk collar avoids a set that its points avoid. -/
theorem shrinkHalfCollar_target_subset_compl {N : Type*} [TopologicalSpace N] {H : Type*}
    [TopologicalSpace H] {J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H} [ChartedSpace H N]
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {c : PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞}
    (hc : c.source = halfCollarSource) {K : Set N}
    (hav : ∀ p, p ∈ halfCollarSource → shrinkHalfCollar hδ c p ∉ K) :
    (shrinkHalfCollar hδ c).target ⊆ Kᶜ := by
  intro x hx
  have hs : (shrinkHalfCollar hδ c).source = halfCollarSource := shrinkHalfCollar_source hδ hδ1 hc
  have hp : (shrinkHalfCollar hδ c).symm x ∈ halfCollarSource :=
    hs ▸ (shrinkHalfCollar hδ c).map_target hx
  have h := hav ((shrinkHalfCollar hδ c).symm x) hp
  exact (shrinkHalfCollar hδ c).toPartialEquiv.right_inv hx ▸ h

/-- **One width for a drilled presentation with ports.** A single `δ ∈ (0, 1]` shrinks the pairing
collars and the external collars of the cut carrier off the closed radius-two tube, and the external
collars of the carrier off the transported closed radius-two tube. -/
theorem exists_fibreRelativeWidth {W : CompactCarrier.{u}} (G : RawGraphPresentation W)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) G.cutCarrier.model
      (PlaneLift.{u} × Circle) G.cutCarrier.Carrier ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (hI : φ.target ⊆ G.cutCarrier.interior) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧
      (∀ j, (shrinkHalfCollar hδ (G.pairing.leftCollar j)).target ⊆
        (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ) ∧
      (∀ j, (shrinkHalfCollar hδ (G.pairing.rightCollar j)).target ⊆
        (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ) ∧
      (∀ j, (shrinkHalfCollar hδ (G.cutExternal.collar j)).target ⊆
        (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ) ∧
      (∀ j, (shrinkHalfCollar hδ (G.external.collar j)).target ⊆
        (G.transportRegularFibreTube φ h3 hI ''
          {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ) := by
  let T := φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2}
  let ψ := G.transportRegularFibreTube φ h3 hI
  let TW := ψ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2}
  -- the cut-side family: pairing collars and external collars of the cut carrier
  let c : (Fin G.pairing.count × Bool) ⊕ Fin G.externalCount →
      PartialDiffeomorph halfCollarModel G.cutCarrier.model
        (Torus × EuclideanHalfSpace 1) G.cutCarrier.Carrier ∞ :=
    Sum.elim (fun a => if a.2 then G.pairing.leftCollar a.1 else G.pairing.rightCollar a.1)
      G.cutExternal.collar
  have hc (a : (Fin G.pairing.count × Bool) ⊕ Fin G.externalCount) :
      (c a).source = halfCollarSource := by
    rcases a with ⟨j, b⟩ | j
    · cases b
      · exact G.pairing.right_source j
      · exact G.pairing.left_source j
    · exact G.cutExternal.source_eq j
  have hb (a : (Fin G.pairing.count × Bool) ⊕ Fin G.externalCount) (t : Torus) :
      G.cutCarrier.model.IsBoundaryPoint (c a (t, halfZero)) := by
    rcases a with ⟨j, b⟩ | j
    · change c (Sum.inl (j, b)) (t, halfZero) ∈ G.cutCarrier.model.boundary G.cutCarrier.Carrier
      rw [G.cut_boundary_exhausted]
      refine Or.inl (mem_iUnion.mpr ⟨j, ?_⟩)
      cases b
      · change G.pairing.rightCollar j (t, halfZero) ∈ G.pairing.gluing.block j
        rw [G.pairing.right_zero]
        exact Or.inr (G.pairing.rightParam j t).property
      · change G.pairing.leftCollar j (t, halfZero) ∈ G.pairing.gluing.block j
        rw [G.pairing.left_zero]
        exact Or.inl (G.pairing.leftParam j t).property
    · exact G.cutExternal.boundary_zero j t
  have hTI : T ⊆ G.cutCarrier.interior := by
    rintro x ⟨p, hp, rfl⟩
    exact hI (φ.map_source (h3 (by
      change ‖p.1.down‖ ≤ 2 at hp
      change ‖p.1.down‖ ≤ 3
      linarith)))
  have hψ3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ ψ.source := by
    rw [G.transportRegularFibreTube_source φ h3 hI]
    exact h3
  have hTWI : TW ⊆ W.interior := by
    rintro x ⟨p, hp, rfl⟩
    exact G.transportRegularFibreTube_interior φ h3 hI (ψ.map_source (hψ3 (by
      change ‖p.1.down‖ ≤ 2 at hp
      change ‖p.1.down‖ ≤ 3
      linarith)))
  obtain ⟨δ₁, hδ₁, -, hav₁⟩ := exists_shrinkHalfCollars_avoiding_compact c hc hb
    (isCompact_image_closedRadius φ h3) hTI
  obtain ⟨δ₂, hδ₂, -, hav₂⟩ := exists_shrinkHalfCollars_avoiding_compact G.external.collar
    G.external.source_eq G.external.boundary_zero (isCompact_image_closedRadius ψ hψ3) hTWI
  let δ := min (min δ₁ δ₂) 1
  have hδ : 0 < δ := lt_min (lt_min hδ₁ hδ₂) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδδ₁ : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδδ₂ : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hcut (a : (Fin G.pairing.count × Bool) ⊕ Fin G.externalCount) :
      (shrinkHalfCollar hδ (c a)).target ⊆ Tᶜ :=
    shrinkHalfCollar_target_subset_compl hδ hδ1 (hc a)
      (shrinkHalfCollar_notMem_of_le hδ₁ hδ hδδ₁ (c a) (hav₁ a))
  refine ⟨δ, hδ, hδ1, fun j => hcut (Sum.inl (j, true)), fun j => hcut (Sum.inl (j, false)),
    fun j => hcut (Sum.inr j), fun j => ?_⟩
  exact shrinkHalfCollar_target_subset_compl hδ hδ1 (G.external.source_eq j)
    (shrinkHalfCollar_notMem_of_le hδ₂ hδ hδδ₂ (G.external.collar j) (hav₂ j))

end GC.GraphManifold.Assembly
