import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelAdapterSep
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelAdapterRadial
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelAdapterImmersion
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport

/-!
# Chapter-14 assembly, relative COMPARE side adapters (e2): the non-separating placement

Lane ASM-L2f, group G1. With one capped component, the capped carrier `Q` itself is connected and
carries a raw presentation. It is drilled twice (`exists_relativeRawAmbientExcision`); the second
drill shrinks the radial port of the first drilled tube by `δ₂`, which the radial reparametrization
`exists_tubeRadial` of that tube absorbs; the second tube is read in `Q` through the partial inverse
of the first drill. The shell chart of the first cut sphere is placed by G2 in `Q`, the shell chart
of the second one by G2 in the complement of the first placed ball (`connectedSpace_compl_ballImage`)
and extended by the identity.

* `solidFill_norm_le`, `mem_range_torus_of_mem_closedTube`, `Drill.mem_boundary_of_mem_closedTube`,
  `Drill.mem_interior_of_mem_interior`: points of a drilled carrier on the closed unit tube.
* `diffeomorphOfEqUniv`: an open subset equal to the whole manifold.
* `image_eq_self_of_mem_iff`: a surjection preserving a set maps it onto itself.
* `SphereCutCapped.shellChart_closedBall_subset`, `shellChart_closedBall_disjoint`: the closed
  radius-two shell balls of the two cut spheres are disjoint.
* `exists_nonseparatingPlacement`: the frozen G6 side adapter (ASM-L2e `Targets.lean`), without
  its unused hypothesis `[ConnectedSpace W.Carrier]`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- A point of the closed unit tube off the open unit tube is on the unit torus. -/
theorem mem_range_torus_of_mem_closedTube {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E3 H} [TopologicalSpace M] [ChartedSpace H M]
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) I (PlaneLift.{u} × Circle) M ∞) {y : M}
    (h1 : y ∈ φ '' {p | ‖p.1.down‖ ≤ 1}) (h2 : y ∉ φ '' {p | ‖p.1.down‖ < 1}) :
    y ∈ range (fun τ : Torus => φ (ULift.up (τ.1 : ℂ), τ.2)) := by
  obtain ⟨p, hp, rfl⟩ := h1
  have hn : ‖p.1.down‖ = 1 := le_antisymm hp (not_lt.mp fun h => h2 ⟨p, h, rfl⟩)
  exact ⟨(⟨p.1.down, mem_sphere_zero_iff_norm.mpr hn⟩, p.2), rfl⟩

/-- The point of the plane factor filled by a point of the solid torus is in the closed unit
tube. -/
theorem solidFill_norm_le (y : solidSet.{u}) :
    ((ULift.up (y.val.1.down / 3), y.val.2) : PlaneLift.{u} × Circle) ∈
      {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} := by
  have hy := (mem_solidSet_iff y.val).mp y.property
  change ‖y.val.1.down / 3‖ ≤ 1
  rw [norm_div, Complex.norm_ofNat]
  linarith

namespace Drill

variable {L W : CompactCarrier.{u}} {η : L.Carrier → W.Carrier}
  {φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) W.model (PlaneLift.{u} × Circle) W.Carrier ∞}

/-- A point of a drilled carrier sent onto the closed unit tube is a boundary point. -/
theorem mem_boundary_of_mem_closedTube (hη : Injective η)
    (hr : range η = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ)
    (hb : η '' L.model.boundary L.Carrier = W.model.boundary W.Carrier ∪
      range (fun τ : Torus => φ (ULift.up (τ.1 : ℂ), τ.2)))
    {z : L.Carrier} (hz : η z ∈ φ '' {p | ‖p.1.down‖ ≤ 1}) :
    z ∈ L.model.boundary L.Carrier := by
  have hz' : η z ∉ φ '' {p | ‖p.1.down‖ < 1} := by
    have h : η z ∈ range η := mem_range_self z
    rw [hr] at h
    exact h
  have hT := mem_range_torus_of_mem_closedTube φ hz hz'
  have hm : η z ∈ η '' L.model.boundary L.Carrier := by
    rw [hb]
    exact Or.inr hT
  obtain ⟨b, hb', he⟩ := hm
  exact hη he ▸ hb'

/-- A drill embedding sends interior points to interior points. -/
theorem mem_interior_of_mem_interior (hη : Injective η)
    (hb : η '' L.model.boundary L.Carrier = W.model.boundary W.Carrier ∪
      range (fun τ : Torus => φ (ULift.up (τ.1 : ℂ), τ.2)))
    {z : L.Carrier} (hz : z ∈ L.model.interior L.Carrier) :
    η z ∈ W.model.interior W.Carrier := by
  rw [← W.model.compl_boundary]
  intro hzb
  have hm : η z ∈ η '' L.model.boundary L.Carrier := by
    rw [hb]
    exact Or.inl hzb
  obtain ⟨b, hb', he⟩ := hm
  rw [← L.model.compl_boundary] at hz
  exact hz (hη he ▸ hb')

/-- An interior point of a drilled carrier is sent off the closed unit tube. -/
theorem not_mem_closedTube_of_mem_interior (hη : Injective η)
    (hr : range η = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ)
    (hb : η '' L.model.boundary L.Carrier = W.model.boundary W.Carrier ∪
      range (fun τ : Torus => φ (ULift.up (τ.1 : ℂ), τ.2)))
    {z : L.Carrier} (hz : z ∈ L.model.interior L.Carrier) :
    η z ∉ φ '' {p | ‖p.1.down‖ ≤ 1} := by
  intro h
  have hzb := mem_boundary_of_mem_closedTube hη hr hb h
  rw [← L.model.compl_boundary] at hz
  exact hz hzb

end Drill

/-- An open subset equal to the whole manifold, as a diffeomorphism onto the manifold. -/
def diffeomorphOfEqUniv {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = univ) : U ≃ₘ⟮I, I⟯ M where
  toFun := Subtype.val
  invFun y := ⟨y, by rw [← SetLike.mem_coe, hU]; exact mem_univ y⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp contMDiff_id

/-- A surjection which preserves membership in a set maps the set onto itself. -/
theorem image_eq_self_of_mem_iff {α : Type*} {f g : α → α} (hfg : ∀ y, f (g y) = y) {A : Set α}
    (h : ∀ p, f p ∈ A ↔ p ∈ A) : f '' A = A := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (h p).mpr hp
  · intro hy
    refine ⟨g y, (h _).mp ?_, hfg y⟩
    rw [hfg y]
    exact hy

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- The closed radius-two shell ball of the cut sphere `t` lies in its cap and its cut collar. -/
theorem shellChart_closedBall_subset (t : Fin 2) :
    X.shellChart t '' closedBall 0 2 ⊆ range (X.capping.cap (Fin.cast X.h2.symm t)) ∪
      X.capping.core '' (X.B.sphere (Fin.cast X.h2.symm t)).target := by
  rintro _ ⟨x, hx, rfl⟩
  by_cases h1 : ‖x‖ < 1
  · have hb : X.shellChart t x ∈ X.shellChart t '' ball 0 1 := ⟨x, mem_ball_zero_iff.mpr h1, rfl⟩
    rw [X.shellChart_image_ball] at hb
    rcases hb with hb | ⟨_, ⟨p, hp, rfl⟩, he⟩
    · exact Or.inl hb
    · refine Or.inr ⟨_, (X.B.sphere _).map_source ?_, he⟩
      rw [X.B.sphere_source]
      change p.2.val 0 < 1
      have := X.shellBase_add_slope_lt_one t
      have := X.shellSlope_pos t
      have hp' : p.2.val 0 < X.shellBase t := hp
      linarith
  · have hx0 : x ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      exact h1 zero_lt_one
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let z : sphere (0 : E3) 1 := ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']⟩
    have hxz : x = ‖x‖ • (z : E3) := by
      change x = ‖x‖ • ‖x‖⁻¹ • x
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hr2 : ‖x‖ ≤ 2 := mem_closedBall_zero_iff.mp hx
    rw [hxz, X.shellChart_smul t z (not_lt.mp h1) hr2]
    refine Or.inr ⟨_, (X.B.sphere _).map_source ?_, rfl⟩
    rw [X.B.sphere_source]
    change (halfSpaceOneLift (X.shellBase t + X.shellSlope t * (‖x‖ - 1))).val 0 < 1
    rw [shellLift_coord, max_eq_left (add_nonneg (X.shellBase_pos t).le
      (mul_nonneg (X.shellSlope_pos t).le (by linarith)))]
    have := X.shellBase_add_slope_lt_one t
    have := X.shellSlope_pos t
    nlinarith

/-- **The two closed shell balls are disjoint.** -/
theorem shellChart_closedBall_disjoint :
    Disjoint (X.shellChart 0 '' closedBall 0 2) (X.shellChart 1 '' closedBall 0 2) := by
  have hne : Fin.cast X.h2.symm 0 ≠ Fin.cast X.h2.symm 1 := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hcore : Injective X.capping.core := X.capping.core_embedding.isEmbedding.injective
  have hcap_core : ∀ {i j : Fin X.B.sphereCount}, i ≠ j → ∀ y : ClosedCell 3,
      ∀ q ∈ (X.B.sphere j).target, X.capping.cap i y ≠ X.capping.core q := by
    intro i j hij y q hq he
    have hm : X.capping.cap i y ∈ range X.capping.core ∩ range (X.capping.cap i) :=
      ⟨⟨q, he.symm⟩, ⟨y, rfl⟩⟩
    rw [X.capping.core_cap_intersection] at hm
    obtain ⟨w, hw⟩ := hm
    rw [← hw] at he
    have hq' := hcore he
    have hs : X.B.sphere i (w, halfZero) ∈ (X.B.sphere i).target := by
      apply (X.B.sphere i).map_source
      rw [X.B.sphere_source]
      change (0 : ℝ) < 1
      norm_num
    exact disjoint_left.mp (X.B.sphere_disjoint hij) hs (hq' ▸ hq)
  refine disjoint_left.mpr fun y h0 h1 => ?_
  rcases X.shellChart_closedBall_subset 0 h0 with ⟨a, rfl⟩ | ⟨q, hq, rfl⟩ <;>
    rcases X.shellChart_closedBall_subset 1 h1 with ⟨b, hb⟩ | ⟨q', hq', hq'e⟩
  · exact disjoint_left.mp (X.capping.cap_disjoint hne) ⟨a, rfl⟩ ⟨b, hb⟩
  · exact hcap_core hne a q' hq' hq'e.symm
  · exact hcap_core hne.symm b q hq hb
  · have he := hcore hq'e
    exact disjoint_left.mp (X.B.sphere_disjoint hne) hq (he ▸ hq')

end SphereCutCapped

/-- **G6 side adapter (non-separating)**, the frozen text of ASM-L2e (`Targets.lean`) without its
unused hypothesis `[ConnectedSpace W.Carrier]` (one capped component already makes the capped
carrier connected); the verbatim form is checked in `build-logs/scratch/ASM-L2f/CheckL2eVerbatim.lean`. -/
theorem exists_nonseparatingPlacement (W : CompactCarrier.{u})
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
    (X : SphereCutCapped W S E) (DQ : X.Q.Components) (h1 : DQ.count = 1)
    (R : ∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i))
    (v : Fin 2 → PartialDiffeomorph (𝓡 3) (𝓡∂ 3) E3 solidSet.{u} ∞)
    (hv : ∀ t, closedBall 0 2 ⊆ (v t).source)
    (hvI : ∀ t, (v t).target ⊆ (𝓡∂ 3).interior solidSet.{u}) :
    ∃ (Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier) (K : Set X.Q.Carrier)
      (φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
        (PlaneLift.{u} × Circle) X.Q.Carrier ∞)
      (L : CompactCarrier.{u}) (η : L.Carrier → X.Q.Carrier)
      (Γ : Fin 2 → PartialDiffeomorph halfCollarModel L.model
        (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
      (c : Fin 2 → PartialDiffeomorph (𝓡 3) X.Q.model E3 X.Q.Carrier ∞) (s₀ μ : Fin 2 → ℝ)
      (hs₀ : ∀ t, 0 < s₀ t) (hμ : ∀ t, 0 < μ t)
      (Θ : Fin 2 → solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}) (ε : Fin 2 → Bool)
      (r : Fin 2 → ℝ),
      IsCompact K ∧ K ⊆ X.Q.interior ∧ (∀ x, x ∉ K → Ψ x = x) ∧
      (∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source) ∧
      (∀ t, (φ t).target ⊆ X.Q.interior) ∧
      Disjoint (φ 0 '' {p | ‖p.1.down‖ ≤ 1}) (φ 1 '' {p | ‖p.1.down‖ ≤ 1}) ∧
      L.kind = .withBoundary ∧ ConnectedSpace L.Carrier ∧
      Nonempty (RawGraphPresentation L) ∧ IsSmoothEmbedding L.model X.Q.model ∞ η ∧
      (∀ x, Bijective (mfderiv L.model X.Q.model η x)) ∧
      range η = (⋃ t, φ t '' {p | ‖p.1.down‖ < 1})ᶜ ∧
      (∀ t, (Γ t).source = halfCollarSource) ∧
      (∀ t p, p ∈ halfCollarSource →
        η (Γ t p) = φ t (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) ∧
      η '' L.model.boundary L.Carrier = X.Q.model.boundary X.Q.Carrier ∪
        ⋃ t, range (fun τ : Torus => φ t (ULift.up (τ.1 : ℂ), τ.2)) ∧
      (∀ t, s₀ t + μ t < 1) ∧ (∀ t, closedBall 0 2 ⊆ (c t).source) ∧
      (∀ t (z : sphere (0 : E3) 1) (r : ℝ) (hr : 1 ≤ r), r ≤ 2 →
        c t (r • (z : E3)) = X.capping.core (X.B.sphere (Fin.cast X.h2.symm t)
          (ULift.up z, halfPoint (s₀ t + μ t * (r - 1))
            (add_nonneg (hs₀ t).le (mul_nonneg (hμ t).le (sub_nonneg.mpr hr)))))) ∧
      (∀ t, c t '' ball 0 1 = range (X.capping.cap (Fin.cast X.h2.symm t)) ∪
        X.capping.core '' (X.B.sphere (Fin.cast X.h2.symm t) '' {p | p.2.val 0 < s₀ t})) ∧
      (∀ t, r t < 3) ∧
      (∀ t (x : solidSet.{u}), r t ≤ ‖x.val.1.down‖ → (Θ t x).val =
        if ε t then (ULift.up ((starRingEnd ℂ) x.val.1.down), x.val.2) else x.val) ∧
      ∀ t, ∀ x ∈ closedBall (0 : E3) 2, Ψ (c t x) = solidTubeFill (φ t) (Θ t (v t x)) := by
  -- the capped carrier is connected and carries a raw presentation
  let i0 : Fin DQ.count := ⟨0, by omega⟩
  have huniv : (DQ.piece i0 : Set X.Q.Carrier) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := exists_mem_componentsPiece DQ x
    have hi0 : i = i0 := Fin.ext (by have := i.isLt; omega)
    exact hi0 ▸ hi
  have hconn0 : ConnectedSpace (DQ.piece i0) := DQ.connected i0
  let eU := diffeomorphOfEqUniv (I := X.Q.model) (DQ.piece i0) huniv
  have : ConnectedSpace X.Q.Carrier := eU.surjective.connectedSpace eU.continuous
  have : PreconnectedSpace (GC.Topology.componentCarrier X.Q DQ i0).Carrier :=
    hconn0.toPreconnectedSpace
  obtain ⟨G⟩ := nonempty_rawGraphPresentation_of_carrierDiffeomorph (R i0) eU
  -- the two drills
  obtain ⟨φ₀, h3₀, hI₀, L₁, η₁, R₁, he₁, δ₁, hδ₁, O₁, -, hk₁, hc₁, hη₁, hr₁, hbij₁, hB₁, hO₁s,
    hO₁, hO₁t, -, hnew₁⟩ := exists_relativeRawAmbientExcision X.Q G
  have := hc₁
  obtain ⟨φ₁', h3₁, hI₁, L₂, η₂, R₂, he₂, δ₂, hδ₂, O₂, hδ₂1, hk₂, hc₂, hη₂, hr₂, hbij₂, hB₂,
    hO₂s, hO₂, hO₂t, hold₂, hnew₂⟩ := exists_relativeRawAmbientExcision L₁ R₁
  obtain ⟨Λ, -, hΛlt, hΛle, hΛ3, hΛband⟩ := exists_tubeRadial.{u} hδ₂ hδ₂1
  have hinj₁ : Injective η₁ := hη₁.isEmbedding.injective
  -- the first tube, reparametrized
  let ψ₀ := Λ.toPartialDiffeomorph.trans φ₀
  have hψ₀ : ∀ p, ψ₀ p = φ₀ (Λ p) := fun p => rfl
  have h3ψ₀ : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ ψ₀.source :=
    fun p hp => ⟨mem_univ _, h3₀ (hΛ3 p hp)⟩
  have hIψ₀ : ψ₀.target ⊆ X.Q.interior := fun y hy => hI₀ hy.1
  have himg₀ : ∀ {A : Set (PlaneLift.{u} × Circle)}, (∀ p, Λ p ∈ A ↔ p ∈ A) →
      ψ₀ '' A = φ₀ '' A := by
    intro A hA
    rw [show (ψ₀ : PlaneLift.{u} × Circle → X.Q.Carrier) = φ₀ ∘ Λ from rfl, image_comp,
      image_eq_self_of_mem_iff (fun y => Λ.apply_symm_apply y) hA]
  have hlt₀ := himg₀ (A := {p | ‖p.1.down‖ < 1}) hΛlt
  have hle₀ := himg₀ (A := {p | ‖p.1.down‖ ≤ 1}) hΛle
  have htor₀ : ∀ τ : Torus, ψ₀ (ULift.up (τ.1 : ℂ), τ.2) = φ₀ (ULift.up (τ.1 : ℂ), τ.2) := by
    intro τ
    have h := hΛband τ.1 τ.2 0 le_rfl
    simp only [zero_div, add_zero, mul_zero, one_smul] at h
    rw [hψ₀, h]
  -- the second tube, read in the capped carrier
  have hint₁ : ∀ z ∈ L₁.model.interior L₁.Carrier, z ∈ O₁.target := by
    intro z hz
    rw [hO₁t]
    exact Drill.not_mem_closedTube_of_mem_interior hinj₁ hr₁ hB₁ hz
  let ψ₁ := φ₁'.trans O₁.symm
  have hψ₁ : ∀ p ∈ φ₁'.source, ψ₁ p = η₁ (φ₁' p) := fun p hp =>
    RelativeDrill.symm_apply_of_mem_target O₁ hO₁ (hint₁ _ (hI₁ (φ₁'.map_source hp)))
  have h3ψ₁ : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ ψ₁.source :=
    fun p hp => ⟨h3₁ hp, hint₁ _ (hI₁ (φ₁'.map_source (h3₁ hp)))⟩
  have htgt₁ : ∀ y ∈ ψ₁.target, ∃ z ∈ L₁.model.interior L₁.Carrier, η₁ z = y :=
    fun y hy => ⟨O₁ y, hI₁ hy.2, hO₁ y hy.1⟩
  have hIψ₁ : ψ₁.target ⊆ X.Q.interior := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := htgt₁ y hy
    exact Drill.mem_interior_of_mem_interior hinj₁ hB₁ hz
  have hoff₁ : ∀ y ∈ ψ₁.target, y ∉ φ₀ '' {p | ‖p.1.down‖ ≤ 1} := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := htgt₁ y hy
    exact Drill.not_mem_closedTube_of_mem_interior hinj₁ hr₁ hB₁ hz
  have himg₁ : ∀ {A : Set (PlaneLift.{u} × Circle)}, A ⊆ {p | ‖p.1.down‖ ≤ 3} →
      ψ₁ '' A = η₁ '' (φ₁' '' A) := by
    intro A hA
    rw [image_image]
    exact image_congr fun p hp => hψ₁ p (h3₁ (hA hp))
  have hle13 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} ⊆ {p | ‖p.1.down‖ ≤ 3} :=
    fun p (hp : ‖p.1.down‖ ≤ 1) => show ‖p.1.down‖ ≤ 3 by linarith
  have hlt13 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1} ⊆ {p | ‖p.1.down‖ ≤ 3} :=
    fun p (hp : ‖p.1.down‖ < 1) => show ‖p.1.down‖ ≤ 3 by linarith
  have hdisj : Disjoint (ψ₀ '' {p | ‖p.1.down‖ ≤ 1}) (ψ₁ '' {p | ‖p.1.down‖ ≤ 1}) := by
    rw [hle₀, disjoint_left]
    rintro y hy0 ⟨p, hp, rfl⟩
    exact hoff₁ _ (ψ₁.map_source (h3ψ₁ (hle13 hp))) hy0
  -- the doubly drilled carrier
  have hcover : ∀ x, η₁ (η₂ x) ∈ O₁.source ∨ η₂ x ∈ O₂.source := by
    intro x
    by_cases h : η₁ (η₂ x) ∈ O₁.source
    · exact Or.inl h
    · right
      rw [hO₁s, mem_compl_iff, not_not] at h
      have hb := Drill.mem_boundary_of_mem_closedTube hinj₁ hr₁ hB₁ h
      rw [hO₂s]
      rintro ⟨p, hp, hpe⟩
      have hpi : φ₁' p ∈ L₁.model.interior L₁.Carrier := hI₁ (φ₁'.map_source (h3₁ (hle13 hp)))
      rw [hpe, ← L₁.model.compl_boundary] at hpi
      exact hpi hb
  have hO₁t' : O₁.target = η₁ ⁻¹' O₁.source := by rw [hO₁t, hO₁s]
  have hO₂t' : O₂.target = η₂ ⁻¹' O₂.source := by rw [hO₂t, hO₂s]
  have hηemb : IsSmoothEmbedding L₂.model X.Q.model ∞ (η₁ ∘ η₂) :=
    isSmoothEmbedding_comp_of_partialInverses hk₁ hk₂ hη₁ hη₂ O₁ hO₁ hO₁t' O₂ hO₂ hO₂t' hcover
  have hηbij : ∀ x, Bijective (mfderiv L₂.model X.Q.model (η₁ ∘ η₂) x) := by
    intro x
    rw [mfderiv_comp x (hη₁.contMDiff.mdifferentiableAt (by simp))
      (hη₂.contMDiff.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
    exact (hbij₁ (η₂ x)).comp (hbij₂ x)
  have hηr : range (η₁ ∘ η₂) = (⋃ t, ![ψ₀, ψ₁] t '' {p | ‖p.1.down‖ < 1})ᶜ := by
    ext y
    simp only [range_comp, hr₂, mem_compl_iff, mem_iUnion, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, not_or]
    rw [hlt₀, himg₁ hlt13]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · have h : η₁ z ∈ range η₁ := mem_range_self z
        rw [hr₁] at h
        exact h
      · rintro ⟨z', hz', he⟩
        exact hz (hinj₁ he ▸ hz')
    · rintro ⟨h0, h1⟩
      have h : y ∈ range η₁ := by
        rw [hr₁]
        exact h0
      obtain ⟨z, rfl⟩ := h
      exact ⟨z, fun hz => h1 ⟨z, hz, rfl⟩, rfl⟩
  have hηb : (η₁ ∘ η₂) '' L₂.model.boundary L₂.Carrier = X.Q.model.boundary X.Q.Carrier ∪
      ⋃ t, range (fun τ : Torus => ![ψ₀, ψ₁] t (ULift.up (τ.1 : ℂ), τ.2)) := by
    have htor₁ : η₁ '' range (fun τ : Torus => φ₁' (ULift.up (τ.1 : ℂ), τ.2)) =
        range (fun τ : Torus => ψ₁ (ULift.up (τ.1 : ℂ), τ.2)) := by
      rw [← range_comp]
      refine congrArg range (funext fun τ => (hψ₁ _ (h3₁ ?_)).symm)
      change ‖(τ.1 : ℂ)‖ ≤ 3
      rw [Circle.norm_coe]
      norm_num
    have htor₀' : range (fun τ : Torus => φ₀ (ULift.up (τ.1 : ℂ), τ.2)) =
        range (fun τ : Torus => ψ₀ (ULift.up (τ.1 : ℂ), τ.2)) :=
      congrArg range (funext fun τ => (htor₀ τ).symm)
    rw [image_comp, hB₂, image_union, hB₁, htor₁, htor₀']
    ext y
    simp only [mem_union, mem_iUnion, Fin.exists_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    tauto
  -- the two radial ports
  let Γ₀ := R₂.external.collar (Fin.cast he₂.symm (Fin.castSucc (Fin.cast he₁.symm
    (Fin.last G.externalCount))))
  let Γ₁ := R₂.external.collar (Fin.cast he₂.symm (Fin.last R₁.externalCount))
  have hΓ₀ : ∀ p, p ∈ halfCollarSource →
      η₁ (η₂ (Γ₀ p)) = ψ₀ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) := by
    intro p hp
    have hm : (p.1, halfSpaceScale hδ₂ p.2) ∈ halfCollarSource := by
      change (halfSpaceScale hδ₂ p.2).val 0 < 1
      exact halfSpaceScale_mem hδ₂ hδ₂1 hp
    rw [hold₂ _ p hp, shrinkHalfCollar_apply, hnew₁ _ hm, hψ₀,
      hΛband p.1.1 p.1.2 (p.2.val 0) p.2.property]
    change φ₀ (ULift.up ((1 + (halfSpaceScale hδ₂ p.2).val 0 / 2) • (p.1.1 : ℂ)), p.1.2) = _
    rw [halfSpaceScale_coord]
  have hΓ₁ : ∀ p, p ∈ halfCollarSource →
      η₁ (η₂ (Γ₁ p)) = ψ₁ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) := by
    intro p hp
    rw [hnew₂ p hp, hψ₁ _ (h3₁ ?_)]
    have hs0 : 0 ≤ p.2.val 0 := p.2.property
    have hs1 : p.2.val 0 < 1 := hp
    change ‖(1 + p.2.val 0 / 2) • (p.1.1 : ℂ)‖ ≤ 3
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by linarith)]
    linarith
  -- the first placement, in the capped carrier
  obtain ⟨ε₀, Ψ₀, Θ₀, K₀, r₀, hK₀, hK₀I, hfix₀, hr₀, hΘ₀, hmatch₀⟩ :=
    exists_solidPlacement ψ₀ h3ψ₀ hIψ₀ (X.shellChart 0) (X.closedBall_subset_shellChart_source 0)
      (X.shellChart_target_subset 0) (v 0) (hv 0) (hvI 0)
  -- the complement of the first placed ball
  let c₀' := (X.shellChart 0).trans Ψ₀.toPartialDiffeomorph
  have hc₀' : closedBall 0 2 ⊆ c₀'.source :=
    fun x hx => ⟨X.closedBall_subset_shellChart_source 0 hx, mem_univ _⟩
  have hB₀c : IsCompact (c₀' '' closedBall 0 2) :=
    (isCompact_closedBall 0 2).image_of_continuousOn (c₀'.contMDiffOn_toFun.continuousOn.mono hc₀')
  let V : TopologicalSpace.Opens X.Q.Carrier := ⟨(c₀' '' closedBall 0 2)ᶜ, hB₀c.isClosed.isOpen_compl⟩
  have hVconn : ConnectedSpace V := connectedSpace_compl_ballImage c₀' hc₀'
  have hB₀tube : c₀' '' closedBall 0 2 ⊆ φ₀ '' {p | ‖p.1.down‖ ≤ 1} := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hle₀]
    change Ψ₀ (X.shellChart 0 x) ∈ _
    rw [hmatch₀ x hx]
    exact solidTubeFill_mem_image ψ₀ _
  have hψ₁V : ψ₁.target ⊆ V := fun y hy hyB => hoff₁ y hy (hB₀tube hyB)
  have hneV : Nonempty V := by
    have hp0 : ((ULift.up (0 : ℂ), (1 : Circle)) : PlaneLift.{u} × Circle) ∈
        {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} := by
      change ‖(0 : ℂ)‖ ≤ 3
      norm_num
    exact ⟨⟨_, hψ₁V (ψ₁.map_source (h3ψ₁ hp0))⟩⟩
  -- the second tube in the complement
  let φV := codRestrictOpens ψ₁ V hneV
  have h3V : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φV.source := by
    rw [codRestrictOpens_source _ _ _ hψ₁V]
    exact h3ψ₁
  have hIV : φV.target ⊆ X.Q.model.interior V := by
    rw [codRestrictOpens_target]
    intro y hy
    exact (mem_interior_val_iff (I := X.Q.model) (x := y)).mp (hIψ₁ hy)
  -- the second shell chart, moved by the first placement, in the complement
  let c₁' := (X.shellChart 1).trans Ψ₀.toPartialDiffeomorph
  let U₁ := c₁'.source ∩ c₁' ⁻¹' V
  have hU₁ : IsOpen U₁ :=
    c₁'.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c₁'.open_source V.isOpen
  let c₁'' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict c₁' U₁ hU₁
  have hc₁''t : c₁''.target ⊆ V := by
    intro y hy
    have h := hy.2.2
    have hr : c₁'.toPartialEquiv (c₁'.toOpenPartialHomeomorph.symm y) = y :=
      c₁'.toPartialEquiv.right_inv hy.1
    rwa [mem_preimage, hr] at h
  have hc₁''s : closedBall 0 2 ⊆ c₁''.source := by
    intro x hx
    have hs : x ∈ c₁'.source := ⟨X.closedBall_subset_shellChart_source 1 hx, mem_univ _⟩
    refine ⟨hs, hs, ?_⟩
    rintro ⟨x', hx', he⟩
    have he' : X.shellChart 0 x' = X.shellChart 1 x := Ψ₀.injective he
    exact disjoint_left.mp X.shellChart_closedBall_disjoint ⟨x', hx', rfl⟩ (he' ▸ ⟨x, hx, rfl⟩)
  let cV := codRestrictOpens c₁'' V hneV
  have hcV : closedBall 0 2 ⊆ cV.source := by
    rw [codRestrictOpens_source _ _ _ hc₁''t]
    exact hc₁''s
  have hcIV : cV.target ⊆ X.Q.model.interior V := by
    rw [codRestrictOpens_target]
    intro y hy
    apply (mem_interior_val_iff (I := X.Q.model) (x := y)).mp
    have h1 : Ψ₀.symm y.val ∈ (X.shellChart 1).target := hy.1.2
    have h2 : Ψ₀.symm y.val ∈ X.Q.model.interior X.Q.Carrier := X.shellChart_target_subset 1 h1
    rw [← Diffeomorph.preimage_interior (by simp) Ψ₀.symm]
    exact h2
  have hcVval : ∀ x ∈ closedBall (0 : E3) 2, (cV x).val = Ψ₀ (X.shellChart 1 x) := by
    intro x hx
    rw [codRestrictOpens_apply c₁'' V hneV (hc₁''t (c₁''.map_source (hc₁''s hx)))]
    rfl
  -- the second placement, in the complement, extended by the identity
  obtain ⟨ε₁, ΨV, Θ₁, KV, r₁, hKV, hKVI, hfixV, hr₁, hΘ₁, hmatchV⟩ :=
    exists_solidPlacement (M := V) φV h3V hIV cV hcV hcIV (v 1) (hv 1) (hvI 1)
  obtain ⟨Ψ₁, hΨ₁U, hΨ₁fix⟩ := exists_extend_of_isCompact (I := X.Q.model) V ΨV KV hKV hfixV
  refine ⟨Ψ₀.trans Ψ₁, K₀ ∪ Subtype.val '' KV, ![ψ₀, ψ₁], L₂, η₁ ∘ η₂, ![Γ₀, Γ₁], X.shellChart,
    X.shellBase, X.shellSlope, X.shellBase_pos, X.shellSlope_pos, ![Θ₀, Θ₁], ![ε₀, ε₁], ![r₀, r₁],
    hK₀.union (hKV.image continuous_subtype_val), ?_, ?_,
    Fin.forall_fin_two.mpr ⟨h3ψ₀, h3ψ₁⟩, Fin.forall_fin_two.mpr ⟨hIψ₀, hIψ₁⟩, hdisj, hk₂, hc₂,
    ⟨R₂⟩, hηemb, hηbij, hηr, Fin.forall_fin_two.mpr ⟨R₂.external.source_eq _,
      R₂.external.source_eq _⟩, Fin.forall_fin_two.mpr ⟨hΓ₀, hΓ₁⟩, hηb,
    X.shellBase_add_slope_lt_one, X.closedBall_subset_shellChart_source, ?_,
    X.shellChart_image_ball, Fin.forall_fin_two.mpr ⟨hr₀, hr₁⟩,
    Fin.forall_fin_two.mpr ⟨hΘ₀, hΘ₁⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
  · refine union_subset hK₀I ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_interior_val_iff (I := X.Q.model) (x := x)).mpr (hKVI hx)
  · intro x hx
    change Ψ₁ (Ψ₀ x) = x
    rw [hfix₀ x fun h => hx (Or.inl h), hΨ₁fix x fun h => hx (Or.inr h)]
  · intro t z s hs hs2
    exact (X.exists_shell t).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1
      z s hs hs2
  · intro x hx
    change Ψ₁ (Ψ₀ (X.shellChart 0 x)) = solidTubeFill ψ₀ (Θ₀ (v 0 x))
    have hin : Ψ₀ (X.shellChart 0 x) ∈ c₀' '' closedBall 0 2 := ⟨x, hx, rfl⟩
    rw [hΨ₁fix _ fun ⟨y, _, hy⟩ => (hy ▸ y.property) hin, hmatch₀ x hx]
  · intro x hx
    change Ψ₁ (Ψ₀ (X.shellChart 1 x)) = solidTubeFill ψ₁ (Θ₁ (v 1 x))
    rw [← hcVval x hx, hΨ₁U, hmatchV x hx]
    exact codRestrictOpens_apply ψ₁ V hneV (hψ₁V (ψ₁.map_source (h3ψ₁ (hle13
      (solidFill_norm_le (Θ₁ (v 1 x)))))))

end GC.GraphManifold.Assembly
