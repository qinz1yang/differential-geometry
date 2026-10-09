import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutDrillBoundary

/-!
# Chapter-14 assembly, L2-relative DRILL (c), part 1: the ports of a drilled carrier as data

Lane ASM-L2c, row DRILL. A carrier `C` with torus ports `E` is drilled along a regular-fibre chart
`φ`: the retained carrier `K` embeds in `C` by `ι`, with a partial inverse `O` off the closed unit
tube. The old ports are transported to `K` after one recorded shrinking (`drilledPort`), and the
new radial torus is appended last (`drilledBoundaryTori`).

* `closedRadius_one_subset_two`, `subset_source_of_avoid_radiusTwo`, `radialCollar_zero`,
  `radialCollar_target_mem`: the radial collar of the new port lies in the closed radius-two tube.
* `drilledPort` with `_source`, `_apply`, `_zero`, `_target`, `_boundary`, `_disjoint`.
* `drilledBoundaryTori` with `_castSucc`, `_last`, `_image`, `_boundary`, `_disjoint_blocks`:
  the `n + 1` ports and the relative boundary decomposition (blocks, old ports, new port).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Radial

variable {C K : CompactCarrier.{u}}
  (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model (PlaneLift.{u} × Circle) C.Carrier ∞)

/-- The closed unit tube lies in the closed radius-two tube. -/
theorem closedRadius_one_subset_two :
    φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} ⊆
      φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
  apply image_mono
  intro p hp
  change ‖p.1.down‖ ≤ 1 at hp
  change ‖p.1.down‖ ≤ 2
  linarith

/-- A set off the closed radius-two tube lies in the source of the retained partial inverse. -/
theorem subset_source_of_avoid_radiusTwo
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hOs : O.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ) {T : Set C.Carrier}
    (hT : T ⊆ (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2})ᶜ) : T ⊆ O.source := by
  rw [hOs]
  intro x hx h
  exact hT hx (closedRadius_one_subset_two φ h)

/-- The zero section of the radial collar is the unit-radius torus. -/
theorem radialCollar_zero (ι : K.Carrier → C.Carrier)
    (Γ : PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓ : ∀ p, p ∈ halfCollarSource →
      ι (Γ p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (t : Torus) : ι (Γ (t, halfZero)) = φ (ULift.up (t.1 : ℂ), t.2) := by
  have he := hΓ (t, halfZero) (zero_mem_halfCollarSource t)
  change ι (Γ (t, halfZero)) = φ (ULift.up ((1 + 0 / 2) • (t.1 : ℂ)), t.2) at he
  simpa using he

/-- The radial collar of the new port lies over the closed radius-two tube. -/
theorem radialCollar_target_mem (ι : K.Carrier → C.Carrier)
    (Γ : PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓs : Γ.source = halfCollarSource)
    (hΓ : ∀ p, p ∈ halfCollarSource →
      ι (Γ p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    {x : K.Carrier} (hx : x ∈ Γ.target) :
    ι x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2} := by
  have hp : Γ.symm x ∈ halfCollarSource := hΓs ▸ Γ.map_target hx
  have hxp : Γ (Γ.symm x) = x := Γ.toPartialEquiv.right_inv hx
  have he := hΓ (Γ.symm x) hp
  rw [hxp] at he
  rw [he]
  refine ⟨_, ?_, rfl⟩
  have hn := (Γ.symm x).2.property
  change (Γ.symm x).2.val 0 < 1 at hp
  change ‖(1 + (Γ.symm x).2.val 0 / 2) • ((Γ.symm x).1.1 : ℂ)‖ ≤ 2
  rw [norm_smul, Real.norm_of_nonneg (by linarith), Circle.norm_coe, mul_one]
  linarith

end Radial

section Ports

variable {C K : CompactCarrier.{u}} {n : ℕ}

/-- An old port, shrunk by `δ` and transported to the drilled carrier through `O`. -/
def drilledPort (E : BoundaryTori C n) (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    {δ : ℝ} (hδ : 0 < δ) (j : Fin n) :
    PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞ :=
  (shrinkHalfCollar hδ (E.collar j)).trans O

theorem drilledPort_source (E : BoundaryTori C n)
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hsO : ∀ j, (shrinkHalfCollar hδ (E.collar j)).target ⊆ O.source)
    (j : Fin n) : (drilledPort E O hδ j).source = halfCollarSource :=
  transportCollar_source O _ (shrinkHalfCollar_source hδ hδ1 (E.source_eq j)) (hsO j)

theorem drilledPort_apply (E : BoundaryTori C n) {ι : K.Carrier → C.Carrier}
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsO : ∀ j, (shrinkHalfCollar hδ (E.collar j)).target ⊆ O.source) (j : Fin n)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    ι (drilledPort E O hδ j p) = shrinkHalfCollar hδ (E.collar j) p :=
  transportCollar_apply ι O hO _ (shrinkHalfCollar_source hδ hδ1 (E.source_eq j)) (hsO j) p hp

theorem drilledPort_zero (E : BoundaryTori C n) {ι : K.Carrier → C.Carrier}
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsO : ∀ j, (shrinkHalfCollar hδ (E.collar j)).target ⊆ O.source) (j : Fin n)
    (t : Torus) : ι (drilledPort E O hδ j (t, halfZero)) = E.torusMap j t := by
  rw [drilledPort_apply E O hO hδ hδ1 hsO j _ (zero_mem_halfCollarSource t),
    shrinkHalfCollar_apply, halfSpaceScale_halfZero]
  rfl

theorem drilledPort_target (E : BoundaryTori C n) {ι : K.Carrier → C.Carrier}
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ) (j : Fin n) {x : K.Carrier}
    (hx : x ∈ (drilledPort E O hδ j).target) : ι x ∈ (E.collar j).target :=
  shrinkHalfCollar_target_subset hδ (E.collar j) (transportCollar_target ι O hO _ hx)

theorem drilledPort_boundary (E : BoundaryTori C n) {ι : K.Carrier → C.Carrier}
    (hι : Injective ι) {S : Set C.Carrier}
    (hbK : ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪ S)
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsO : ∀ j, (shrinkHalfCollar hδ (E.collar j)).target ⊆ O.source) (j : Fin n)
    (t : Torus) : K.model.IsBoundaryPoint (drilledPort E O hδ j (t, halfZero)) := by
  apply isBoundaryPoint_of_image_boundary hι hbK
  rw [drilledPort_zero E O hO hδ hδ1 hsO j t]
  exact E.boundary_zero j t

theorem drilledPort_disjoint (E : BoundaryTori C n) {ι : K.Carrier → C.Carrier}
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ) :
    Pairwise fun i j => Disjoint (drilledPort E O hδ i).target (drilledPort E O hδ j).target := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact Set.disjoint_left.mp (E.disjoint hij) (drilledPort_target E O hO hδ i hxi)
    (drilledPort_target E O hO hδ j hxj)

/-- **The `n + 1` ports of a drilled carrier**: the transported old ports, then the new port. -/
def drilledBoundaryTori (E : BoundaryTori C n) {ι : K.Carrier → C.Carrier} (hι : Injective ι)
    {S : Set C.Carrier}
    (hbK : ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪ S)
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsO : ∀ j, (shrinkHalfCollar hδ (E.collar j)).target ⊆ O.source)
    (Γ : PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓs : Γ.source = halfCollarSource) (hΓb : ∀ t, K.model.IsBoundaryPoint (Γ (t, halfZero)))
    (hΓd : ∀ j, Disjoint (drilledPort E O hδ j).target Γ.target) : BoundaryTori K (n + 1) :=
  appendBoundaryTori (drilledPort E O hδ) (drilledPort_source E O hδ hδ1 hsO)
    (drilledPort_boundary E hι hbK O hO hδ hδ1 hsO) (drilledPort_disjoint E O hO hδ) Γ hΓs hΓb hΓd

theorem drilledBoundaryTori_castSucc (E : BoundaryTori C n) {ι : K.Carrier → C.Carrier}
    (hι : Injective ι) {S : Set C.Carrier}
    (hbK : ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪ S)
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsO : ∀ j, (shrinkHalfCollar hδ (E.collar j)).target ⊆ O.source)
    (Γ : PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓs : Γ.source = halfCollarSource) (hΓb : ∀ t, K.model.IsBoundaryPoint (Γ (t, halfZero)))
    (hΓd : ∀ j, Disjoint (drilledPort E O hδ j).target Γ.target) (j : Fin n) :
    (drilledBoundaryTori E hι hbK O hO hδ hδ1 hsO Γ hΓs hΓb hΓd).collar (Fin.castSucc j) =
      drilledPort E O hδ j := by
  simp only [drilledBoundaryTori, appendBoundaryTori, Fin.lastCases_castSucc]

theorem drilledBoundaryTori_last (E : BoundaryTori C n) {ι : K.Carrier → C.Carrier}
    (hι : Injective ι) {S : Set C.Carrier}
    (hbK : ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪ S)
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsO : ∀ j, (shrinkHalfCollar hδ (E.collar j)).target ⊆ O.source)
    (Γ : PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓs : Γ.source = halfCollarSource) (hΓb : ∀ t, K.model.IsBoundaryPoint (Γ (t, halfZero)))
    (hΓd : ∀ j, Disjoint (drilledPort E O hδ j).target Γ.target) :
    (drilledBoundaryTori E hι hbK O hO hδ hδ1 hsO Γ hΓs hΓb hΓd).collar (Fin.last n) = Γ := by
  simp only [drilledBoundaryTori, appendBoundaryTori, Fin.lastCases_last]

theorem drilledBoundaryTori_image (E : BoundaryTori C n) {ι : K.Carrier → C.Carrier}
    (hι : Injective ι) {S : Set C.Carrier}
    (hbK : ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪ S)
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsO : ∀ j, (shrinkHalfCollar hδ (E.collar j)).target ⊆ O.source)
    (Γ : PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓs : Γ.source = halfCollarSource) (hΓb : ∀ t, K.model.IsBoundaryPoint (Γ (t, halfZero)))
    (hΓd : ∀ j, Disjoint (drilledPort E O hδ j).target Γ.target) :
    (drilledBoundaryTori E hι hbK O hO hδ hδ1 hsO Γ hΓs hΓb hΓd).image =
      (⋃ j, range fun t : Torus => drilledPort E O hδ j (t, halfZero)) ∪
        range fun t : Torus => Γ (t, halfZero) :=
  appendBoundaryTori_image _ _ _ _ _ _ _ _

/-- **Relative boundary of the drilled carrier**: blocks, transported old ports, new port. -/
theorem drilledBoundaryTori_boundary (E : BoundaryTori C n) {ι : K.Carrier → C.Carrier}
    (hι : Injective ι) (newC : Torus → C.Carrier)
    (hbK : ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪ range newC)
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsO : ∀ j, (shrinkHalfCollar hδ (E.collar j)).target ⊆ O.source)
    (Γ : PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓs : Γ.source = halfCollarSource) (hΓb : ∀ t, K.model.IsBoundaryPoint (Γ (t, halfZero)))
    (hΓd : ∀ j, Disjoint (drilledPort E O hδ j).target Γ.target)
    (hnew : ∀ t, ι (Γ (t, halfZero)) = newC t) {m : ℕ} (BC : Fin m → Set C.Carrier)
    (BK : Fin m → Set K.Carrier) (hblock : ∀ j x, x ∈ BK j ↔ ι x ∈ BC j)
    (hbC : C.model.boundary C.Carrier = (⋃ j, BC j) ∪ E.image) :
    K.model.boundary K.Carrier =
      (⋃ j, BK j) ∪ (drilledBoundaryTori E hι hbK O hO hδ hδ1 hsO Γ hΓs hΓb hΓd).image := by
  rw [drilledBoundaryTori_image]
  exact boundary_eq_of_embedding_relative hι BC BK hblock E.torusMap
    (fun j t => drilledPort E O hδ j (t, halfZero)) (drilledPort_zero E O hO hδ hδ1 hsO)
    newC (fun t => Γ (t, halfZero)) hnew hbC hbK

/-- The blocks of the drilled carrier avoid all of its ports. -/
theorem drilledBoundaryTori_disjoint_blocks (E : BoundaryTori C n) {ι : K.Carrier → C.Carrier}
    (hι : Injective ι) {S : Set C.Carrier}
    (hbK : ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪ S)
    (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞)
    (hO : ∀ x, x ∈ O.source → ι (O x) = x) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsO : ∀ j, (shrinkHalfCollar hδ (E.collar j)).target ⊆ O.source)
    (Γ : PartialDiffeomorph halfCollarModel K.model (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (hΓs : Γ.source = halfCollarSource) (hΓb : ∀ t, K.model.IsBoundaryPoint (Γ (t, halfZero)))
    (hΓd : ∀ j, Disjoint (drilledPort E O hδ j).target Γ.target) {m : ℕ}
    (BC : Fin m → Set C.Carrier) (BK : Fin m → Set K.Carrier)
    (hblock : ∀ j x, x ∈ BK j → ι x ∈ BC j) (hdC : Disjoint (⋃ j, BC j) E.image)
    (hnewC : ∀ t, ι (Γ (t, halfZero)) ∉ ⋃ j, BC j) :
    Disjoint (⋃ j, BK j) (drilledBoundaryTori E hι hbK O hO hδ hδ1 hsO Γ hΓs hΓb hΓd).image := by
  rw [drilledBoundaryTori_image, Set.disjoint_left]
  intro x hx hx'
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  have hC : ι x ∈ ⋃ j, BC j := mem_iUnion.mpr ⟨j, hblock j x hj⟩
  rcases hx' with hx' | ⟨t, rfl⟩
  · obtain ⟨k, t, rfl⟩ := mem_iUnion.mp hx'
    rw [drilledPort_zero E O hO hδ hδ1 hsO k t] at hC
    exact Set.disjoint_left.mp hdC hC (mem_iUnion.mpr ⟨k, t, rfl⟩)
  · exact hnewC t hC

end Ports

end GC.GraphManifold.Assembly
