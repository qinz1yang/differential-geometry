import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreExcision
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutSystem
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter

/-!
# Chapter-14 assembly, relative COMPARE shared seams: the radius-one torus of a placed tube

Lane ASM-L2e2, shared seam group (for G5 SEP and G6 NONSEP; any number of pieces). For a tube
`φ : PlaneLift × Circle ⇀ Q` of a carrier `Q`, a diffeomorphism `Ψ` of `Q` and a partial
diffeomorphism `F : Q ⇀ W`, the thin band of radii `(1 - κ, 1 + κ)` of the tube, read through
`Ψ⁻¹` and `F`, is a torus seam of `W`:
`σ (τ, s) = F (Ψ⁻¹ (φ ((1 + κ s) τ₁, τ₂)))` (`tubeSeam`), once the band lies in the source of `φ`
and its `Ψ⁻¹`-image in the source of `F`. The band chart is `fibreExcisionPolar` scaled by `2 κ`.

* `tubeBand κ`, `tubeSeamCollar`, `tubeSeamCollar_apply`, `tubeSeamCollar_zero`,
  `tubeSeamCollar_source`, `mem_tubeSeamCollar_target`, `tubeSeam`.
* The two half collars of the seam from given radial collars of the two sides:
  `tubeSeam_inner_lift` (a collar `(τ, s) ↦ F (Ψ⁻¹ (φ ((1 - ν s / 2) τ₁, τ₂)))`, shrunk by
  `2 κ / ν`) and `drillSeamLift` / `drillSeamLift_eq` (a collar `(τ, s) ↦ φ ((1 + s / 2) τ₁, τ₂)` of a
  carrier mapped by `η`, shrunk by `2 κ`, carried into a piece by a diffeomorphism).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The open band of radii `(1 - κ, 1 + κ)` of the tube model. -/
def tubeBand (κ : ℝ) : Set (PlaneLift.{u} × Circle) :=
  {p | 1 - κ < ‖p.1.down‖ ∧ ‖p.1.down‖ < 1 + κ}

theorem norm_smul_circle {r : ℝ} (hr : 0 ≤ r) (z : Circle) : ‖r • (z : ℂ)‖ = r := by
  rw [norm_smul, Real.norm_of_nonneg hr, Circle.norm_coe, mul_one]

theorem mem_tubeBand {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) (τ : Torus) {s : ℝ} (hs1 : -1 < s)
    (hs2 : s < 1) :
    ((ULift.up ((1 + κ * s) • (τ.1 : ℂ)), τ.2) : PlaneLift.{u} × Circle) ∈ tubeBand κ := by
  have hpos : 0 ≤ 1 + κ * s := by nlinarith
  change 1 - κ < ‖(1 + κ * s) • (τ.1 : ℂ)‖ ∧ ‖(1 + κ * s) • (τ.1 : ℂ)‖ < 1 + κ
  rw [norm_smul_circle hpos]
  constructor <;> nlinarith

theorem fibreExcisionPolar_scale {κ : ℝ} (p : Torus × ℝ) :
    CircleFibration.fibreExcisionPolar.{u} (p.1, 2 * κ * p.2) =
      ((ULift.up ((1 + κ * p.2) • (p.1.1 : ℂ)), p.1.2) : PlaneLift.{u} × Circle) := by
  change ((ULift.up ((1 + 2 * κ * p.2 / 2) • (p.1.1 : ℂ)), p.1.2) : PlaneLift.{u} × Circle) = _
  rw [show 1 + 2 * κ * p.2 / 2 = 1 + κ * p.2 by ring]

section Seam

variable {Q W : CompactCarrier.{u}}
  (F : PartialDiffeomorph Q.model W.model Q.Carrier W.Carrier ∞)
  (Ψ : Q.Carrier ≃ₘ⟮Q.model, Q.model⟯ Q.Carrier)
  (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) Q.model (PlaneLift.{u} × Circle) Q.Carrier ∞)
  {κ : ℝ} (hκ : 0 < κ)

/-- The band of the tube `φ` of radii `(1 - κ, 1 + κ)`, read through `Ψ⁻¹` and `F`, as a signed
collar. -/
def tubeSeamCollar : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞ :=
  shrinkSignedCollar (mul_pos two_pos hκ)
    (CircleFibration.fibreExcisionPolar.trans (φ.trans (Ψ.symm.toPartialDiffeomorph.trans F)))

theorem tubeSeamCollar_apply (p : Torus × ℝ) :
    tubeSeamCollar F Ψ φ hκ p =
      F (Ψ.symm (φ (ULift.up ((1 + κ * p.2) • (p.1.1 : ℂ)), p.1.2))) := by
  change F (Ψ.symm (φ (ULift.up ((1 + 2 * κ * p.2 / 2) • (p.1.1 : ℂ)), p.1.2))) = _
  rw [show 1 + 2 * κ * p.2 / 2 = 1 + κ * p.2 by ring]

theorem tubeSeamCollar_zero (τ : Torus) :
    tubeSeamCollar F Ψ φ hκ (τ, 0) = F (Ψ.symm (φ (ULift.up (τ.1 : ℂ), τ.2))) := by
  rw [tubeSeamCollar_apply, mul_zero, add_zero, one_smul]

theorem tubeSeamCollar_source_subset : (tubeSeamCollar F Ψ φ hκ).source ⊆ signedCollarSource :=
  fun _ hp => hp.2

theorem tubeSeamCollar_source (hκ1 : κ < 1) (hB : tubeBand κ ⊆ φ.source)
    (hBF : ∀ p ∈ tubeBand κ, Ψ.symm (φ p) ∈ F.source) :
    (tubeSeamCollar F Ψ φ hκ).source = signedCollarSource := by
  refine Subset.antisymm (tubeSeamCollar_source_subset F Ψ φ hκ) fun p hp => ?_
  have hs : -1 < p.2 ∧ p.2 < 1 := hp
  have hb := mem_tubeBand hκ hκ1 p.1 hs.1 hs.2
  have hpol := fibreExcisionPolar_scale (κ := κ) p
  refine ⟨⟨mem_univ _, ?_, ?_⟩, hp⟩
  · change -2 < 2 * κ * p.2
    nlinarith
  · change CircleFibration.fibreExcisionPolar.{u} (p.1, 2 * κ * p.2) ∈
      (φ.trans (Ψ.symm.toPartialDiffeomorph.trans F)).source
    rw [hpol]
    exact ⟨hB hb, mem_univ _, hBF _ hb⟩

/-- Every point of the seam target is the image of a band point. -/
theorem mem_tubeSeamCollar_target (hκ1 : κ < 1) {y : W.Carrier}
    (hy : y ∈ (tubeSeamCollar F Ψ φ hκ).target) :
    ∃ p ∈ tubeBand κ, p ∈ φ.source ∧ Ψ.symm (φ p) ∈ F.source ∧ y = F (Ψ.symm (φ p)) := by
  set G := tubeSeamCollar F Ψ φ hκ
  have hx : G.symm y ∈ G.source := G.map_target hy
  have hyx : G (G.symm y) = y := G.right_inv hy
  obtain ⟨⟨-, -, hφs, -, hFs⟩, hsrc⟩ := hx
  have hs : -1 < (G.symm y).2 ∧ (G.symm y).2 < 1 := hsrc
  have hpol := fibreExcisionPolar_scale (κ := κ) (G.symm y)
  refine ⟨_, mem_tubeBand hκ hκ1 (G.symm y).1 hs.1 hs.2, ?_, ?_, ?_⟩
  · have h : CircleFibration.fibreExcisionPolar.{u} ((G.symm y).1, 2 * κ * (G.symm y).2) ∈
        φ.source := hφs
    rwa [hpol] at h
  · have h : Ψ.symm (φ (CircleFibration.fibreExcisionPolar.{u}
        ((G.symm y).1, 2 * κ * (G.symm y).2))) ∈ F.source := hFs
    rwa [hpol] at h
  · conv_lhs => rw [← hyx]
    exact tubeSeamCollar_apply F Ψ φ hκ _

/-- The `F`-image of an interior tube point read through `Ψ⁻¹` is interior. -/
theorem isInteriorPoint_tube (hφI : φ.target ⊆ Q.interior) {p : PlaneLift.{u} × Circle}
    (hp : p ∈ φ.source) (hpF : Ψ.symm (φ p) ∈ F.source) :
    W.model.IsInteriorPoint (F (Ψ.symm (φ p))) := by
  have h1 : Q.model.IsInteriorPoint (φ p) := hφI (φ.map_source hp)
  have h2 : Q.model.IsInteriorPoint (Ψ.symm (φ p)) :=
    ((Ψ.symm.isLocalDiffeomorph (φ p)).isInteriorPoint_iff (by simp)).mp h1
  exact ((F.isLocalDiffeomorphAt Q.model W.model ∞ hpF).isInteriorPoint_iff (by simp)).mp h2

theorem tubeSeamCollar_target_interior (hκ1 : κ < 1) (hφI : φ.target ⊆ Q.interior) :
    (tubeSeamCollar F Ψ φ hκ).target ⊆ W.interior := by
  intro y hy
  obtain ⟨p, -, hp, hpF, rfl⟩ := mem_tubeSeamCollar_target F Ψ φ hκ hκ1 hy
  exact isInteriorPoint_tube F Ψ φ hφI hp hpF

/-- **The seam of a placed tube**: the band of radii `(1 - κ, 1 + κ)` read through `Ψ⁻¹` and `F`. -/
def tubeSeam (hκ1 : κ < 1) (hB : tubeBand κ ⊆ φ.source)
    (hBF : ∀ p ∈ tubeBand κ, Ψ.symm (φ p) ∈ F.source) (hφI : φ.target ⊆ Q.interior) :
    TorusSeam W where
  collar := tubeSeamCollar F Ψ φ hκ
  source_eq := tubeSeamCollar_source F Ψ φ hκ hκ1 hB hBF
  target_interior := tubeSeamCollar_target_interior F Ψ φ hκ hκ1 hφI

/-! ### The two half collars of the seam -/

/-- **The inner side.** A half collar `(τ, s) ↦ F (Ψ⁻¹ (φ ((1 - ν s / 2) τ₁, τ₂)))` of a map into
`W`, shrunk by `2 κ / ν`, is the negative half of the seam. -/
theorem tubeSeam_inner_lift {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    (g : N → W.Carrier)
    (ℓ : PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞)
    {ν : ℝ} (hν : 0 < ν) (hκν : 2 * κ ≤ ν)
    (hℓ : ∀ p, p ∈ halfCollarSource → g (ℓ p) =
      F (Ψ.symm (φ (ULift.up ((1 - ν * p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))))
    (τ : Torus) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    g (shrinkHalfCollar (div_pos (mul_pos two_pos hκ) hν) ℓ (τ, halfPoint s hs)) =
      tubeSeamCollar F Ψ φ hκ (τ, -s) := by
  have hδ1 : 2 * κ / ν ≤ 1 := (div_le_one hν).mpr hκν
  have hmem : (τ, halfSpaceScale (div_pos (mul_pos two_pos hκ) hν) (halfPoint s hs)) ∈
      halfCollarSource := halfSpaceScale_mem _ hδ1 (show s < 1 from hs1)
  rw [shrinkHalfCollar_apply, hℓ _ hmem, tubeSeamCollar_apply, halfSpaceScale_coord]
  have h : 1 - ν * (2 * κ / ν * (halfPoint s hs).val 0) / 2 = 1 + κ * -s := by
    change 1 - ν * (2 * κ / ν * s) / 2 = 1 + κ * -s
    field_simp
    ring
  rw [h]

theorem shrinkHalfCollar_zero {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    (ℓ : PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞) {δ : ℝ}
    (hδ : 0 < δ) (τ : Torus) : shrinkHalfCollar hδ ℓ (τ, halfZero) = ℓ (τ, halfZero) := by
  rw [shrinkHalfCollar_apply, halfSpaceScale_halfZero]

/-- **The outer side.** A half collar `Γ` of a carrier `L` with `η (Γ (τ, s)) = φ ((1 + s/2) τ₁, τ₂)`,
shrunk by `2 κ` and carried into a manifold `N` by a diffeomorphism `e`. -/
def drillSeamLift {L : CompactCarrier.{u}} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 3) N]
    (Γ : PartialDiffeomorph halfCollarModel L.model (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
    (e : L.Carrier ≃ₘ⟮L.model, 𝓡∂ 3⟯ N) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) N ∞ :=
  (shrinkHalfCollar (mul_pos two_pos hκ) Γ).trans e.toPartialDiffeomorph

theorem drillSeamLift_apply {L : CompactCarrier.{u}} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 3) N]
    (Γ : PartialDiffeomorph halfCollarModel L.model (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
    (e : L.Carrier ≃ₘ⟮L.model, 𝓡∂ 3⟯ N) (p : Torus × EuclideanHalfSpace 1) :
    drillSeamLift hκ Γ e p = e (Γ (p.1, halfSpaceScale (mul_pos two_pos hκ) p.2)) :=
  rfl

theorem drillSeamLift_source {L : CompactCarrier.{u}} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 3) N]
    {Γ : PartialDiffeomorph halfCollarModel L.model (Torus × EuclideanHalfSpace 1) L.Carrier ∞}
    (hΓs : Γ.source = halfCollarSource) (e : L.Carrier ≃ₘ⟮L.model, 𝓡∂ 3⟯ N)
    (hκ2 : 2 * κ ≤ 1) : (drillSeamLift hκ Γ e).source = halfCollarSource := by
  change (shrinkHalfCollar (mul_pos two_pos hκ) Γ).source ∩ _ = _
  rw [shrinkHalfCollar_source _ hκ2 hΓs]
  exact inter_univ _

theorem drillSeamLift_zero {L : CompactCarrier.{u}} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 3) N]
    (Γ : PartialDiffeomorph halfCollarModel L.model (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
    (e : L.Carrier ≃ₘ⟮L.model, 𝓡∂ 3⟯ N) (τ : Torus) :
    drillSeamLift hκ Γ e (τ, halfZero) = e (Γ (τ, halfZero)) := by
  rw [drillSeamLift_apply, halfSpaceScale_halfZero]

theorem drillSeamLift_eq {L : CompactCarrier.{u}} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 3) N]
    {Γ : PartialDiffeomorph halfCollarModel L.model (Torus × EuclideanHalfSpace 1) L.Carrier ∞}
    {η : L.Carrier → Q.Carrier}
    (hΓ : ∀ p, p ∈ halfCollarSource →
      η (Γ p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (e : L.Carrier ≃ₘ⟮L.model, 𝓡∂ 3⟯ N) (g : N → W.Carrier)
    (hg : ∀ x, g (e x) = F (Ψ.symm (η x))) (hκ2 : 2 * κ ≤ 1)
    (τ : Torus) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    g (drillSeamLift hκ Γ e (τ, halfPoint s hs)) = tubeSeamCollar F Ψ φ hκ (τ, s) := by
  have hmem : (τ, halfSpaceScale (mul_pos two_pos hκ) (halfPoint s hs)) ∈ halfCollarSource :=
    halfSpaceScale_mem _ hκ2 (show s < 1 from hs1)
  rw [drillSeamLift_apply, hg, hΓ _ hmem, tubeSeamCollar_apply, halfSpaceScale_coord]
  have h : 1 + 2 * κ * (halfPoint s hs).val 0 / 2 = 1 + κ * s := by
    change 1 + 2 * κ * s / 2 = 1 + κ * s
    ring
  rw [h]

end Seam

end GC.GraphManifold.Assembly
