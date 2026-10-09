import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryLift
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphWallTwo

/-!
# Spherical tube coordinates at a vertex

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §5, with
review 32 §6.2–6.4). At a vertex `v` of the spherical chart, with a unit factor `μ`, a Bézout
column `(a, b)` of a cone `(p, q)` and the signed fibre step `ℓ`, the tube coordinate is
`sphTube x = (μ · disc_v z · e(a s), e(p s))`, `s = t/ℓ + β z`, `e(σ) = exp(2πiσ)`, with ONE
convention: `β = -ψ_v/ℓ + β̂`, `ψ_v = psiS v`, so that `s = τ/ℓ + β̂ z` with the centred fibre
coordinate `τ = t + arg(1 + v̄ z)` (`sphTubeS_eq_centred`).
* Central local diffeomorphism (review §6.4): the map is the composite of
  `x ↦ (g z, s x)` with `(w, s) ↦ (w e(a s), e(p s))`, and is a local diffeomorphism at every point
  where `g` has a nonzero complex derivative and `β` is smooth, including the centre
  (`isLocalDiffeomorphAt_tubeLift_of_hasDerivAt`, `isLocalDiffeomorphAt_sphTube`); `ℓ` may be
  negative.
* Invariance (review §6.3): for the clockwise screw `screwSph v (-2π/p) (-ℓq/p)` read in the chart
  by `screwChart`, if `β̂` is invariant and `2π = n ℓ` (`n ∈ ℤ`), then the full tube map is
  invariant, `sphTube ∘ screwChart = sphTube` (`sphTube_screwChart`), by `p b - a q = 1`; the base
  coordinate itself turns by `e^{-2πi/p}` (`disc_screwChart`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ContDiff Manifold ComplexConjugate

namespace GC.Seifert

namespace ClosedTriangle

open TwoConeFold

theorem isLocalDiffeomorphAt_tubeLift_of_hasDerivAt {g : ℂ → ℂ} {g' : ℂ} (hg' : g' ≠ 0) (a : ℤ)
    {P : ℕ} (hP : P ≠ 0) {ℓ : ℝ} (hℓ : ℓ ≠ 0) {β : ℂ → ℝ} {O : Set ℂ} (hO : IsOpen O)
    (hg : ContDiffOn ℝ ∞ g O) (hβ : ContDiffOn ℝ ∞ β O) {p : ModelCoordinates}
    (hp : planeOf p ∈ O) (hgd : HasDerivAt g g' (planeOf p)) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞
      (fun x => (g (planeOf x) * (eC (a * (x 2 / ℓ + β (planeOf x))) : ℂ),
        eC (P * (x 2 / ℓ + β (planeOf x))))) p := by
  set U : Set ModelCoordinates := planeOf ⁻¹' O with hUdef
  have hU : IsOpen U := hO.preimage contDiff_planeOf.continuous
  have hmaps : MapsTo planeOf U O := fun x hx => hx
  have hproj : ContDiff ℝ ∞ (fun x : ModelCoordinates => x 2 / ℓ) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff).div_const ℓ
  have ht : ContDiffOn ℝ ∞ (fun x : ModelCoordinates => x 2 / ℓ + β (planeOf x)) U :=
    hproj.contDiffOn.add (hβ.comp contDiff_planeOf.contDiffOn hmaps)
  have hω : ContDiffOn ℝ ∞ (fun x => g (planeOf x)) U :=
    hg.comp contDiff_planeOf.contDiffOn hmaps
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun w : Circle => (w : ℂ)) := contMDiff_circle_coe
  have hGs : ContMDiffOn (𝓡 3) PlaneCircleModel ∞
      (fun x => (g (planeOf x) * (eC (a * (x 2 / ℓ + β (planeOf x))) : ℂ),
        eC (P * (x 2 / ℓ + β (planeOf x))))) U := by
    refine ContMDiffOn.prodMk ?_ ?_
    · have h2 : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℂ) ∞
          (fun x => (eC (a * (x 2 / ℓ + β (planeOf x))) : ℂ)) U :=
        hcoe.comp_contMDiffOn (contMDiff_eC.comp_contMDiffOn
          (contDiffOn_const.mul ht).contMDiffOn)
      exact chartContMDiffComplexMul.comp_contMDiffOn (hω.contMDiffOn.prodMk_space h2)
    · exact contMDiff_eC.comp_contMDiffOn (contDiffOn_const.mul ht).contMDiffOn
  set Lg : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) g').restrictScalars ℝ
    with hLg
  have hLg_apply (w : ℂ) : Lg w = w * g' := by simp [hLg]
  have hωf : HasFDerivAt (fun x => g (planeOf x)) (Lg ∘L planeOfL) p :=
    (hgd.hasFDerivAt.restrictScalars ℝ).comp p (hasFDerivAt_planeOf p)
  have hβd : HasFDerivAt β (fderiv ℝ β (planeOf p)) (planeOf p) :=
    ((hβ.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  set Lt : ModelCoordinates →L[ℝ] ℝ :=
    ℓ⁻¹ • (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)) + fderiv ℝ β (planeOf p) ∘L planeOfL
    with hLt
  have htd : HasFDerivAt (fun x : ModelCoordinates => x 2 / ℓ + β (planeOf x)) Lt p :=
    (hasFDerivAt_div_two p).add (hβd.comp p (hasFDerivAt_planeOf p))
  obtain ⟨L₁, hL₁, hL₁v⟩ := hasFDerivAt_eC_comp (htd.const_mul (a : ℝ))
  obtain ⟨L₂, hL₂, hL₂v⟩ := hasFDerivAt_eC_comp (htd.const_mul (P : ℝ))
  have hf1 := hωf.mul hL₁
  refine isLocalDiffeomorphAt_of_plane hU hp hGs (hf1.prodMk hL₂) ?_
  rw [injective_iff_map_eq_zero]
  intro w hw
  rw [ContinuousLinearMap.prod_apply, Prod.mk_eq_zero] at hw
  obtain ⟨hw1, hw2⟩ := hw
  have h2 : L₂ w = 0 := hw2
  rw [hL₂v] at h2
  have htw0 : Lt w = 0 := by
    have hne : ((2 * Real.pi : ℝ) : ℂ) * I *
        (eC ((P : ℝ) * (p 2 / ℓ + β (planeOf p))) : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ I_ne_zero) (Circle.coe_ne_zero _)
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    have := (mul_eq_zero.mp h2).resolve_left hne
    have e : (((P : ℝ) • Lt) w) = (P : ℝ) * Lt w := rfl
    rw [e] at this
    have hPt : (P : ℝ) * Lt w = 0 := by exact_mod_cast this
    rcases mul_eq_zero.mp hPt with h | h
    · exact absurd h (by exact_mod_cast hP)
    · exact h
  have h1 : g (planeOf p) * L₁ w +
      (eC ((a : ℝ) * (p 2 / ℓ + β (planeOf p))) : ℂ) * Lg (planeOfL w) = 0 := by
    have := hw1
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  rw [hL₁v, hLg_apply] at h1
  have hzw : planeOfL w = 0 := by
    have hat : ((((a : ℝ) • Lt) w : ℝ) : ℂ) = 0 := by
      have e : (((a : ℝ) • Lt) w) = (a : ℝ) * Lt w := rfl
      rw [e, htw0, mul_zero, ofReal_zero]
    rw [hat, mul_zero, mul_zero, zero_add] at h1
    have hne : (eC ((a : ℝ) * (p 2 / ℓ + β (planeOf p))) : ℂ) * g' ≠ 0 :=
      mul_ne_zero (Circle.coe_ne_zero _) hg'
    have : (eC ((a : ℝ) * (p 2 / ℓ + β (planeOf p))) : ℂ) * g' * planeOfL w = 0 := by
      rw [← h1]; ring
    exact (mul_eq_zero.mp this).resolve_left hne
  have hzw' := hzw
  rw [planeOfL_apply] at hzw'
  obtain ⟨h0, h1'⟩ := planeOf_eq_zero hzw'
  have h2' : w 2 = 0 := by
    have := htw0
    rw [hLt, add_apply, ContinuousLinearMap.comp_apply, hzw, map_zero,
      add_zero] at this
    have h3 : ℓ⁻¹ * w 2 = 0 := by simpa using this
    exact (mul_eq_zero.mp h3).resolve_left (inv_ne_zero hℓ)
  exact eq_zero_of_coords h0 h1' h2'

namespace Sph

def discV (v z : ℂ) : ℂ := (z - v) / (1 + conj v * z)

def sphTubeS (ℓ : ℝ) (β : ℂ → ℝ) (x : ModelCoordinates) : ℝ := x 2 / ℓ + β (planeOf x)

def sphTube (v μ : ℂ) (a : ℤ) (P : ℕ) (ℓ : ℝ) (β : ℂ → ℝ) (x : ModelCoordinates) :
    ℂ × Circle :=
  (μ * discV v (planeOf x) * (eC (a * sphTubeS ℓ β x) : ℂ), eC (P * sphTubeS ℓ β x))

theorem hasDerivAt_discV (v : ℂ) {z : ℂ} (hz : 1 + conj v * z ≠ 0) :
    HasDerivAt (discV v) ((1 + conj v * v) / (1 + conj v * z) ^ 2) z := by
  have h1 : HasDerivAt (fun z : ℂ => z - v) 1 z := (hasDerivAt_id z).sub_const v
  have h2 : HasDerivAt (fun z : ℂ => 1 + conj v * z) (conj v) z := by
    simpa using ((hasDerivAt_id z).const_mul (conj v)).const_add 1
  refine (h1.div h2 hz).congr_deriv ?_
  congr 1
  ring

theorem differentiableOn_discV (v : ℂ) {O : Set ℂ} (hO : ∀ z ∈ O, 1 + conj v * z ≠ 0) :
    DifferentiableOn ℂ (discV v) O :=
  fun z hz => (hasDerivAt_discV v (hO z hz)).differentiableAt.differentiableWithinAt

theorem isLocalDiffeomorphAt_sphTube {v μ : ℂ} (hμ : μ ≠ 0) (a : ℤ) {P : ℕ} (hP : P ≠ 0)
    {ℓ : ℝ} (hℓ : ℓ ≠ 0) {β : ℂ → ℝ} {O : Set ℂ} (hO : IsOpen O)
    (hOv : ∀ z ∈ O, 1 + conj v * z ≠ 0) (hβ : ContDiffOn ℝ ∞ β O) {p : ModelCoordinates}
    (hp : planeOf p ∈ O) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ (sphTube v μ a P ℓ β) p := by
  have hv : 1 + conj v * v ≠ 0 := by
    rw [mul_comm, mul_conj]
    have : (0 : ℝ) < 1 + normSq v := by have := normSq_nonneg v; linarith
    exact_mod_cast this.ne'
  have hg : ContDiffOn ℝ ∞ (fun z => μ * discV v z) O :=
    (((differentiableOn_discV v hOv).const_mul μ).contDiffOn hO).restrict_scalars ℝ
  have hgd : HasDerivAt (fun z => μ * discV v z)
      (μ * ((1 + conj v * v) / (1 + conj v * planeOf p) ^ 2)) (planeOf p) :=
    (hasDerivAt_discV v (hOv _ hp)).const_mul μ
  exact isLocalDiffeomorphAt_tubeLift_of_hasDerivAt
    (mul_ne_zero hμ (div_ne_zero hv (pow_ne_zero 2 (hOv _ hp)))) a hP hℓ hO hg hβ hp hgd

theorem sphTubeS_eq_centred (ℓ : ℝ) (v : ℂ) (β : ℂ → ℝ) (x : ModelCoordinates) :
    sphTubeS ℓ (fun z => -psiS v z / ℓ + β z) x = centred v x 2 / ℓ + β (planeOf x) := by
  simp only [sphTubeS, centred, ofPlane_apply_two, psiS]
  ring

theorem planeOf_centred (v : ℂ) (x : ModelCoordinates) :
    planeOf (centred v x) = discV v (planeOf x) := by
  rw [centred, planeOf_ofPlane]
  rfl

theorem disc_screwChart {v : ℂ} {θ s : ℝ} {x : ModelCoordinates}
    (hx : 1 + conj v * planeOf x ≠ 0)
    (hy : 1 - conj v * planeOf (screwDiffeomorph θ s (centred v x)) ≠ 0)
    (hx' : 1 + conj v * planeOf (screwChart v θ s x) ≠ 0) :
    discV v (planeOf (screwChart v θ s x)) = exp (θ * I) * discV v (planeOf x) := by
  rw [← planeOf_centred, ← planeOf_centred]
  exact (centred_screwChart hx hy hx').1

theorem sphTube_screwChart {v μ : ℂ} {a b q : ℤ} {p : ℕ} (hp : 0 < p)
    (hbez : (p : ℤ) * b - a * q = 1) {ℓ : ℝ} (hℓ : ℓ ≠ 0) {n : ℤ}
    (hn : 2 * Real.pi = n * ℓ) {β : ℂ → ℝ} {x : ModelCoordinates}
    (hx : 1 + conj v * planeOf x ≠ 0)
    (hy : 1 - conj v * planeOf (screwDiffeomorph (-2 * Real.pi / p) (-ℓ * q / p)
      (centred v x)) ≠ 0)
    (hx' : 1 + conj v * planeOf (screwChart v (-2 * Real.pi / p) (-ℓ * q / p) x) ≠ 0)
    (hβ : β (planeOf (screwChart v (-2 * Real.pi / p) (-ℓ * q / p) x)) = β (planeOf x)) :
    sphTube v μ a p ℓ (fun z => -psiS v z / ℓ + β z)
        (screwChart v (-2 * Real.pi / p) (-ℓ * q / p) x) =
      sphTube v μ a p ℓ (fun z => -psiS v z / ℓ + β z) x := by
  obtain ⟨hdisc, m, hm⟩ := centred_screwChart hx hy hx'
  rw [planeOf_centred, planeOf_centred] at hdisc
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hS : sphTubeS ℓ (fun z => -psiS v z / ℓ + β z)
      (screwChart v (-2 * Real.pi / p) (-ℓ * q / p) x) =
        sphTubeS ℓ (fun z => -psiS v z / ℓ + β z) x + (-(q : ℝ) / p + (n * m : ℤ)) := by
    rw [sphTubeS_eq_centred, sphTubeS_eq_centred, hm, hβ, hn]
    push_cast
    field_simp
    ring
  have hrot : exp (((-2 * Real.pi / p : ℝ) : ℂ) * I) = (eC (-1 / p) : ℂ) := by
    rw [eC, Circle.coe_exp]
    congr 1
    push_cast
    ring
  have hbezR : (1 : ℝ) + a * q = p * b := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hbez
    push_cast at this
    linarith
  unfold sphTube
  rw [hdisc, hS]
  congr 1
  · rw [hrot]
    have e : (a : ℝ) * (sphTubeS ℓ (fun z => -psiS v z / ℓ + β z) x +
        (-(q : ℝ) / p + ((n * m : ℤ) : ℝ))) = a * sphTubeS ℓ (fun z => -psiS v z / ℓ + β z) x +
          (-(a * q) / p + ((a * (n * m) : ℤ) : ℝ)) := by
      push_cast
      ring
    rw [e, eC_add, eC_add, eC_int, mul_one]
    have e2 : (-1 / (p : ℝ)) + -((a : ℝ) * q) / p = ((-b : ℤ) : ℝ) := by
      push_cast
      field_simp
      linarith
    calc μ * ((eC (-1 / p) : ℂ) * discV v (planeOf x)) *
          ((eC (a * sphTubeS ℓ (fun z => -psiS v z / ℓ + β z) x) : ℂ) *
            (eC (-(a * q) / p) : ℂ))
        = μ * discV v (planeOf x) * (eC (a * sphTubeS ℓ (fun z => -psiS v z / ℓ + β z) x) : ℂ) *
            ((eC (-1 / p) * eC (-(a * q) / p) : Circle) : ℂ) := by
          push_cast
          ring
      _ = _ := by rw [← eC_add, e2, eC_int, Circle.coe_one, mul_one]
  · have e : (p : ℝ) * (sphTubeS ℓ (fun z => -psiS v z / ℓ + β z) x +
        (-(q : ℝ) / p + ((n * m : ℤ) : ℝ))) = p * sphTubeS ℓ (fun z => -psiS v z / ℓ + β z) x +
          ((-q + p * (n * m) : ℤ) : ℝ) := by
      push_cast
      field_simp
    rw [e, eC_add, eC_int, mul_one]

end Sph

end ClosedTriangle

end GC.Seifert
