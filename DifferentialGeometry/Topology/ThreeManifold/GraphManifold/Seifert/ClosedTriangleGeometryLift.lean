import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryLift
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatScrews

/-!
# Flat base lifts and signed tube lifts

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§2.3, with review 27 item 1: the fibre step `ℓ` is any nonzero real, possibly negative). On
`ModelCoordinates` with plane coordinate `z = planeOf x` and fibre coordinate `t = x 2`:
the base lift `x ↦ (f z, e(t/ℓ) Ψ z)` is a local diffeomorphism wherever `f`, `Ψ` are smooth and
`det Df ≠ 0` (`isLocalDiffeomorphAt_flatBaseLift`), and the tube lift
`x ↦ (μ (z - v) e(a s), e(P s))`, `s = t/ℓ + β z`, is a local diffeomorphism wherever `β` is smooth,
for `μ ≠ 0`, `P ≠ 0`, `ℓ ≠ 0`, including on the central fibre `z = v`
(`isLocalDiffeomorphAt_flatTubeLift`): after the embedding `ℂ × S¹ ⊂ ℂ × ℂ` the derivative is
injective, the fibre direction being detected by `2πiP/ℓ` and the base by the complex
multiplication by `μ e(a s)`. Here `e(σ) = exp(2πiσ)`.
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

namespace GC.Seifert

namespace ClosedTriangle

open TwoConeFold

def planeOfL : ModelCoordinates →L[ℝ] ℂ :=
  Complex.ofRealCLM ∘L (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)) +
    (Complex.ofRealCLM ∘L (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))).smulRight I

theorem planeOfL_apply (v : ModelCoordinates) : planeOfL v = planeOf v := by
  simp [planeOfL, planeOf, ContinuousLinearMap.smulRight_apply]

theorem hasFDerivAt_planeOf (p : ModelCoordinates) : HasFDerivAt planeOf planeOfL p := by
  have : (planeOf : ModelCoordinates → ℂ) = planeOfL := funext fun v => (planeOfL_apply v).symm
  rw [this]
  exact planeOfL.hasFDerivAt

theorem contDiff_planeOf : ContDiff ℝ ∞ planeOf := by
  have : (planeOf : ModelCoordinates → ℂ) = planeOfL := funext fun v => (planeOfL_apply v).symm
  rw [this]
  exact planeOfL.contDiff

theorem planeOf_eq_zero {v : ModelCoordinates} (h : planeOf v = 0) : v 0 = 0 ∧ v 1 = 0 := by
  constructor
  · simpa using congrArg Complex.re h
  · simpa using congrArg Complex.im h

theorem hasFDerivAt_div_two {ℓ : ℝ} (p : ModelCoordinates) :
    HasFDerivAt (fun x : ModelCoordinates => x 2 / ℓ)
      (ℓ⁻¹ • (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) p := by
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt (x := p)).const_smul ℓ⁻¹
  convert h using 1
  funext x
  simp [div_eq_inv_mul]

theorem isLocalDiffeomorphAt_flatBaseLift {f : ℂ → ℂ} {Ψ : ℂ → Circle} {O : Set ℂ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hΨ : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ Ψ O)
    {ℓ : ℝ} (hℓ : ℓ ≠ 0) {p : ModelCoordinates} (hp : planeOf p ∈ O)
    (hdet : (fderiv ℝ f (planeOf p)).det ≠ 0) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞
      (fun x => (f (planeOf x), eC (x 2 / ℓ) * Ψ (planeOf x))) p := by
  set U : Set ModelCoordinates := planeOf ⁻¹' O with hUdef
  have hU : IsOpen U := hO.preimage contDiff_planeOf.continuous
  have hmaps : MapsTo planeOf U O := fun x hx => hx
  have hproj : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : ModelCoordinates => x 2 / ℓ) :=
    (((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff).div_const ℓ).contMDiff
  have hs2 : ContMDiff (𝓡 3) (𝓡 1) ∞ (fun x : ModelCoordinates => eC (x 2 / ℓ)) :=
    contMDiff_eC.comp hproj
  have hGs : ContMDiffOn (𝓡 3) PlaneCircleModel ∞
      (fun x => (f (planeOf x), eC (x 2 / ℓ) * Ψ (planeOf x))) U := by
    refine ContMDiffOn.prodMk ?_ ?_
    · exact (hf.comp contDiff_planeOf.contDiffOn hmaps).contMDiffOn
    · exact hs2.contMDiffOn.mul (hΨ.comp contDiff_planeOf.contMDiff.contMDiffOn hmaps)
  have hfz : HasFDerivAt f (fderiv ℝ f (planeOf p)) (planeOf p) :=
    ((hf.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hΨc : ContDiffAt ℝ ∞ (fun z => (Ψ z : ℂ)) (planeOf p) := by
    have := contMDiff_circle_coe.contMDiffAt.comp (planeOf p) (hΨ.contMDiffAt (hO.mem_nhds hp))
    exact contMDiffAt_iff_contDiffAt.mp this
  have hΨd : HasFDerivAt (fun z => (Ψ z : ℂ)) (fderiv ℝ (fun z => (Ψ z : ℂ)) (planeOf p))
      (planeOf p) :=
    (hΨc.differentiableAt (by simp)).hasFDerivAt
  obtain ⟨Le, he, hLe⟩ := hasFDerivAt_eC_comp (hasFDerivAt_div_two (ℓ := ℓ) p)
  have h1 := hfz.comp p (hasFDerivAt_planeOf p)
  have h2 := he.mul (hΨd.comp p (hasFDerivAt_planeOf p))
  refine isLocalDiffeomorphAt_of_plane hU hp hGs (h1.prodMk h2) ?_
  rw [injective_iff_map_eq_zero]
  intro v hv
  rw [ContinuousLinearMap.prod_apply, Prod.mk_eq_zero] at hv
  obtain ⟨hv1, hv2⟩ := hv
  rw [ContinuousLinearMap.comp_apply] at hv1
  have hz0 : planeOfL v = 0 :=
    injective_of_det_ne_zero' hdet (hv1.trans (map_zero _).symm)
  rw [planeOfL_apply] at hz0
  obtain ⟨h0, h1'⟩ := planeOf_eq_zero hz0
  have key : (eC (p 2 / ℓ) : ℂ) * fderiv ℝ (fun z => (Ψ z : ℂ)) (planeOf p) (planeOfL v) +
      (Ψ (planeOf p) : ℂ) * Le v = 0 := hv2
  rw [planeOfL_apply, hz0, map_zero, mul_zero, zero_add, hLe] at key
  have hne : ((2 * Real.pi : ℝ) : ℂ) * I * (eC (p 2 / ℓ) : ℂ) * (Ψ (planeOf p) : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ I_ne_zero) (Circle.coe_ne_zero _))
      (Circle.coe_ne_zero _)
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have h2v : (((ℓ⁻¹ • (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) v : ℝ) : ℂ) = 0 := by
    have : ((2 * Real.pi : ℝ) : ℂ) * I * (eC (p 2 / ℓ) : ℂ) * (Ψ (planeOf p) : ℂ) *
        (((ℓ⁻¹ • (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) v : ℝ) : ℂ) = 0 := by
      rw [← key]
      ring
    exact (mul_eq_zero.mp this).resolve_left hne
  have h2r : ℓ⁻¹ * v 2 = 0 := by
    have : ((ℓ⁻¹ • (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3))) v : ℝ) = 0 := by
      exact_mod_cast h2v
    simpa using this
  have hv2' : v 2 = 0 := (mul_eq_zero.mp h2r).resolve_left (inv_ne_zero hℓ)
  exact eq_zero_of_coords h0 h1' hv2'

theorem isLocalDiffeomorphAt_flatTubeLift {μ : ℂ} (hμ : μ ≠ 0) (v : ℂ) (a : ℤ) {P : ℕ}
    (hP : P ≠ 0) {ℓ : ℝ} (hℓ : ℓ ≠ 0) {β : ℂ → ℝ} {O : Set ℂ} (hO : IsOpen O)
    (hβ : ContDiffOn ℝ ∞ β O) {p : ModelCoordinates} (hp : planeOf p ∈ O) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞
      (fun x => (μ * (planeOf x - v) * (eC (a * (x 2 / ℓ + β (planeOf x))) : ℂ),
        eC (P * (x 2 / ℓ + β (planeOf x))))) p := by
  set U : Set ModelCoordinates := planeOf ⁻¹' O with hUdef
  have hU : IsOpen U := hO.preimage contDiff_planeOf.continuous
  have hmaps : MapsTo planeOf U O := fun x hx => hx
  have hproj : ContDiff ℝ ∞ (fun x : ModelCoordinates => x 2 / ℓ) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff).div_const ℓ
  have ht : ContDiffOn ℝ ∞ (fun x : ModelCoordinates => x 2 / ℓ + β (planeOf x)) U :=
    hproj.contDiffOn.add (hβ.comp contDiff_planeOf.contDiffOn hmaps)
  have hω : ContDiff ℝ ∞ (fun x => μ * (planeOf x - v)) :=
    contDiff_const.mul (contDiff_planeOf.sub contDiff_const)
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun w : Circle => (w : ℂ)) := contMDiff_circle_coe
  have hGs : ContMDiffOn (𝓡 3) PlaneCircleModel ∞
      (fun x => (μ * (planeOf x - v) * (eC (a * (x 2 / ℓ + β (planeOf x))) : ℂ),
        eC (P * (x 2 / ℓ + β (planeOf x))))) U := by
    refine ContMDiffOn.prodMk ?_ ?_
    · have h2 : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℂ) ∞
          (fun x => (eC (a * (x 2 / ℓ + β (planeOf x))) : ℂ)) U :=
        hcoe.comp_contMDiffOn (contMDiff_eC.comp_contMDiffOn
          (contDiffOn_const.mul ht).contMDiffOn)
      exact chartContMDiffComplexMul.comp_contMDiffOn (hω.contMDiff.contMDiffOn.prodMk_space h2)
    · exact contMDiff_eC.comp_contMDiffOn (contDiffOn_const.mul ht).contMDiffOn
  have hωf : HasFDerivAt (fun x => μ * (planeOf x - v)) (μ • planeOfL) p := by
    have := ((hasFDerivAt_planeOf p).sub_const v).const_mul μ
    convert this using 1
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
  have h1 : (μ * (planeOf p - v)) * L₁ w +
      (eC ((a : ℝ) * (p 2 / ℓ + β (planeOf p))) : ℂ) * (μ * planeOfL w) = 0 := by
    have := hw1
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  rw [hL₁v] at h1
  have hzw : planeOfL w = 0 := by
    have hat : ((((a : ℝ) • Lt) w : ℝ) : ℂ) = 0 := by
      have e : (((a : ℝ) • Lt) w) = (a : ℝ) * Lt w := rfl
      rw [e, htw0, mul_zero, ofReal_zero]
    rw [hat, mul_zero, mul_zero, zero_add] at h1
    have hne : (eC ((a : ℝ) * (p 2 / ℓ + β (planeOf p))) : ℂ) * μ ≠ 0 :=
      mul_ne_zero (Circle.coe_ne_zero _) hμ
    have : (eC ((a : ℝ) * (p 2 / ℓ + β (planeOf p))) : ℂ) * μ * planeOfL w = 0 := by
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

end ClosedTriangle

end GC.Seifert
