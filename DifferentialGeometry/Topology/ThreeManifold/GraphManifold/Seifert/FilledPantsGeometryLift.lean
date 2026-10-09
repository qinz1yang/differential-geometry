import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryDomain
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryIsometries
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldDiffeo

/-!
# Lifts of the two-cone fold to the model and their local invertibility

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.1,
with review 21 §4.1, §5.5). Maps from `ModelCoordinates` (`z = logPoint p`, `s = p 2`) to
`ℂ × S¹` used by the two-cone fold: the base lift `(f z, e(s) Ψ z)` and the tube coordinates
`(μ ω_v(z) e(a(s + β z)), e(P(s + β z)))` at a cone vertex `v`, with `e(t) = exp(2πit)`. Both
are local diffeomorphisms wherever they are smooth and, respectively, `det Df ≠ 0` or the tube
data are as stated (`isLocalDiffeomorphAt_baseLift`, `isLocalDiffeomorphAt_tubeLift`): the
derivative after the embedding `ℂ × S¹ ⊂ ℂ × ℂ` is injective (the base directions are detected
by `Df` resp. the nonvanishing derivative of the disc coordinate, then the fibre direction by
`∂ₛ`), and the inverse function theorem applies. The reflection `conjPair (ζ, t) = (ζ̄, t⁻¹)`
commutes with the seam maps at a real centre (`seamFwd_conjPair`, `seamBwd_conjPair`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

namespace GC.Seifert

namespace TwoConeFold

def eC (t : ℝ) : Circle := Circle.exp (2 * Real.pi * t)

def conjPair (y : ℂ × Circle) : ℂ × Circle := (conj y.1, y.2⁻¹)

def zOf (p : ModelCoordinates) : ℂ := (logPoint p : ℂ)

theorem eC_add (s t : ℝ) : eC (s + t) = eC s * eC t := by
  rw [eC, mul_add, Circle.exp_add]
  rfl

theorem eC_neg (t : ℝ) : eC (-t) = (eC t)⁻¹ := by
  rw [eC, mul_neg, Circle.exp_neg]
  rfl

theorem eC_int (n : ℤ) : eC n = 1 := by
  rw [eC, show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring,
    Circle.exp_int_mul_two_pi]

theorem eC_zpow (t : ℝ) (n : ℤ) : eC t ^ n = eC (n * t) := by
  rw [eC, eC, ← Circle.exp_intCast_mul]
  congr 1
  ring

theorem coe_eC (t : ℝ) : (eC t : ℂ) = exp (((2 * Real.pi * t : ℝ) : ℂ) * I) := by
  rw [eC, Circle.coe_exp]

theorem conjPair_conjPair (y : ℂ × Circle) : conjPair (conjPair y) = y := by
  simp [conjPair]

theorem unitOf_conj'' (w : ℂ) : unitOf (conj w) = (unitOf w)⁻¹ := by
  by_cases hw : w = 0
  · simp [hw, unitOf]
  apply Circle.ext
  rw [coe_unitOf (by simpa using hw), Circle.coe_inv_eq_conj, coe_unitOf hw]
  simp [Complex.real_smul]

theorem seamFwd_conjPair (c : ℝ) (P : ℕ) (p q a b : ℤ) (y : ℂ × Circle) :
    seamFwd c P p q a b (conjPair y) = conjPair (seamFwd c P p q a b y) := by
  have h1 : unitOf (conj y.1) ^ p * (y.2⁻¹) ^ (-a) = (unitOf y.1 ^ p * y.2 ^ (-a))⁻¹ := by
    rw [unitOf_conj'']
    simp only [inv_zpow, mul_inv]
  have h2 : unitOf (conj y.1) ^ (-q) * (y.2⁻¹) ^ b = (unitOf y.1 ^ (-q) * y.2 ^ b)⁻¹ := by
    rw [unitOf_conj'']
    simp only [inv_zpow, mul_inv]
  apply Prod.ext
  · change (c : ℂ) + ((‖conj y.1‖ ^ P / 2 : ℝ) : ℂ) *
      ((unitOf (conj y.1) ^ p * (y.2⁻¹) ^ (-a) : Circle) : ℂ) =
        conj ((c : ℂ) + ((‖y.1‖ ^ P / 2 : ℝ) : ℂ) * ((unitOf y.1 ^ p * y.2 ^ (-a) : Circle) : ℂ))
    rw [h1, Circle.coe_inv_eq_conj, norm_conj, map_add, map_mul, conj_ofReal, conj_ofReal]
  · change unitOf (conj y.1) ^ (-q) * (y.2⁻¹) ^ b = (unitOf y.1 ^ (-q) * y.2 ^ b)⁻¹
    exact h2

theorem seamBwd_conjPair (c : ℝ) (P : ℕ) (p q a b : ℤ) (y : ℂ × Circle) :
    seamBwd c P p q a b (conjPair y) = conjPair (seamBwd c P p q a b y) := by
  have hsub : conj y.1 - c = conj (y.1 - c) := by simp [conj_ofReal]
  have h1 : unitOf (conj y.1 - c) ^ b * (y.2⁻¹) ^ a = (unitOf (y.1 - c) ^ b * y.2 ^ a)⁻¹ := by
    rw [hsub, unitOf_conj'']
    simp only [inv_zpow, mul_inv]
  have h2 : unitOf (conj y.1 - c) ^ q * (y.2⁻¹) ^ p = (unitOf (y.1 - c) ^ q * y.2 ^ p)⁻¹ := by
    rw [hsub, unitOf_conj'']
    simp only [inv_zpow, mul_inv]
  apply Prod.ext
  · change ((((2 * ‖conj y.1 - c‖) ^ ((P : ℝ)⁻¹) : ℝ)) : ℂ) *
      ((unitOf (conj y.1 - c) ^ b * (y.2⁻¹) ^ a : Circle) : ℂ) =
        conj ((((2 * ‖y.1 - c‖) ^ ((P : ℝ)⁻¹) : ℝ) : ℂ) *
          ((unitOf (y.1 - c) ^ b * y.2 ^ a : Circle) : ℂ))
    rw [h1, Circle.coe_inv_eq_conj, hsub, norm_conj, map_mul, conj_ofReal]
  · change unitOf (conj y.1 - c) ^ q * (y.2⁻¹) ^ p = (unitOf (y.1 - c) ^ q * y.2 ^ p)⁻¹
    exact h2

theorem coe_logPoint_flipMap (c : ℝ) (p : ModelCoordinates) :
    zOf (flipMap c p) = -conj (zOf p) := by
  apply Complex.ext <;> simp [zOf, coe_logPoint, flipMap_zero, flipMap_one]

theorem isLocalDiffeomorphAt_of_plane {G : ModelCoordinates → ℂ × Circle}
    {U : Set ModelCoordinates} (hU : IsOpen U) {p : ModelCoordinates} (hp : p ∈ U)
    (hG : ContMDiffOn (𝓡 3) PlaneCircleModel ∞ G U) {L : ModelCoordinates →L[ℝ] ℂ × ℂ}
    (hL : HasFDerivAt (fun x => circlePlaneMap (G x)) L p) (hinj : Function.Injective L) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ G p := by
  have hGd : MDifferentiableAt (𝓡 3) PlaneCircleModel G p :=
    (hG.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)
  have hcd : MDifferentiableAt PlaneCircleModel 𝓘(ℝ, ℂ × ℂ) circlePlaneMap (G p) :=
    contMDiff_circlePlaneMap.contMDiffAt.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp p hcd hGd
  have hmf : mfderiv (𝓡 3) 𝓘(ℝ, ℂ × ℂ) (circlePlaneMap ∘ G) p = L := by
    rw [mfderiv_eq_fderiv]
    exact hL.fderiv
  rw [hmf] at hchain
  let D : ModelCoordinates →L[ℝ] ℂ × EuclideanSpace ℝ (Fin 1) :=
    mfderiv (𝓡 3) PlaneCircleModel G p
  have hinjG : Function.Injective D := by
    intro v w hvw
    apply hinj
    rw [hchain]
    exact congrArg (mfderiv PlaneCircleModel 𝓘(ℝ, ℂ × ℂ) circlePlaneMap (G p)) hvw
  have hrank : Module.finrank ℝ ModelCoordinates =
      Module.finrank ℝ (ℂ × EuclideanSpace ℝ (Fin 1)) := by
    rw [finrank_euclideanSpace_fin]
    exact finrank_planeCircleModel.symm
  let A : ModelCoordinates ≃L[ℝ] (ℂ × EuclideanSpace ℝ (Fin 1)) :=
    (LinearMap.linearEquivOfInjective (D : ModelCoordinates →ₗ[ℝ] ℂ × EuclideanSpace ℝ (Fin 1))
      hinjG hrank).toContinuousLinearEquiv
  refine Manifold.isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
    G hG hU p hp A ?_
  have hA : (A : ModelCoordinates →L[ℝ] ℂ × EuclideanSpace ℝ (Fin 1)) = D :=
    ContinuousLinearMap.ext fun v => rfl
  rw [hA]
  exact hGd.hasMFDerivAt

theorem injective_of_det_ne_zero' {f : ℂ →L[ℝ] ℂ} (h : f.det ≠ 0) : Function.Injective f := by
  have hu : IsUnit (f : ℂ →ₗ[ℝ] ℂ) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hu)

theorem logPointDeriv_eq_zero {p v : ModelCoordinates} (h : logPointDeriv p v = 0) :
    v 0 = 0 ∧ v 1 = 0 := by
  rw [logPointDeriv_apply] at h
  have h0 : v 0 = 0 := by simpa using congrArg Complex.re h
  have h1 : (exp ((p 1 : ℝ) : ℂ)).re = 0 ∨ v 1 = 0 := by simpa using congrArg Complex.im h
  refine ⟨h0, h1.resolve_left ?_⟩
  rw [exp_ofReal_re]
  exact (Real.exp_pos _).ne'

theorem hasFDerivAt_eC_two (p : ModelCoordinates) :
    ∃ L : ModelCoordinates →L[ℝ] ℂ, HasFDerivAt (fun x : ModelCoordinates => (eC (x 2) : ℂ)) L p ∧
      ∀ v, L v = ((2 * Real.pi : ℝ) : ℂ) * I * (eC (p 2) : ℂ) * ((v 2 : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun x : ModelCoordinates => ((2 * Real.pi * x 2 : ℝ) : ℂ) * I)
      ((Complex.ofRealCLM ∘L ((2 * Real.pi) • PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2)).smulRight I)
      p := by
    have := (Complex.ofRealCLM.hasFDerivAt.comp p
      (((PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2).hasFDerivAt).const_smul (2 * Real.pi)))
    convert this.mul_const I using 1
    · funext x
      simp [smul_eq_mul]
    · ext v
      simp [ContinuousLinearMap.smulRight_apply]
      ring
  refine ⟨_, h1.cexp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => coe_eC _), ?_⟩
  intro v
  simp only [Fin.isValue, ofReal_mul, ofReal_ofNat, ContinuousLinearMap.comp_smulₛₗ,
    Real.ringHom_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, ofRealCLM_apply, real_smul, smul_eq_mul]
  rw [coe_eC]
  push_cast
  ring

theorem hasFDerivAt_eC_comp {g : ModelCoordinates → ℝ} {g' : ModelCoordinates →L[ℝ] ℝ}
    {p : ModelCoordinates} (hg : HasFDerivAt g g' p) :
    ∃ L : ModelCoordinates →L[ℝ] ℂ, HasFDerivAt (fun x => (eC (g x) : ℂ)) L p ∧
      ∀ v, L v = ((2 * Real.pi : ℝ) : ℂ) * I * (eC (g p) : ℂ) * ((g' v : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun x : ModelCoordinates => ((2 * Real.pi * g x : ℝ) : ℂ) * I)
      ((Complex.ofRealCLM ∘L ((2 * Real.pi) • g')).smulRight I) p := by
    have := Complex.ofRealCLM.hasFDerivAt.comp p (hg.const_smul (2 * Real.pi))
    convert this.mul_const I using 1
    · funext x
      simp [smul_eq_mul]
    · ext v
      simp [ContinuousLinearMap.smulRight_apply]
      ring
  refine ⟨_, h1.cexp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => coe_eC _), ?_⟩
  intro v
  simp only [ofReal_mul, ofReal_ofNat, ContinuousLinearMap.comp_smulₛₗ, Real.ringHom_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ofRealCLM_apply, real_smul, smul_eq_mul]
  rw [coe_eC]
  push_cast
  ring

theorem hasFDerivAt_zOf (p : ModelCoordinates) : HasFDerivAt zOf (logPointDeriv p) p :=
  hasFDerivAt_logPoint p

theorem contDiff_zOf : ContDiff ℝ ∞ zOf := contDiff_coe_logPoint

theorem eq_zero_of_coords {v : ModelCoordinates} (h0 : v 0 = 0) (h1 : v 1 = 0) (h2 : v 2 = 0) :
    v = 0 := by
  ext i
  fin_cases i <;> simp [h0, h1, h2]

theorem contMDiff_eC : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ eC :=
  contMDiff_circleExp.comp (contDiff_const.mul contDiff_id).contMDiff

theorem isLocalDiffeomorphAt_baseLift {f : ℂ → ℂ} {Ψ : ℂ → Circle} {O : Set ℂ} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (hΨ : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ Ψ O) {p : ModelCoordinates}
    (hp : zOf p ∈ O) (hdet : (fderiv ℝ f (zOf p)).det ≠ 0) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞
      (fun x => (f (zOf x), eC (x 2) * Ψ (zOf x))) p := by
  set U : Set ModelCoordinates := zOf ⁻¹' O with hUdef
  have hU : IsOpen U := hO.preimage contDiff_zOf.continuous
  have hmaps : MapsTo zOf U O := fun x hx => hx
  have hproj : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : ModelCoordinates => x 2) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff).contMDiff
  have hs2 : ContMDiff (𝓡 3) (𝓡 1) ∞ (fun x : ModelCoordinates => eC (x 2)) :=
    contMDiff_eC.comp hproj
  have hGs : ContMDiffOn (𝓡 3) PlaneCircleModel ∞
      (fun x => (f (zOf x), eC (x 2) * Ψ (zOf x))) U := by
    refine ContMDiffOn.prodMk ?_ ?_
    · exact (hf.comp contDiff_zOf.contDiffOn hmaps).contMDiffOn
    · exact hs2.contMDiffOn.mul (hΨ.comp contDiff_zOf.contMDiff.contMDiffOn hmaps)
  have hfz : HasFDerivAt f (fderiv ℝ f (zOf p)) (zOf p) :=
    ((hf.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hΨc : ContDiffAt ℝ ∞ (fun z => (Ψ z : ℂ)) (zOf p) := by
    have := contMDiff_circle_coe.contMDiffAt.comp (zOf p) (hΨ.contMDiffAt (hO.mem_nhds hp))
    exact contMDiffAt_iff_contDiffAt.mp this
  have hΨd : HasFDerivAt (fun z => (Ψ z : ℂ)) (fderiv ℝ (fun z => (Ψ z : ℂ)) (zOf p)) (zOf p) :=
    (hΨc.differentiableAt (by simp)).hasFDerivAt
  obtain ⟨Le, he, hLe⟩ := hasFDerivAt_eC_comp
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt (x := p))
  have h1 := hfz.comp p (hasFDerivAt_zOf p)
  have h2 := he.mul (hΨd.comp p (hasFDerivAt_zOf p))
  refine isLocalDiffeomorphAt_of_plane hU hp hGs (h1.prodMk h2) ?_
  rw [injective_iff_map_eq_zero]
  intro v hv
  rw [ContinuousLinearMap.prod_apply, Prod.mk_eq_zero] at hv
  obtain ⟨hv1, hv2⟩ := hv
  rw [ContinuousLinearMap.comp_apply] at hv1
  have hz0 : logPointDeriv p v = 0 :=
    injective_of_det_ne_zero' hdet (hv1.trans (map_zero _).symm)
  obtain ⟨h0, h1'⟩ := logPointDeriv_eq_zero hz0
  have key : (eC (p 2) : ℂ) * fderiv ℝ (fun z => (Ψ z : ℂ)) (zOf p) (logPointDeriv p v) +
      (Ψ (zOf p) : ℂ) * Le v = 0 := hv2
  rw [hz0, map_zero, mul_zero, zero_add, hLe] at key
  have hne : ((2 * Real.pi : ℝ) : ℂ) * I * (eC (p 2) : ℂ) * (Ψ (zOf p) : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ I_ne_zero) (Circle.coe_ne_zero _))
      (Circle.coe_ne_zero _)
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have h2v : ((v 2 : ℝ) : ℂ) = 0 := by
    have : ((2 * Real.pi : ℝ) : ℂ) * I * (eC (p 2) : ℂ) * (Ψ (zOf p) : ℂ) *
        ((v 2 : ℝ) : ℂ) = 0 := by
      rw [← key]
      change _ = (Ψ (zOf p) : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * I * (eC (p 2) : ℂ) * ((v 2 : ℝ) : ℂ))
      ring
    exact (mul_eq_zero.mp this).resolve_left hne
  exact eq_zero_of_coords h0 h1' (by exact_mod_cast h2v)

theorem contDiffAt_coneDisc' {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    ContDiffAt ℝ ∞ (coneDisc v) z :=
  (contDiffAt_coneDisc hv hz).restrict_scalars ℝ

theorem isLocalDiffeomorphAt_tubeLift {v : ℂ} (hv : 0 < v.im) {μ : ℂ} (hμ : μ ≠ 0) (a : ℤ)
    {P : ℕ} (hP : P ≠ 0) {β : ℂ → ℝ} {O : Set ℂ} (hO : IsOpen O) (hOup : O ⊆ {z | 0 < z.im})
    (hβ : ContDiffOn ℝ ∞ β O) {p : ModelCoordinates} (hp : zOf p ∈ O) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞
      (fun x => (μ * coneDisc v (zOf x) * (eC (a * (x 2 + β (zOf x))) : ℂ),
        eC (P * (x 2 + β (zOf x))))) p := by
  set U : Set ModelCoordinates := zOf ⁻¹' O with hUdef
  have hU : IsOpen U := hO.preimage contDiff_zOf.continuous
  have hmaps : MapsTo zOf U O := fun x hx => hx
  have hproj : ContDiff ℝ ∞ (fun x : ModelCoordinates => x 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff
  have ht : ContDiffOn ℝ ∞ (fun x : ModelCoordinates => x 2 + β (zOf x)) U :=
    hproj.contDiffOn.add (hβ.comp contDiff_zOf.contDiffOn hmaps)
  have hω : ContDiffOn ℝ ∞ (fun x => coneDisc v (zOf x)) U := fun x hx =>
    ((contDiffAt_coneDisc' hv (hOup (hmaps hx))).comp x contDiff_zOf.contDiffAt).contDiffWithinAt
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun w : Circle => (w : ℂ)) := contMDiff_circle_coe
  have hGs : ContMDiffOn (𝓡 3) PlaneCircleModel ∞
      (fun x => (μ * coneDisc v (zOf x) * (eC (a * (x 2 + β (zOf x))) : ℂ),
        eC (P * (x 2 + β (zOf x))))) U := by
    refine ContMDiffOn.prodMk ?_ ?_
    · have h1 : ContDiffOn ℝ ∞ (fun x => μ * coneDisc v (zOf x)) U := contDiffOn_const.mul hω
      have h2 : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun x => (eC (a * (x 2 + β (zOf x))) : ℂ)) U :=
        hcoe.comp_contMDiffOn (contMDiff_eC.comp_contMDiffOn
          (contDiffOn_const.mul ht).contMDiffOn)
      exact chartContMDiffComplexMul.comp_contMDiffOn (h1.contMDiffOn.prodMk_space h2)
    · exact contMDiff_eC.comp_contMDiffOn (contDiffOn_const.mul ht).contMDiffOn
  have hzp : 0 < (zOf p).im := hOup hp
  have hd := hasDerivAt_coneDisc hv hzp
  set d := (v - conj v) / (zOf p - conj v) ^ 2 with hddef
  have hdne : d ≠ 0 := by
    have h1 : v - conj v ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    exact div_ne_zero h1 (pow_ne_zero _ (sub_conj_ne_zero hv hzp))
  have hωf : HasFDerivAt (coneDisc v)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ) (zOf p) :=
    hd.hasFDerivAt.restrictScalars ℝ
  have hβd : HasFDerivAt β (fderiv ℝ β (zOf p)) (zOf p) :=
    ((hβ.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have htd : HasFDerivAt (fun x : ModelCoordinates => x 2 + β (zOf x))
      (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) + fderiv ℝ β (zOf p) ∘L logPointDeriv p) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt.add (hβd.comp p (hasFDerivAt_zOf p))
  obtain ⟨L₁, hL₁, hL₁v⟩ := hasFDerivAt_eC_comp (htd.const_mul (a : ℝ))
  obtain ⟨L₂, hL₂, hL₂v⟩ := hasFDerivAt_eC_comp (htd.const_mul (P : ℝ))
  have hf1 := ((hωf.comp p (hasFDerivAt_zOf p)).const_mul μ).mul hL₁
  refine isLocalDiffeomorphAt_of_plane hU hp hGs (hf1.prodMk hL₂) ?_
  rw [injective_iff_map_eq_zero]
  intro w hw
  rw [ContinuousLinearMap.prod_apply, Prod.mk_eq_zero] at hw
  obtain ⟨hw1, hw2⟩ := hw
  set tw := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) + fderiv ℝ β (zOf p) ∘L logPointDeriv p) w
    with htw
  have h2 : L₂ w = 0 := hw2
  rw [hL₂v] at h2
  have htw0 : tw = 0 := by
    have hne : ((2 * Real.pi : ℝ) : ℂ) * I * (eC ((P : ℝ) * (p 2 + β (zOf p))) : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ I_ne_zero) (Circle.coe_ne_zero _)
      exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    have := (mul_eq_zero.mp h2).resolve_left hne
    have e : (((P : ℝ) • (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) +
        fderiv ℝ β (zOf p) ∘L logPointDeriv p)) w) = (P : ℝ) * tw := rfl
    rw [e] at this
    have hPt : (P : ℝ) * tw = 0 := by exact_mod_cast this
    rcases mul_eq_zero.mp hPt with h | h
    · exact absurd h (by exact_mod_cast hP)
    · exact h
  have h1 : (μ * coneDisc v (zOf p)) * L₁ w +
      (eC ((a : ℝ) * (p 2 + β (zOf p))) : ℂ) * (μ * (logPointDeriv p w * d)) = 0 := by
    have := hw1
    simpa [ContinuousLinearMap.smulRight_apply, mul_comm, mul_left_comm, mul_assoc] using this
  rw [hL₁v] at h1
  have hzw : logPointDeriv p w = 0 := by
    have hat : ((((a : ℝ) • (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) +
        fderiv ℝ β (zOf p) ∘L logPointDeriv p)) w : ℝ) : ℂ) = 0 := by
      have e : (((a : ℝ) • (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3) +
          fderiv ℝ β (zOf p) ∘L logPointDeriv p)) w) = (a : ℝ) * tw := rfl
      rw [e, htw0, mul_zero, ofReal_zero]
    rw [hat, mul_zero, mul_zero, zero_add] at h1
    have hne : (eC ((a : ℝ) * (p 2 + β (zOf p))) : ℂ) * μ * d ≠ 0 :=
      mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) hμ) hdne
    have : (eC ((a : ℝ) * (p 2 + β (zOf p))) : ℂ) * μ * d * logPointDeriv p w = 0 := by
      rw [← h1]; ring
    exact (mul_eq_zero.mp this).resolve_left hne
  obtain ⟨h0, h1'⟩ := logPointDeriv_eq_zero hzw
  have h2' : w 2 = 0 := by
    have := htw0
    rw [htw] at this
    simpa [hzw] using this
  exact eq_zero_of_coords h0 h1' h2'

end TwoConeFold

end GC.Seifert
