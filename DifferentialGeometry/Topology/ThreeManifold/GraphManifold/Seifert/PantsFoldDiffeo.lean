import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsBlockGeometry

/-!
# The pants quotient is the open pants times the circle, given the fold estimates

Packet K16d, tiers 3 and 4. The analytic input on the explicit map `foldCore` of
`Seifert/PantsFold.lean` is stated as three named propositions, all on the closed ideal
triangle: `PantsFoldJacobianBound` (positive Jacobian determinant of `foldCore`),
`PantsFoldImageBound` (`foldCore` lands in the open pants `planarFunction 3 < 0`) and
`PantsFoldCoreBijective` (`foldCore` is injective and onto the closed upper half of the open
pants). Outside the overlap of the weights each statement is about a single polar model and is
elementary; on the overlap the evidence is numerical (`build-logs/worker-K16d.md`).

Given them, `pantsFold` maps onto the open pants (`range_pantsFold`), the derivative of
`pantsFold` is injective (`injective_fderiv_pantsFold`: chain rule through Mathlib's derivative
`smulFDeriv` of the Möbius action, the Jacobian bound and `κ`), and the map
`pantsFoldMap p = (pantsFold (logPoint p), exp (2πi p₂))` on the log model descends to
`pantsQuotientMap : PantsQuotient → ℂ × S¹`, injective (`injective_pantsQuotientMap`) with
range `pantsImage` (`range_pantsQuotientMap`). It is smooth through the quotient covering, and
its differential is injective because the differential of `pantsFoldPlane = (pantsFold ∘
logPoint, exp (2πi p₂))` is (`injective_mfderiv_pantsQuotientMap`), so it is a local
diffeomorphism (`isLocalDiffeomorph_pantsQuotientMap`) and, being injective, a diffeomorphism
onto its image `pantsImage`: `pantsQuotientDiffeo_of_fold` proves `PantsQuotientDiffeo`.
-/

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Matrix GC.Geometry
open scoped MatrixGroups ComplexConjugate ContDiff Topology Manifold

namespace GC.Seifert

attribute [local instance] finrank_real_complex_fact'

def PantsFoldJacobianBound : Prop :=
  ∀ z : ℍ, z ∈ idealTriangle → 0 < (fderiv ℝ foldCore (z : ℂ)).det

def PantsFoldImageBound : Prop :=
  ∀ z : ℍ, z ∈ idealTriangle → planarFunction 3 (foldCore z) < 0

def PantsFoldCoreBijective : Prop :=
  Set.InjOn (fun z : ℍ => foldCore z) idealTriangle ∧
    ∀ u : ℂ, planarFunction 3 u < 0 → 0 ≤ u.im → ∃ z : ℍ, z ∈ idealTriangle ∧ foldCore z = u

theorem planarFunction_three_conj (u : ℂ) : planarFunction 3 (conj u) = planarFunction 3 u := by
  have h (c : ℝ) : ‖conj u - (c : ℂ)‖ = ‖u - (c : ℂ)‖ := by
    rw [show conj u - (c : ℂ) = conj (u - c) by rw [map_sub, Complex.conj_ofReal],
      Complex.norm_conj]
  rw [planarFunction_three, planarFunction_three, Complex.norm_conj, h, h]

theorem range_pantsFold (hI : PantsFoldImageBound) (hB : PantsFoldCoreBijective) :
    Set.range pantsFold = {u | planarFunction 3 u < 0} := by
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    have hζ := foldChoice_smul_mem z
    have h := hI _ hζ
    change planarFunction 3 (foldSign (foldChoice z) (foldCore ((foldChoice z • z : ℍ) : ℂ))) < 0
    unfold foldSign
    split_ifs
    · exact h
    · rwa [planarFunction_three_conj]
  · intro hu
    by_cases him : 0 ≤ u.im
    · obtain ⟨z, hz, hzu⟩ := hB.2 u hu him
      exact ⟨z, by rw [pantsFold_of_mem_idealTriangle hz, hzu]⟩
    · obtain ⟨z, hz, hzu⟩ := hB.2 (conj u) (by rwa [planarFunction_three_conj])
        (by rw [Complex.conj_im]; linarith)
      refine ⟨wallReflection 0 • z, ?_⟩
      rw [pantsFold_wallReflection_smul, pantsFold_of_mem_idealTriangle hz, hzu,
        Complex.conj_conj]

theorem injective_of_det_pos {f : ℂ →L[ℝ] ℂ} (h : 0 < f.det) : Function.Injective f := by
  have hu : IsUnit (f : ℂ →ₗ[ℝ] ℂ) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h.ne')
  exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hu)

theorem pantsFold_ofComplex_eventuallyEq {u : ℂ} (hu : 0 < u.im) :
    ∀ᶠ v in 𝓝 u, pantsFold (ofComplex v) = foldSign (foldChoice ⟨u, hu⟩)
      (foldCore ((foldChoice ⟨u, hu⟩ • ofComplex v : ℍ) : ℂ)) := by
  have hnhds : 𝓝 u = Filter.map UpperHalfPlane.coe (𝓝 (⟨u, hu⟩ : ℍ)) :=
    (isOpenEmbedding_coe.map_nhds_eq (⟨u, hu⟩ : ℍ)).symm
  rw [hnhds, Filter.eventually_map]
  exact (pantsFold_eventuallyEq _).mono fun z hz => by rw [ofComplex_apply]; exact hz

theorem exists_hasFDerivAt_foldSign (w : GL (Fin 2) ℝ) :
    ∃ S : ℂ →L[ℝ] ℂ, Function.Injective S ∧ ∀ u, HasFDerivAt (foldSign w) S u := by
  by_cases h : 0 < w.det.val
  · have he : foldSign w = fun u => u := funext fun u => foldSign_of_det_pos h u
    exact ⟨ContinuousLinearMap.id ℝ ℂ, fun a b hab => hab, fun u => he ▸ hasFDerivAt_id u⟩
  · have he : foldSign w = fun u => Complex.conjCLE u := funext fun u => by
      simp only [foldSign, h, ↓reduceIte, Complex.conjCLE_apply]
    exact ⟨Complex.conjCLE.toContinuousLinearMap, Complex.conjCLE.injective,
      fun u => he ▸ Complex.conjCLE.hasFDerivAt⟩

theorem injective_smulFDeriv (g : GL (Fin 2) ℝ) (z : ℍ) : Function.Injective (smulFDeriv g z) := by
  have hc : (g.det.val : ℂ) / denom g z ^ 2 ≠ 0 :=
    div_ne_zero (by exact_mod_cast val_det_ne_zero g) (pow_ne_zero 2 (denom_ne_zero g z))
  intro a b hab
  simp only [smulFDeriv, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul] at hab
  exact mul_right_cancel₀ hc ((σ g).injective hab)

theorem injective_fderiv_pantsFold (hJ : PantsFoldJacobianBound) {u : ℂ} (hu : 0 < u.im) :
    Function.Injective (fderiv ℝ (fun v : ℂ => pantsFold (ofComplex v)) u) := by
  set z₀ : ℍ := ⟨u, hu⟩
  set w := foldChoice z₀
  set ζ : ℍ := w • ofComplex u
  have hζ : ζ ∈ idealTriangle := by
    change w • ofComplex u ∈ idealTriangle
    rw [ofComplex_apply_of_im_pos hu]
    exact foldChoice_smul_mem z₀
  obtain ⟨S, hSinj, hS⟩ := exists_hasFDerivAt_foldSign w
  have hcore : HasFDerivAt foldCore (fderiv ℝ foldCore (ζ : ℂ)) (ζ : ℂ) :=
    ((contDiffAt_foldCore ζ.im_pos (foldDenom_pos hζ)).differentiableAt (by decide)).hasFDerivAt
  have hsm : HasFDerivAt (fun v : ℂ => ((w • ofComplex v : ℍ) : ℂ)) (smulFDeriv w z₀) u :=
    (hasStrictFDerivAt_smul w z₀).hasFDerivAt
  have h1 := hcore.comp u hsm
  have hcomp := (hS (foldCore (ζ : ℂ))).comp u h1
  rw [(hcomp.congr_of_eventuallyEq (pantsFold_ofComplex_eventuallyEq hu)).fderiv]
  exact hSinj.comp ((injective_of_det_pos (hJ _ hζ)).comp (injective_smulFDeriv w z₀))

def pantsFoldMap (p : ModelCoordinates) : ℂ × Circle :=
  (pantsFold (logPoint p), Circle.exp (2 * Real.pi * p 2))

theorem pantsFoldMap_smul (γ : pantsGroup × Multiplicative ℤ) (p : ModelCoordinates) :
    pantsFoldMap (γ • p) = pantsFoldMap p := by
  rw [pantsFoldMap, pantsFoldMap, logPoint_pants_smul, pantsFold_smul γ.1.2, pants_smul_two]
  congr 1
  rw [mul_add, Circle.exp_add, show 2 * Real.pi * ((Multiplicative.toAdd γ.2 : ℤ) : ℝ) =
    ((Multiplicative.toAdd γ.2 : ℤ) : ℝ) * (2 * Real.pi) by ring, Circle.exp_int_mul_two_pi,
    mul_one]

def pantsQuotientMap : PantsQuotient → ℂ × Circle :=
  Quotient.lift pantsFoldMap fun a b h => by
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact pantsFoldMap_smul γ b

theorem pantsQuotientMap_mk (p : ModelCoordinates) :
    pantsQuotientMap (Quotient.mk'' p) = pantsFoldMap p :=
  rfl

theorem injective_pantsQuotientMap (hB : PantsFoldCoreBijective) :
    Function.Injective pantsQuotientMap := by
  rintro ⟨p⟩ ⟨q⟩ h
  change pantsFoldMap p = pantsFoldMap q at h
  simp only [pantsFoldMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨γ, hγ, hγp⟩ := exists_mem_pantsGroup_smul_eq_of_pantsFold_eq hB.1 h1
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h2
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hp2 : p 2 = q 2 + m := mul_left_cancel₀ hpi (by linear_combination hm)
  apply Quot.sound
  refine MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2
    ⟨(⟨γ⁻¹, inv_mem hγ⟩, Multiplicative.ofAdd m), ?_⟩)
  change logCoords ((γ⁻¹ : SL(2, ℤ)) • logPoint q) (q 2 + ((Multiplicative.toAdd
    (Multiplicative.ofAdd m) : ℤ) : ℝ)) = p
  rw [← hγp, inv_smul_smul, toAdd_ofAdd, ← hp2, logCoords_logPoint]

theorem range_pantsQuotientMap (hI : PantsFoldImageBound) (hB : PantsFoldCoreBijective) :
    Set.range pantsQuotientMap = (pantsImage : Set (ℂ × Circle)) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨p, rfl⟩ := Quotient.mk''_surjective q
    change planarFunction 3 (pantsFold (logPoint p)) < 0
    have h : pantsFold (logPoint p) ∈ Set.range pantsFold := ⟨_, rfl⟩
    rw [range_pantsFold hI hB] at h
    exact h
  · intro hy
    have h : y.1 ∈ Set.range pantsFold := by
      rw [range_pantsFold hI hB]
      exact mem_pantsImage.1 hy
    obtain ⟨z, hz⟩ := h
    refine ⟨Quotient.mk'' (logCoords z (liftAngle 0 (y.2 : ℂ))), Prod.ext ?_ ?_⟩
    · change pantsFold (logPoint (logCoords z _)) = y.1
      rw [logPoint_logCoords, hz]
    · change Circle.exp (2 * Real.pi * logCoords z (liftAngle 0 (y.2 : ℂ)) 2) = y.2
      rw [logCoords_two]
      exact circleExp_liftAngle 0 y.2

theorem contDiff_pantsFold_logPoint :
    ContDiff ℝ ∞ (fun p : ModelCoordinates => pantsFold (logPoint p)) := by
  have h : (fun p : ModelCoordinates => pantsFold (logPoint p)) =
      (fun v : ℂ => pantsFold (ofComplex v)) ∘ (fun p : ModelCoordinates => (logPoint p : ℂ)) :=
    funext fun p => by simp only [Function.comp_apply, ofComplex_apply]
  rw [h]
  exact contDiff_iff_contDiffAt.2 fun p =>
    (contDiffAt_pantsFold_ofComplex (logPoint p).im_pos).comp p contDiff_coe_logPoint.contDiffAt

theorem contMDiff_pantsFoldMap : ContMDiff (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ pantsFoldMap := by
  have hc : ContDiff ℝ ∞ (fun p : ModelCoordinates => p 2) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).contDiff
  exact contDiff_pantsFold_logPoint.contMDiff.prodMk
    (contMDiff_circleExp.comp (contDiff_const.mul hc).contMDiff)

theorem contMDiff_pantsQuotientMap :
    ContMDiff (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ pantsQuotientMap :=
  (isLocalDiffeomorph_orbitMk (𝓡 3) (pantsGroup × Multiplicative ℤ)
    ModelCoordinates).contMDiff_of_comp_of_surjective Quotient.mk''_surjective
    contMDiff_pantsFoldMap

def circlePlaneMap (y : ℂ × Circle) : ℂ × ℂ := (y.1, (y.2 : ℂ))

theorem contMDiff_circlePlaneMap :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℂ × ℂ) ∞ circlePlaneMap :=
  contMDiff_fst.prodMk_space (contMDiff_coe_sphere.comp contMDiff_snd)

def pantsFoldPlane (p : ModelCoordinates) : ℂ × ℂ :=
  (pantsFold (logPoint p), Complex.exp (((2 * Real.pi * p 2 : ℝ) : ℂ) * Complex.I))

theorem circlePlaneMap_comp : circlePlaneMap ∘ pantsFoldMap = pantsFoldPlane := by
  funext p
  simp only [Function.comp_apply, circlePlaneMap, pantsFoldMap, pantsFoldPlane, Circle.coe_exp]

theorem injective_fderiv_pantsFoldPlane (hJ : PantsFoldJacobianBound) (p : ModelCoordinates) :
    Function.Injective (fderiv ℝ pantsFoldPlane p) := by
  have hu : 0 < ((logPoint p : ℂ)).im := (logPoint p).im_pos
  have hd1 := ((contDiffAt_pantsFold_ofComplex hu).differentiableAt (by decide)).hasFDerivAt
  have h1 : HasFDerivAt (fun q : ModelCoordinates => pantsFold (logPoint q))
      ((fderiv ℝ (fun v : ℂ => pantsFold (ofComplex v)) (logPoint p)).comp (logPointDeriv p)) p :=
    (hd1.comp p (hasFDerivAt_logPoint p)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q => by simp [ofComplex_apply])
  have hθ := (Complex.ofRealCLM.hasFDerivAt.comp p
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).hasFDerivAt.const_mul
      (2 * Real.pi))).mul_const Complex.I
  have h2 := hθ.cexp
  have hP : HasFDerivAt pantsFoldPlane _ p := (h1.prodMk h2).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => by simp [pantsFoldPlane])
  rw [hP.fderiv, injective_iff_map_eq_zero]
  intro v hv
  rw [ContinuousLinearMap.prod_apply, Prod.mk_eq_zero] at hv
  obtain ⟨hv1, hv2⟩ := hv
  have hv2' : v 2 = 0 := by simpa [Complex.exp_ne_zero, Real.pi_ne_zero] using hv2
  rw [ContinuousLinearMap.comp_apply] at hv1
  have hl : logPointDeriv p v = 0 :=
    injective_fderiv_pantsFold hJ hu (hv1.trans (map_zero _).symm)
  rw [logPointDeriv_apply] at hl
  have hre : v 0 = 0 := by simpa using congrArg Complex.re hl
  have him : (Complex.exp ((p 1 : ℝ) : ℂ)).re = 0 ∨ v 1 = 0 := by
    simpa using congrArg Complex.im hl
  have hv1' : v 1 = 0 := by
    rcases him with h | h
    · exact absurd h (by rw [Complex.exp_ofReal_re]; exact (Real.exp_pos _).ne')
    · exact h
  ext i
  fin_cases i <;> simp [hre, hv1', hv2']

theorem injective_mfderiv_pantsQuotientMap (hJ : PantsFoldJacobianBound) (q : PantsQuotient) :
    Function.Injective (mfderiv (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) pantsQuotientMap q) := by
  obtain ⟨p, rfl⟩ := Quotient.mk''_surjective q
  have hπ := isLocalDiffeomorph_orbitMk (𝓡 3) (pantsGroup × Multiplicative ℤ) ModelCoordinates
  obtain ⟨e, he⟩ := hπ.isInvertible_mfderiv (by decide) p
  have hπd := (hπ.contMDiff.mdifferentiableAt (by decide) : MDifferentiableAt (𝓡 3) (𝓡 3)
    (Quotient.mk'' : ModelCoordinates → PantsQuotient) p)
  have hF := (contMDiff_pantsQuotientMap.mdifferentiableAt (by decide) :
    MDifferentiableAt (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) pantsQuotientMap (Quotient.mk'' p))
  have hι := (contMDiff_circlePlaneMap.mdifferentiableAt (by decide) :
    MDifferentiableAt (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℂ × ℂ) circlePlaneMap
      (pantsQuotientMap (Quotient.mk'' p)))
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨v, rfl⟩ := e.surjective w
  have hcomp : pantsFoldPlane = circlePlaneMap ∘
      (pantsQuotientMap ∘ (Quotient.mk'' : ModelCoordinates → PantsQuotient)) :=
    circlePlaneMap_comp.symm
  have hchain : mfderiv (𝓡 3) 𝓘(ℝ, ℂ × ℂ) pantsFoldPlane p v = 0 := by
    rw [hcomp, mfderiv_comp_apply p hι (hF.comp p hπd), mfderiv_comp_apply p hF hπd, ← he,
      ContinuousLinearEquiv.coe_coe, hw, map_zero]
  have hfd : fderiv ℝ pantsFoldPlane p v = 0 := by
    rw [mfderiv_eq_fderiv] at hchain
    exact hchain
  have hv0 : v = 0 := injective_fderiv_pantsFoldPlane hJ p (hfd.trans (map_zero _).symm)
  rw [hv0, map_zero]

theorem isLocalDiffeomorph_pantsQuotientMap (hJ : PantsFoldJacobianBound) :
    IsLocalDiffeomorph (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ pantsQuotientMap :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv pantsQuotientMap
    contMDiff_pantsQuotientMap (injective_mfderiv_pantsQuotientMap hJ)
    (by rw [finrank_euclideanSpace_fin, finrank_planeCircleModel])

theorem pantsQuotientDiffeo_of_fold (hJ : PantsFoldJacobianBound) (hI : PantsFoldImageBound)
    (hB : PantsFoldCoreBijective) : PantsQuotientDiffeo := by
  have hloc := isLocalDiffeomorph_pantsQuotientMap hJ
  have himg : hloc.image = pantsImage := TopologicalSpace.Opens.ext (by
    change hloc.image.1 = _
    rw [IsLocalDiffeomorph.image_coe]
    exact range_pantsQuotientMap hI hB)
  exact ⟨himg ▸ DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage pantsQuotientMap hloc
    (injective_pantsQuotientMap hB)⟩

end GC.Seifert
