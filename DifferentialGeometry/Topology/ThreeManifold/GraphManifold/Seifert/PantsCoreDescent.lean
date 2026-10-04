import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldDiffeo

/-!
# The pants quotient from an arbitrary core map of the ideal triangle

Packet K16f. The descent of `Seifert/PantsFold.lean` and `Seifert/PantsFoldDiffeo.lean`, redone
for an arbitrary core map `F : ℂ → ℂ`, smooth on an open neighbourhood `U` of the closed ideal
triangle, in place of `foldCore`. The wall hypothesis `F (σᵢ • z) = conj (F z)` near `wall i`
makes `F` real on the walls (`core_conj_of_mem_wall`), so `coreFold F z = κ(w) (F (w • z))` is
well defined (`coreFold_eq`), invariant under `pantsGroup` (`coreFold_smul`) and given near every
point by one such formula (`coreFold_eventuallyEq`), hence smooth
(`contDiffAt_coreFold_ofComplex`); its derivative is injective where `det F' ≠ 0`
(`injective_fderiv_coreFold`).

By the inverse function theorem a point of the triangle where `F` is real lies on a wall
(`core_exists_mem_wall_of_im_eq_zero`: otherwise `F` would map an interior neighbourhood onto a
neighbourhood of a real point, against `0 ≤ im F`). With the bijection of the triangle onto the
closed upper half of the open pants this gives injectivity modulo `pantsGroup`
(`exists_mem_pantsGroup_smul_eq_of_coreFold_eq`) and `range_coreFold`. The map
`coreFoldMap F p = (coreFold F (logPoint p), exp (2πi p₂))` descends to `coreQuotientMap`, an
injective local diffeomorphism `PantsQuotient → ℂ × S¹` with range `pantsImage`, and
`pantsQuotientDiffeo_of_core` proves `PantsQuotientDiffeo` exactly as `pantsQuotientDiffeo_of_fold`.
-/

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Matrix GC.Geometry
open scoped MatrixGroups ComplexConjugate ContDiff Topology Manifold

namespace GC.Seifert

attribute [local instance] finrank_real_complex_fact'

def coreFold (F : ℂ → ℂ) (z : ℍ) : ℂ :=
  foldSign (foldChoice z) (F ((foldChoice z • z : ℍ) : ℂ))

theorem core_conj_of_mem_wall {F : ℂ → ℂ}
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z))
    (i : Fin 3) (z : ℍ) (hz : z ∈ wall i) : conj (F z) = F z := by
  obtain ⟨V, -, hV, hF⟩ := hwall i
  have h := hF z (hV hz)
  rw [wallReflection_smul_of_mem_wall hz] at h
  exact h.symm

theorem coreFold_eq {F : ℂ → ℂ} (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z)
    {w : GL (Fin 2) ℝ} (hw : w ∈ triangleGroup) {z : ℍ} (hz : w • z ∈ idealTriangle) :
    coreFold F z = foldSign w (F ((w • z : ℍ) : ℂ)) := by
  have h₀ := foldChoice_smul_mem z
  have hmem : w * (foldChoice z)⁻¹ ∈ triangleGroup := mul_mem hw (inv_mem (foldChoice_mem z))
  have hsm : (w * (foldChoice z)⁻¹) • (foldChoice z • z) = w • z := by
    rw [mul_smul, inv_smul_smul]
  obtain ⟨heq, hcase⟩ := smul_mem_idealTriangle hmem h₀ (hsm.symm ▸ hz)
  rw [hsm] at heq
  unfold coreFold
  rw [heq]
  rcases hcase with h1 | ⟨i, hi, -⟩
  · rw [mul_inv_eq_one.mp h1]
  · have hr := hreal i _ hi
    rw [foldSign_of_conj_eq _ hr, foldSign_of_conj_eq _ hr]

theorem coreFold_of_mem_idealTriangle {F : ℂ → ℂ}
    (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z) {z : ℍ} (hz : z ∈ idealTriangle) :
    coreFold F z = F z := by
  rw [coreFold_eq hreal (one_mem _) (by rw [one_smul]; exact hz), one_smul,
    foldSign_of_det_pos (by simp)]

theorem coreFold_wallReflection_smul {F : ℂ → ℂ}
    (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z) (i : Fin 3) (z : ℍ) :
    coreFold F (wallReflection i • z) = conj (coreFold F z) := by
  have hw : foldChoice z * wallReflection i ∈ triangleGroup :=
    mul_mem (foldChoice_mem z) (wallReflection_mem_triangleGroup i)
  have hsm : (foldChoice z * wallReflection i) • (wallReflection i • z) = foldChoice z • z := by
    rw [mul_smul, wallReflection_smul_smul]
  rw [coreFold_eq hreal hw (hsm.symm ▸ foldChoice_smul_mem z), hsm,
    foldSign_mul_of_det_neg (by rw [val_det_wallReflection]; norm_num)]
  rfl

theorem coreFold_smul {F : ℂ → ℂ} (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z)
    {γ : SL(2, ℤ)} (hγ : γ ∈ pantsGroup) (z : ℍ) : coreFold F (γ • z) = coreFold F z := by
  obtain ⟨w, hw, hdet, hγw⟩ := exists_triangleGroup_smul_eq hγ
  rw [hγw]
  have hw' : foldChoice z * w⁻¹ ∈ triangleGroup := mul_mem (foldChoice_mem z) (inv_mem hw)
  have hsm : (foldChoice z * w⁻¹) • (w • z) = foldChoice z • z := by
    rw [mul_smul, inv_smul_smul]
  rw [coreFold_eq hreal hw' (hsm.symm ▸ foldChoice_smul_mem z), hsm,
    foldSign_mul_of_det_pos (by rw [map_inv, hdet, inv_one, Units.val_one]; norm_num)]
  rfl

theorem coreFold_eventuallyEq {F : ℂ → ℂ}
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z)) (z₀ : ℍ) :
    ∀ᶠ z in 𝓝 z₀,
      coreFold F z = foldSign (foldChoice z₀) (F ((foldChoice z₀ • z : ℍ) : ℂ)) := by
  have hreal := core_conj_of_mem_wall hwall
  have hw₀ := foldChoice_mem z₀
  have hζ₀ := foldChoice_smul_mem z₀
  have hc : Continuous (fun z : ℍ => foldChoice z₀ • z) := continuous_const_smul _
  by_cases hint : ∀ i, 0 < wallSide i (foldChoice z₀ • z₀)
  · have hev : ∀ᶠ z in 𝓝 z₀, ∀ i, 0 < wallSide i (foldChoice z₀ • z) := by
      rw [Filter.eventually_all]
      intro i
      exact ((continuous_wallSide i).comp hc).continuousAt.eventually (lt_mem_nhds (hint i))
    filter_upwards [hev] with z hz
    exact coreFold_eq hreal hw₀ ((mem_idealTriangle_iff _).2 fun i => (hz i).le)
  · push Not at hint
    obtain ⟨i, hi⟩ := hint
    have hi0 : wallSide i (foldChoice z₀ • z₀) = 0 :=
      le_antisymm hi ((mem_idealTriangle_iff _).1 hζ₀ i)
    have hzw : foldChoice z₀ • z₀ ∈ wall i := (mem_wall_iff i _).2 hi0
    have hother : ∀ j, j ≠ i → 0 < wallSide j (foldChoice z₀ • z₀) := fun j hj =>
      pos_wallSide_of_mem_idealTriangle hζ₀
        fun hj' => Set.disjoint_left.1 (wall_disjoint hj) hj' hzw
    have hfix : wallReflection i • foldChoice z₀ • z₀ = foldChoice z₀ • z₀ :=
      wallReflection_smul_of_mem_wall hzw
    have hc2 : Continuous (fun z : ℍ => wallReflection i • foldChoice z₀ • z) :=
      (continuous_const_smul _).comp hc
    have e1 : ∀ᶠ z in 𝓝 z₀, ∀ j, j ≠ i → 0 < wallSide j (foldChoice z₀ • z) := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : j = i
      · exact Filter.Eventually.of_forall fun z h => absurd hj h
      · exact (((continuous_wallSide j).comp hc).continuousAt.eventually
          (lt_mem_nhds (hother j hj))).mono fun z hz hji => hz
    have e2 : ∀ᶠ z in 𝓝 z₀, ∀ j, j ≠ i →
        0 < wallSide j (wallReflection i • foldChoice z₀ • z) := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : j = i
      · exact Filter.Eventually.of_forall fun z h => absurd hj h
      · have h0 : 0 < wallSide j (wallReflection i • foldChoice z₀ • z₀) := by
          rw [hfix]
          exact hother j hj
        exact (((continuous_wallSide j).comp hc2).continuousAt.eventually
          (lt_mem_nhds h0)).mono fun z hz hji => hz
    obtain ⟨V, hVo, hWV, hVF⟩ := hwall i
    have e3 : ∀ᶠ z in 𝓝 z₀, foldChoice z₀ • z ∈ V :=
      hc.continuousAt.preimage_mem_nhds (hVo.mem_nhds (hWV hzw))
    filter_upwards [e1, e2, e3] with z h1 h2 h3
    by_cases hs : 0 ≤ wallSide i (foldChoice z₀ • z)
    · refine coreFold_eq hreal hw₀ ((mem_idealTriangle_iff _).2 fun j => ?_)
      by_cases hj : j = i
      · rw [hj]
        exact hs
      · exact (h1 j hj).le
    · push Not at hs
      have hmem : wallReflection i • foldChoice z₀ • z ∈ idealTriangle := by
        refine (mem_idealTriangle_iff _).2 fun j => ?_
        by_cases hj : j = i
        · rw [hj]
          exact ((wallSide_wallReflection_smul_pos_iff i _).2 hs).le
        · exact (h2 j hj).le
      have hw' : wallReflection i * foldChoice z₀ ∈ triangleGroup :=
        mul_mem (wallReflection_mem_triangleGroup i) hw₀
      rw [coreFold_eq hreal hw' (by rw [mul_smul]; exact hmem), mul_smul, hVF _ h3,
        foldSign_comm_mul_of_det_neg (by rw [val_det_wallReflection]; norm_num), foldSign_conj,
        Complex.conj_conj]

theorem coreFold_ofComplex_eventuallyEq {F : ℂ → ℂ}
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z)) {u : ℂ} (hu : 0 < u.im) :
    ∀ᶠ v in 𝓝 u, coreFold F (ofComplex v) = foldSign (foldChoice ⟨u, hu⟩)
      (F ((foldChoice ⟨u, hu⟩ • ofComplex v : ℍ) : ℂ)) := by
  have hnhds : 𝓝 u = Filter.map UpperHalfPlane.coe (𝓝 (⟨u, hu⟩ : ℍ)) :=
    (isOpenEmbedding_coe.map_nhds_eq (⟨u, hu⟩ : ℍ)).symm
  rw [hnhds, Filter.eventually_map]
  exact (coreFold_eventuallyEq hwall _).mono fun z hz => by rw [ofComplex_apply]; exact hz

theorem contDiffAt_coreFold_ofComplex {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z)) {u : ℂ} (hu : 0 < u.im) :
    ContDiffAt ℝ ∞ (fun v : ℂ => coreFold F (ofComplex v)) u := by
  set z₀ : ℍ := ⟨u, hu⟩ with hz₀
  set w₀ := foldChoice z₀ with hw₀
  have h1 := coreFold_ofComplex_eventuallyEq hwall hu
  have hopen : ∀ᶠ v in 𝓝 u, 0 < v.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hu
  have h2 : ∀ᶠ v in 𝓝 u, coreFold F (ofComplex v) =
      foldSign w₀ (F (foldSign w₀ (num w₀ v / denom w₀ v))) := by
    filter_upwards [h1, hopen] with v hv hvim
    rw [hv, ofComplex_apply_of_im_pos hvim, coe_smul, sigma_apply_eq_foldSign]
  have hden : denom w₀ u ≠ 0 := denom_ne_zero_of_im w₀ hu.ne'
  have hq : ContDiffAt ℂ ∞ (fun v : ℂ => num w₀ v / denom w₀ v) u :=
    ContDiffAt.div (f := fun v : ℂ => (w₀ 0 0 : ℂ) * v + w₀ 0 1)
      (g := fun v : ℂ => (w₀ 1 0 : ℂ) * v + w₀ 1 1)
      ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
      ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const) hden
  have hpt : foldSign w₀ (num w₀ u / denom w₀ u) = ((w₀ • z₀ : ℍ) : ℂ) := by
    rw [coe_smul, sigma_apply_eq_foldSign]
  have hζ := foldChoice_smul_mem z₀
  have hcore : ContDiffAt ℝ ∞ F (foldSign w₀ (num w₀ u / denom w₀ u)) := by
    rw [hpt]
    exact hF.contDiffAt (hU.mem_nhds (hΔU _ hζ))
  have hinner : ContDiffAt ℝ ∞ (fun v : ℂ => foldSign w₀ (num w₀ v / denom w₀ v)) u :=
    (contDiff_foldSign w₀).contDiffAt.comp u (hq.restrict_scalars ℝ)
  have hmid : ContDiffAt ℝ ∞ (fun v : ℂ => F (foldSign w₀ (num w₀ v / denom w₀ v))) u :=
    ContDiffAt.comp (g := F) u hcore hinner
  have hG : ContDiffAt ℝ ∞
      (fun v : ℂ => foldSign w₀ (F (foldSign w₀ (num w₀ v / denom w₀ v)))) u :=
    ContDiffAt.comp (g := foldSign w₀) u (contDiff_foldSign w₀).contDiffAt hmid
  exact hG.congr_of_eventuallyEq h2

private theorem injective_of_det_ne_zero {f : ℂ →L[ℝ] ℂ} (h : f.det ≠ 0) :
    Function.Injective f := by
  have hu : IsUnit (f : ℂ →ₗ[ℝ] ℂ) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hu)

theorem injective_fderiv_coreFold {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z))
    (hdet : ∀ z : ℍ, z ∈ idealTriangle → (fderiv ℝ F z).det ≠ 0) {u : ℂ} (hu : 0 < u.im) :
    Function.Injective (fderiv ℝ (fun v : ℂ => coreFold F (ofComplex v)) u) := by
  set z₀ : ℍ := ⟨u, hu⟩
  set w := foldChoice z₀
  set ζ : ℍ := w • ofComplex u
  have hζ : ζ ∈ idealTriangle := by
    change w • ofComplex u ∈ idealTriangle
    rw [ofComplex_apply_of_im_pos hu]
    exact foldChoice_smul_mem z₀
  obtain ⟨S, hSinj, hS⟩ := exists_hasFDerivAt_foldSign w
  have hcore : HasFDerivAt F (fderiv ℝ F (ζ : ℂ)) (ζ : ℂ) :=
    ((hF.contDiffAt (hU.mem_nhds (hΔU ζ hζ))).differentiableAt (by decide)).hasFDerivAt
  have hsm : HasFDerivAt (fun v : ℂ => ((w • ofComplex v : ℍ) : ℂ)) (smulFDeriv w z₀) u :=
    (hasStrictFDerivAt_smul w z₀).hasFDerivAt
  have h1 := hcore.comp u hsm
  have hcomp := (hS (F (ζ : ℂ))).comp u h1
  rw [(hcomp.congr_of_eventuallyEq (coreFold_ofComplex_eventuallyEq hwall hu)).fderiv]
  exact hSinj.comp ((injective_of_det_ne_zero (hdet _ hζ)).comp (injective_smulFDeriv w z₀))

theorem core_exists_mem_wall_of_im_eq_zero {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hdet : ∀ z : ℍ, z ∈ idealTriangle → (fderiv ℝ F z).det ≠ 0)
    (him : ∀ z : ℍ, z ∈ idealTriangle → 0 ≤ (F z).im) {z : ℍ} (hz : z ∈ idealTriangle)
    (h : (F z).im = 0) : ∃ i, z ∈ wall i := by
  by_contra hcon
  push Not at hcon
  have hzI : z ∈ idealTriangleInterior :=
    (mem_idealTriangleInterior_iff z).2 fun i => pos_wallSide_of_mem_idealTriangle hz (hcon i)
  have hopen : IsOpen (UpperHalfPlane.coe '' idealTriangleInterior) :=
    isOpenEmbedding_coe.isOpenMap _ (interior_idealTriangle ▸ isOpen_interior)
  have hstrict := (hF.contDiffAt (hU.mem_nhds (hΔU z hz))).hasStrictFDerivAt (by decide)
  have hrange : LinearMap.range (fderiv ℝ F (z : ℂ) : ℂ →ₗ[ℝ] ℂ) = ⊤ := by
    have hu : IsUnit ((fderiv ℝ F (z : ℂ)) : ℂ →ₗ[ℝ] ℂ) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hdet z hz))
    exact (LinearMap.isUnit_iff_range_eq_top _).1 hu
  have hmem : F '' (UpperHalfPlane.coe '' idealTriangleInterior) ∈ 𝓝 (F z) := by
    rw [← hstrict.map_nhds_eq_of_surj hrange]
    exact Filter.image_mem_map (hopen.mem_nhds ⟨z, hzI, rfl⟩)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
  have hv : F z - ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ Metric.ball (F z) ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  obtain ⟨-, ⟨y, hy, rfl⟩, hyv⟩ := hball hv
  have hy0 := him y (idealTriangleInterior_subset hy)
  rw [hyv] at hy0
  simp [h] at hy0
  linarith

theorem exists_mem_pantsGroup_smul_eq_of_coreFold_eq {F : ℂ → ℂ}
    (hinj : Set.InjOn (fun z : ℍ => F z) idealTriangle)
    (him : ∀ z : ℍ, z ∈ idealTriangle → 0 ≤ (F z).im)
    (hwim : ∀ z : ℍ, z ∈ idealTriangle → (F z).im = 0 → ∃ i, z ∈ wall i) {z z' : ℍ}
    (h : coreFold F z = coreFold F z') : ∃ γ ∈ pantsGroup, γ • z = z' := by
  have hw := foldChoice_mem z
  have hw' := foldChoice_mem z'
  have hζ := foldChoice_smul_mem z
  have hζ' := foldChoice_smul_mem z'
  suffices hv : ∃ v ∈ triangleGroup, v.det = 1 ∧ v • z = z' by
    obtain ⟨v, hv, hdet, hvz⟩ := hv
    obtain ⟨γ, hγ, hγv⟩ := exists_pantsGroup_smul_eq hv hdet
    exact ⟨γ, hγ, by rw [← hγv, hvz]⟩
  have hi := him _ hζ
  have hi' := him _ hζ'
  unfold coreFold at h
  have hdirect (heq : foldChoice z • z = foldChoice z' • z')
      (hd : (foldChoice z).det.val = (foldChoice z').det.val) :
      ∃ v ∈ triangleGroup, v.det = 1 ∧ v • z = z' := by
    refine ⟨(foldChoice z')⁻¹ * foldChoice z, mul_mem (inv_mem hw') hw, ?_, ?_⟩
    · refine Units.val_eq_one.mp ?_
      rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hd,
        inv_mul_cancel₀ (val_det_ne_zero _)]
    · rw [mul_smul, heq, inv_smul_smul]
  have hwl (heq : foldChoice z • z = foldChoice z' • z') (i : Fin 3)
      (hiw : foldChoice z • z ∈ wall i)
      (hd : (foldChoice z).det.val = -(foldChoice z').det.val) :
      ∃ v ∈ triangleGroup, v.det = 1 ∧ v • z = z' := by
    refine ⟨(foldChoice z')⁻¹ * wallReflection i * foldChoice z,
      mul_mem (mul_mem (inv_mem hw') (wallReflection_mem_triangleGroup i)) hw, ?_, ?_⟩
    · refine Units.val_eq_one.mp ?_
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val,
        val_det_wallReflection, hd]
      have := val_det_ne_zero (foldChoice z')
      field_simp
    · rw [mul_smul, mul_smul, wallReflection_smul_of_mem_wall hiw, heq, inv_smul_smul]
  rcases val_det_eq_one_or_of_mem_triangleGroup hw with hd | hd <;>
    rcases val_det_eq_one_or_of_mem_triangleGroup hw' with hd' | hd'
  · rw [foldSign_of_det_pos (by rw [hd]; norm_num), foldSign_of_det_pos (by rw [hd']; norm_num)]
      at h
    exact hdirect (hinj hζ hζ' h) (by rw [hd, hd'])
  · rw [foldSign_of_det_pos (by rw [hd]; norm_num), foldSign_of_det_neg (by rw [hd']; norm_num)]
      at h
    have hz0 : (F ((foldChoice z' • z' : ℍ) : ℂ)).im = 0 := by
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    have hreal : conj (F ((foldChoice z' • z' : ℍ) : ℂ)) = F ((foldChoice z' • z' : ℍ) : ℂ) :=
      Complex.conj_eq_iff_im.2 hz0
    rw [hreal] at h
    have heq := hinj hζ hζ' h
    obtain ⟨i, hiw⟩ := hwim _ hζ (by
      have := congrArg Complex.im h
      rw [hz0] at this
      exact this)
    exact hwl heq i hiw (by linarith)
  · rw [foldSign_of_det_neg (by rw [hd]; norm_num), foldSign_of_det_pos (by rw [hd']; norm_num)]
      at h
    have hz0 : (F ((foldChoice z • z : ℍ) : ℂ)).im = 0 := by
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    have hreal : conj (F ((foldChoice z • z : ℍ) : ℂ)) = F ((foldChoice z • z : ℍ) : ℂ) :=
      Complex.conj_eq_iff_im.2 hz0
    rw [hreal] at h
    have heq := hinj hζ hζ' h
    obtain ⟨i, hiw⟩ := hwim _ hζ hz0
    exact hwl heq i hiw (by linarith)
  · rw [foldSign_of_det_neg (by rw [hd]; norm_num), foldSign_of_det_neg (by rw [hd']; norm_num)]
      at h
    exact hdirect (hinj hζ hζ' ((starRingEnd ℂ).injective h)) (by rw [hd, hd'])

theorem range_coreFold {F : ℂ → ℂ} (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z)
    (hbij : Set.BijOn (fun z : ℍ => F z) idealTriangle
      {u : ℂ | planarFunction 3 u < 0 ∧ 0 ≤ u.im}) :
    Set.range (coreFold F) = {u | planarFunction 3 u < 0} := by
  ext u
  constructor
  · rintro ⟨z, rfl⟩
    have h : planarFunction 3 (F ((foldChoice z • z : ℍ) : ℂ)) < 0 :=
      (hbij.mapsTo (foldChoice_smul_mem z)).1
    change planarFunction 3 (foldSign (foldChoice z) (F ((foldChoice z • z : ℍ) : ℂ))) < 0
    unfold foldSign
    split_ifs
    · exact h
    · rwa [planarFunction_three_conj]
  · intro hu
    by_cases hui : 0 ≤ u.im
    · obtain ⟨z, hz, hzu⟩ := hbij.surjOn (show u ∈ {u : ℂ | planarFunction 3 u < 0 ∧ 0 ≤ u.im}
        from ⟨hu, hui⟩)
      exact ⟨z, (coreFold_of_mem_idealTriangle hreal hz).trans hzu⟩
    · obtain ⟨z, hz, hzu⟩ := hbij.surjOn (show conj u ∈ {u : ℂ | planarFunction 3 u < 0 ∧
        0 ≤ u.im} from ⟨by rwa [planarFunction_three_conj], by rw [Complex.conj_im]; linarith⟩)
      refine ⟨wallReflection 0 • z, ?_⟩
      have hzu' : F z = conj u := hzu
      rw [coreFold_wallReflection_smul hreal, coreFold_of_mem_idealTriangle hreal hz, hzu',
        Complex.conj_conj]

def coreFoldMap (F : ℂ → ℂ) (p : ModelCoordinates) : ℂ × Circle :=
  (coreFold F (logPoint p), Circle.exp (2 * Real.pi * p 2))

theorem coreFoldMap_smul {F : ℂ → ℂ} (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z)
    (γ : pantsGroup × Multiplicative ℤ) (p : ModelCoordinates) :
    coreFoldMap F (γ • p) = coreFoldMap F p := by
  rw [coreFoldMap, coreFoldMap, logPoint_pants_smul, coreFold_smul hreal γ.1.2, pants_smul_two]
  congr 1
  rw [mul_add, Circle.exp_add, show 2 * Real.pi * ((Multiplicative.toAdd γ.2 : ℤ) : ℝ) =
    ((Multiplicative.toAdd γ.2 : ℤ) : ℝ) * (2 * Real.pi) by ring, Circle.exp_int_mul_two_pi,
    mul_one]

def coreQuotientMap {F : ℂ → ℂ} (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z) :
    PantsQuotient → ℂ × Circle :=
  Quotient.lift (coreFoldMap F) fun a b h => by
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 h)
    exact coreFoldMap_smul hreal γ b

theorem injective_coreQuotientMap {F : ℂ → ℂ}
    (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z)
    (hinj : Set.InjOn (fun z : ℍ => F z) idealTriangle)
    (him : ∀ z : ℍ, z ∈ idealTriangle → 0 ≤ (F z).im)
    (hwim : ∀ z : ℍ, z ∈ idealTriangle → (F z).im = 0 → ∃ i, z ∈ wall i) :
    Function.Injective (coreQuotientMap hreal) := by
  rintro ⟨p⟩ ⟨q⟩ h
  change coreFoldMap F p = coreFoldMap F q at h
  simp only [coreFoldMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨γ, hγ, hγp⟩ := exists_mem_pantsGroup_smul_eq_of_coreFold_eq hinj him hwim h1
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h2
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hp2 : p 2 = q 2 + m := mul_left_cancel₀ hpi (by linear_combination hm)
  apply Quot.sound
  refine MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2
    ⟨(⟨γ⁻¹, inv_mem hγ⟩, Multiplicative.ofAdd m), ?_⟩)
  change logCoords ((γ⁻¹ : SL(2, ℤ)) • logPoint q) (q 2 + ((Multiplicative.toAdd
    (Multiplicative.ofAdd m) : ℤ) : ℝ)) = p
  rw [← hγp, inv_smul_smul, toAdd_ofAdd, ← hp2, logCoords_logPoint]

theorem range_coreQuotientMap {F : ℂ → ℂ}
    (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z)
    (hbij : Set.BijOn (fun z : ℍ => F z) idealTriangle
      {u : ℂ | planarFunction 3 u < 0 ∧ 0 ≤ u.im}) :
    Set.range (coreQuotientMap hreal) = (pantsImage : Set (ℂ × Circle)) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨p, rfl⟩ := Quotient.mk''_surjective q
    change planarFunction 3 (coreFold F (logPoint p)) < 0
    have h : coreFold F (logPoint p) ∈ Set.range (coreFold F) := ⟨logPoint p, rfl⟩
    rw [range_coreFold hreal hbij] at h
    exact h
  · intro hy
    have h : y.1 ∈ Set.range (coreFold F) := by
      rw [range_coreFold hreal hbij]
      exact mem_pantsImage.1 hy
    obtain ⟨z, hz⟩ := h
    refine ⟨Quotient.mk'' (logCoords z (liftAngle 0 (y.2 : ℂ))), Prod.ext ?_ ?_⟩
    · change coreFold F (logPoint (logCoords z _)) = y.1
      rw [logPoint_logCoords, hz]
    · change Circle.exp (2 * Real.pi * logCoords z (liftAngle 0 (y.2 : ℂ)) 2) = y.2
      rw [logCoords_two]
      exact circleExp_liftAngle 0 y.2

theorem contDiff_coreFold_logPoint {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z)) :
    ContDiff ℝ ∞ (fun p : ModelCoordinates => coreFold F (logPoint p)) := by
  have h : (fun p : ModelCoordinates => coreFold F (logPoint p)) =
      (fun v : ℂ => coreFold F (ofComplex v)) ∘ (fun p : ModelCoordinates => (logPoint p : ℂ)) :=
    funext fun p => by simp only [Function.comp_apply, ofComplex_apply]
  rw [h]
  exact contDiff_iff_contDiffAt.2 fun p =>
    (contDiffAt_coreFold_ofComplex hU hΔU hF hwall (logPoint p).im_pos).comp p
      contDiff_coe_logPoint.contDiffAt

theorem contMDiff_coreFoldMap {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z)) :
    ContMDiff (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ (coreFoldMap F) := by
  have hc : ContDiff ℝ ∞ (fun p : ModelCoordinates => p 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff
  exact (contDiff_coreFold_logPoint hU hΔU hF hwall).contMDiff.prodMk
    (contMDiff_circleExp.comp (contDiff_const.mul hc).contMDiff)

theorem contMDiff_coreQuotientMap {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z)) :
    ContMDiff (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
      (coreQuotientMap (core_conj_of_mem_wall hwall)) :=
  (isLocalDiffeomorph_orbitMk (𝓡 3) (pantsGroup × Multiplicative ℤ)
    ModelCoordinates).contMDiff_of_comp_of_surjective Quotient.mk''_surjective
    (contMDiff_coreFoldMap hU hΔU hF hwall)

def coreFoldPlane (F : ℂ → ℂ) (p : ModelCoordinates) : ℂ × ℂ :=
  (coreFold F (logPoint p), Complex.exp (((2 * Real.pi * p 2 : ℝ) : ℂ) * Complex.I))

theorem circlePlaneMap_comp_coreFoldMap (F : ℂ → ℂ) :
    circlePlaneMap ∘ coreFoldMap F = coreFoldPlane F := by
  funext p
  simp only [Function.comp_apply, circlePlaneMap, coreFoldMap, coreFoldPlane, Circle.coe_exp]

theorem injective_fderiv_coreFoldPlane {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z))
    (hdet : ∀ z : ℍ, z ∈ idealTriangle → (fderiv ℝ F z).det ≠ 0) (p : ModelCoordinates) :
    Function.Injective (fderiv ℝ (coreFoldPlane F) p) := by
  have hu : 0 < ((logPoint p : ℂ)).im := (logPoint p).im_pos
  have hd1 :=
    ((contDiffAt_coreFold_ofComplex hU hΔU hF hwall hu).differentiableAt (by decide)).hasFDerivAt
  have h1 : HasFDerivAt (fun q : ModelCoordinates => coreFold F (logPoint q))
      ((fderiv ℝ (fun v : ℂ => coreFold F (ofComplex v)) (logPoint p)).comp
        (logPointDeriv p)) p :=
    (hd1.comp p (hasFDerivAt_logPoint p)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q => by simp [ofComplex_apply])
  have hθ := (Complex.ofRealCLM.hasFDerivAt.comp p
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt.const_mul
      (2 * Real.pi))).mul_const Complex.I
  have h2 := hθ.cexp
  have hP : HasFDerivAt (coreFoldPlane F) _ p := (h1.prodMk h2).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => by simp [coreFoldPlane])
  rw [hP.fderiv, injective_iff_map_eq_zero]
  intro v hv
  rw [ContinuousLinearMap.prod_apply, Prod.mk_eq_zero] at hv
  obtain ⟨hv1, hv2⟩ := hv
  have hv2' : v 2 = 0 := by simpa [Complex.exp_ne_zero, Real.pi_ne_zero] using hv2
  rw [ContinuousLinearMap.comp_apply] at hv1
  have hl : logPointDeriv p v = 0 :=
    injective_fderiv_coreFold hU hΔU hF hwall hdet hu (hv1.trans (map_zero _).symm)
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

theorem injective_mfderiv_coreQuotientMap {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z))
    (hdet : ∀ z : ℍ, z ∈ idealTriangle → (fderiv ℝ F z).det ≠ 0) (q : PantsQuotient) :
    Function.Injective (mfderiv (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1))
      (coreQuotientMap (core_conj_of_mem_wall hwall)) q) := by
  obtain ⟨p, rfl⟩ := Quotient.mk''_surjective q
  have hπ := isLocalDiffeomorph_orbitMk (𝓡 3) (pantsGroup × Multiplicative ℤ) ModelCoordinates
  obtain ⟨e, he⟩ := hπ.isInvertible_mfderiv (by decide) p
  have hπd := (hπ.contMDiff.mdifferentiableAt (by decide) : MDifferentiableAt (𝓡 3) (𝓡 3)
    (Quotient.mk'' : ModelCoordinates → PantsQuotient) p)
  have hF' := ((contMDiff_coreQuotientMap hU hΔU hF hwall).mdifferentiableAt (by decide) :
    MDifferentiableAt (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) (coreQuotientMap (core_conj_of_mem_wall hwall))
      (Quotient.mk'' p))
  have hι := (contMDiff_circlePlaneMap.mdifferentiableAt (by decide) :
    MDifferentiableAt (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℂ × ℂ) circlePlaneMap
      (coreQuotientMap (core_conj_of_mem_wall hwall) (Quotient.mk'' p)))
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨v, rfl⟩ := e.surjective w
  have hcomp : coreFoldPlane F = circlePlaneMap ∘
      (coreQuotientMap (core_conj_of_mem_wall hwall) ∘
        (Quotient.mk'' : ModelCoordinates → PantsQuotient)) :=
    (circlePlaneMap_comp_coreFoldMap F).symm
  have hchain : mfderiv (𝓡 3) 𝓘(ℝ, ℂ × ℂ) (coreFoldPlane F) p v = 0 := by
    rw [hcomp, mfderiv_comp_apply p hι (hF'.comp p hπd), mfderiv_comp_apply p hF' hπd, ← he,
      ContinuousLinearEquiv.coe_coe, hw, map_zero]
  have hfd : fderiv ℝ (coreFoldPlane F) p v = 0 := by
    rw [mfderiv_eq_fderiv] at hchain
    exact hchain
  have hv0 : v = 0 :=
    injective_fderiv_coreFoldPlane hU hΔU hF hwall hdet p (hfd.trans (map_zero _).symm)
  rw [hv0, map_zero]

theorem isLocalDiffeomorph_coreQuotientMap {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z))
    (hdet : ∀ z : ℍ, z ∈ idealTriangle → (fderiv ℝ F z).det ≠ 0) :
    IsLocalDiffeomorph (𝓡 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
      (coreQuotientMap (core_conj_of_mem_wall hwall)) :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
    (coreQuotientMap (core_conj_of_mem_wall hwall)) (contMDiff_coreQuotientMap hU hΔU hF hwall)
    (injective_mfderiv_coreQuotientMap hU hΔU hF hwall hdet)
    (by rw [finrank_euclideanSpace_fin, finrank_planeCircleModel])

theorem pantsQuotientDiffeo_of_core {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z))
    (hdet : ∀ z : ℍ, z ∈ idealTriangle → (fderiv ℝ F z).det ≠ 0)
    (hbij : Set.BijOn (fun z : ℍ => F z) idealTriangle
      {u : ℂ | planarFunction 3 u < 0 ∧ 0 ≤ u.im}) :
    PantsQuotientDiffeo := by
  have hreal := core_conj_of_mem_wall hwall
  have him : ∀ z : ℍ, z ∈ idealTriangle → 0 ≤ (F z).im := fun z hz => (hbij.mapsTo hz).2
  have hwim : ∀ z : ℍ, z ∈ idealTriangle → (F z).im = 0 → ∃ i, z ∈ wall i := fun z hz h =>
    core_exists_mem_wall_of_im_eq_zero hU hΔU hF hdet him hz h
  have hloc := isLocalDiffeomorph_coreQuotientMap hU hΔU hF hwall hdet
  have himg : hloc.image = pantsImage := TopologicalSpace.Opens.ext (by
    change hloc.image.1 = _
    rw [IsLocalDiffeomorph.image_coe]
    exact range_coreQuotientMap hreal hbij)
  exact ⟨himg ▸ DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage
    (coreQuotientMap hreal) hloc (injective_coreQuotientMap hreal hbij.injOn him hwim)⟩

end GC.Seifert
