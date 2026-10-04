import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledGluing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsDegrees
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Adapters

/-!
# The pants with one filled hole as a Seifert block

Chapter 6, packet K06c. For a `ConeFilling` `c` (`p ≥ 1`, `p b - a q = 1`) the cut carrier
`productSet 3 ⊕ solidSet` with the pairing `filledPairing` (solid torus on the left, the hole about
`3/2` of the pants on the right, `matching = linearTorusDiffeomorph !![-p, a; -q, b]`) and the two
free tori of the pants is a torus presentation `filledPresentation` of `filledCarrier`. The cut
carrier is oriented by pulling back along the fold, so `quotient_oriented` holds by construction,
and the two collars reverse the boundary orientation because, after folding, they are the seam
composed with `s ↦ -s` and the seam itself (`filledReversing`). The interior of the cut carrier is
identified with the interior of the filled carrier minus the seam torus
(`filledInteriorDiffeomorph`).

The pants piece is product fibred over `pantsPlanarBase` (`filledProductPiece`, ports: outer
circle, filled hole, second hole) and the solid torus over `discPlanarBase p`
(`filledSolidPiece`). The matrix of `linearTorusDiffeomorph A` is `A`
(`torusMapMatrix_linearTorusMap`, the named input `TorusMatrixLinear` of K08 for all `A`), so the
meridian goes to `-(p, q)` and `filledBlock` is a `SeifertBlock` for `oneConeData p q`
(`k = 3`, two free ports, one cone `(p, q)`, `p ≥ 2`). It is good by `isGoodBlock_of_one_filling`
(`filledBlock_isGoodBlock`). `oneConeBlock p q` builds it from any coprime `(p, q)`, `p ≥ 2`,
through Bézout coefficients (`coneFillingOf`).
-/

set_option autoImplicit false

noncomputable section
open Set Metric Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem torusMapMatrix_linearTorusMap (A : Matrix (Fin 2) (Fin 2) ℤ) :
    torusMapMatrix ⟨linearTorusMap A, (contMDiff_linearTorusMap A).continuous⟩ = A := by
  have h : (⟨linearTorusMap A, (contMDiff_linearTorusMap A).continuous⟩ : C(Torus, Torus)) =
      torusFst ^ A 0 0 * (torusFst.comp torusSwap) ^ A 0 1 * (torusSwap.comp torusFst) ^ A 1 0 *
        (torusSwap.comp (torusFst.comp torusSwap)) ^ A 1 1 := by
    ext x <;> simp [linearTorusMap, torusFst, torusSwap]
  rw [h, torusMapMatrix_mul, torusMapMatrix_mul, torusMapMatrix_mul, torusMapMatrix_zpow,
    torusMapMatrix_zpow, torusMapMatrix_zpow, torusMapMatrix_zpow]
  simp only [torusMapMatrix_comp, torusMapMatrix_torusFst, torusMapMatrix_torusSwap]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

namespace ConeFilling

variable (c : ConeFilling)

theorem isOpen_halfCollarSource : IsOpen halfCollarSource :=
  isOpen_lt ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const

def rightCollarMatched :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) FilledCut.{u} ∞ :=
  (c.matching.prodCongr
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans rightCollar

theorem halfCollarHeight_mem_seam_source (t : Torus) :
    halfCollarHeight (t, halfZero) ∈ c.seam.{u}.source := by
  change -1 < halfZero.val 0 ∧ halfZero.val 0 < 1
  rw [show halfZero.val 0 = 0 from rfl]
  norm_num

theorem filledFold_leftCollar_eventuallyEq (t : Torus) :
    c.filledFold.{u} ∘ c.leftCollar =ᶠ[𝓝 (t, halfZero)]
      c.seam ∘ seamReflection ∘ halfCollarHeight := by
  filter_upwards [isOpen_halfCollarSource.mem_nhds (zero_mem_halfCollarSource t)] with q hq
  have hq' : q.2.val 0 < 1 := hq
  have h0 : 0 ≤ q.2.val 0 := q.2.2
  apply Subtype.ext
  change (solidCollar.{u} c.p q).val = (c.seam (q.1, -q.2.val 0)).val
  rw [c.seam_apply_val ⟨by linarith, by linarith⟩]
  exact c.solidCollar_val_eq q.1 hq

theorem filledFold_rightCollarMatched_eventuallyEq (t : Torus) :
    c.filledFold.{u} ∘ c.rightCollarMatched =ᶠ[𝓝 (t, halfZero)] c.seam ∘ halfCollarHeight := by
  filter_upwards [isOpen_halfCollarSource.mem_nhds (zero_mem_halfCollarSource t)] with q hq
  have hq' : q.2.val 0 < 1 := hq
  have h0 : 0 ≤ q.2.val 0 := q.2.2
  apply Subtype.ext
  change c.coneLift (productCollar.{u} 3 (Or.inr rfl) 1 (c.matching q.1, q.2)).val =
    (c.seam (q.1, q.2.val 0)).val
  rw [c.seam_apply_val ⟨by linarith, hq'⟩]
  exact c.coneLift_productCollar_matching q.1 hq

theorem mfderiv_seam_congr (y₁ y₂ : Torus × ℝ) (h : y₁ = y₂)
    (w : TangentSpace signedCollarModel y₁) :
    mfderiv signedCollarModel (𝓡∂ 3) c.seam.{u} y₁ w =
      mfderiv signedCollarModel (𝓡∂ 3) c.seam.{u} y₂ w := by
  subst h
  rfl

theorem mfderiv_filledFold_leftCollar_apply (t : Torus)
    (v : TangentSpace halfCollarModel ((t, halfZero) : Torus × EuclideanHalfSpace 1)) :
    mfderiv (𝓡∂ 3) (𝓡∂ 3) c.filledFold (c.leftCollar.{u} (t, halfZero))
      (mfderiv halfCollarModel (𝓡∂ 3) c.leftCollar.{u} (t, halfZero) v) =
      mfderiv signedCollarModel (𝓡∂ 3) c.seam.{u} (halfCollarHeight (t, halfZero))
        (mfderiv signedCollarModel signedCollarModel seamReflection (halfCollarHeight (t, halfZero))
          (mfderiv halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) v)) := by
  have hq0 : ((t, halfZero) : Torus × EuclideanHalfSpace 1) ∈ c.leftCollar.{u}.source := by
    rw [leftCollar_source]
    exact zero_mem_halfCollarSource t
  have hy0 := c.halfCollarHeight_mem_seam_source.{u} t
  have hfold : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) c.filledFold (c.leftCollar.{u} (t, halfZero)) :=
    c.contMDiff_filledFold.mdifferentiableAt (by simp)
  have hl : MDifferentiableAt halfCollarModel (𝓡∂ 3) c.leftCollar.{u} (t, halfZero) :=
    c.leftCollar.mdifferentiableAt (by simp) hq0
  have hj : MDifferentiableAt halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) :=
    contMDiff_halfCollarHeight.mdifferentiableAt (by simp)
  have hρ : MDifferentiableAt signedCollarModel signedCollarModel seamReflection
      (halfCollarHeight (t, halfZero)) :=
    contMDiff_seamReflection.mdifferentiableAt (by simp)
  have hS : MDifferentiableAt signedCollarModel (𝓡∂ 3) c.seam.{u}
      (seamReflection (halfCollarHeight (t, halfZero))) := by
    rw [seamReflection_halfCollarHeight_zero]
    exact c.seam.mdifferentiableAt (by simp) hy0
  have e1 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hfold hl) v
  have e2 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hS (hρ.comp (t, halfZero) hj)) v
  have e3 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hρ hj) v
  have e4 := DFunLike.congr_fun (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel)
    (I' := 𝓡∂ 3) (c.filledFold_leftCollar_eventuallyEq.{u} t)) v
  exact ((e1.symm.trans e4).trans e2).trans ((congrArg (mfderiv signedCollarModel (𝓡∂ 3) c.seam
    (seamReflection (halfCollarHeight (t, halfZero)))) e3).trans
      (c.mfderiv_seam_congr _ _ (seamReflection_halfCollarHeight_zero t) _))

theorem mfderiv_filledFold_rightCollar_apply (t : Torus)
    (v : TangentSpace halfCollarModel ((t, halfZero) : Torus × EuclideanHalfSpace 1)) :
    mfderiv (𝓡∂ 3) (𝓡∂ 3) c.filledFold (c.rightCollarMatched.{u} (t, halfZero))
      (mfderiv halfCollarModel (𝓡∂ 3) c.rightCollarMatched.{u} (t, halfZero) v) =
      mfderiv signedCollarModel (𝓡∂ 3) c.seam.{u} (halfCollarHeight (t, halfZero))
        (mfderiv halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) v) := by
  have hq0 : ((t, halfZero) : Torus × EuclideanHalfSpace 1) ∈
      c.rightCollarMatched.{u}.source := by
    refine ⟨mem_univ _, ?_⟩
    change (c.matching t, halfZero) ∈ rightCollar.{u}.source
    rw [rightCollar_source]
    exact zero_mem_halfCollarSource _
  have hy0 := c.halfCollarHeight_mem_seam_source.{u} t
  have hfold : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) c.filledFold
      (c.rightCollarMatched.{u} (t, halfZero)) :=
    c.contMDiff_filledFold.mdifferentiableAt (by simp)
  have hr : MDifferentiableAt halfCollarModel (𝓡∂ 3) c.rightCollarMatched.{u} (t, halfZero) :=
    c.rightCollarMatched.mdifferentiableAt (by simp) hq0
  have hj : MDifferentiableAt halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) :=
    contMDiff_halfCollarHeight.mdifferentiableAt (by simp)
  have hS : MDifferentiableAt signedCollarModel (𝓡∂ 3) c.seam.{u}
      (halfCollarHeight (t, halfZero)) :=
    c.seam.mdifferentiableAt (by simp) hy0
  have e1 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hfold hr) v
  have e2 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hS hj) v
  have e4 := DFunLike.congr_fun (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel)
    (I' := 𝓡∂ 3) (c.filledFold_rightCollarMatched_eventuallyEq.{u} t)) v
  exact (e1.symm.trans e4).trans e2

theorem filledReversing :
    ReversesBoundaryOrientation c.filledCutCarrier.{u} c.leftCollar
      (fun p => rightCollar (c.matching p.1, p.2)) := by
  intro t
  let q0 : Torus × EuclideanHalfSpace 1 := (t, halfZero)
  have hq0l : q0 ∈ c.leftCollar.{u}.source := by
    rw [leftCollar_source]
    exact zero_mem_halfCollarSource t
  have hq0r : q0 ∈ c.rightCollarMatched.{u}.source := by
    refine ⟨mem_univ _, ?_⟩
    change (c.matching t, halfZero) ∈ rightCollar.{u}.source
    rw [rightCollar_source]
    exact zero_mem_halfCollarSource _
  have hl := c.leftCollar.{u}.isLocalDiffeomorphAt halfCollarModel (𝓡∂ 3) ∞ hq0l
  have hr := c.rightCollarMatched.{u}.isLocalDiffeomorphAt halfCollarModel (𝓡∂ 3) ∞ hq0r
  let L := (hl.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let R := (hr.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  refine ⟨L, R, fun v => rfl, fun v => rfl, ?_⟩
  let D : (x : FilledCut.{u}) → EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fun x => (Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡∂ 3) c.filledFold
      c.mfderiv_filledFold_bijective x).toLinearEquiv
  have hO : ∀ x : FilledCut.{u}, c.filledCutOrientation.orientation x =
      Orientation.map (Fin 3) (D x).symm
        (c.filledCarrier.orientation.orientation (c.filledFold x)) := by
    intro x
    rw [← c.orientation_map_filledCutOrientation x]
    exact (Equiv.symm_apply_apply (Orientation.map (Fin 3) (D x)) _).symm
  let y0 : Torus × ℝ := halfCollarHeight q0
  have hS := c.seam.{u}.isLocalDiffeomorphAt signedCollarModel (𝓡∂ 3) ∞
    (c.halfCollarHeight_mem_seam_source.{u} t)
  let dS := (hS.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let A := L.trans (D (c.leftCollar q0))
  let B := R.trans (D (c.rightCollarMatched q0))
  let J := B.trans dS.symm
  let P : (TangentSpace signedCollarModel y0) →ₗ[ℝ] (TangentSpace signedCollarModel y0) :=
    (LinearMap.id : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) →ₗ[ℝ] _).prodMap
      (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hJ : ∀ v, J v = mfderiv halfCollarModel signedCollarModel halfCollarHeight q0 v := by
    intro v
    apply dS.injective
    exact (dS.apply_symm_apply (B v)).trans (c.mfderiv_filledFold_rightCollar_apply t v)
  have hdet : LinearMap.det ((A.trans B.symm : _ ≃ₗ[ℝ] _) :
      TangentSpace halfCollarModel q0 →ₗ[ℝ] TangentSpace halfCollarModel q0) < 0 := by
    let Sₗ : TangentSpace signedCollarModel y0 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) := dS.toLinearMap
    rw [det_trans_symm_eq_det A B J P Sₗ]
    · rw [show LinearMap.det P = -1 from
        det_prodMap_id_neg (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))]
      norm_num
    · intro v
      change D (c.leftCollar q0) (L v) = Sₗ (P (J v))
      rw [hJ]
      exact (c.mfderiv_filledFold_leftCollar_apply t v).trans
        (congrArg Sₗ (mfderiv_seamReflection_apply _ _))
    · intro v
      change D (c.rightCollarMatched q0) (R v) = Sₗ (J v)
      rw [hJ]
      exact c.mfderiv_filledFold_rightCollar_apply t v
  have hpt : c.filledFold (c.rightCollarMatched.{u} q0) = c.filledFold (c.leftCollar.{u} q0) := by
    apply Subtype.ext
    exact (c.filledFold_rightTorus_matching t).trans (c.filledFold_leftTorus t).symm
  have hOS : ∀ p₁ p₂ : c.filledSet.{u}, p₁ = p₂ →
      c.filledCarrier.orientation.orientation p₁ =
        c.filledCarrier.orientation.orientation p₂ := by
    rintro _ _ rfl
    rfl
  change Orientation.map (Fin 3) L.symm
      (c.filledCutOrientation.orientation (c.leftCollar q0)) =
    -Orientation.map (Fin 3) R.symm
      (c.filledCutOrientation.orientation (c.rightCollarMatched q0))
  rw [hO, hO, hOS _ _ hpt]
  let o := c.filledCarrier.orientation.orientation (c.filledFold (c.leftCollar.{u} q0))
  have key := orientation_map_symm_eq_neg_of_det_neg (finrank_halfCollarTangent q0) A B o hdet
  have hA' : A.symm = (D (c.leftCollar q0)).symm.trans L.symm :=
    LinearEquiv.ext fun _ => rfl
  have hB' : B.symm = (D (c.rightCollarMatched q0)).symm.trans R.symm :=
    LinearEquiv.ext fun _ => rfl
  rw [hA', hB'] at key
  exact (DifferentialGeometry.orientation_map_trans (D (c.leftCollar q0)).symm L.symm
    o).symm.trans (key.trans (congrArg Neg.neg (DifferentialGeometry.orientation_map_trans
      (D (c.rightCollarMatched q0)).symm R.symm o)))

abbrev filledPairing : TorusPairing c.filledCutCarrier.{u} where
  count := 1
  gluing := c.gluing
  leftParam _ := c.leftParam
  rightParam _ := rightParam
  matching _ := c.matching
  matching_eq _ t := c.attaching_leftParam t
  leftCollar _ := c.leftCollar
  rightCollar _ := rightCollar
  left_source _ := c.leftCollar_source
  right_source _ := rightCollar_source
  left_zero _ _ := rfl
  right_zero _ _ := rfl
  reversing _ := c.filledReversing

theorem planarFunction_three_neg_iff (z : ℂ) : planarFunction 3 z < 0 ↔
    ‖z‖ < 3 ∧ 1 / 2 < ‖z - ((3 / 2 : ℝ) : ℂ)‖ ∧ 1 / 2 < ‖z - ((-(3 / 2) : ℝ) : ℂ)‖ := by
  have h0 := norm_nonneg z
  have hb0 := norm_nonneg (z - ((3 / 2 : ℝ) : ℂ))
  have hc0 := norm_nonneg (z - ((-(3 / 2) : ℝ) : ℂ))
  constructor
  · intro h
    have hm := (mem_planarModel_three z).mp ((planarFunction_nonpos_iff (Or.inr rfl) z).mp h.le)
    rw [planarFunction_three] at h
    refine ⟨lt_of_le_of_ne hm.1 fun he => ?_, lt_of_le_of_ne hm.2.1 fun he => ?_,
      lt_of_le_of_ne hm.2.2 fun he => ?_⟩
    · rw [he] at h
      norm_num at h
    · rw [← he] at h
      norm_num at h
    · rw [← he] at h
      norm_num at h
  · rintro ⟨h1, h2, h3⟩
    rw [planarFunction_three]
    exact mul_neg_of_neg_of_pos (by nlinarith) (mul_pos (by nlinarith) (by nlinarith))

theorem filledFunction_neg_iff {ζ : ℂ} (hζ : filledFunction ζ ≤ 0) :
    filledFunction ζ < 0 ↔ ‖ζ‖ < 3 ∧ 1 / 2 < ‖ζ - ((-(3 / 2) : ℝ) : ℂ)‖ := by
  have hm := (filledFunction_nonpos_iff ζ).mp hζ
  have h0 := norm_nonneg ζ
  have hc0 := norm_nonneg (ζ - ((-(3 / 2) : ℝ) : ℂ))
  constructor
  · intro h
    unfold filledFunction sqDist at h
    rw [sub_zero] at h
    refine ⟨lt_of_le_of_ne hm.1 fun he => ?_, lt_of_le_of_ne hm.2 fun he => ?_⟩
    · rw [he] at h
      norm_num at h
    · rw [← he] at h
      norm_num at h
  · rintro ⟨h1, h2⟩
    unfold filledFunction sqDist
    rw [sub_zero]
    exact mul_neg_of_neg_of_pos (by nlinarith) (by nlinarith)

def filledInteriorImage : TopologicalSpace.Opens c.filledSet.{u} :=
  ⟨{y | filledFunction (c.conePoint y.val) < 0 ∧ ‖y.val.1.down‖ ≠ 3},
    (isOpen_lt (c.contMDiff_filledFunction_conePoint.continuous.comp continuous_subtype_val)
      continuous_const).inter (isOpen_ne_fun (continuous_norm.comp (continuous_uliftDown.comp
        (continuous_fst.comp continuous_subtype_val))) continuous_const)⟩

theorem seamRadius_ne_three {d : ℝ} (hd : 0 < d) : seamRadius c.p d ≠ 3 := by
  intro h
  have h1 := seamDepth_seamRadius c.p (s := d) (by linarith)
  rw [h] at h1
  simp [seamDepth] at h1
  linarith

theorem filledFold_mem_interiorImage (x : c.filledCutCarrier.{u}.interior) :
    c.filledFold x.val ∈ c.filledInteriorImage := by
  obtain ⟨x, hx⟩ := x
  change (𝓡∂ 3).IsInteriorPoint x at hx
  rcases x with a | b
  · have ha := (productSet_isInteriorPoint_iff a).mp ((cut_isInteriorPoint_inl_iff a).mp hx)
    have hne := ne_three_halves_of_mem_productSet a
    obtain ⟨h1, h2, h3⟩ := (planarFunction_three_neg_iff _).mp ha
    refine ⟨?_, ?_⟩
    · change filledFunction (c.conePoint (c.coneLift a.val)) < 0
      rw [c.conePoint_coneLift _ hne]
      have hle : filledFunction a.val.1.down ≤ 0 :=
        (filledFunction_nonpos_iff _).mpr ⟨h1.le, h3.le⟩
      exact (filledFunction_neg_iff hle).mpr ⟨h1, h3⟩
    · change ‖(c.coneLift a.val).1.down‖ ≠ 3
      rw [c.norm_coneLift _ hne]
      refine c.seamRadius_ne_three ?_
      unfold coneDepth
      linarith
  · have hb := (solidSet_isInteriorPoint_iff b).mp ((cut_isInteriorPoint_inr_iff b).mp hx)
    exact ⟨c.filledFunction_conePoint_neg_of_mem_solidSet b.2, hb.ne⟩

def interiorForward (x : c.filledCutCarrier.{u}.interior) : c.filledInteriorImage.{u} :=
  ⟨c.filledFold x.val, c.filledFold_mem_interiorImage x⟩

theorem three_lt_of_not_lt {y : c.filledInteriorImage.{u}} (h : ¬ ‖y.val.val.1.down‖ < 3) :
    3 < ‖y.val.val.1.down‖ :=
  lt_of_le_of_ne (not_lt.mp h) y.2.2.symm

theorem coneChart_interior {y : c.filledInteriorImage.{u}} (h : ¬ ‖y.val.val.1.down‖ < 3) :
    (𝓡∂ 3).IsInteriorPoint (⟨c.coneChart y.val.val,
      c.coneChart_mem_productSet y.val.2 (c.three_lt_of_not_lt h)⟩ : productSet.{u} 3) := by
  have h3 := c.three_lt_of_not_lt h
  rw [productSet_isInteriorPoint_iff]
  change planarFunction 3 (c.conePoint y.val.val) < 0
  obtain ⟨h1, h2⟩ := (filledFunction_neg_iff y.val.2).mp y.2.1
  refine (planarFunction_three_neg_iff _).mpr ⟨h1, ?_, h2⟩
  rw [c.norm_conePoint_sub]
  have : 1 < (‖y.val.val.1.down‖ / 3) ^ c.p :=
    one_lt_pow₀ (by rw [lt_div_iff₀ (by norm_num)]; linarith) (NeZero.ne c.p)
  linarith

def interiorBackward (y : c.filledInteriorImage.{u}) : c.filledCutCarrier.{u}.interior :=
  if h : ‖y.val.val.1.down‖ < 3 then
    ⟨Sum.inr ⟨y.val.val, (mem_solidSet_iff _).mpr h.le⟩,
      (cut_isInteriorPoint_inr_iff _).mpr ((solidSet_isInteriorPoint_iff _).mpr h)⟩
  else
    ⟨Sum.inl ⟨c.coneChart y.val.val, c.coneChart_mem_productSet y.val.2 (c.three_lt_of_not_lt h)⟩,
      (cut_isInteriorPoint_inl_iff _).mpr (c.coneChart_interior h)⟩

open Classical in
def solidOfFilled (y : c.filledSet.{u}) : solidSet.{u} :=
  if h : y.val ∈ solidSet.{u} then ⟨y.val, h⟩ else Classical.arbitrary _

open Classical in
def productOfFilled (y : c.filledSet.{u}) : productSet.{u} 3 :=
  if h : c.coneChart y.val ∈ productSet.{u} 3 then ⟨c.coneChart y.val, h⟩
  else Classical.arbitrary _

theorem contMDiffAt_solidOfFilled {y : c.filledSet.{u}} (hy : ‖y.val.1.down‖ < 3) :
    ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ c.solidOfFilled y := by
  have hopen : IsOpen {y : c.filledSet.{u} | ‖y.val.1.down‖ < 3} :=
    isOpen_lt (continuous_norm.comp (continuous_uliftDown.comp
      (continuous_fst.comp continuous_subtype_val))) continuous_const
  have h : ContMDiffAt (𝓡∂ 3) PlaneCircleModel ∞ (Subtype.val ∘ c.solidOfFilled) y := by
    apply (c.filledAtlas.contMDiff_subtype_val y).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hy] with z hz
    have hz' : z.val ∈ solidSet.{u} := (mem_solidSet_iff _).mpr (le_of_lt hz)
    change (c.solidOfFilled z).val = z.val
    rw [solidOfFilled, dite_eq_left hz']
  exact contMDiffWithinAt_univ.mp ((solidAtlas.contMDiffWithinAt_iff_subtype_val
    c.solidOfFilled univ y).mpr h.contMDiffWithinAt)

theorem contMDiffAt_productOfFilled {y : c.filledSet.{u}} (hy : 3 < ‖y.val.1.down‖) :
    ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ c.productOfFilled y := by
  have hopen : IsOpen {y : c.filledSet.{u} | 3 < ‖y.val.1.down‖} :=
    isOpen_lt continuous_const (continuous_norm.comp (continuous_uliftDown.comp
      (continuous_fst.comp continuous_subtype_val)))
  have h : ContMDiffAt (𝓡∂ 3) PlaneCircleModel ∞ (Subtype.val ∘ c.productOfFilled) y := by
    apply ((c.contMDiffAt_coneChart (ne_zero_of_three_lt hy)).comp y
      (c.filledAtlas.contMDiff_subtype_val y)).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hy] with z hz
    have hz' := c.coneChart_mem_productSet z.2 hz
    change (c.productOfFilled z).val = c.coneChart z.val
    rw [productOfFilled, dite_eq_left hz']
  exact contMDiffWithinAt_univ.mp (((productAtlas.{u} 3).contMDiffWithinAt_iff_subtype_val
    c.productOfFilled univ y).mpr h.contMDiffWithinAt)

theorem contMDiff_interiorBackward_val :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
      (fun y : c.filledInteriorImage.{u} => (c.interiorBackward y).val) := by
  intro y
  have hval : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (Subtype.val : c.filledInteriorImage.{u} → _) y :=
    contMDiff_subtype_val y
  have hcont : Continuous fun z : c.filledInteriorImage.{u} => ‖z.val.val.1.down‖ :=
    continuous_norm.comp (continuous_uliftDown.comp
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)))
  by_cases hy : ‖y.val.val.1.down‖ < 3
  · have h1 : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞
        (fun z : c.filledInteriorImage.{u} =>
          (Sum.inr (c.solidOfFilled z.val) : FilledCut.{u})) y :=
      ContMDiff.inr.contMDiffAt.comp y ((c.contMDiffAt_solidOfFilled hy).comp y hval)
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds hy] with z hz
    have hz' : ‖z.val.val.1.down‖ < 3 := hz
    have hz'' : z.val.val ∈ solidSet.{u} := (mem_solidSet_iff _).mpr hz'.le
    change (c.interiorBackward z).val = Sum.inr (c.solidOfFilled z.val)
    rw [interiorBackward, dite_eq_left hz', solidOfFilled, dite_eq_left hz'']
  · have h3 := c.three_lt_of_not_lt hy
    have h1 : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞
        (fun z : c.filledInteriorImage.{u} =>
          (Sum.inl (c.productOfFilled z.val) : FilledCut.{u})) y :=
      ContMDiff.inl.contMDiffAt.comp y ((c.contMDiffAt_productOfFilled h3).comp y hval)
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds h3] with z hz
    have hz' : ¬ ‖z.val.val.1.down‖ < 3 := not_lt.mpr (le_of_lt hz)
    have hz'' := c.coneChart_mem_productSet z.val.2 hz
    change (c.interiorBackward z).val = Sum.inl (c.productOfFilled z.val)
    rw [interiorBackward, dite_eq_right hz', productOfFilled, dite_eq_left hz'']

def filledInteriorDiffeomorph :
    c.filledCutCarrier.{u}.interior ≃ₘ⟮c.filledCutCarrier.{u}.model, c.filledCarrier.{u}.model⟯
      c.filledInteriorImage.{u} where
  toFun := c.interiorForward
  invFun := c.interiorBackward
  left_inv := by
    rintro ⟨x, hx⟩
    have hx' : (𝓡∂ 3).IsInteriorPoint x := hx
    apply Subtype.ext
    change (c.interiorBackward (c.interiorForward ⟨x, hx⟩)).val = x
    unfold interiorBackward
    rcases x with a | b
    · have hne := ne_three_halves_of_mem_productSet a
      have ha := (productSet_isInteriorPoint_iff a).mp ((cut_isInteriorPoint_inl_iff a).mp hx')
      have hgt : ¬ ‖(c.coneLift a.val).1.down‖ < 3 := by
        rw [c.norm_coneLift _ hne, not_lt]
        have h1 := seamDepth_seamRadius c.p (coneDepth_gt hne)
        by_contra hlt
        rw [not_le] at hlt
        have h2 : seamDepth c.p (seamRadius c.p (coneDepth a.val)) ≤ 0 :=
          seamDepth_nonpos c.p (seamRadius_pos c.p (coneDepth_gt hne)).le hlt.le
        have h3 := (planarFunction_three_neg_iff _).mp ha
        unfold coneDepth at h1 h2
        linarith [h3.2.1]
      split_ifs with h
      · exact absurd h hgt
      · exact congrArg Sum.inl (Subtype.ext (c.coneChart_coneLift a.val hne))
    · have hb := (solidSet_isInteriorPoint_iff b).mp ((cut_isInteriorPoint_inr_iff b).mp hx')
      split_ifs with h
      · rfl
      · exact absurd hb h
  right_inv := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    change (c.filledFold (c.interiorBackward y).val).val = y.val.val
    unfold interiorBackward
    split_ifs with hy
    · rfl
    · exact c.coneLift_coneChart y.val.val (ne_zero_of_three_lt (c.three_lt_of_not_lt hy))
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff c.filledInteriorImage.{u} _).mp
    (c.contMDiff_filledFold.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff c.filledCutCarrier.{u}.interior _).mp
    c.contMDiff_interiorBackward_val

abbrev filledPresentation : TorusPresentation c.filledCarrier.{u} where
  cutCarrier := c.filledCutCarrier
  components := c.filledComponents
  pairing := c.filledPairing
  externalCount := 2
  external := c.external
  cutExternal := c.cutExternal
  external_exhausted := c.filled_boundary
  cut_boundary_exhausted := c.cut_boundary
  external_disjoint := c.cut_external_disjoint
  reconstruction := c.filledReconstruction
  quotient_smooth := c.contMDiff_filledFold
  quotient_oriented x := ⟨(Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡∂ 3) c.filledFold
    c.mfderiv_filledFold_bijective x).toLinearEquiv, fun _ => rfl,
      c.orientation_map_filledCutOrientation x⟩
  interiorImage := c.filledInteriorImage
  interiorDiffeomorph := c.filledInteriorDiffeomorph
  interior_map _ := rfl
  seam _ := c.seam
  seam_source _ := rfl
  seam_zero _ t := by
    apply Subtype.ext
    rw [c.seam_apply_val (by constructor <;> norm_num)]
    exact (c.filledFold_leftTorus t).symm
  seam_positive _ t s hs hs1 := by
    apply Subtype.ext
    rw [c.seam_apply_val ⟨by linarith, hs1⟩]
    exact (c.coneLift_productCollar_matching t (h := halfPoint s hs) hs1).symm
  seam_negative _ t s hs hs1 := by
    apply Subtype.ext
    rw [c.seam_apply_val ⟨hs1, by linarith⟩]
    change _ = (solidCollar.{u} c.p (t, halfPoint (-s) (neg_nonneg.mpr hs))).val
    rw [c.solidCollar_val_eq t (by change -s < 1; linarith)]
    change c.seamPoint (t, s) = c.seamPoint (t, -(-s))
    rw [neg_neg]
  seam_interior _ := c.seam_target_subset_interior
  seam_disjoint i j h := (h (Subsingleton.elim i j)).elim
  marked_collar i p hp := c.cut_filled_external i p hp
  external_seam_disjoint i _ := c.external_seam_disjoint i
  leftPiece _ := 1
  rightPiece _ := 0
  left_owned _ := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  right_owned _ := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  externalPiece _ := 0
  external_owned _ := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, rfl⟩

def productPortFun (j : Fin 3) : c.filledPresentation.{u}.OwnedSide 0 :=
  ![⟨.inr (.inr 0), rfl⟩, ⟨.inr (.inl 0), rfl⟩, ⟨.inr (.inr 1), rfl⟩] j

def productPortInv : c.filledPresentation.{u}.OwnedSide 0 → Fin 3
  | ⟨.inl _, _⟩ => 1
  | ⟨.inr (.inl _), _⟩ => 1
  | ⟨.inr (.inr e), _⟩ => externalPort e

def productPort : Fin 3 ≃ c.filledPresentation.{u}.OwnedSide 0 where
  toFun := c.productPortFun
  invFun := c.productPortInv
  left_inv j := by
    rcases fin_three_cases j with rfl | rfl | rfl <;> rfl
  right_inv s := by
    rcases s with ⟨m | m | e, h⟩
    · change (1 : Fin 2) = 0 at h
      exact absurd h (by decide)
    · obtain rfl : m = 0 := Subsingleton.elim m 0
      rfl
    · rcases fin_two_cases e with rfl | rfl <;> rfl

def productTrivialization :
    (planarSet.{u} 3 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯
      (⟨range Sum.inl, isOpen_range_inl⟩ : TopologicalSpace.Opens FilledCut.{u}) :=
  (productDiffeomorph 3).trans (sumInlRangeDiffeomorph (I := 𝓡∂ 3)).symm

def filledProductPiece : ProductFibredPiece c.filledPresentation.{u} 0 3 where
  base := pantsPlanarBase
  port := c.productPort
  trivialization := productTrivialization
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
    rcases fin_three_cases j with rfl | rfl | rfl <;> rfl

def solidPort : Fin 1 ≃ c.filledPresentation.{u}.OwnedSide 1 where
  toFun _ := ⟨.inl 0, rfl⟩
  invFun _ := 0
  left_inv j := Subsingleton.elim _ _
  right_inv s := by
    rcases s with ⟨m | m | e, h⟩
    · obtain rfl : m = 0 := Subsingleton.elim m 0
      rfl
    · change (0 : Fin 2) = 1 at h
      exact absurd h (by decide)
    · change (0 : Fin 2) = 1 at h
      exact absurd h (by decide)

def solidTrivialization :
    (discSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯
      (⟨range Sum.inr, isOpen_range_inr⟩ : TopologicalSpace.Opens FilledCut.{u}) :=
  solidDiffeomorph.trans (sumInrRangeDiffeomorph (I := 𝓡∂ 3)).symm

def filledSolidPiece : SolidTorusPiece c.filledPresentation.{u} 1 where
  base := discPlanarBase c.p
  port := c.solidPort
  trivialization := solidTrivialization
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp, Subsingleton.elim j 0]
    rfl

theorem torusMatrix_matching : torusMatrix c.matching = c.matchingMatrix :=
  torusMatrix_linearTorusDiffeomorph c.matchingUnit

theorem gcd_eq_one : Int.gcd (c.p : ℤ) c.q = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one]
  exact ⟨c.b, -c.a, by linear_combination c.det_eq⟩

end ConeFilling

abbrev oneConeData (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1) : SeifertData where
  k := 3
  ports := 2
  cones := [(p, q)]
  normals := []
  one_le_k := by norm_num
  k_le_three := le_rfl
  two_le_of_mem_cones x hx := by
    rw [List.mem_singleton] at hx
    rw [hx]
    exact hp
  gcd_eq_one_of_mem_cones x hx := by
    rw [List.mem_singleton] at hx
    rw [hx]
    exact hpq
  ports_add_length_add_length := rfl

namespace ConeFilling

variable (c : ConeFilling)

theorem eq_zero_of_fillingCount (hp : 2 ≤ c.p)
    (m : Fin (oneConeData c.p c.q hp c.gcd_eq_one).fillingCount) : m.val = 0 := by
  have h := m.isLt
  change m.val < 1 at h
  omega

def pieceEquiv (hp : 2 ≤ c.p) :
    Option (Fin (oneConeData c.p c.q hp c.gcd_eq_one).fillingCount) ≃
      Fin c.filledPresentation.{u}.components.count where
  toFun o := o.elim 0 fun _ => 1
  invFun i := if i = 0 then none else some ⟨0, Nat.one_pos⟩
  left_inv o := by
    rcases o with _ | m
    · rfl
    · have hm : m = ⟨0, Nat.one_pos⟩ := Fin.ext (c.eq_zero_of_fillingCount hp m)
      subst hm
      rfl
  right_inv i := by
    rcases fin_two_cases i with rfl | rfl <;> rfl

def portEquiv (hp : 2 ≤ c.p) :
    Fin (oneConeData c.p c.q hp c.gcd_eq_one).ports ⊕
      Fin (oneConeData c.p c.q hp c.gcd_eq_one).fillingCount ≃
      Fin (oneConeData c.p c.q hp c.gcd_eq_one).k where
  toFun := Sum.elim externalPort fun _ => 1
  invFun j := if j = 1 then .inr ⟨0, Nat.one_pos⟩ else if j = 0 then .inl 0 else .inl 1
  left_inv o := by
    rcases o with r | m
    · rcases fin_two_cases r with rfl | rfl <;> rfl
    · have hm : m = ⟨0, Nat.one_pos⟩ := Fin.ext (c.eq_zero_of_fillingCount hp m)
      subst hm
      rfl
  right_inv j := by
    rcases fin_three_cases j with rfl | rfl | rfl <;> rfl

theorem fillingSlope_oneConeData (hp : 2 ≤ c.p)
    (m : Fin (oneConeData c.p c.q hp c.gcd_eq_one).fillingCount) :
    (oneConeData c.p c.q hp c.gcd_eq_one).fillingSlope m = ((c.p : ℤ), c.q) := by
  have hm : m = ⟨0, Nat.one_pos⟩ := Fin.ext (c.eq_zero_of_fillingCount hp m)
  subst hm
  rfl

def filledBlock (hp : 2 ≤ c.p) :
    SeifertBlock c.filledCarrier.{u} (oneConeData c.p c.q hp c.gcd_eq_one) where
  presentation := c.filledPresentation
  piece := c.pieceEquiv.{u} hp
  product := c.filledProductPiece
  solid _ := c.filledSolidPiece
  port := c.portEquiv hp
  seam := Equiv.refl _
  free := Equiv.refl _
  free_port r := by
    rcases fin_two_cases r with rfl | rfl <;> rfl
  filled_port m := congrArg (fun k => Sum.inr (Sum.inl k))
    (Fin.ext (c.eq_zero_of_fillingCount hp m).symm)
  solid_port m := congrArg Sum.inl (Fin.ext (c.eq_zero_of_fillingCount hp m).symm)
  slope m := by
    rw [meridianSlope, PrimitiveSlope.smul_mk, PrimitiveSlope.mk_eq_mk_iff,
      c.fillingSlope_oneConeData hp m]
    right
    change ((c.p : ℤ), c.q) = -smulVec (torusMatrix c.matching) (1, 0)
    rw [torusMatrix_matching]
    simp [smulVec, matchingMatrix, reflectMatrix, chartMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem filledBlock_isGoodBlock (hp : 2 ≤ c.p) : (c.filledBlock.{u} hp).IsGoodBlock :=
  SeifertBlock.isGoodBlock_of_one_filling _ rfl rfl

end ConeFilling

def coneFillingOf (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1) : ConeFilling where
  p := p
  q := q
  a := -Int.gcdB p q
  b := Int.gcdA p q
  one_le := by omega
  det_eq := by
    have h := Int.gcd_eq_gcd_ab (p : ℤ) q
    rw [hpq] at h
    linear_combination -h

def oneConeBlock (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1) :
    SeifertBlock (coneFillingOf p q hp hpq).filledCarrier.{u} (oneConeData p q hp hpq) :=
  (coneFillingOf p q hp hpq).filledBlock hp

theorem oneConeBlock_isGoodBlock (p : ℕ) (q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd (p : ℤ) q = 1) :
    (oneConeBlock.{u} p q hp hpq).IsGoodBlock :=
  (coneFillingOf p q hp hpq).filledBlock_isGoodBlock hp

end GC.Seifert
