import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryTangent
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryOrientation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FibreCoordinate
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordReversal

/-!
The signed torus collar inherits a smooth orientation from the original two half collars.
Boundary reversal identifies their induced orientations after reflection of the normal coordinate.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold.TorusPairing

def surgeryHalfDomain : Opens (Torus × EuclideanHalfSpace 1) :=
  ⟨halfCollarSource, by
    change IsOpen {p : Torus × EuclideanHalfSpace 1 | p.2.val 0 < 1}
    exact isOpen_lt (by fun_prop) continuous_const⟩

instance : PreconnectedSpace surgeryHalfDomain :=
  isPreconnected_iff_preconnectedSpace.mp isPreconnected_halfCollarSource

def surgeryHalfSignedCoordinate (σ : ℝ) (p : Torus × EuclideanHalfSpace 1) :
    Torus × ℝ := (p.1, σ * p.2.val 0)

theorem surgeryHalfSignedCoordinate_contMDiff (σ : ℝ) :
    ContMDiff halfCollarModel signedCollarModel ∞ (surgeryHalfSignedCoordinate σ) :=
  contMDiff_fst.prodMk (contMDiff_const.mul (contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd))

theorem surgeryHalfSignedCoordinate_bijective {σ : ℝ} (hσ : σ ≠ 0)
    (p : Torus × EuclideanHalfSpace 1) :
    Bijective (mfderiv halfCollarModel signedCollarModel (surgeryHalfSignedCoordinate σ) p) := by
  have hi := injective_mfderiv_scaledHalfSpaceOneProductCoordinate torusModel hσ p
  refine ⟨hi, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfderiv halfCollarModel signedCollarModel
      (surgeryHalfSignedCoordinate σ) p).toLinearMap) (by
        change Module.finrank ℝ
          ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
            EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ
          ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ)
        simp)).mp
  exact hi

def surgeryHalfSignedTangent (σ : ℝ) (hσ : σ ≠ 0)
    (p : Torus × EuclideanHalfSpace 1) :
    TangentSpace halfCollarModel p ≃ₗ[ℝ]
      TangentSpace signedCollarModel (surgeryHalfSignedCoordinate σ p) :=
  LinearEquiv.ofBijective
    (mfderiv halfCollarModel signedCollarModel (surgeryHalfSignedCoordinate σ) p).toLinearMap
    (surgeryHalfSignedCoordinate_bijective hσ p)

theorem surgeryHalfSignedTangent_apply (σ : ℝ) (hσ : σ ≠ 0)
    (p : Torus × EuclideanHalfSpace 1) (v : TangentSpace halfCollarModel p) :
    surgeryHalfSignedTangent σ hσ p v = (v.1, σ * v.2 0) := by
  change mfderiv halfCollarModel signedCollarModel (surgeryHalfSignedCoordinate σ) p v = _
  have ht : HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ)
      (fun h : EuclideanHalfSpace 1 => σ * h.val 0) p.2
      (σ • (PiLp.equivOfUnique 2 ℝ (fun j : Fin 1 => ℝ)).toContinuousLinearMap) :=
    (hasMFDerivAt_halfSpaceOneCoordinate p.2).const_smul σ
  change mfderiv halfCollarModel signedCollarModel
    (Prod.map id (fun h : EuclideanHalfSpace 1 => σ * h.val 0)) p v = _
  rw [mfderiv_prodMap mdifferentiableAt_id ht.mdifferentiableAt, mfderiv_id, ht.mfderiv]
  rfl

def surgerySignedReferenceOrientation : ManifoldOrientation signedCollarModel (Torus × ℝ) 3 :=
  productOrientation torusModel 𝓘(ℝ, ℝ) (by norm_num) le_rfl
    productTorusOrientation realLineOrientation

section HalfPullback

variable {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] [TopologicalSpace N]
  {J : ModelWithCorners ℝ F H} [ChartedSpace H N] [IsManifold J ∞ N]

theorem exists_surgeryHalfPullbackOrientation
    (f : Torus × EuclideanHalfSpace 1 → N)
    (hf : ContMDiffOn halfCollarModel J ∞ f halfCollarSource)
    (A : ∀ p : surgeryHalfDomain, TangentSpace halfCollarModel p.val ≃ₗ[ℝ]
      TangentSpace J (f p.val))
    (hA : ∀ p v, A p v = mfderiv halfCollarModel J f p.val v)
    (O : ManifoldOrientation J N 3) :
    ∃ OH : ManifoldOrientation halfCollarModel surgeryHalfDomain 3,
      ∀ p, Orientation.map (Fin 3) (A p) (OH.orientation p) = O.orientation (f p.val) := by
  have hs : ContMDiff halfCollarModel J ∞ (fun p : surgeryHalfDomain => f p.val) := by
    intro p
    rw [contMDiffAt_subtype_iff]
    exact hf.contMDiffAt (surgeryHalfDomain.isOpen.mem_nhds p.property)
  have hb : ∀ p : surgeryHalfDomain,
      Bijective (mfderiv halfCollarModel J (fun q : surgeryHalfDomain => f q.val) p) := by
    intro p
    rw [DifferentialGeometry.mfderiv_restrict_open]
    have he : mfderiv halfCollarModel J f p.val = (A p).toLinearMap.toContinuousLinearMap := by
      ext v
      exact (hA p v).symm
    rw [he]
    exact (A p).bijective
  obtain ⟨OH, ho⟩ := exists_manifoldOrientation_pullback halfCollarModel J (by
      change Module.finrank ℝ
        ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
          EuclideanSpace ℝ (Fin 1)) = 3
      simp) (fun p : surgeryHalfDomain => f p.val) hs hb O
  refine ⟨OH, fun p => ?_⟩
  have he : (differentialEquivOfBijective halfCollarModel J
      (fun q : surgeryHalfDomain => f q.val) hb p).toLinearEquiv = A p := by
    ext v
    change mfderiv halfCollarModel J (fun q : surgeryHalfDomain => f q.val) p v = A p v
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact (hA p v).symm
  rw [← he]
  exact ho p

end HalfPullback

def surgerySignedNormalReflection :
    ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ) ≃ₗ[ℝ]
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ) :=
  (LinearEquiv.refl ℝ _).prodCongr (LinearEquiv.neg ℝ)

theorem surgerySignedNormalReflection_map
    (o : Orientation ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ) (Fin 3)) :
    Orientation.map (Fin 3) surgerySignedNormalReflection o = -o := by
  apply (Orientation.map_eq_neg_iff_det_neg o surgerySignedNormalReflection (by simp)).mpr
  have he : surgerySignedNormalReflection.toLinearMap =
      (LinearMap.id : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) →ₗ[ℝ] _).prodMap
        (-LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    apply LinearMap.ext
    intro v
    rfl
  rw [he, det_prodMap_id_neg]
  norm_num

theorem surgeryHalfSignedTangent_negative (p : Torus × EuclideanHalfSpace 1) :
    surgeryHalfSignedTangent (-1) (by norm_num) p =
      (surgeryHalfSignedTangent 1 (by norm_num) p).trans surgerySignedNormalReflection := by
  ext v
  rw [surgeryHalfSignedTangent_apply]
  change (v.1, -1 * v.2 0) =
    surgerySignedNormalReflection (surgeryHalfSignedTangent 1 (by norm_num) p v)
  rw [surgeryHalfSignedTangent_apply]
  simp [surgerySignedNormalReflection]

variable {C : CompactCarrier.{u}}

def surgeryMatchedRightCollar (P : TorusPairing C) (j : Fin P.count) :
    PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞ :=
  let m := (P.matching j).prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)
  m.toPartialDiffeomorph.trans (P.rightCollar j)

theorem surgeryMatchedRightCollar_apply (P : TorusPairing C) (j : Fin P.count)
    (p : Torus × EuclideanHalfSpace 1) :
    P.surgeryMatchedRightCollar j p = P.rightCollar j (P.matching j p.1, p.2) := rfl

theorem surgeryMatchedRightCollar_source (P : TorusPairing C) (j : Fin P.count) :
    (P.surgeryMatchedRightCollar j).source = halfCollarSource := by
  ext p
  change (p ∈ univ ∧ (P.matching j p.1, p.2) ∈ (P.rightCollar j).source) ↔ _
  rw [P.right_source]
  simp only [mem_univ, true_and]
  rfl

theorem surgeryMatchedRightCollar_mem_target (P : TorusPairing C) (j : Fin P.count)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    P.surgeryMatchedRightCollar j p ∈ (P.rightCollar j).target := by
  rw [surgeryMatchedRightCollar_apply]
  apply (P.rightCollar j).map_source'
  rw [P.right_source]
  exact hp

theorem exists_surgeryHalfCollarOrientation
    (c : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞) (hc : c.source = halfCollarSource) :
    ∃ O : ManifoldOrientation halfCollarModel surgeryHalfDomain 3,
      ∀ p, Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv c
        (hc.symm ▸ (show p.val ∈ halfCollarSource from p.property)))
        (O.orientation p) = C.orientation.orientation (c p.val) :=
  exists_surgeryHalfPullbackOrientation c (hc ▸ c.contMDiffOn)
    (fun p => carrierSurgeryPatchTangentEquiv c
      (hc.symm ▸ (show p.val ∈ halfCollarSource from p.property)))
    (fun p v => carrierSurgeryPatchTangentEquiv_apply c
      (hc.symm ▸ (show p.val ∈ halfCollarSource from p.property)) v) C.orientation

theorem exists_surgeryHalfSignedOrientation (σ : ℝ) (hσ : σ ≠ 0)
    (O : ManifoldOrientation signedCollarModel (Torus × ℝ) 3) :
    ∃ OH : ManifoldOrientation halfCollarModel surgeryHalfDomain 3,
      ∀ p, Orientation.map (Fin 3) (surgeryHalfSignedTangent σ hσ p.val)
        (OH.orientation p) = O.orientation (surgeryHalfSignedCoordinate σ p.val) :=
  exists_surgeryHalfPullbackOrientation (surgeryHalfSignedCoordinate σ)
    (surgeryHalfSignedCoordinate_contMDiff σ).contMDiffOn
    (fun p => surgeryHalfSignedTangent σ hσ p.val)
    (fun p v => show surgeryHalfSignedTangent σ hσ p.val v =
      mfderiv halfCollarModel signedCollarModel (surgeryHalfSignedCoordinate σ) p.val v from rfl) O

set_option backward.isDefEq.respectTransparency false in
theorem surgeryHalfCollarOrientation_reversing (P : TorusPairing C) (j : Fin P.count)
    (OL OR : ManifoldOrientation halfCollarModel surgeryHalfDomain 3)
    (hL : ∀ p, Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv (P.leftCollar j)
        ((P.left_source j).symm ▸ (show p.val ∈ halfCollarSource from p.property)))
      (OL.orientation p) = C.orientation.orientation (P.leftCollar j p.val))
    (hR : ∀ p, Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv (P.surgeryMatchedRightCollar j)
        ((P.surgeryMatchedRightCollar_source j).symm ▸
          (show p.val ∈ halfCollarSource from p.property)))
      (OR.orientation p) = C.orientation.orientation (P.surgeryMatchedRightCollar j p.val))
    (t : Torus) :
    OL.orientation ⟨(t, halfZero), halfZero_mem_halfCollarSource t⟩ =
      -OR.orientation ⟨(t, halfZero), halfZero_mem_halfCollarSource t⟩ := by
  let p : surgeryHalfDomain := ⟨(t, halfZero), halfZero_mem_halfCollarSource t⟩
  obtain ⟨L, R, hl, hr, ho⟩ := P.reversing j t
  have hle : L = carrierSurgeryPatchTangentEquiv (P.leftCollar j)
      ((P.left_source j).symm ▸ halfZero_mem_halfCollarSource t) :=
    LinearEquiv.ext hl
  have hre : R = carrierSurgeryPatchTangentEquiv (P.surgeryMatchedRightCollar j)
      ((P.surgeryMatchedRightCollar_source j).symm ▸ halfZero_mem_halfCollarSource t) :=
    LinearEquiv.ext hr
  rw [hle, hre] at ho
  change Orientation.map (Fin 3) _ (C.orientation.orientation (P.leftCollar j p.val)) =
    -Orientation.map (Fin 3) _ (C.orientation.orientation (P.surgeryMatchedRightCollar j p.val))
      at ho
  rw [← hL p, ← hR p] at ho
  have hlc := Equiv.symm_apply_apply
    (Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (P.leftCollar j)
      ((P.left_source j).symm ▸ halfZero_mem_halfCollarSource t))) (OL.orientation p)
  have hrc := Equiv.symm_apply_apply
    (Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (P.surgeryMatchedRightCollar j)
      ((P.surgeryMatchedRightCollar_source j).symm ▸ halfZero_mem_halfCollarSource t)))
    (OR.orientation p)
  exact hlc.symm.trans (ho.trans (congrArg Neg.neg hrc))

set_option backward.isDefEq.respectTransparency false in
theorem exists_surgerySignedOrientation_halves (P : TorusPairing C) (j : Fin P.count) :
    ∃ O : ManifoldOrientation signedCollarModel (Torus × ℝ) 3,
      ∃ OL OR : ManifoldOrientation halfCollarModel surgeryHalfDomain 3,
        (∀ p, Orientation.map (Fin 3)
          (carrierSurgeryPatchTangentEquiv (P.leftCollar j)
            ((P.left_source j).symm ▸ (show p.val ∈ halfCollarSource from p.property)))
          (OL.orientation p) = C.orientation.orientation (P.leftCollar j p.val)) ∧
        (∀ p, Orientation.map (Fin 3)
          (carrierSurgeryPatchTangentEquiv (P.surgeryMatchedRightCollar j)
            ((P.surgeryMatchedRightCollar_source j).symm ▸
              (show p.val ∈ halfCollarSource from p.property)))
          (OR.orientation p) = C.orientation.orientation (P.surgeryMatchedRightCollar j p.val)) ∧
        (∀ p, Orientation.map (Fin 3) (surgeryHalfSignedTangent (-1) (by norm_num) p.val)
          (OL.orientation p) = O.orientation (surgeryHalfSignedCoordinate (-1) p.val)) ∧
        (∀ p, Orientation.map (Fin 3) (surgeryHalfSignedTangent 1 (by norm_num) p.val)
          (OR.orientation p) = O.orientation (surgeryHalfSignedCoordinate 1 p.val)) := by
  classical
  obtain ⟨OL, hL⟩ := exists_surgeryHalfCollarOrientation (P.leftCollar j) (P.left_source j)
  obtain ⟨OR, hR⟩ := exists_surgeryHalfCollarOrientation
    (P.surgeryMatchedRightCollar j) (P.surgeryMatchedRightCollar_source j)
  let p0 : surgeryHalfDomain := ⟨(1, halfZero), halfZero_mem_halfCollarSource 1⟩
  obtain ⟨OS, hS⟩ := exists_surgeryHalfSignedOrientation (-1) (by norm_num)
    surgerySignedReferenceOrientation
  have hc : Fintype.card (Fin 3) = Module.finrank ℝ (TangentSpace halfCollarModel p0) := by
    change Fintype.card (Fin 3) = Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))
    simp
  have hchoose : ∃ O : ManifoldOrientation signedCollarModel (Torus × ℝ) 3,
      ∀ p, Orientation.map (Fin 3) (surgeryHalfSignedTangent (-1) (by norm_num) p.val)
        (OL.orientation p) = O.orientation (surgeryHalfSignedCoordinate (-1) p.val) := by
    rcases Orientation.eq_or_eq_neg (OL.orientation p0) (OS.orientation p0) hc with hp | hp
    · refine ⟨surgerySignedReferenceOrientation, ?_⟩
      rw [ManifoldOrientation.eq_of_eq_at OL OS p0 hp]
      exact hS
    · refine ⟨surgerySignedReferenceOrientation.opposite, ?_⟩
      have he : OL = OS.opposite := ManifoldOrientation.eq_of_eq_at OL OS.opposite p0 hp
      intro p
      rw [he, ManifoldOrientation.opposite_orientation, Orientation.map_neg, hS p]
      rfl
  obtain ⟨O, hoL⟩ := hchoose
  obtain ⟨OP, hP⟩ := exists_surgeryHalfSignedOrientation 1 (by norm_num) O
  have hz : OR.orientation p0 = OP.orientation p0 := by
    apply (Orientation.map (Fin 3) (surgeryHalfSignedTangent 1 (by norm_num) p0.val)).injective
    have hr0 : OL.orientation p0 = -OR.orientation p0 :=
      P.surgeryHalfCollarOrientation_reversing j OL OR hL hR 1
    have hl0 := hoL p0
    rw [surgeryHalfSignedTangent_negative, DifferentialGeometry.orientation_map_trans] at hl0
    have hsign := surgerySignedNormalReflection_map
      (Orientation.map (Fin 3) (surgeryHalfSignedTangent 1 (by norm_num) p0.val)
        (OL.orientation p0))
    have hl0' := hsign.symm.trans hl0
    have hn : OR.orientation p0 = -OL.orientation p0 :=
      (neg_neg (OR.orientation p0)).symm.trans (congrArg Neg.neg hr0.symm)
    have hzero : surgeryHalfSignedCoordinate (-1) p0.val =
        surgeryHalfSignedCoordinate 1 p0.val := by
      apply Prod.ext
      · rfl
      · change (-1 : ℝ) * 0 = 1 * 0
        norm_num
    rw [hn, Orientation.map_neg, hP p0]
    exact hl0'.trans (congrArg (fun y : Torus × ℝ =>
      (show Orientation ℝ
        ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ) (Fin 3)
          from O.orientation y)) hzero)
  refine ⟨O, OL, OR, hL, hR, hoL, ?_⟩
  rw [ManifoldOrientation.eq_of_eq_at OR OP p0 hz]
  exact hP

theorem surgerySeamInverseCoordinates_leftCollar (P : TorusPairing C) (j : Fin P.count)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    P.surgerySeamInverseCoordinates j (P.leftCollar j p) =
      surgeryHalfSignedCoordinate (-1) p := by
  classical
  have hs : p ∈ (P.leftCollar j).source := (P.left_source j).symm ▸ hp
  have ht := (P.leftCollar j).map_source' hs
  have hi : (P.leftCollar j).symm (P.leftCollar j p) = p := (P.leftCollar j).left_inv' hs
  simp only [surgerySeamInverseCoordinates, ht, ↓reduceIte, hi,
    surgeryHalfSignedCoordinate, neg_one_mul]

theorem surgerySeamInverseCoordinates_matchedRightCollar (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target) (j : Fin P.count)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    P.surgerySeamInverseCoordinates j (P.surgeryMatchedRightCollar j p) =
      surgeryHalfSignedCoordinate 1 p := by
  classical
  have hs : (P.matching j p.1, p.2) ∈ (P.rightCollar j).source := by
    rw [P.right_source]
    exact hp
  have ht := (P.rightCollar j).map_source' hs
  have hn : P.rightCollar j (P.matching j p.1, p.2) ∉ (P.leftCollar j).target :=
    fun hl => (hd (Sum.inl_ne_inr : Sum.inl j ≠ Sum.inr j)).le_bot ⟨hl, ht⟩
  have hi : (P.rightCollar j).symm (P.rightCollar j (P.matching j p.1, p.2)) =
      (P.matching j p.1, p.2) := (P.rightCollar j).left_inv' hs
  rw [surgeryMatchedRightCollar_apply]
  simp only [surgerySeamInverseCoordinates, hn, ↓reduceIte, hi,
    Diffeomorph.symm_apply_apply, surgeryHalfSignedCoordinate, one_mul]

set_option backward.isDefEq.respectTransparency false in
theorem surgerySeamCoordinatesTangent_comp (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target) (j : Fin P.count)
    (c : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (σ : ℝ) (hσ : σ ≠ 0) {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ c.source)
    (hx : c p ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target)
    (he : (fun q => P.surgerySeamInverseCoordinates j (c q)) =ᶠ[𝓝 p]
      surgeryHalfSignedCoordinate σ) :
    (carrierSurgeryPatchTangentEquiv c hp).trans
      (P.surgerySeamInverseCoordinatesTangentEquiv hd j hx) =
        surgeryHalfSignedTangent σ hσ p := by
  have hs := (P.surgerySeamInverseCoordinates_contMDiffOn hd j).contMDiffAt
    (((P.leftCollar j).open_target.union (P.rightCollar j).open_target).mem_nhds hx)
  have hdif := he.mfderiv_eq (I := halfCollarModel) (I' := signedCollarModel)
  have hc := mfderiv_comp p (hs.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) hp)
  apply LinearEquiv.ext
  intro v
  change mfderiv C.model signedCollarModel (P.surgerySeamInverseCoordinates j) (c p)
    (mfderiv halfCollarModel C.model c p v) =
      mfderiv halfCollarModel signedCollarModel (surgeryHalfSignedCoordinate σ) p v
  exact (congrArg (fun A => A v) hc).symm.trans (congrArg (fun A => A v) hdif)

theorem surgerySeamCoordinatesTangent_left (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target) (j : Fin P.count)
    (p : surgeryHalfDomain) :
    (carrierSurgeryPatchTangentEquiv (P.leftCollar j)
      ((P.left_source j).symm ▸ (show p.val ∈ halfCollarSource from p.property))).trans
      (P.surgerySeamInverseCoordinatesTangentEquiv hd j
        (Or.inl ((P.leftCollar j).map_source'
          ((P.left_source j).symm ▸ (show p.val ∈ halfCollarSource from p.property))))) =
      surgeryHalfSignedTangent (-1) (by norm_num) p.val := by
  apply P.surgerySeamCoordinatesTangent_comp
  filter_upwards [surgeryHalfDomain.isOpen.mem_nhds p.property] with q hq
  exact P.surgerySeamInverseCoordinates_leftCollar j hq

theorem surgerySeamCoordinatesTangent_right (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target) (j : Fin P.count)
    (p : surgeryHalfDomain) :
    (carrierSurgeryPatchTangentEquiv (P.surgeryMatchedRightCollar j)
      ((P.surgeryMatchedRightCollar_source j).symm ▸
        (show p.val ∈ halfCollarSource from p.property))).trans
      (P.surgerySeamInverseCoordinatesTangentEquiv hd j
        (x := P.surgeryMatchedRightCollar j p.val)
        (Or.inr (P.surgeryMatchedRightCollar_mem_target j p.property))) =
      surgeryHalfSignedTangent 1 (by norm_num) p.val := by
  have hs : p.val ∈ (P.surgeryMatchedRightCollar j).source :=
    (P.surgeryMatchedRightCollar_source j).symm ▸
      (show p.val ∈ halfCollarSource from p.property)
  have ht : P.surgeryMatchedRightCollar j p.val ∈ (P.leftCollar j).target ∪
      (P.rightCollar j).target := Or.inr (P.surgeryMatchedRightCollar_mem_target j p.property)
  have he : (fun q => P.surgerySeamInverseCoordinates j (P.surgeryMatchedRightCollar j q))
      =ᶠ[𝓝 p.val] surgeryHalfSignedCoordinate 1 := by
    filter_upwards [surgeryHalfDomain.isOpen.mem_nhds p.property] with q hq
    exact P.surgerySeamInverseCoordinates_matchedRightCollar hd j hq
  exact P.surgerySeamCoordinatesTangent_comp hd j (P.surgeryMatchedRightCollar j)
    1 (by norm_num) hs ht he

theorem surgerySeamOrientation_congr (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target) (j : Fin P.count)
    (O : ManifoldOrientation signedCollarModel (Torus × ℝ) 3)
    {x y : C.Carrier}
    (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target)
    (hy : y ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target) (hxy : x = y) :
    (Orientation.map (Fin 3) (P.surgerySeamInverseCoordinatesTangentEquiv hd j hx)
      (C.orientation.orientation x) = O.orientation (P.surgerySeamInverseCoordinates j x)) ↔
    (Orientation.map (Fin 3) (P.surgerySeamInverseCoordinatesTangentEquiv hd j hy)
      (C.orientation.orientation y) = O.orientation (P.surgerySeamInverseCoordinates j y)) := by
  subst y
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem exists_surgerySignedOrientation (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target) (j : Fin P.count) :
    ∃ O : ManifoldOrientation signedCollarModel surgerySignedDomain 3,
      ∀ x (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target),
        Orientation.map (Fin 3) (P.surgerySeamInverseCoordinatesTangentEquiv hd j hx)
          (C.orientation.orientation x) =
        O.orientation ⟨P.surgerySeamInverseCoordinates j x,
          P.surgerySeamInverseCoordinates_mem j hx⟩ := by
  obtain ⟨O, OL, OR, hL, hR, hnL, hnR⟩ := P.exists_surgerySignedOrientation_halves j
  have hl (p : surgeryHalfDomain) :
      Orientation.map (Fin 3) (P.surgerySeamInverseCoordinatesTangentEquiv hd j
        (Or.inl ((P.leftCollar j).map_source'
          ((P.left_source j).symm ▸ (show p.val ∈ halfCollarSource from p.property)))))
        (C.orientation.orientation (P.leftCollar j p.val)) =
      O.orientation (P.surgerySeamInverseCoordinates j (P.leftCollar j p.val)) := by
    let A := carrierSurgeryPatchTangentEquiv (P.leftCollar j)
      ((P.left_source j).symm ▸ (show p.val ∈ halfCollarSource from p.property))
    let F := P.surgerySeamInverseCoordinatesTangentEquiv hd j
      (Or.inl ((P.leftCollar j).map_source'
        ((P.left_source j).symm ▸ (show p.val ∈ halfCollarSource from p.property))))
    calc
      Orientation.map (Fin 3) F (C.orientation.orientation (P.leftCollar j p.val)) =
          Orientation.map (Fin 3) F (Orientation.map (Fin 3) A (OL.orientation p)) :=
        congrArg (Orientation.map (Fin 3) F) (hL p).symm
      _ = Orientation.map (Fin 3) (A.trans F) (OL.orientation p) :=
        (DifferentialGeometry.orientation_map_trans A F (OL.orientation p)).symm
      _ = Orientation.map (Fin 3) (surgeryHalfSignedTangent (-1) (by norm_num) p.val)
          (OL.orientation p) := by
            rw [P.surgerySeamCoordinatesTangent_left hd j p]
            rfl
      _ = O.orientation (surgeryHalfSignedCoordinate (-1) p.val) := hnL p
      _ = O.orientation (P.surgerySeamInverseCoordinates j (P.leftCollar j p.val)) := by
        rw [P.surgerySeamInverseCoordinates_leftCollar j p.property]
  have hr (p : surgeryHalfDomain) :
      Orientation.map (Fin 3) (P.surgerySeamInverseCoordinatesTangentEquiv hd j
        (x := P.surgeryMatchedRightCollar j p.val)
        (Or.inr (P.surgeryMatchedRightCollar_mem_target j p.property)))
        (C.orientation.orientation (P.surgeryMatchedRightCollar j p.val)) =
      O.orientation (P.surgerySeamInverseCoordinates j (P.surgeryMatchedRightCollar j p.val)) := by
    let A := carrierSurgeryPatchTangentEquiv (P.surgeryMatchedRightCollar j)
      ((P.surgeryMatchedRightCollar_source j).symm ▸
        (show p.val ∈ halfCollarSource from p.property))
    let F := P.surgerySeamInverseCoordinatesTangentEquiv hd j
      (x := P.surgeryMatchedRightCollar j p.val)
      (Or.inr (P.surgeryMatchedRightCollar_mem_target j p.property))
    calc
      Orientation.map (Fin 3) F
          (C.orientation.orientation (P.surgeryMatchedRightCollar j p.val)) =
          Orientation.map (Fin 3) F (Orientation.map (Fin 3) A (OR.orientation p)) :=
        congrArg (Orientation.map (Fin 3) F) (hR p).symm
      _ = Orientation.map (Fin 3) (A.trans F) (OR.orientation p) :=
        (DifferentialGeometry.orientation_map_trans A F (OR.orientation p)).symm
      _ = Orientation.map (Fin 3) (surgeryHalfSignedTangent 1 (by norm_num) p.val)
          (OR.orientation p) := by
            rw [P.surgerySeamCoordinatesTangent_right hd j p]
            rfl
      _ = O.orientation (surgeryHalfSignedCoordinate 1 p.val) := hnR p
      _ = O.orientation (P.surgerySeamInverseCoordinates j
          (P.surgeryMatchedRightCollar j p.val)) := by
        rw [P.surgerySeamInverseCoordinates_matchedRightCollar hd j p.property]
  refine ⟨O.restrictOpen surgerySignedDomain, fun x hx => ?_⟩
  change Orientation.map (Fin 3) (P.surgerySeamInverseCoordinatesTangentEquiv hd j hx)
    (C.orientation.orientation x) = O.orientation (P.surgerySeamInverseCoordinates j x)
  rcases hx with hx | hx
  · let p : surgeryHalfDomain := ⟨(P.leftCollar j).symm x,
      (show (P.leftCollar j).symm x ∈ halfCollarSource from
        (P.left_source j) ▸ (P.leftCollar j).map_target' hx)⟩
    have he : P.leftCollar j p.val = x := (P.leftCollar j).right_inv' hx
    have ht : P.leftCollar j p.val ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target :=
      Or.inl ((P.leftCollar j).map_source'
        ((P.left_source j).symm ▸ (show p.val ∈ halfCollarSource from p.property)))
    exact (P.surgerySeamOrientation_congr hd j O ht (Or.inl hx) he).mp (hl p)
  · let q := (P.rightCollar j).symm x
    have hq : q ∈ halfCollarSource := (P.right_source j) ▸ (P.rightCollar j).map_target' hx
    let p : surgeryHalfDomain := ⟨((P.matching j).symm q.1, q.2), hq⟩
    have he : P.surgeryMatchedRightCollar j p.val = x := by
      rw [surgeryMatchedRightCollar_apply]
      change P.rightCollar j (P.matching j ((P.matching j).symm q.1), q.2) = x
      rw [Diffeomorph.apply_symm_apply]
      exact (P.rightCollar j).right_inv' hx
    have ht : P.surgeryMatchedRightCollar j p.val ∈
        (P.leftCollar j).target ∪ (P.rightCollar j).target :=
      Or.inr (P.surgeryMatchedRightCollar_mem_target j p.property)
    exact (P.surgerySeamOrientation_congr hd j O ht (Or.inr hx) he).mp (hr p)

def surgerySignedOrientation (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target) (j : Fin P.count) :
    ManifoldOrientation signedCollarModel surgerySignedDomain 3 :=
  (P.exists_surgerySignedOrientation hd j).choose

theorem surgerySignedOrientation_map (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target) (j : Fin P.count) {x : C.Carrier}
    (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target) :
    Orientation.map (Fin 3) (P.surgerySeamInverseCoordinatesTangentEquiv hd j hx)
      (C.orientation.orientation x) =
    (P.surgerySignedOrientation hd j).orientation
      ⟨P.surgerySeamInverseCoordinates j x, P.surgerySeamInverseCoordinates_mem j hx⟩ :=
  (P.exists_surgerySignedOrientation hd j).choose_spec x hx

end GC.GraphManifold.TorusPairing
