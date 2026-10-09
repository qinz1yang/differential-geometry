import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Adapters
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.LinearSeams
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensSolidTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMerge
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ContractAlongPresentation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CliffordBlocks

/-!
# The carrier of a single distance-one filling

Only the filling seam is identified. Every other internal seam remains as two boundary tori.
The carrier and its smooth fold use the completed selected-quotient local geometry, independently
of a full contraction constructor. The forward fibre-coordinate change belongs to the host;
its filling degree is negative and its other boundary degrees have the opposite total.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem fillingProduct_internal (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) :
    ∀ r ∈ ({j} : Finset (Fin E.toTorus.pairing.count)),
      E.toTorus.leftPiece r ∈ E.toTorus.seamPair j ∧
        E.toTorus.rightPiece r ∈ E.toTorus.seamPair j := by
  intro r hr
  have he : r = j := Finset.mem_singleton.mp hr
  subst r
  exact ⟨E.toTorus.left_mem_seamPair j, E.toTorus.right_mem_seamPair j⟩

@[reducible]
def fillingProductCarrier (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) : CompactCarrier.{u} :=
  E.toTorus.restrictAlongCarrier (E.toTorus.seamPair j) {j} (fillingProduct_internal E j)
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)


instance fillingProductCarrier_charts (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) :
    ChartedSpace (EuclideanHalfSpace 3) (fillingProductCarrier E j).Carrier :=
  (fillingProductCarrier E j).charts

instance fillingProductCarrier_smooth (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) :
    IsManifold (modelWithCornersEuclideanHalfSpace 3) ∞ (fillingProductCarrier E j).Carrier :=
  (fillingProductCarrier E j).smooth

def fillingProductFold (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) : (fillingProductCarrier E j).Carrier → Q.Carrier :=
  E.toTorus.restrictAlongMap (E.toTorus.seamPair j) {j} (fillingProduct_internal E j)

theorem fillingProductFold_smooth (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) :
    ContMDiff (fillingProductCarrier E j).model (NoCuts.carrier Q).model ∞
      (fillingProductFold E j) :=
  E.toTorus.contMDiff_restrictAlongMap (E.toTorus.seamPair j) {j}
    (fillingProduct_internal E j) (TorusPresentation.externalPiece_not_mem_of_closed _ _)

theorem fillingProductFold_mfderiv (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (x : (fillingProductCarrier E j).Carrier) :
    Function.Bijective (mfderiv (fillingProductCarrier E j).model (NoCuts.carrier Q).model
      (fillingProductFold E j) x) :=
  E.toTorus.mfderiv_restrictAlongMap_bijective (E.toTorus.seamPair j) {j}
    (fillingProduct_internal E j) (TorusPresentation.externalPiece_not_mem_of_closed _ _) x

def fillingProductCollar (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count)
    (a : E.toTorus.AlongBoundarySide (E.toTorus.seamPair j) {j}) :
    PartialDiffeomorph halfCollarModel (fillingProductCarrier E j).model
      (Torus × EuclideanHalfSpace 1) (fillingProductCarrier E j).Carrier ∞ :=
  E.toTorus.restrictAlongBoundaryCollar (E.toTorus.seamPair j) {j}
    (fillingProduct_internal E j) (TorusPresentation.externalPiece_not_mem_of_closed _ _) a

theorem fillingProductCollar_source (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count)
    (a : E.toTorus.AlongBoundarySide (E.toTorus.seamPair j) {j}) :
    (fillingProductCollar E j a).source = halfCollarSource :=
  E.toTorus.restrictAlongHalfCollar_source (E.toTorus.seamPair j) {j}
    (fillingProduct_internal E j) a

theorem fillingProductCollar_disjoint (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) :
    Pairwise fun a a' : E.toTorus.AlongBoundarySide (E.toTorus.seamPair j) {j} =>
      Disjoint (fillingProductCollar E j a).target (fillingProductCollar E j a').target :=
  E.toTorus.restrictAlongHalfCollar_disjoint (E.toTorus.seamPair j) {j}
    (fillingProduct_internal E j)

theorem fillingProduct_boundary_iff (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (x : (fillingProductCarrier E j).Carrier) :
    (fillingProductCarrier E j).model.IsBoundaryPoint x ↔
      ∃ a : E.toTorus.AlongBoundarySide (E.toTorus.seamPair j) {j}, ∃ t : Torus,
        x = fillingProductCollar E j a (t, halfZero) :=
  (E.toTorus.restrictAlong_isBoundaryPoint_iff (E.toTorus.seamPair j) {j}
    (fillingProduct_internal E j) (TorusPresentation.externalPiece_not_mem_of_closed _ _) x).trans
      (E.toTorus.alongBoundaryImage_mem_iff (E.toTorus.seamPair j) {j}
        (fillingProduct_internal E j) x)

theorem fillingProductFold_collar (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count)
    (a : E.toTorus.AlongBoundarySide (E.toTorus.seamPair j) {j})
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    fillingProductFold E j (fillingProductCollar E j a p) =
      E.toTorus.cutMap (E.toTorus.sideCollar a.val p) := by
  change E.toTorus.restrictAlongMap (E.toTorus.seamPair j) {j}
    (fillingProduct_internal E j)
    (E.toTorus.restrictAlongHalfCollar (E.toTorus.seamPair j) {j}
      (fillingProduct_internal E j) a p) = _
  rw [E.toTorus.restrictAlongHalfCollar_apply _ _ _ _ hp,
    E.toTorus.restrictAlongMap_quotientMap, E.toTorus.subCollar_apply _ _ _ hp]

def fillingHostFibreChange {r : ℕ} (B : PlanarBase.{u} r)
    (g : B.surface.Carrier → Circle)
    (hg : ContMDiff (SurfaceModel.model B.surface.kind) (𝓡 1) ∞ g) :
    (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      (SurfaceModel.model B.surface.kind).prod (𝓡 1)⟯ B.surface.Carrier × Circle where
  toFun x := (x.1, g x.1 * x.2)
  invFun y := (y.1, (g y.1)⁻¹ * y.2)
  left_inv x := by simp
  right_inv y := by simp
  contMDiff_toFun := contMDiff_fst.prodMk ((hg.comp contMDiff_fst).mul contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk ((hg.inv.comp contMDiff_fst).mul contMDiff_snd)

def fillingHostPhase {r : ℕ} (B : PlanarBase.{u} r) (i : Fin r) (n : ℤ)
    (z : B.surface.Carrier) : Circle :=
  unitOf (B.embedding z - planarCenter r i) ^ n

theorem fillingHostPhase_smooth {r : ℕ} (B : PlanarBase.{u} r) (i : Fin r)
    (hi : i.val ≠ 0) (n : ℤ) :
    ContMDiff (SurfaceModel.model B.surface.kind) (𝓡 1) ∞ (fillingHostPhase B i n) := by
  intro z
  have hz : B.embedding z ∈ planarModel r := B.range_embedding ▸ Set.mem_range_self z
  have hnorm := hz.2 i hi
  have hne : B.embedding z - planarCenter r i ≠ 0 := by
    intro he
    rw [he, norm_zero] at hnorm
    norm_num at hnorm
  exact (contMDiff_circle_zpow n).contMDiffAt.comp z
    ((contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp z
      ((B.isSmoothEmbedding.contMDiff.sub contMDiff_const).contMDiffAt))

theorem fillingHostPhase_inner {r : ℕ} (B : PlanarBase.{u} r) (i : Fin r)
    (hi : i.val ≠ 0) (n : ℤ) (t : Circle) :
    fillingHostPhase B i n (B.collar i (t, halfZero)) = t ^ (-n) := by
  unfold fillingHostPhase
  rw [B.embedding_collar]
  have he : planarCircleMap r i t - planarCenter r i =
      (1 / 2 : ℝ) • ((t⁻¹ : Circle) : ℂ) := by
    rw [Circle.coe_inv_eq_conj]
    simp [planarCircleMap, planarRadius, hi, Complex.real_smul]
  rw [he, unitOf_smul (by norm_num), inv_zpow']

theorem fillingMeridian_normalization (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool) (h : E.IsMergeSeam j b) :
    ∃ q : ℤ, E.mergeSlope j b = Merge.sectionSlope q ∧
      Merge.fibreShear (-q) • E.mergeSlope j b = meridianSlope := by
  obtain ⟨q, hq⟩ := h.exists_mergeSlope_eq
  refine ⟨q, hq, ?_⟩
  rw [hq, Merge.fibreShear_smul_sectionSlope, add_neg_cancel, Merge.sectionSlope_zero]

def fillingHostInnerChange {r : ℕ} (B : PlanarBase.{u} r) (i : Fin r)
    (hi : i.val ≠ 0) (q : ℤ) :
    (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      (SurfaceModel.model B.surface.kind).prod (𝓡 1)⟯ B.surface.Carrier × Circle :=
  fillingHostFibreChange B (fillingHostPhase B i q) (fillingHostPhase_smooth B i hi q)

theorem fillingHostInnerChange_boundary {r : ℕ} (B : PlanarBase.{u} r) (i : Fin r)
    (hi : i.val ≠ 0) (q : ℤ) (t v : Circle) :
    fillingHostInnerChange B i hi q (B.collar i (t, halfZero), v) =
      (B.collar i (t, halfZero), t ^ (-q) * v) := by
  change (B.collar i (t, halfZero), fillingHostPhase B i q
    (B.collar i (t, halfZero)) * v) = _
  rw [fillingHostPhase_inner B i hi q t]

def fillingSolidBasisChange (n : ℤ) :
    (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), (𝓡∂ 2).prod (𝓡 1)⟯
      UnitDisc.{0} × Circle where
  toFun x := (discRotate (x.2 ^ n) x.1, x.2)
  invFun y := (discRotate (y.2 ^ (-n)) y.1, y.2)
  left_inv x := by
    dsimp
    rw [discRotate_discRotate, ← zpow_add, neg_add_cancel, zpow_zero, discRotate_one]
  right_inv y := by
    dsimp
    rw [discRotate_discRotate, ← zpow_add, add_neg_cancel, zpow_zero, discRotate_one]
  contMDiff_toFun := (contMDiff_discRotate.comp
    (((contMDiff_circle_zpow n).comp contMDiff_snd).prodMk contMDiff_fst)).prodMk
      contMDiff_snd
  contMDiff_invFun := (contMDiff_discRotate.comp
    (((contMDiff_circle_zpow (-n)).comp contMDiff_snd).prodMk contMDiff_fst)).prodMk
      contMDiff_snd

def fillingDiscBoundary (t : Circle) : UnitDisc.{0} :=
  ULift.up ⟨(t : ℂ), by change ‖(t : ℂ)‖ ^ 2 ≤ 1; simp⟩

theorem fillingSolidBasisChange_boundary (n : ℤ) (t v : Circle) :
    fillingSolidBasisChange n (fillingDiscBoundary t, v) =
      (fillingDiscBoundary (v ^ n * t), v) := by
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    exact Circle.coe_mul (v ^ n) t
  · rfl

theorem fillingSolidBasisChange_meridian (n : ℤ) (t : Circle) :
    fillingSolidBasisChange n (fillingDiscBoundary t, 1) = (fillingDiscBoundary t, 1) := by
  rw [fillingSolidBasisChange_boundary, one_zpow, one_mul]

end GC.Seifert.ElementaryPresentation

namespace GC.Seifert

open Set
open DifferentialGeometry.Topology.Manifold
open ElementaryPresentation

private theorem fillingHalfLift_coordinate (s : EuclideanHalfSpace 1) :
    halfSpaceOneLift (s.val 0) = s := by
  apply Subtype.ext
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  change max (s.val 0) 0 = s.val 0
  exact max_eq_left s.property

theorem exists_collarExtension_of_isotopic_identity {C : CompactCarrier}
    (c : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hc : c.source = halfCollarSource)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : IsotopicDiffeomorph f (Diffeomorph.refl torusModel Torus ∞)) :
    ∃ Θ : C.Carrier ≃ₘ⟮C.model, C.model⟯ C.Carrier,
      (∀ t s, s.val 0 ≤ 1 / 4 → Θ (c (t, s)) = c (f t, s)) ∧
      ∀ x, x ∉ c '' (univ ×ˢ (halfSpaceOneLift '' Icc (0 : ℝ) (1 / 2))) → Θ x = x := by
  obtain ⟨F, hF, hFi, hF0, hF1⟩ := hf
  let G : ℝ → Torus ≃ₘ⟮torusModel, torusModel⟯ Torus := fun s => F (seamCut s)
  have hG : ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      (fun q : ℝ × Torus => G q.1 q.2) :=
    hF.comp ((contDiff_seamCut.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  have hGi : ContMDiff (𝓘(ℝ).prod torusModel) torusModel ∞
      (fun q : ℝ × Torus => (G q.1).symm q.2) :=
    hFi.comp ((contDiff_seamCut.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  let D := sliceDiffeomorph G hG hGi (fun s : EuclideanHalfSpace 1 => s.val 0)
    contMDiff_halfSpaceOneCoordinate
  let K : Set (Torus × EuclideanHalfSpace 1) :=
    univ ×ˢ (halfSpaceOneLift '' Icc (0 : ℝ) (1 / 2))
  have hLift : Continuous halfSpaceOneLift := by
    rw [funext halfSpaceOneLift_eq]
    exact halfSpaceOneHomeomorph.symm.continuous.comp
      ((continuous_const.max continuous_id).subtype_mk fun s => le_max_left 0 s)
  have hK : IsCompact K := isCompact_univ.prod (isCompact_Icc.image hLift)
  have hKs : K ⊆ c.source := by
    rintro ⟨t, s⟩ ⟨ht, a, ha, rfl⟩
    rw [hc]
    change max a 0 < 1
    rw [max_eq_left ha.1]
    linarith [ha.2]
  have hfix : ∀ z, z ∉ K → D z = z := by
    intro z hz
    have hle : 1 / 2 ≤ z.2.val 0 := by
      by_contra h
      apply hz
      exact ⟨mem_univ z.1, z.2.val 0,
        ⟨z.2.property, (not_le.mp h).le⟩, fillingHalfLift_coordinate z.2⟩
    change (F (seamCut (z.2.val 0)) z.1, z.2) = z
    rw [seamCut_of_ge hle, hF1]
    rfl
  obtain ⟨Θ, hΘ, hΘfix⟩ := exists_chartTwist c D hK hKs hfix
  refine ⟨Θ, ?_, hΘfix⟩
  intro t s hs
  have hsrc : (t, s) ∈ c.source := by
    rw [hc]
    change s.val 0 < 1
    linarith
  rw [hΘ (t, s) hsrc]
  change c (F (seamCut (s.val 0)) t, s) = c (f t, s)
  rw [seamCut_of_le hs, hF0]

theorem exists_collarBoundaryExtension_of_isotopic {C : CompactCarrier}
    (c : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hc : c.source = halfCollarSource)
    (f L : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : IsotopicDiffeomorph f L)
    (H : C.Carrier ≃ₘ⟮C.model, C.model⟯ C.Carrier)
    (hH : ∀ t, H (c (t, halfZero)) = c (L t, halfZero)) :
    ∃ Θ : C.Carrier ≃ₘ⟮C.model, C.model⟯ C.Carrier,
      ∀ t, Θ (c (t, halfZero)) = c (f t, halfZero) := by
  obtain ⟨F, hF, hFi, hF0, hF1⟩ := hf
  let R := L.symm.trans f
  have hR : IsotopicDiffeomorph R (Diffeomorph.refl torusModel Torus ∞) := by
    refine ⟨fun s => L.symm.trans (F s), ?_, ?_, ?_, ?_⟩
    · exact hF.comp (contMDiff_fst.prodMk (L.symm.contMDiff.comp contMDiff_snd))
    · exact L.contMDiff.comp hFi
    · change L.symm.trans (F 0) = L.symm.trans f
      rw [hF0]
    · change L.symm.trans (F 1) = Diffeomorph.refl torusModel Torus ∞
      rw [hF1, Diffeomorph.symm_trans_self]
  obtain ⟨K, hK, hKfix⟩ := exists_collarExtension_of_isotopic_identity c hc R hR
  refine ⟨H.trans K, fun t => ?_⟩
  change K (H (c (t, halfZero))) = c (f t, halfZero)
  rw [hH, hK (L t) halfZero (by change (0 : ℝ) ≤ 1 / 4; norm_num)]
  change c (f (L.symm (L t)), halfZero) = c (f t, halfZero)
  rw [L.symm_apply_apply]

theorem meridianStabilizer_entries (A : GL (Fin 2) ℤ)
    (hA : A • meridianSlope = meridianSlope) :
    A.val 1 0 = 0 ∧ (A.val 0 0 = 1 ∨ A.val 0 0 = -1) ∧
      (A.val 1 1 = 1 ∨ A.val 1 1 = -1) := by
  change A • PrimitiveSlope.mk (1, 0) (by decide) =
    PrimitiveSlope.mk (1, 0) (by decide) at hA
  rw [PrimitiveSlope.smul_mk, PrimitiveSlope.mk_eq_mk_iff] at hA
  have hcol : A.val 1 0 = 0 ∧ (A.val 0 0 = 1 ∨ A.val 0 0 = -1) := by
    rcases hA with hA | hA
    · have h0 := congrArg Prod.fst hA
      have h1 := congrArg Prod.snd hA
      simp only [smulVec, mul_one, mul_zero, add_zero] at h0 h1
      exact ⟨h1.symm, Or.inl h0.symm⟩
    · have h0 := congrArg Prod.fst hA
      have h1 := congrArg Prod.snd hA
      simp only [smulVec, Prod.fst_neg, Prod.snd_neg, mul_one, mul_zero, add_zero]
        at h0 h1
      exact ⟨by omega, Or.inr (by omega)⟩
  refine ⟨hcol.1, hcol.2, ?_⟩
  have hdet := Int.isUnit_iff.mp (Matrix.isUnits_det_units A)
  rw [Matrix.det_fin_two, hcol.1, mul_zero, sub_zero] at hdet
  rcases hcol.2 with h0 | h0 <;> rw [h0] at hdet
  · simpa only [one_mul] using hdet
  · rcases hdet with hdet | hdet
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

theorem torusMatrix_matchingResidual (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    torusMatrix ((linearTorusDiffeomorph (torusUnit f)).symm.trans f) = 1 := by
  have hL : torusMatrix (linearTorusDiffeomorph (torusUnit f)) = torusMatrix f :=
    torusMatrix_linearTorusDiffeomorph (torusUnit f)
  rw [torusMatrix_trans, ← hL, ← torusMatrix_trans,
    Diffeomorph.symm_trans_self, torusMatrix_refl]

private def fillingDiscConj (z : UnitDisc.{0}) : UnitDisc.{0} :=
  ULift.up ⟨starRingEnd ℂ z.down.val, by
    change ‖starRingEnd ℂ z.down.val‖ ^ 2 ≤ 1
    rw [Complex.norm_conj]
    exact z.down.property⟩

private theorem fillingDiscConj_smooth : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ fillingDiscConj := by
  have hv : ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞
      (fun z : UnitDisc.{0} => starRingEnd ℂ z.down.val) :=
    Complex.conjCLE.contDiff.contMDiff.comp contMDiff_disc_val
  have hd : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞
      (fun z : UnitDisc.{0} => (fillingDiscConj z).down) :=
    (unitDiscAtlas.contMDiff_iff_subtype_val _).mpr hv
  exact (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).contMDiff.comp hd

private def fillingDiscConjDiffeomorph : UnitDisc.{0} ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ UnitDisc.{0} where
  toFun := fillingDiscConj
  invFun := fillingDiscConj
  left_inv z := by
    apply ULift.ext
    apply Subtype.ext
    exact Complex.conj_conj z.down.val
  right_inv z := by
    apply ULift.ext
    apply Subtype.ext
    exact Complex.conj_conj z.down.val
  contMDiff_toFun := fillingDiscConj_smooth
  contMDiff_invFun := fillingDiscConj_smooth

private def fillingCircleInv : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv t := inv_inv t
  right_inv t := inv_inv t
  contMDiff_toFun := contMDiff_inv (𝓡 1) ∞
  contMDiff_invFun := contMDiff_inv (𝓡 1) ∞

private theorem fillingDiscConj_boundary (t : Circle) :
    fillingDiscConjDiffeomorph (fillingDiscBoundary t) = fillingDiscBoundary t⁻¹ := by
  apply ULift.ext
  apply Subtype.ext
  exact (Circle.coe_inv_eq_conj t).symm

theorem exists_linearSolidExtension_of_meridianStabilizer (A : GL (Fin 2) ℤ)
    (hA : A • meridianSlope = meridianSlope) :
    ∃ D : (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), (𝓡∂ 2).prod (𝓡 1)⟯
        UnitDisc.{0} × Circle,
      ∀ t v : Circle, D (fillingDiscBoundary t, v) =
        (fillingDiscBoundary (linearTorusDiffeomorph A (t, v)).1,
          (linearTorusDiffeomorph A (t, v)).2) := by
  obtain ⟨h10, h00, h11⟩ := meridianStabilizer_entries A hA
  let I := Diffeomorph.refl (𝓡∂ 2) UnitDisc.{0} ∞
  let J := Diffeomorph.refl (𝓡 1) Circle ∞
  rcases h00 with h00 | h00 <;> rcases h11 with h11 | h11
  · refine ⟨fillingSolidBasisChange (A.val 0 1), fun t v => ?_⟩
    rw [fillingSolidBasisChange_boundary, mul_comm]
    change (fillingDiscBoundary (t * v ^ A.val 0 1), v) =
      (fillingDiscBoundary (t ^ A.val 0 0 * v ^ A.val 0 1),
        t ^ A.val 1 0 * v ^ A.val 1 1)
    simp only [h00, h10, h11, zpow_one, zpow_zero, one_mul]
  · refine ⟨(fillingSolidBasisChange (A.val 0 1)).trans
      (I.prodCongr fillingCircleInv), fun t v => ?_⟩
    change (I.prodCongr fillingCircleInv) (fillingSolidBasisChange (A.val 0 1)
      (fillingDiscBoundary t, v)) = _
    rw [fillingSolidBasisChange_boundary, mul_comm]
    change (fillingDiscBoundary (t * v ^ A.val 0 1), v⁻¹) =
      (fillingDiscBoundary (t ^ A.val 0 0 * v ^ A.val 0 1),
        t ^ A.val 1 0 * v ^ A.val 1 1)
    rw [h00, h10, h11, zpow_one, zpow_zero, one_mul, zpow_neg_one]
  · refine ⟨(fillingDiscConjDiffeomorph.prodCongr J).trans
      (fillingSolidBasisChange (A.val 0 1)), fun t v => ?_⟩
    change fillingSolidBasisChange (A.val 0 1)
      (fillingDiscConjDiffeomorph (fillingDiscBoundary t), v) = _
    rw [fillingDiscConj_boundary, fillingSolidBasisChange_boundary, mul_comm]
    change (fillingDiscBoundary (t⁻¹ * v ^ A.val 0 1), v) =
      (fillingDiscBoundary (t ^ A.val 0 0 * v ^ A.val 0 1),
        t ^ A.val 1 0 * v ^ A.val 1 1)
    rw [h00, h10, h11, zpow_one, zpow_zero, one_mul, zpow_neg_one]
  · refine ⟨((fillingDiscConjDiffeomorph.prodCongr J).trans
      (fillingSolidBasisChange (A.val 0 1))).trans (I.prodCongr fillingCircleInv), fun t v => ?_⟩
    change (I.prodCongr fillingCircleInv) (fillingSolidBasisChange (A.val 0 1)
      (fillingDiscConjDiffeomorph (fillingDiscBoundary t), v)) = _
    rw [fillingDiscConj_boundary, fillingSolidBasisChange_boundary, mul_comm]
    change (fillingDiscBoundary (t⁻¹ * v ^ A.val 0 1), v⁻¹) =
      (fillingDiscBoundary (t ^ A.val 0 0 * v ^ A.val 0 1),
        t ^ A.val 1 0 * v ^ A.val 1 1)
    rw [h00, h10, h11, zpow_zero, one_mul, zpow_neg_one, zpow_neg_one]

private theorem fillingSolidDiscCircle_boundary (t v : Circle) :
    solidTorusDiscCircle (solidTorusCollar.{0} ((t, v), halfZero)) =
      (fillingDiscBoundary t, v) := by
  rw [solidTorusCollar_eq_symm, solidTorusDiscCircle.apply_symm_apply]
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    exact cliffordDiscCollarMap_zero_val t
  · rfl

theorem exists_solidExtension_of_meridianStabilizer
    (hT : TorusMappingClassLinear) (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hf : torusUnit f • meridianSlope = meridianSlope) :
    ∃ D : (UnitDisc.{0} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), (𝓡∂ 2).prod (𝓡 1)⟯
        UnitDisc.{0} × Circle,
      ∀ t v : Circle, D (fillingDiscBoundary t, v) =
        (fillingDiscBoundary (f (t, v)).1, (f (t, v)).2) := by
  obtain ⟨D, hD⟩ := exists_linearSolidExtension_of_meridianStabilizer (torusUnit f) hf
  let H := (solidTorusDiscCircle.{0}.trans D).trans solidTorusDiscCircle.symm
  have hH : ∀ t, H (solidTorusCollar.{0} (t, halfZero)) =
      solidTorusCollar (linearTorusDiffeomorph (torusUnit f) t, halfZero) := by
    intro t
    change solidTorusDiscCircle.symm
      (D (solidTorusDiscCircle (solidTorusCollar (t, halfZero)))) = _
    rw [fillingSolidDiscCircle_boundary, hD]
    rw [← fillingSolidDiscCircle_boundary]
    exact solidTorusDiscCircle.symm_apply_apply _
  obtain ⟨Θ, hΘ⟩ := exists_collarBoundaryExtension_of_isotopic
    (C := solidTorusCarrier.{0}) solidTorusCollar solidTorusCollar_source.{0} f
    (linearTorusDiffeomorph (torusUnit f)) (hT f) H hH
  refine ⟨(solidTorusDiscCircle.symm.trans Θ).trans solidTorusDiscCircle, ?_⟩
  intro t v
  change solidTorusDiscCircle (Θ (solidTorusDiscCircle.symm
    (fillingDiscBoundary t, v))) = _
  rw [← fillingSolidDiscCircle_boundary, solidTorusDiscCircle.symm_apply_apply, hΘ]
  exact fillingSolidDiscCircle_boundary (f (t, v)).1 (f (t, v)).2

end GC.Seifert

namespace GC.Seifert.ElementaryPresentation

def cappingBaseSet : Set PlaneLift.{u} :=
  {z | ConeFilling.filledFunction z.down ≤ 0}

theorem cappingBaseFunction_smooth :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun z : PlaneLift.{u} => ConeFilling.filledFunction z.down) :=
  ConeFilling.contDiff_filledFunction.contMDiff.comp contMDiff_planeLift_down

theorem cappingBaseFunction_regular (z : PlaneLift.{u})
    (hz : ConeFilling.filledFunction z.down = 0) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ)
      (fun w : PlaneLift.{u} => ConeFilling.filledFunction w.down) z ≠ 0 := by
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ))
    (s := ULift.up) (y := z.down)
    (cappingBaseFunction_smooth.mdifferentiableAt (by simp))
    (contMDiff_planeLift_up.mdifferentiableAt (by simp)) ?_
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ConeFilling.filledFunction z.down ≠ 0
  rw [mfderiv_eq_fderiv]
  exact ConeFilling.filledFunction_regular hz

def cappingBaseAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℂ) 2 cappingBaseSet.{u} :=
  SmoothBoundaryAtlas.regularSublevel 𝓘(ℝ, ℂ) (n := 1) Complex.finrank_real_complex
    cappingBaseFunction_smooth 0 cappingBaseFunction_regular

instance : ChartedSpace (EuclideanHalfSpace 2) cappingBaseSet.{u} :=
  cappingBaseAtlas.toChartedSpace

instance : IsManifold (𝓡∂ 2) ∞ cappingBaseSet.{u} := cappingBaseAtlas.isManifold

def sectionCappingDiffeomorph (q : ℤ) :
    (cappingBaseSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯
      (Merge.sectionFilling q).filledSet.{u} where
  toFun x := ⟨(ULift.up (6 * (x.1.val.down - ((3 / 2 : ℝ) : ℂ))), x.2), by
    rw [Merge.mem_filledSet_sectionFilling_iff]
    have he : ((3 / 2 : ℝ) : ℂ) + 6 * (x.1.val.down - ((3 / 2 : ℝ) : ℂ)) / 6 =
        x.1.val.down := by ring
    rw [he]
    exact x.1.property⟩
  invFun y := (⟨ULift.up (((3 / 2 : ℝ) : ℂ) + y.val.1.down / 6),
    (Merge.mem_filledSet_sectionFilling_iff q y.val).mp y.property⟩, y.val.2)
  left_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      apply ULift.ext
      dsimp
      ring
    · rfl
  right_inv y := by
    apply Subtype.ext
    apply Prod.ext
    · apply ULift.ext
      dsimp
      ring
    · rfl
  contMDiff_toFun := by
    apply ((Merge.sectionFilling q).filledAtlas.contMDiff_iff_subtype_val _).mpr
    have ha : ContDiff ℝ ∞ (fun z : ℂ => 6 * (z - ((3 / 2 : ℝ) : ℂ))) :=
      contDiff_const.mul (contDiff_id.sub contDiff_const)
    exact (contMDiff_planeLift_up.comp (ha.contMDiff.comp
      (contMDiff_planeLift_down.comp
        (cappingBaseAtlas.contMDiff_subtype_val.comp contMDiff_fst)))).prodMk contMDiff_snd
  contMDiff_invFun := by
    refine ContMDiff.prodMk ?_
      (contMDiff_snd.comp (Merge.sectionFilling q).filledAtlas.contMDiff_subtype_val)
    apply (cappingBaseAtlas.contMDiff_iff_subtype_val _).mpr
    have ha : ContDiff ℝ ∞ (fun z : ℂ => ((3 / 2 : ℝ) : ℂ) + z / 6) :=
      contDiff_const.add (contDiff_id.div_const 6)
    exact contMDiff_planeLift_up.comp (ha.contMDiff.comp
      (contMDiff_planeLift_down.comp
        (contMDiff_fst.comp (Merge.sectionFilling q).filledAtlas.contMDiff_subtype_val)))

def cappingPantsBaseDiffeomorph (B : PlanarBase.{u} 3) :
    planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, SurfaceModel.model B.surface.kind⟯ B.surface.Carrier :=
  pantsPlanarBase.isSmoothEmbedding.diffeomorphOfRangeEq B.isSmoothEmbedding
    (by rw [pantsPlanarBase.range_embedding, B.range_embedding])

theorem cappingPantsBaseDiffeomorph_embedding (B : PlanarBase.{u} 3)
    (z : planarSet.{u} 3) :
    B.embedding (cappingPantsBaseDiffeomorph B z) = z.val.down :=
  pantsPlanarBase.isSmoothEmbedding.comp_diffeomorphOfRangeEq B.isSmoothEmbedding _ z

theorem cappingPantsBaseDiffeomorph_boundary (B : PlanarBase.{u} 3)
    (i : Fin 3) (t : Circle) :
    cappingPantsBaseDiffeomorph B (planarCollar 3 (Or.inr rfl) i (t, halfZero)) =
      B.collar i (t, halfZero) := by
  apply B.isSmoothEmbedding.isEmbedding.injective
  rw [cappingPantsBaseDiffeomorph_embedding, B.embedding_collar]
  exact planarCollar_zero_val.{u} (Or.inr rfl) i t

def cappingOuterRadius (t : Circle) : ℝ :=
  (3 / 2) * (t : ℂ).re + Real.sqrt ((9 / 4) * (t : ℂ).re ^ 2 + 27 / 4)

theorem cappingOuterRadius_eq (t : Circle) :
    cappingOuterRadius t ^ 2 - 3 * (t : ℂ).re * cappingOuterRadius t = 27 / 4 := by
  have hs := Real.sq_sqrt (by positivity :
    0 ≤ (9 / 4) * (t : ℂ).re ^ 2 + 27 / 4)
  dsimp [cappingOuterRadius]
  nlinarith

theorem cappingOuterRadius_gt_half (t : Circle) :
    1 / 2 < cappingOuterRadius t := by
  have hr : -1 ≤ (t : ℂ).re := by
    have he := Complex.abs_re_le_norm (t : ℂ)
    rw [Circle.norm_coe] at he
    exact (abs_le.mp he).1
  have hs := Real.sq_sqrt (by positivity :
    0 ≤ (9 / 4) * (t : ℂ).re ^ 2 + 27 / 4)
  have hsp := Real.sqrt_nonneg ((9 / 4) * (t : ℂ).re ^ 2 + 27 / 4)
  dsimp [cappingOuterRadius]
  nlinarith [sq_nonneg ((t : ℂ).re)]

def cappingPolarPoint (r : ℝ) (t : Circle) : ℂ :=
  ((-(3 / 2) : ℝ) : ℂ) + r • (t : ℂ)

theorem cappingPolarPoint_radius (r : ℝ) (hr : 0 ≤ r) (t : Circle) :
    ‖cappingPolarPoint r t - ((-(3 / 2) : ℝ) : ℂ)‖ = r := by
  rw [cappingPolarPoint, add_sub_cancel_left, norm_smul, Circle.norm_coe,
    mul_one, Real.norm_of_nonneg hr]

theorem cappingPolarPoint_norm_sq (r : ℝ) (t : Circle) :
    ‖cappingPolarPoint r t‖ ^ 2 = r ^ 2 - 3 * (t : ℂ).re * r + 9 / 4 := by
  have ht : (t : ℂ).re ^ 2 + (t : ℂ).im ^ 2 = 1 := by
    calc
      (t : ℂ).re ^ 2 + (t : ℂ).im ^ 2 = ‖(t : ℂ)‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      _ = 1 := by rw [Circle.norm_coe]; norm_num
  simp only [Complex.sq_norm, Complex.normSq_apply, cappingPolarPoint,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, zero_add]
  nlinarith [congrArg (fun a : ℝ => r ^ 2 * a) ht]

theorem cappingPolarPoint_outer (t : Circle) :
    ‖cappingPolarPoint (cappingOuterRadius t) t‖ = 3 := by
  have he := cappingOuterRadius_eq t
  have hn := cappingPolarPoint_norm_sq (cappingOuterRadius t) t
  have hp := norm_nonneg (cappingPolarPoint (cappingOuterRadius t) t)
  nlinarith

theorem cappingPolarPoint_mem_iff (r : ℝ) (hr : 1 / 2 ≤ r) (t : Circle) :
    ConeFilling.filledFunction (cappingPolarPoint r t) ≤ 0 ↔
      r ≤ cappingOuterRadius t := by
  rw [ConeFilling.filledFunction_nonpos_iff,
    cappingPolarPoint_radius r (by linarith) t, and_iff_left hr]
  have he := cappingOuterRadius_eq t
  have hn := cappingPolarPoint_norm_sq r t
  have hR := cappingOuterRadius_gt_half t
  have hsq : 0 < cappingOuterRadius t + r - 3 * (t : ℂ).re := by
    have hs := Real.sq_sqrt (by positivity :
      0 ≤ (9 / 4) * (t : ℂ).re ^ 2 + 27 / 4)
    have hp := Real.sqrt_nonneg ((9 / 4) * (t : ℂ).re ^ 2 + 27 / 4)
    dsimp [cappingOuterRadius]
    nlinarith
  have hf : r ^ 2 - 3 * (t : ℂ).re * r - 27 / 4 =
      (r - cappingOuterRadius t) *
        (cappingOuterRadius t + r - 3 * (t : ℂ).re) := by
    nlinarith [he]
  constructor
  · intro h
    have hprod : (r - cappingOuterRadius t) *
        (cappingOuterRadius t + r - 3 * (t : ℂ).re) ≤ 0 := by
      rw [← hf]
      nlinarith [norm_nonneg (cappingPolarPoint r t)]
    exact sub_nonpos.mp ((mul_nonpos_iff.mp hprod).resolve_left
      (by intro h; exact (not_le.mpr hsq) h.2)).1
  · intro h
    have hprod := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hsq.le
    rw [← hf] at hprod
    nlinarith [norm_nonneg (cappingPolarPoint r t)]

theorem cappingOuterRadius_smooth : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ cappingOuterRadius := by
  have h : ContDiff ℝ ∞ (fun z : ℂ =>
      (3 / 2) * z.re + Real.sqrt ((9 / 4) * z.re ^ 2 + 27 / 4)) :=
    (contDiff_const.mul Complex.reCLM.contDiff).add
      (((contDiff_const.mul (Complex.reCLM.contDiff.pow 2)).add contDiff_const).sqrt
        (fun z => by positivity))
  exact h.contMDiff.comp contMDiff_circle_coe

def cappingStretch (t : Circle) (s : ℝ) : ℝ :=
  1 / 2 + (s - 1 / 2) * (cappingOuterRadius t - 1 / 2) / (5 / 2)

def cappingUnstretch (t : Circle) (r : ℝ) : ℝ :=
  1 / 2 + (r - 1 / 2) * (5 / 2) / (cappingOuterRadius t - 1 / 2)

theorem cappingUnstretch_stretch (t : Circle) (s : ℝ) :
    cappingUnstretch t (cappingStretch t s) = s := by
  have hn : 2 * cappingOuterRadius t - 1 ≠ 0 := by
    linarith [cappingOuterRadius_gt_half t]
  unfold cappingStretch cappingUnstretch
  field_simp [hn]
  ring

theorem cappingStretch_unstretch (t : Circle) (r : ℝ) :
    cappingStretch t (cappingUnstretch t r) = r := by
  have hn : 2 * cappingOuterRadius t - 1 ≠ 0 := by
    linarith [cappingOuterRadius_gt_half t]
  unfold cappingStretch cappingUnstretch
  field_simp [hn]
  ring

theorem cappingStretch_bounds (t : Circle) (s : ℝ) (hs : 1 / 2 ≤ s ∧ s ≤ 3) :
    1 / 2 ≤ cappingStretch t s ∧ cappingStretch t s ≤ cappingOuterRadius t := by
  have hp := cappingOuterRadius_gt_half t
  have h1 := mul_nonneg (sub_nonneg.mpr hs.1) (sub_nonneg.mpr hp.le)
  have h2 := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hp.le)
  dsimp [cappingStretch]
  constructor <;> nlinarith

theorem cappingUnstretch_bounds (t : Circle) (r : ℝ)
    (hr : 1 / 2 ≤ r ∧ r ≤ cappingOuterRadius t) :
    1 / 2 ≤ cappingUnstretch t r ∧ cappingUnstretch t r ≤ 3 := by
  have hp : 0 < cappingOuterRadius t - 1 / 2 := by
    linarith [cappingOuterRadius_gt_half t]
  dsimp [cappingUnstretch]
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (by linarith) (by norm_num)) hp.le)
  · have he := (div_le_iff₀ hp).mpr
      (show (r - 1 / 2) * (5 / 2) ≤ (5 / 2) *
        (cappingOuterRadius t - 1 / 2) by nlinarith [hr.2])
    linarith

def cappingAnnulusForward (x : planarSet.{u} 2) : cappingBaseSet.{u} :=
  ⟨ULift.up (cappingPolarPoint
    (cappingStretch (unitOf x.val.down) ‖x.val.down‖) (unitOf x.val.down)), by
    have hx : 1 / 2 ≤ ‖x.val.down‖ ∧ ‖x.val.down‖ ≤ 3 :=
      ((mem_planarModel_two x.val.down).mp
        ((mem_planarSet_iff (Or.inl rfl) x.val).mp x.property)).symm
    have hb := cappingStretch_bounds (unitOf x.val.down) ‖x.val.down‖ hx
    exact (cappingPolarPoint_mem_iff _ hb.1 _).mpr hb.2⟩

def cappingAnnulusInverse (y : cappingBaseSet.{u}) : planarSet.{u} 2 :=
  ⟨ULift.up (cappingUnstretch
      (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ)))
      ‖y.val.down - ((-(3 / 2) : ℝ) : ℂ)‖ •
        (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ)) : ℂ)), by
    have hy := (ConeFilling.filledFunction_nonpos_iff y.val.down).mp y.property
    have he : cappingPolarPoint ‖y.val.down - ((-(3 / 2) : ℝ) : ℂ)‖
        (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ))) = y.val.down := by
      rw [cappingPolarPoint, norm_smul_unitOf]
      ring
    have hh : ConeFilling.filledFunction y.val.down ≤ 0 := y.property
    have hr := (cappingPolarPoint_mem_iff _ hy.2 _).mp (he.symm ▸ hh)
    have hb := cappingUnstretch_bounds _ _ ⟨hy.2, hr⟩
    apply (mem_planarSet_iff (Or.inl rfl) _).mpr
    apply (mem_planarModel_two _).mpr
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by linarith [hb.1])]
    exact hb.symm⟩

theorem cappingAnnulusInverse_forward (x : planarSet.{u} 2) :
    cappingAnnulusInverse (cappingAnnulusForward x) = x := by
  have hx : 1 / 2 ≤ ‖x.val.down‖ ∧ ‖x.val.down‖ ≤ 3 :=
    ((mem_planarModel_two x.val.down).mp
      ((mem_planarSet_iff (Or.inl rfl) x.val).mp x.property)).symm
  have hp : 0 < cappingStretch (unitOf x.val.down) ‖x.val.down‖ := by
    linarith [(cappingStretch_bounds (unitOf x.val.down) _ hx).1]
  apply Subtype.ext
  apply ULift.ext
  change cappingUnstretch
    (unitOf (cappingPolarPoint
      (cappingStretch (unitOf x.val.down) ‖x.val.down‖) (unitOf x.val.down) -
        ((-(3 / 2) : ℝ) : ℂ)))
    ‖cappingPolarPoint
      (cappingStretch (unitOf x.val.down) ‖x.val.down‖) (unitOf x.val.down) -
        ((-(3 / 2) : ℝ) : ℂ)‖ •
    (unitOf (cappingPolarPoint
      (cappingStretch (unitOf x.val.down) ‖x.val.down‖) (unitOf x.val.down) -
        ((-(3 / 2) : ℝ) : ℂ)) : ℂ) = x.val.down
  unfold cappingPolarPoint
  rw [add_sub_cancel_left, unitOf_smul hp, norm_smul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg hp.le, cappingUnstretch_stretch, norm_smul_unitOf]

theorem cappingAnnulusForward_inverse (y : cappingBaseSet.{u}) :
    cappingAnnulusForward (cappingAnnulusInverse y) = y := by
  have hy := (ConeFilling.filledFunction_nonpos_iff y.val.down).mp y.property
  have he : cappingPolarPoint ‖y.val.down - ((-(3 / 2) : ℝ) : ℂ)‖
      (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ))) = y.val.down := by
    rw [cappingPolarPoint, norm_smul_unitOf]
    ring
  have hh : ConeFilling.filledFunction y.val.down ≤ 0 := y.property
  have hr := (cappingPolarPoint_mem_iff _ hy.2 _).mp (he.symm ▸ hh)
  have hp : 0 < cappingUnstretch
      (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ)))
      ‖y.val.down - ((-(3 / 2) : ℝ) : ℂ)‖ := by
    linarith [(cappingUnstretch_bounds _ _ ⟨hy.2, hr⟩).1]
  apply Subtype.ext
  apply ULift.ext
  change cappingPolarPoint
    (cappingStretch
      (unitOf (cappingUnstretch
        (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ)))
        ‖y.val.down - ((-(3 / 2) : ℝ) : ℂ)‖ •
          (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ)) : ℂ)))
      ‖cappingUnstretch (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ)))
        ‖y.val.down - ((-(3 / 2) : ℝ) : ℂ)‖ •
          (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ)) : ℂ)‖)
    (unitOf (cappingUnstretch (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ)))
      ‖y.val.down - ((-(3 / 2) : ℝ) : ℂ)‖ •
        (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ)) : ℂ))) = y.val.down
  rw [unitOf_smul hp, norm_smul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg hp.le, cappingStretch_unstretch]
  exact he

theorem cappingAnnulusForward_smooth :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ cappingAnnulusForward.{u} := by
  apply (cappingBaseAtlas.contMDiff_iff_subtype_val _).mpr
  intro x
  have hx : 1 / 2 ≤ ‖x.val.down‖ :=
    ((mem_planarModel_two x.val.down).mp
      ((mem_planarSet_iff (Or.inl rfl) x.val).mp x.property)).2
  have hne : x.val.down ≠ 0 := by
    intro he
    rw [he, norm_zero] at hx
    norm_num at hx
  have hd := (contMDiff_planarSet_down 2).contMDiffAt (x := x)
  have hu := (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp x hd
  have hn := (contDiffAt_norm ℝ hne).contMDiffAt.comp x hd
  have hR := cappingOuterRadius_smooth.contMDiffAt.comp x hu
  have hs : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
      (fun z : planarSet.{u} 2 => cappingStretch (unitOf z.val.down) ‖z.val.down‖) x :=
    contMDiffAt_const.add
      (((hn.sub contMDiffAt_const).mul (hR.sub contMDiffAt_const)).div_const (5 / 2))
  exact contMDiff_planeLift_up.contMDiffAt.comp x
    (contMDiffAt_const.add (hs.smul (contMDiff_circle_coe.contMDiffAt.comp x hu)))

theorem cappingAnnulusInverse_smooth :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ cappingAnnulusInverse.{u} := by
  apply ((planarAtlas 2).contMDiff_iff_subtype_val _).mpr
  intro y
  have hy := (ConeFilling.filledFunction_nonpos_iff y.val.down).mp y.property
  have hne : y.val.down - ((-(3 / 2) : ℝ) : ℂ) ≠ 0 := by
    intro he
    rw [he, norm_zero] at hy
    norm_num at hy
  have hd : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞
      (fun z : cappingBaseSet.{u} => z.val.down - ((-(3 / 2) : ℝ) : ℂ)) y :=
    (contMDiff_planeLift_down.comp cappingBaseAtlas.contMDiff_subtype_val).contMDiffAt.sub
      contMDiffAt_const
  have hu := (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp y hd
  have hn := (contDiffAt_norm ℝ hne).contMDiffAt.comp y hd
  have hR := cappingOuterRadius_smooth.contMDiffAt.comp y hu
  have hs : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
      (fun z : cappingBaseSet.{u} => cappingUnstretch
        (unitOf (z.val.down - ((-(3 / 2) : ℝ) : ℂ)))
        ‖z.val.down - ((-(3 / 2) : ℝ) : ℂ)‖) y :=
    contMDiffAt_const.add (((hn.sub contMDiffAt_const).mul contMDiffAt_const).div₀
      (hR.sub contMDiffAt_const) (ne_of_gt (by
        linarith [cappingOuterRadius_gt_half
          (unitOf (y.val.down - ((-(3 / 2) : ℝ) : ℂ)))])))
  exact contMDiff_planeLift_up.contMDiffAt.comp y
    (hs.smul (contMDiff_circle_coe.contMDiffAt.comp y hu))

def cappingAnnulusDiffeomorph :
    planarSet.{u} 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ cappingBaseSet.{u} where
  toFun := cappingAnnulusForward
  invFun := cappingAnnulusInverse
  left_inv := cappingAnnulusInverse_forward
  right_inv := cappingAnnulusForward_inverse
  contMDiff_toFun := cappingAnnulusForward_smooth
  contMDiff_invFun := cappingAnnulusInverse_smooth

def sectionCappingAnnulusProductDiffeomorph (q : ℤ) :
    (planarSet.{u} 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯
      (Merge.sectionFilling q).filledSet.{u} :=
  (cappingAnnulusDiffeomorph.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans
    (sectionCappingDiffeomorph q)

theorem cappingAnnulusForward_inner (t : Circle) :
    (cappingAnnulusForward
      (planarCollar.{u} 2 (Or.inl rfl) 1 (t, halfZero))).val.down =
        planarCircleMap 3 2 t := by
  change cappingPolarPoint
    (cappingStretch (unitOf
      (planarCollar.{u} 2 (Or.inl rfl) 1 (t, halfZero)).val.down)
      ‖(planarCollar.{u} 2 (Or.inl rfl) 1 (t, halfZero)).val.down‖)
    (unitOf (planarCollar.{u} 2 (Or.inl rfl) 1 (t, halfZero)).val.down) = _
  rw [planarCollar_zero_val]
  have he : planarCircleMap 2 1 t = (1 / 2 : ℝ) • ((t⁻¹ : Circle) : ℂ) := by
    rw [Circle.coe_inv_eq_conj]
    simp [planarCircleMap, planarCenter, planarRadius, Complex.real_smul]
  rw [he, unitOf_smul (by norm_num), norm_smul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simp only [cappingStretch, sub_self, zero_mul, zero_div, add_zero, cappingPolarPoint]
  rw [Circle.coe_inv_eq_conj]
  simp [planarCircleMap, planarCenter, planarRadius, Complex.real_smul]

theorem cappingAnnulusForward_outer (t : Circle) :
    (cappingAnnulusForward
      (planarCollar.{u} 2 (Or.inl rfl) 0 (t, halfZero))).val.down =
        cappingPolarPoint (cappingOuterRadius t) t := by
  change cappingPolarPoint
    (cappingStretch (unitOf
      (planarCollar.{u} 2 (Or.inl rfl) 0 (t, halfZero)).val.down)
      ‖(planarCollar.{u} 2 (Or.inl rfl) 0 (t, halfZero)).val.down‖)
    (unitOf (planarCollar.{u} 2 (Or.inl rfl) 0 (t, halfZero)).val.down) = _
  rw [planarCollar_zero_val]
  have he : planarCircleMap 2 0 t = (3 : ℝ) • (t : ℂ) := by
    simp [planarCircleMap, planarCenter, planarRadius, Complex.real_smul]
  rw [he, unitOf_smul (by norm_num), norm_smul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  unfold cappingStretch
  ring

theorem cappingHostPhase_outer (B : PlanarBase.{u} 3) (q : ℤ) (t : Circle) :
    unitOf (B.embedding (B.collar 0 (t, halfZero)) - (3 / 2 : ℂ)) ^ q =
      unitOf ((3 : ℂ) * t - (3 / 2 : ℂ)) ^ q := by
  rw [B.embedding_collar]
  simp [planarCircleMap, planarCenter, planarRadius]

theorem cappingHostPhase_other (B : PlanarBase.{u} 3) (q : ℤ) (t : Circle) :
    unitOf (B.embedding (B.collar 2 (t, halfZero)) - (3 / 2 : ℂ)) ^ q =
      unitOf ((-3 : ℂ) + (1 / 2 : ℂ) * starRingEnd ℂ t) ^ q := by
  rw [B.embedding_collar]
  simp only [planarCircleMap, planarCenter, planarRadius, Fin.val_two,
    Nat.reduceEqDiff, ite_false, ite_true]
  congr 3
  push_cast
  ring

theorem sectionCappingDiffeomorph_retainedCollar (q : ℤ) (i : Fin 2)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    ((sectionCappingDiffeomorph.{u} q).symm
      ((Merge.sectionFilling q).externalCollar.{u} i p)).1.val.down =
        (productCollar.{u} 3 (Or.inr rfl) (ConeFilling.externalPort i) p).val.1.down ∧
    ((sectionCappingDiffeomorph.{u} q).symm
      ((Merge.sectionFilling q).externalCollar.{u} i p)).2 =
        unitOf ((productCollar.{u} 3 (Or.inr rfl) (ConeFilling.externalPort i) p).val.1.down -
          ((3 / 2 : ℝ) : ℂ)) ^ q * p.1.2 := by
  have hval := (Merge.sectionFilling q).externalCollar_apply_val.{u} i hp
  constructor
  · change ((3 / 2 : ℝ) : ℂ) +
      ((Merge.sectionFilling q).externalCollar i p).val.1.down / 6 = _
    rw [← Merge.conePoint_sectionFilling, hval]
    exact (Merge.sectionFilling q).conePoint_coneLift _
      ((Merge.sectionFilling q).mem_outerAmbient_source_of.{u}
        (lt_trans (by norm_num) (ConeFilling.productCollar_far.{u} i hp))).1
  · change ((Merge.sectionFilling q).externalCollar i p).val.2 = _
    have hs := congrArg Prod.snd hval
    rw [Merge.coneLift_snd_sectionFilling] at hs
    have hp2 : (productCollar.{u} 3 (Or.inr rfl)
        (ConeFilling.externalPort i) p).val.2 = p.1.2 := rfl
    rw [hp2] at hs
    exact hs

theorem exists_sectionCapping_annulusProduct (q : ℤ) :
    ∃ B : PlanarBase.{u} 2,
      Nonempty ((B.surface.Carrier × Circle) ≃ₘ⟮
        (SurfaceModel.model B.surface.kind).prod (𝓡 1), 𝓡∂ 3⟯
          (Merge.sectionFilling q).filledSet.{u}) :=
  ⟨annulusPlanarBase, ⟨sectionCappingAnnulusProductDiffeomorph q⟩⟩

def cappingOuterPhasePath (q : ℤ) : C(unitInterval × Circle, Circle) where
  toFun p := unitOf ((3 : ℝ) • (p.2 : ℂ) - ((p.1.val * (3 / 2) : ℝ) : ℂ)) ^ q
  continuous_toFun := by
    have hv : Continuous (fun p : unitInterval × Circle =>
        (3 : ℝ) • (p.2 : ℂ) - ((p.1.val * (3 / 2) : ℝ) : ℂ)) :=
      ((continuous_const : Continuous (fun p : unitInterval × Circle => (3 : ℝ))).smul
        (contMDiff_circle_coe.continuous.comp continuous_snd)).sub
        (Complex.continuous_ofReal.comp
          ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
    have hne (p : unitInterval × Circle) :
        (3 : ℝ) • (p.2 : ℂ) - ((p.1.val * (3 / 2) : ℝ) : ℂ) ≠ 0 := by
      have hp : 0 ≤ p.1.val * (3 / 2) :=
        mul_nonneg p.1.property.1 (by norm_num)
      intro he
      have hh := congrArg norm (sub_eq_zero.mp he)
      rw [norm_smul, Circle.norm_coe, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hp] at hh
      norm_num at hh
      linarith [p.1.property.2]
    exact (contMDiff_circle_zpow q).continuous.comp
      (contMDiffOn_unitOf.continuousOn.comp_continuous hv hne)

theorem cappingOuterPhasePath_zero (q : ℤ) (t : Circle) :
    cappingOuterPhasePath q (0, t) = t ^ q := by
  change unitOf ((3 : ℝ) • (t : ℂ) - ((0 * (3 / 2) : ℝ) : ℂ)) ^ q = t ^ q
  rw [zero_mul, Complex.ofReal_zero, sub_zero, unitOf_smul (by norm_num)]

theorem cappingOuterPhasePath_one (q : ℤ) (t : Circle) :
    cappingOuterPhasePath q (1, t) =
      unitOf ((3 : ℂ) * t - (3 / 2 : ℂ)) ^ q := by
  change unitOf ((3 : ℝ) • (t : ℂ) - ((1 * (3 / 2) : ℝ) : ℂ)) ^ q = _
  rw [one_mul, Complex.real_smul]
  norm_num

def cappingOtherPhasePath (q : ℤ) : C(unitInterval × Circle, Circle) where
  toFun p := unitOf ((-3 : ℂ) + (p.1.val / 2) • starRingEnd ℂ (p.2 : ℂ)) ^ q
  continuous_toFun := by
    have hv : Continuous (fun p : unitInterval × Circle =>
        (-3 : ℂ) + (p.1.val / 2) • starRingEnd ℂ (p.2 : ℂ)) :=
      continuous_const.add
        (((continuous_subtype_val.comp continuous_fst).div_const 2).smul
          (Complex.continuous_conj.comp
            (contMDiff_circle_coe.continuous.comp continuous_snd)))
    have hne (p : unitInterval × Circle) :
        (-3 : ℂ) + (p.1.val / 2) • starRingEnd ℂ (p.2 : ℂ) ≠ 0 := by
      have hp : 0 ≤ p.1.val / 2 := div_nonneg p.1.property.1 (by norm_num)
      intro he
      have he' : (p.1.val / 2) • starRingEnd ℂ (p.2 : ℂ) = 3 := by
        linear_combination he
      have hh := congrArg norm he'
      rw [norm_smul, Complex.norm_conj, Circle.norm_coe, mul_one,
        Real.norm_of_nonneg hp] at hh
      norm_num at hh
      linarith [p.1.property.2]
    exact (contMDiff_circle_zpow q).continuous.comp
      (contMDiffOn_unitOf.continuousOn.comp_continuous hv hne)

theorem cappingOtherPhasePath_zero (q : ℤ) (t : Circle) :
    cappingOtherPhasePath q (0, t) = unitOf (-3 : ℂ) ^ q := by
  change unitOf ((-3 : ℂ) + (0 / 2 : ℝ) • starRingEnd ℂ (t : ℂ)) ^ q = _
  rw [zero_div, zero_smul, add_zero]

theorem cappingOtherPhasePath_one (q : ℤ) (t : Circle) :
    cappingOtherPhasePath q (1, t) =
      unitOf ((-3 : ℂ) + (1 / 2 : ℂ) * starRingEnd ℂ t) ^ q := by
  change unitOf ((-3 : ℂ) + (1 / 2 : ℝ) • starRingEnd ℂ (t : ℂ)) ^ q = _
  rw [Complex.real_smul]
  norm_num

theorem cappingPants_neg_mem (z : ℂ) (hz : z ∈ planarModel 3) :
    -z ∈ planarModel 3 := by
  rw [mem_planarModel_three] at hz ⊢
  have he1 : -z - ((3 / 2 : ℝ) : ℂ) = -(z - ((-(3 / 2) : ℝ) : ℂ)) := by
    push_cast
    ring
  have he2 : -z - ((-(3 / 2) : ℝ) : ℂ) = -(z - ((3 / 2 : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [norm_neg, he1, he2, norm_neg, norm_neg]
  exact ⟨hz.1, hz.2.2, hz.2.1⟩

def cappingPantsNeg (x : planarSet.{u} 3) : planarSet.{u} 3 :=
  ⟨ULift.up (-x.val.down), (mem_planarSet_iff (Or.inr rfl) _).mpr
    (cappingPants_neg_mem _ ((mem_planarSet_iff (Or.inr rfl) x.val).mp x.property))⟩

theorem cappingPantsNeg_smooth : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ cappingPantsNeg.{u} := by
  apply ((planarAtlas 3).contMDiff_iff_subtype_val _).mpr
  exact contMDiff_planeLift_up.comp ((contDiff_id.neg.contMDiff).comp
    (contMDiff_planarSet_down 3))

def cappingPantsNegDiffeomorph : planarSet.{u} 3 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ planarSet.{u} 3 where
  toFun := cappingPantsNeg
  invFun := cappingPantsNeg
  left_inv x := by
    apply Subtype.ext
    apply ULift.ext
    exact neg_neg x.val.down
  right_inv x := by
    apply Subtype.ext
    apply ULift.ext
    exact neg_neg x.val.down
  contMDiff_toFun := cappingPantsNeg_smooth
  contMDiff_invFun := cappingPantsNeg_smooth

def cappingCircleNeg (t : Circle) : Circle := unitOf (-(t : ℂ))

theorem cappingCircleNeg_coe (t : Circle) :
    (cappingCircleNeg t : ℂ) = -(t : ℂ) := by
  have he := norm_smul_unitOf (-(t : ℂ))
  rw [norm_neg, Circle.norm_coe, one_smul] at he
  exact he

theorem cappingCircleNeg_smooth : ContMDiff (𝓡 1) (𝓡 1) ∞ cappingCircleNeg := by
  intro t
  have hne : -(t : ℂ) ≠ 0 := neg_ne_zero.mpr (Circle.coe_ne_zero t)
  exact (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp t
    ((contDiff_id.neg.contMDiff.comp contMDiff_circle_coe).contMDiffAt)

def cappingCircleNegDiffeomorph : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toFun := cappingCircleNeg
  invFun := cappingCircleNeg
  left_inv t := by
    apply Circle.ext
    rw [cappingCircleNeg_coe, cappingCircleNeg_coe, neg_neg]
  right_inv t := by
    apply Circle.ext
    rw [cappingCircleNeg_coe, cappingCircleNeg_coe, neg_neg]
  contMDiff_toFun := cappingCircleNeg_smooth
  contMDiff_invFun := cappingCircleNeg_smooth

theorem cappingPantsNeg_boundary_outer (t : Circle) :
    cappingPantsNegDiffeomorph
      (planarCollar.{u} 3 (Or.inr rfl) 0 (t, halfZero)) =
        planarCollar 3 (Or.inr rfl) 0 (cappingCircleNeg t, halfZero) := by
  apply Subtype.ext
  apply ULift.ext
  change -(planarCollar.{u} 3 (Or.inr rfl) 0 (t, halfZero)).val.down = _
  rw [planarCollar_zero_val, planarCollar_zero_val]
  simp [planarCircleMap, planarCenter, planarRadius, cappingCircleNeg_coe]

theorem cappingPantsNeg_boundary_one (t : Circle) :
    cappingPantsNegDiffeomorph
      (planarCollar.{u} 3 (Or.inr rfl) 1 (t, halfZero)) =
        planarCollar 3 (Or.inr rfl) 2 (cappingCircleNeg t, halfZero) := by
  apply Subtype.ext
  apply ULift.ext
  change -(planarCollar.{u} 3 (Or.inr rfl) 1 (t, halfZero)).val.down = _
  rw [planarCollar_zero_val, planarCollar_zero_val]
  simp only [planarCircleMap, planarCenter, planarRadius,
    Fin.val_one, Fin.val_two, Nat.reduceEqDiff, ite_false, ite_true, cappingCircleNeg_coe,
    map_neg]
  push_cast
  ring

theorem cappingPantsNeg_boundary_two (t : Circle) :
    cappingPantsNegDiffeomorph
      (planarCollar.{u} 3 (Or.inr rfl) 2 (t, halfZero)) =
        planarCollar 3 (Or.inr rfl) 1 (cappingCircleNeg t, halfZero) := by
  apply Subtype.ext
  apply ULift.ext
  change -(planarCollar.{u} 3 (Or.inr rfl) 2 (t, halfZero)).val.down = _
  rw [planarCollar_zero_val, planarCollar_zero_val]
  simp only [planarCircleMap, planarCenter, planarRadius,
    Fin.val_one, Fin.val_two, Nat.reduceEqDiff, ite_false, ite_true, cappingCircleNeg_coe,
    map_neg]
  push_cast
  ring

theorem cappingPantsNeg_collar_outer (p : Circle × EuclideanHalfSpace 1) :
    cappingPantsNegDiffeomorph (planarCollar.{u} 3 (Or.inr rfl) 0 p) =
      planarCollar 3 (Or.inr rfl) 0 (cappingCircleNeg p.1, p.2) := by
  apply Subtype.ext
  apply ULift.ext
  change -(planarCollarFormula 3 0 ((p.1 : ℂ), min (p.2.val 0) 1)) =
    planarCollarFormula 3 0 ((cappingCircleNeg p.1 : ℂ), min (p.2.val 0) 1)
  simp only [planarCollarFormula, planarCenter, planarRadius, planarSign, planarTwist,
    Fin.val_zero, Nat.reduceEqDiff, ite_false, ite_true,
    cappingCircleNeg_coe, map_neg, Complex.real_smul]
  push_cast
  ring

theorem cappingPantsNeg_collar_one (p : Circle × EuclideanHalfSpace 1) :
    cappingPantsNegDiffeomorph (planarCollar.{u} 3 (Or.inr rfl) 1 p) =
      planarCollar 3 (Or.inr rfl) 2 (cappingCircleNeg p.1, p.2) := by
  apply Subtype.ext
  apply ULift.ext
  change -(planarCollarFormula 3 1 ((p.1 : ℂ), min (p.2.val 0) 1)) =
    planarCollarFormula 3 2 ((cappingCircleNeg p.1 : ℂ), min (p.2.val 0) 1)
  simp only [planarCollarFormula, planarCenter, planarRadius, planarSign, planarTwist,
    Fin.val_one, Fin.val_two, Nat.reduceEqDiff, ite_false, ite_true,
    cappingCircleNeg_coe, map_neg, Complex.real_smul]
  push_cast
  ring

theorem cappingPantsNeg_collar_two (p : Circle × EuclideanHalfSpace 1) :
    cappingPantsNegDiffeomorph (planarCollar.{u} 3 (Or.inr rfl) 2 p) =
      planarCollar 3 (Or.inr rfl) 1 (cappingCircleNeg p.1, p.2) := by
  apply Subtype.ext
  apply ULift.ext
  change -(planarCollarFormula 3 2 ((p.1 : ℂ), min (p.2.val 0) 1)) =
    planarCollarFormula 3 1 ((cappingCircleNeg p.1 : ℂ), min (p.2.val 0) 1)
  simp only [planarCollarFormula, planarCenter, planarRadius, planarSign, planarTwist,
    Fin.val_one, Fin.val_two, Nat.reduceEqDiff, ite_false, ite_true,
    cappingCircleNeg_coe, map_neg, Complex.real_smul]
  push_cast
  ring

def cappingOuterHostMap (x : planarSet.{u} 3) : ℂ :=
  (x.val.down - (3 / 2 : ℂ))⁻¹

theorem cappingOuterHost_denominator (x : planarSet.{u} 3) :
    x.val.down - (3 / 2 : ℂ) ≠ 0 := by
  have hx := (mem_planarModel_three x.val.down).mp
    ((mem_planarSet_iff (Or.inr rfl) x.val).mp x.property)
  intro he
  have hh : ‖x.val.down - (3 / 2 : ℂ)‖ = 0 := by rw [he, norm_zero]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hx
  linarith [hx.2.1]

theorem cappingOuterHostMap_smooth :
    ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ cappingOuterHostMap.{u} := by
  intro x
  have ha : ContDiffAt ℝ ∞ (fun z : ℂ => (z - (3 / 2 : ℂ))⁻¹) x.val.down :=
    ((contDiffAt_id : ContDiffAt ℝ ∞ (id : ℂ → ℂ) x.val.down).sub
      contDiffAt_const).inv (cappingOuterHost_denominator x)
  have ha' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun z : ℂ => (z - (3 / 2 : ℂ))⁻¹) x.val.down := ha.contMDiffAt
  change ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞
    ((fun z : ℂ => (z - (3 / 2 : ℂ))⁻¹) ∘ fun y : planarSet.{u} 3 => y.val.down) x
  exact ha'.comp x (contMDiff_planarSet_down 3).contMDiffAt

theorem cappingOuterHostMap_injective : Function.Injective cappingOuterHostMap.{u} := by
  intro x y h
  have he : x.val.down = y.val.down := by
    exact sub_left_inj.mp (inv_injective h)
  apply Subtype.ext
  exact ULift.ext he

def cappingOuterDiscMap (x : UnitDisc.{u}) : ℂ :=
  x.down.val / (3 - (3 / 2 : ℂ) * x.down.val)

theorem cappingOuterDisc_denominator (x : UnitDisc.{u}) :
    3 - (3 / 2 : ℂ) * x.down.val ≠ 0 := by
  have hx : ‖x.down.val‖ ≤ 1 := by
    have hh := x.down.property
    change ‖x.down.val‖ ^ 2 ≤ 1 at hh
    nlinarith [norm_nonneg x.down.val]
  intro he
  have hh := congrArg norm (sub_eq_zero.mp he)
  rw [norm_mul] at hh
  norm_num at hh
  nlinarith

theorem cappingOuterDiscMap_smooth :
    ContMDiff (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ cappingOuterDiscMap.{u} := by
  intro x
  have hi : ContDiffAt ℂ ∞ (id : ℂ → ℂ) x.down.val := contDiffAt_id
  have hd : ContDiffAt ℂ ∞ (fun z : ℂ => 3 - (3 / 2 : ℂ) * z) x.down.val :=
    contDiffAt_const.sub (contDiffAt_const.mul hi)
  have hc : ContDiffAt ℂ ∞ (fun z : ℂ => z / (3 - (3 / 2 : ℂ) * z)) x.down.val :=
    hi.div hd (cappingOuterDisc_denominator x)
  have ha : ContDiffAt ℝ ∞ (fun z : ℂ => z / (3 - (3 / 2 : ℂ) * z)) x.down.val :=
    hc.restrict_scalars ℝ
  exact ha.contMDiffAt.comp x contMDiff_disc_val.contMDiffAt

theorem cappingOuterDiscMap_injective : Function.Injective cappingOuterDiscMap.{u} := by
  intro x y h
  have he := (div_eq_div_iff (cappingOuterDisc_denominator x)
    (cappingOuterDisc_denominator y)).mp h
  have hev : x.down.val = y.down.val := by
    linear_combination (1 / 3 : ℂ) * he
  apply ULift.ext
  exact Subtype.ext hev

theorem cappingOuter_boundary_identity (t : Circle) :
    (t : ℂ) / (3 - (3 / 2 : ℂ) * t) =
      ((3 : ℝ) • ((t⁻¹ : Circle) : ℂ) - (3 / 2 : ℂ))⁻¹ := by
  rw [Circle.coe_inv, Complex.real_smul]
  norm_num only [Complex.ofReal_ofNat]
  have ht : (t : ℂ) ≠ 0 := Circle.coe_ne_zero t
  have he : (3 : ℂ) * (t : ℂ)⁻¹ - (3 / 2 : ℂ) =
      (3 - (3 / 2 : ℂ) * t) / t := by
    field_simp
  rw [he, inv_div]

end GC.Seifert.ElementaryPresentation

namespace GC.Seifert.ElementaryPresentation

def outerCappingRing : Set ℂ :=
  {w | ‖w‖ ≤ 2 ∧ 2 / 35 ≤ ‖w + (12 / 35 : ℂ)‖}

theorem outerCapping_circleIdentity (d : ℂ) :
    ‖1 + (12 / 35 : ℂ) * d‖ ^ 2 - (2 / 35 : ℝ) ^ 2 * ‖d‖ ^ 2 =
      (4 / 35 : ℝ) * (‖d + 3‖ ^ 2 - (1 / 2 : ℝ) ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.one_re, Complex.one_im]
  norm_num
  ring

theorem outerCapping_inverse_mem (z : ℂ)
    (hp : 1 / 2 ≤ ‖z - (3 / 2 : ℂ)‖)
    (hm : 1 / 2 ≤ ‖z + (3 / 2 : ℂ)‖) :
    (z - (3 / 2 : ℂ))⁻¹ ∈ outerCappingRing := by
  have hd : 0 < ‖z - (3 / 2 : ℂ)‖ := by linarith
  have hne : z - (3 / 2 : ℂ) ≠ 0 := norm_pos_iff.mp hd
  have he : ((z - (3 / 2 : ℂ))⁻¹ + (12 / 35 : ℂ)) * (z - (3 / 2 : ℂ)) =
      1 + (12 / 35 : ℂ) * (z - (3 / 2 : ℂ)) := by
    rw [add_mul, inv_mul_cancel₀ hne]
  have hn := congrArg (fun w : ℂ => ‖w‖ ^ 2) he
  rw [norm_mul, mul_pow] at hn
  have hi := outerCapping_circleIdentity (z - (3 / 2 : ℂ))
  have hs : z - (3 / 2 : ℂ) + 3 = z + (3 / 2 : ℂ) := by ring
  rw [hs] at hi
  have hf : 0 ≤
      (‖(z - (3 / 2 : ℂ))⁻¹ + (12 / 35 : ℂ)‖ ^ 2 - (2 / 35 : ℝ) ^ 2) *
        ‖z - (3 / 2 : ℂ)‖ ^ 2 := by
    have hp' : 0 ≤ (4 / 35 : ℝ) * (‖z + (3 / 2 : ℂ)‖ ^ 2 - (1 / 2 : ℝ) ^ 2) :=
      mul_nonneg (by norm_num) (by nlinarith [norm_nonneg (z + (3 / 2 : ℂ))])
    nlinarith [hi, hn]
  have hf' := nonneg_of_mul_nonneg_left hf (sq_pos_of_pos hd)
  constructor
  · rw [norm_inv, inv_eq_one_div]
    exact (div_le_iff₀ hd).mpr (by linarith)
  · nlinarith [norm_nonneg ((z - (3 / 2 : ℂ))⁻¹ + (12 / 35 : ℂ))]

theorem outerCapping_inverse_mem_iff (z : ℂ) (hne : z - (3 / 2 : ℂ) ≠ 0) :
    (z - (3 / 2 : ℂ))⁻¹ ∈ outerCappingRing ↔
      1 / 2 ≤ ‖z - (3 / 2 : ℂ)‖ ∧ 1 / 2 ≤ ‖z + (3 / 2 : ℂ)‖ := by
  constructor
  · intro hz
    have hd : 0 < ‖z - (3 / 2 : ℂ)‖ := norm_pos_iff.mpr hne
    have he : ((z - (3 / 2 : ℂ))⁻¹ + (12 / 35 : ℂ)) * (z - (3 / 2 : ℂ)) =
        1 + (12 / 35 : ℂ) * (z - (3 / 2 : ℂ)) := by
      rw [add_mul, inv_mul_cancel₀ hne]
    have hn := congrArg (fun w : ℂ => ‖w‖ ^ 2) he
    rw [norm_mul, mul_pow] at hn
    have hi := outerCapping_circleIdentity (z - (3 / 2 : ℂ))
    have hs : z - (3 / 2 : ℂ) + 3 = z + (3 / 2 : ℂ) := by ring
    rw [hs] at hi
    have hprod := mul_nonneg
      (show 0 ≤ ‖(z - (3 / 2 : ℂ))⁻¹ + (12 / 35 : ℂ)‖ ^ 2 - (2 / 35 : ℝ) ^ 2 by
        nlinarith [hz.2]) (sq_nonneg ‖z - (3 / 2 : ℂ)‖)
    constructor
    · have hnorm := hz.1
      rw [norm_inv, inv_eq_one_div] at hnorm
      have hh := (div_le_iff₀ hd).mp hnorm
      linarith
    · nlinarith [hi, hn, hprod, norm_nonneg (z + (3 / 2 : ℂ))]
  · rintro ⟨hp, hm⟩
    exact outerCapping_inverse_mem z hp hm

theorem outerCapping_exterior_holes (z : ℂ) (hz : 3 ≤ ‖z‖) :
    1 / 2 ≤ ‖z - (3 / 2 : ℂ)‖ ∧ 1 / 2 ≤ ‖z + (3 / 2 : ℂ)‖ := by
  have hp := (norm_sub_real_bounds z (3 / 2)).1
  have hm := (norm_sub_real_bounds z (-(3 / 2))).1
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), abs_neg,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg, sub_neg_eq_add] at hp hm
  constructor <;> linarith

theorem outerCapping_disc_mem (x : ℂ) (hx : ‖x‖ ≤ 1) :
    x / (3 - (3 / 2 : ℂ) * x) ∈ outerCappingRing := by
  by_cases he : x = 0
  · subst x
    norm_num [outerCappingRing]
  · have hz : 3 ≤ ‖(3 : ℂ) / x‖ := by
      rw [norm_div]
      norm_num only [Complex.norm_ofNat]
      exact (le_div_iff₀ (norm_pos_iff.mpr he)).mpr (by linarith)
    obtain ⟨hp, hm⟩ := outerCapping_exterior_holes ((3 : ℂ) / x) hz
    have hmem := outerCapping_inverse_mem ((3 : ℂ) / x) hp hm
    have hi : ((3 : ℂ) / x - (3 / 2 : ℂ))⁻¹ = x / (3 - (3 / 2 : ℂ) * x) := by
      have hh : (3 : ℂ) / x - (3 / 2 : ℂ) = (3 - (3 / 2 : ℂ) * x) / x := by
        field_simp
      rw [hh, inv_div]
    exact hi ▸ hmem

theorem outerCappingRing_cover (w : ℂ) (hw : w ∈ outerCappingRing) :
    (∃ z : ℂ, z ∈ planarModel 3 ∧ w = (z - (3 / 2 : ℂ))⁻¹) ∨
      ∃ x : ℂ, ‖x‖ ≤ 1 ∧ w = x / (3 - (3 / 2 : ℂ) * x) := by
  by_cases h0 : w = 0
  · right
    refine ⟨0, by norm_num, ?_⟩
    simp [h0]
  · let z : ℂ := (3 / 2 : ℂ) + w⁻¹
    have hne : z - (3 / 2 : ℂ) ≠ 0 := by
      dsimp [z]
      rw [add_sub_cancel_left]
      exact inv_ne_zero h0
    have he : (z - (3 / 2 : ℂ))⁻¹ = w := by
      dsimp [z]
      rw [add_sub_cancel_left, inv_inv]
    have hz := (outerCapping_inverse_mem_iff z hne).mp (he.symm ▸ hw)
    by_cases hb : ‖z‖ ≤ 3
    · left
      refine ⟨z, ?_, he.symm⟩
      rw [mem_planarModel_three]
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg,
        sub_neg_eq_add]
      exact ⟨hb, hz⟩
    · right
      have hzp : 0 < ‖z‖ := by linarith [not_le.mp hb]
      have hzn : z ≠ 0 := norm_pos_iff.mp hzp
      refine ⟨(3 : ℂ) / z, ?_, ?_⟩
      · rw [norm_div]
        norm_num only [Complex.norm_ofNat]
        exact (div_le_iff₀ hzp).mpr (by linarith [not_le.mp hb])
      · rw [← he]
        field_simp [hzn, hne]

theorem outerCappingRing_mem_iff (w : ℂ) :
    w ∈ outerCappingRing ↔
      (∃ z : ℂ, z ∈ planarModel 3 ∧ w = (z - (3 / 2 : ℂ))⁻¹) ∨
        ∃ x : ℂ, ‖x‖ ≤ 1 ∧ w = x / (3 - (3 / 2 : ℂ) * x) := by
  constructor
  · exact outerCappingRing_cover w
  · intro hw
    rcases hw with ⟨z, hz, rfl⟩ | ⟨x, hx, rfl⟩
    · rw [mem_planarModel_three] at hz
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg,
        sub_neg_eq_add] at hz
      exact outerCapping_inverse_mem z hz.2.1 hz.2.2
    · exact outerCapping_disc_mem x hx

def outerCappingFunction (z : ℂ) : ℝ :=
  sqDist 0 2 z * sqDist (-12 / 35 : ℂ) (2 / 35) z

theorem outerCappingFunction_smooth : ContDiff ℝ ∞ outerCappingFunction :=
  (contDiff_sqDist _ _).mul (contDiff_sqDist _ _)

theorem outerCappingFunction_nonpos_iff (z : ℂ) :
    outerCappingFunction z ≤ 0 ↔ z ∈ outerCappingRing := by
  have hb := norm_sub_real_bounds z (-12 / 35)
  norm_num at hb
  have hz := norm_nonneg z
  have hd := norm_nonneg (z + (12 / 35 : ℂ))
  change outerCappingFunction z ≤ 0 ↔ ‖z‖ ≤ 2 ∧ 2 / 35 ≤ ‖z + (12 / 35 : ℂ)‖
  unfold outerCappingFunction sqDist
  rw [sub_zero, neg_div, sub_neg_eq_add]
  constructor
  · intro h
    by_contra hn
    rw [not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · have hp : 0 < (‖z‖ ^ 2 - 2 ^ 2) *
          (‖z + (12 / 35 : ℂ)‖ ^ 2 - (2 / 35 : ℝ) ^ 2) :=
        mul_pos (by nlinarith) (by nlinarith [hb.1])
      linarith
    · have hp : 0 < (‖z‖ ^ 2 - 2 ^ 2) *
          (‖z + (12 / 35 : ℂ)‖ ^ 2 - (2 / 35 : ℝ) ^ 2) :=
        mul_pos_of_neg_of_neg (by nlinarith [hb.2]) (by nlinarith)
      linarith
  · rintro ⟨h1, h2⟩
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (by nlinarith)

theorem outerCappingFunction_regular {z : ℂ} (hz : outerCappingFunction z = 0) :
    fderiv ℝ outerCappingFunction z ≠ 0 := by
  have hb := norm_sub_real_bounds z (-12 / 35)
  norm_num at hb
  have hd (c : ℂ) (r : ℝ) : DifferentiableAt ℝ (sqDist c r) z :=
    (contDiff_sqDist c r).differentiable (by simp) z
  unfold outerCappingFunction at hz ⊢
  rcases mul_eq_zero.mp hz with h | h
  · have hn := norm_sub_eq_of_sqDist_eq_zero (by norm_num : (0 : ℝ) ≤ 2) h
    rw [sub_zero] at hn
    refine fderiv_sqDist_mul_ne_zero (hd _ _) h ?_ (by norm_num)
    simp only [sqDist, neg_div, sub_neg_eq_add]
    nlinarith [hb.1, norm_nonneg (z + (12 / 35 : ℂ))]
  · have hn := norm_sub_eq_of_sqDist_eq_zero
      (by norm_num : (0 : ℝ) ≤ 2 / 35) h
    rw [neg_div, sub_neg_eq_add] at hn
    rw [show (fun w => sqDist 0 2 w * sqDist (-12 / 35 : ℂ) (2 / 35) w) =
      fun w => sqDist (-12 / 35 : ℂ) (2 / 35) w * sqDist 0 2 w from
        funext fun w => mul_comm _ _]
    refine fderiv_sqDist_mul_ne_zero (hd _ _) h ?_ (by norm_num)
    simp only [sqDist, sub_zero]
    nlinarith [hb.2, norm_nonneg z]

def outerCappingBaseSet : Set PlaneLift.{u} :=
  {z | outerCappingFunction z.down ≤ 0}

theorem outerCappingBaseFunction_smooth :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
      (fun z : PlaneLift.{u} => outerCappingFunction z.down) :=
  outerCappingFunction_smooth.contMDiff.comp contMDiff_planeLift_down

theorem outerCappingBaseFunction_regular (z : PlaneLift.{u})
    (hz : outerCappingFunction z.down = 0) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ)
      (fun w : PlaneLift.{u} => outerCappingFunction w.down) z ≠ 0 := by
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ))
    (s := ULift.up) (y := z.down)
    (outerCappingBaseFunction_smooth.mdifferentiableAt (by simp))
    (contMDiff_planeLift_up.mdifferentiableAt (by simp)) ?_
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) outerCappingFunction z.down ≠ 0
  rw [mfderiv_eq_fderiv]
  exact outerCappingFunction_regular hz

def outerCappingBaseAtlas : SmoothBoundaryAtlas 𝓘(ℝ, ℂ) 2 outerCappingBaseSet.{u} :=
  SmoothBoundaryAtlas.regularSublevel 𝓘(ℝ, ℂ) (n := 1) Complex.finrank_real_complex
    outerCappingBaseFunction_smooth 0 outerCappingBaseFunction_regular

instance : ChartedSpace (EuclideanHalfSpace 2) outerCappingBaseSet.{u} :=
  outerCappingBaseAtlas.toChartedSpace

instance : IsManifold (𝓡∂ 2) ∞ outerCappingBaseSet.{u} := outerCappingBaseAtlas.isManifold

def outerCappingHost (x : planarSet.{u} 3) : outerCappingBaseSet.{u} :=
  ⟨ULift.up (cappingOuterHostMap x), by
    have hx := (mem_planarModel_three x.val.down).mp
      ((mem_planarSet_iff (Or.inr rfl) x.val).mp x.property)
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg,
      sub_neg_eq_add] at hx
    exact (outerCappingFunction_nonpos_iff _).mpr
      (outerCapping_inverse_mem x.val.down hx.2.1 hx.2.2)⟩

def outerCappingDisc (x : UnitDisc.{u}) : outerCappingBaseSet.{u} :=
  ⟨ULift.up (cappingOuterDiscMap x), by
    have hx : ‖x.down.val‖ ≤ 1 := by
      have hh := x.down.property
      change ‖x.down.val‖ ^ 2 ≤ 1 at hh
      nlinarith [norm_nonneg x.down.val]
    exact (outerCappingFunction_nonpos_iff _).mpr
      (outerCapping_disc_mem x.down.val hx)⟩

theorem outerCappingHost_smooth :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ outerCappingHost.{u} :=
  (outerCappingBaseAtlas.contMDiff_iff_subtype_val _).mpr
    (contMDiff_planeLift_up.comp cappingOuterHostMap_smooth)

theorem outerCappingDisc_smooth :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ outerCappingDisc.{u} :=
  (outerCappingBaseAtlas.contMDiff_iff_subtype_val _).mpr
    (contMDiff_planeLift_up.comp cappingOuterDiscMap_smooth)

theorem outerCappingHost_injective : Function.Injective outerCappingHost.{u} := by
  intro x y h
  exact cappingOuterHostMap_injective (congrArg (fun z => z.val.down) h)

theorem outerCappingDisc_injective : Function.Injective outerCappingDisc.{u} := by
  intro x y h
  exact cappingOuterDiscMap_injective (congrArg (fun z => z.val.down) h)

def outerCappingDiscBoundary (t : Circle) : UnitDisc.{u} :=
  ULift.up ⟨(t : ℂ), by change ‖(t : ℂ)‖ ^ 2 ≤ 1; simp⟩

theorem outerCapping_boundary (t : Circle) :
    outerCappingDisc (outerCappingDiscBoundary.{u} t) =
      outerCappingHost (planarCollar 3 (Or.inr rfl) 0 ((t⁻¹ : Circle), halfZero)) := by
  apply Subtype.ext
  apply ULift.ext
  change (t : ℂ) / (3 - (3 / 2 : ℂ) * t) =
    ((planarCollar.{u} 3 (Or.inr rfl) 0 ((t⁻¹ : Circle), halfZero)).val.down -
      (3 / 2 : ℂ))⁻¹
  rw [planarCollar_zero_val]
  have he : planarCircleMap 3 0 (t⁻¹ : Circle) = (3 : ℝ) • ((t⁻¹ : Circle) : ℂ) := by
    simp [planarCircleMap, planarCenter, planarRadius, Complex.real_smul]
  rw [he]
  exact cappingOuter_boundary_identity t

theorem outerCapping_cover (y : outerCappingBaseSet.{u}) :
    (∃ x : planarSet.{u} 3, outerCappingHost x = y) ∨
      ∃ x : UnitDisc.{u}, outerCappingDisc x = y := by
  have hy := (outerCappingFunction_nonpos_iff y.val.down).mp y.property
  rcases outerCappingRing_cover y.val.down hy with ⟨z, hz, he⟩ | ⟨z, hz, he⟩
  · left
    refine ⟨⟨ULift.up z, (mem_planarSet_iff (Or.inr rfl) _).mpr hz⟩, ?_⟩
    apply Subtype.ext
    exact ULift.ext he.symm
  · right
    refine ⟨ULift.up ⟨z, ?_⟩, ?_⟩
    · change ‖z‖ ^ 2 ≤ 1
      nlinarith [norm_nonneg z]
    · apply Subtype.ext
      exact ULift.ext he.symm

end GC.Seifert.ElementaryPresentation

namespace GC.Seifert.ElementaryPresentation

theorem outerCapping_overlap (z x : ℂ) (hz : z ∈ planarModel 3) (hx : ‖x‖ ≤ 1)
    (he : (z - (3 / 2 : ℂ))⁻¹ = x / (3 - (3 / 2 : ℂ) * x)) :
    ‖x‖ = 1 ∧ ‖z‖ = 3 ∧ (3 : ℂ) = x * z := by
  rw [mem_planarModel_three] at hz
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg,
    sub_neg_eq_add] at hz
  have hd : z - (3 / 2 : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    norm_num at hz
  have hc : 3 - (3 / 2 : ℂ) * x ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.mp h)
    rw [norm_mul] at hn
    norm_num at hn
    nlinarith
  have hh := (eq_div_iff hc).mp he
  have hmul := congrArg (fun y : ℂ => y * (z - (3 / 2 : ℂ))) hh
  have hmul' : (3 : ℂ) = x * z := by
    rw [mul_right_comm, inv_mul_cancel₀ hd, one_mul] at hmul
    linear_combination hmul
  have hn := congrArg norm hmul'
  rw [norm_mul] at hn
  norm_num at hn
  have hx0 := norm_nonneg x
  have hz0 := norm_nonneg z
  have hx1 : ‖x‖ = 1 := by nlinarith [hz.1]
  refine ⟨hx1, ?_, hmul'⟩
  nlinarith

end GC.Seifert.ElementaryPresentation

namespace GC.Seifert.ElementaryPresentation

theorem outerCappingFunction_nonpos_iff_radius (z : ℂ) :
    outerCappingFunction z ≤ 0 ↔
      ‖z‖ ≤ 2 ∧ 2 / 35 ≤ ‖z - ((-(12 / 35) : ℝ) : ℂ)‖ := by
  rw [outerCappingFunction_nonpos_iff]
  simp only [outerCappingRing, Set.mem_ofPred_eq, Complex.ofReal_neg, sub_neg_eq_add,
    Complex.ofReal_div, Complex.ofReal_ofNat]

def outerCappingOuterRadius (t : Circle) : ℝ :=
  (12 / 35) * (t : ℂ).re + Real.sqrt ((144 / 1225) * (t : ℂ).re ^ 2 + 4756 / 1225)

theorem outerCappingOuterRadius_eq (t : Circle) :
    outerCappingOuterRadius t ^ 2 -
      (24 / 35) * (t : ℂ).re * outerCappingOuterRadius t = 4756 / 1225 := by
  have hs := Real.sq_sqrt (by positivity :
    0 ≤ (144 / 1225) * (t : ℂ).re ^ 2 + 4756 / 1225)
  dsimp [outerCappingOuterRadius]
  nlinarith

theorem outerCappingOuterRadius_gt_inner (t : Circle) :
    2 / 35 < outerCappingOuterRadius t := by
  have hr : -1 ≤ (t : ℂ).re := by
    have he := Complex.abs_re_le_norm (t : ℂ)
    rw [Circle.norm_coe] at he
    exact (abs_le.mp he).1
  have hs := Real.sq_sqrt (by positivity :
    0 ≤ (144 / 1225) * (t : ℂ).re ^ 2 + 4756 / 1225)
  have hsp := Real.sqrt_nonneg ((144 / 1225) * (t : ℂ).re ^ 2 + 4756 / 1225)
  dsimp [outerCappingOuterRadius]
  nlinarith [sq_nonneg ((t : ℂ).re)]

def outerCappingPolarPoint (r : ℝ) (t : Circle) : ℂ :=
  ((-(12 / 35) : ℝ) : ℂ) + r • (t : ℂ)

theorem outerCappingPolarPoint_radius (r : ℝ) (hr : 0 ≤ r) (t : Circle) :
    ‖outerCappingPolarPoint r t - ((-(12 / 35) : ℝ) : ℂ)‖ = r := by
  rw [outerCappingPolarPoint, add_sub_cancel_left, norm_smul, Circle.norm_coe,
    mul_one, Real.norm_of_nonneg hr]

theorem outerCappingPolarPoint_norm_sq (r : ℝ) (t : Circle) :
    ‖outerCappingPolarPoint r t‖ ^ 2 = r ^ 2 - (24 / 35) * (t : ℂ).re * r + 144 / 1225 := by
  have ht : (t : ℂ).re ^ 2 + (t : ℂ).im ^ 2 = 1 := by
    calc
      (t : ℂ).re ^ 2 + (t : ℂ).im ^ 2 = ‖(t : ℂ)‖ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      _ = 1 := by rw [Circle.norm_coe]; norm_num
  simp only [Complex.sq_norm, Complex.normSq_apply, outerCappingPolarPoint,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul, zero_add]
  nlinarith [congrArg (fun a : ℝ => r ^ 2 * a) ht]

theorem outerCappingPolarPoint_outer (t : Circle) :
    ‖outerCappingPolarPoint (outerCappingOuterRadius t) t‖ = 2 := by
  have he := outerCappingOuterRadius_eq t
  have hn := outerCappingPolarPoint_norm_sq (outerCappingOuterRadius t) t
  have hp := norm_nonneg (outerCappingPolarPoint (outerCappingOuterRadius t) t)
  nlinarith

theorem outerCappingPolarPoint_mem_iff (r : ℝ) (hr : 2 / 35 ≤ r) (t : Circle) :
    outerCappingFunction (outerCappingPolarPoint r t) ≤ 0 ↔
      r ≤ outerCappingOuterRadius t := by
  rw [outerCappingFunction_nonpos_iff_radius,
    outerCappingPolarPoint_radius r (by linarith) t, and_iff_left hr]
  have he := outerCappingOuterRadius_eq t
  have hn := outerCappingPolarPoint_norm_sq r t
  have hR := outerCappingOuterRadius_gt_inner t
  have hsq : 0 < outerCappingOuterRadius t + r - (24 / 35) * (t : ℂ).re := by
    have hs := Real.sq_sqrt (by positivity :
      0 ≤ (144 / 1225) * (t : ℂ).re ^ 2 + 4756 / 1225)
    have hp := Real.sqrt_nonneg ((144 / 1225) * (t : ℂ).re ^ 2 + 4756 / 1225)
    dsimp [outerCappingOuterRadius]
    nlinarith
  have hf : r ^ 2 - (24 / 35) * (t : ℂ).re * r - 4756 / 1225 =
      (r - outerCappingOuterRadius t) *
        (outerCappingOuterRadius t + r - (24 / 35) * (t : ℂ).re) := by
    nlinarith [he]
  constructor
  · intro h
    have hprod : (r - outerCappingOuterRadius t) *
        (outerCappingOuterRadius t + r - (24 / 35) * (t : ℂ).re) ≤ 0 := by
      rw [← hf]
      nlinarith [norm_nonneg (outerCappingPolarPoint r t)]
    exact sub_nonpos.mp ((mul_nonpos_iff.mp hprod).resolve_left
      (by intro h; exact (not_le.mpr hsq) h.2)).1
  · intro h
    have hprod := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hsq.le
    rw [← hf] at hprod
    nlinarith [norm_nonneg (outerCappingPolarPoint r t)]

theorem outerCappingOuterRadius_smooth : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ) ∞ outerCappingOuterRadius := by
  have h : ContDiff ℝ ∞ (fun z : ℂ =>
      (12 / 35) * z.re + Real.sqrt ((144 / 1225) * z.re ^ 2 + 4756 / 1225)) :=
    (contDiff_const.mul Complex.reCLM.contDiff).add
      (((contDiff_const.mul (Complex.reCLM.contDiff.pow 2)).add contDiff_const).sqrt
        (fun z => by positivity))
  exact h.contMDiff.comp contMDiff_circle_coe

def outerCappingStretch (t : Circle) (s : ℝ) : ℝ :=
  2 / 35 + (s - 1 / 2) * (outerCappingOuterRadius t - 2 / 35) / (5 / 2)

def outerCappingUnstretch (t : Circle) (r : ℝ) : ℝ :=
  1 / 2 + (r - 2 / 35) * (5 / 2) / (outerCappingOuterRadius t - 2 / 35)

theorem outerCappingUnstretch_stretch (t : Circle) (s : ℝ) :
    outerCappingUnstretch t (outerCappingStretch t s) = s := by
  have hn : 35 * outerCappingOuterRadius t - 2 ≠ 0 := by
    linarith [outerCappingOuterRadius_gt_inner t]
  unfold outerCappingStretch outerCappingUnstretch
  field_simp [hn]
  ring

theorem outerCappingStretch_unstretch (t : Circle) (r : ℝ) :
    outerCappingStretch t (outerCappingUnstretch t r) = r := by
  have hn : 35 * outerCappingOuterRadius t - 2 ≠ 0 := by
    linarith [outerCappingOuterRadius_gt_inner t]
  unfold outerCappingStretch outerCappingUnstretch
  field_simp [hn]
  ring

theorem outerCappingStretch_bounds (t : Circle) (s : ℝ) (hs : 1 / 2 ≤ s ∧ s ≤ 3) :
    2 / 35 ≤ outerCappingStretch t s ∧ outerCappingStretch t s ≤ outerCappingOuterRadius t := by
  have hp := outerCappingOuterRadius_gt_inner t
  have h1 := mul_nonneg (sub_nonneg.mpr hs.1) (sub_nonneg.mpr hp.le)
  have h2 := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hp.le)
  dsimp [outerCappingStretch]
  constructor <;> nlinarith

theorem outerCappingUnstretch_bounds (t : Circle) (r : ℝ)
    (hr : 2 / 35 ≤ r ∧ r ≤ outerCappingOuterRadius t) :
    1 / 2 ≤ outerCappingUnstretch t r ∧ outerCappingUnstretch t r ≤ 3 := by
  have hp : 0 < outerCappingOuterRadius t - 2 / 35 := by
    linarith [outerCappingOuterRadius_gt_inner t]
  dsimp [outerCappingUnstretch]
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (by linarith) (by norm_num)) hp.le)
  · have he := (div_le_iff₀ hp).mpr
      (show (r - 2 / 35) * (5 / 2) ≤ (5 / 2) *
        (outerCappingOuterRadius t - 2 / 35) by nlinarith [hr.2])
    linarith

def outerCappingAnnulusForward (x : planarSet.{u} 2) : outerCappingBaseSet.{u} :=
  ⟨ULift.up (outerCappingPolarPoint
    (outerCappingStretch (unitOf x.val.down) ‖x.val.down‖) (unitOf x.val.down)), by
    have hx : 1 / 2 ≤ ‖x.val.down‖ ∧ ‖x.val.down‖ ≤ 3 :=
      ((mem_planarModel_two x.val.down).mp
        ((mem_planarSet_iff (Or.inl rfl) x.val).mp x.property)).symm
    have hb := outerCappingStretch_bounds (unitOf x.val.down) ‖x.val.down‖ hx
    exact (outerCappingPolarPoint_mem_iff _ hb.1 _).mpr hb.2⟩

def outerCappingAnnulusInverse (y : outerCappingBaseSet.{u}) : planarSet.{u} 2 :=
  ⟨ULift.up (outerCappingUnstretch
      (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ)))
      ‖y.val.down - ((-(12 / 35) : ℝ) : ℂ)‖ •
        (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ)) : ℂ)), by
    have hy := (outerCappingFunction_nonpos_iff_radius y.val.down).mp y.property
    have he : outerCappingPolarPoint ‖y.val.down - ((-(12 / 35) : ℝ) : ℂ)‖
        (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ))) = y.val.down := by
      rw [outerCappingPolarPoint, norm_smul_unitOf]
      ring
    have hh : outerCappingFunction y.val.down ≤ 0 := y.property
    have hr := (outerCappingPolarPoint_mem_iff _ hy.2 _).mp (he.symm ▸ hh)
    have hb := outerCappingUnstretch_bounds _ _ ⟨hy.2, hr⟩
    apply (mem_planarSet_iff (Or.inl rfl) _).mpr
    apply (mem_planarModel_two _).mpr
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by linarith [hb.1])]
    exact hb.symm⟩

theorem outerCappingAnnulusInverse_forward (x : planarSet.{u} 2) :
    outerCappingAnnulusInverse (outerCappingAnnulusForward x) = x := by
  have hx : 1 / 2 ≤ ‖x.val.down‖ ∧ ‖x.val.down‖ ≤ 3 :=
    ((mem_planarModel_two x.val.down).mp
      ((mem_planarSet_iff (Or.inl rfl) x.val).mp x.property)).symm
  have hp : 0 < outerCappingStretch (unitOf x.val.down) ‖x.val.down‖ := by
    linarith [(outerCappingStretch_bounds (unitOf x.val.down) _ hx).1]
  apply Subtype.ext
  apply ULift.ext
  change outerCappingUnstretch
    (unitOf (outerCappingPolarPoint
      (outerCappingStretch (unitOf x.val.down) ‖x.val.down‖) (unitOf x.val.down) -
        ((-(12 / 35) : ℝ) : ℂ)))
    ‖outerCappingPolarPoint
      (outerCappingStretch (unitOf x.val.down) ‖x.val.down‖) (unitOf x.val.down) -
        ((-(12 / 35) : ℝ) : ℂ)‖ •
    (unitOf (outerCappingPolarPoint
      (outerCappingStretch (unitOf x.val.down) ‖x.val.down‖) (unitOf x.val.down) -
        ((-(12 / 35) : ℝ) : ℂ)) : ℂ) = x.val.down
  unfold outerCappingPolarPoint
  rw [add_sub_cancel_left, unitOf_smul hp, norm_smul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg hp.le, outerCappingUnstretch_stretch, norm_smul_unitOf]

theorem outerCappingAnnulusForward_inverse (y : outerCappingBaseSet.{u}) :
    outerCappingAnnulusForward (outerCappingAnnulusInverse y) = y := by
  have hy := (outerCappingFunction_nonpos_iff_radius y.val.down).mp y.property
  have he : outerCappingPolarPoint ‖y.val.down - ((-(12 / 35) : ℝ) : ℂ)‖
      (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ))) = y.val.down := by
    rw [outerCappingPolarPoint, norm_smul_unitOf]
    ring
  have hh : outerCappingFunction y.val.down ≤ 0 := y.property
  have hr := (outerCappingPolarPoint_mem_iff _ hy.2 _).mp (he.symm ▸ hh)
  have hp : 0 < outerCappingUnstretch
      (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ)))
      ‖y.val.down - ((-(12 / 35) : ℝ) : ℂ)‖ := by
    linarith [(outerCappingUnstretch_bounds _ _ ⟨hy.2, hr⟩).1]
  apply Subtype.ext
  apply ULift.ext
  change outerCappingPolarPoint
    (outerCappingStretch
      (unitOf (outerCappingUnstretch
        (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ)))
        ‖y.val.down - ((-(12 / 35) : ℝ) : ℂ)‖ •
          (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ)) : ℂ)))
      ‖outerCappingUnstretch (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ)))
        ‖y.val.down - ((-(12 / 35) : ℝ) : ℂ)‖ •
          (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ)) : ℂ)‖)
    (unitOf (outerCappingUnstretch (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ)))
      ‖y.val.down - ((-(12 / 35) : ℝ) : ℂ)‖ •
        (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ)) : ℂ))) = y.val.down
  rw [unitOf_smul hp, norm_smul, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg hp.le, outerCappingStretch_unstretch]
  exact he

theorem outerCappingAnnulusForward_smooth :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ outerCappingAnnulusForward.{u} := by
  apply (outerCappingBaseAtlas.contMDiff_iff_subtype_val _).mpr
  intro x
  have hx : 1 / 2 ≤ ‖x.val.down‖ :=
    ((mem_planarModel_two x.val.down).mp
      ((mem_planarSet_iff (Or.inl rfl) x.val).mp x.property)).2
  have hne : x.val.down ≠ 0 := by
    intro he
    rw [he, norm_zero] at hx
    norm_num at hx
  have hd := (contMDiff_planarSet_down 2).contMDiffAt (x := x)
  have hu := (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp x hd
  have hn := (contDiffAt_norm ℝ hne).contMDiffAt.comp x hd
  have hR := outerCappingOuterRadius_smooth.contMDiffAt.comp x hu
  have hs : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
      (fun z : planarSet.{u} 2 => outerCappingStretch (unitOf z.val.down) ‖z.val.down‖) x :=
    contMDiffAt_const.add
      (((hn.sub contMDiffAt_const).mul (hR.sub contMDiffAt_const)).div_const (5 / 2))
  exact contMDiff_planeLift_up.contMDiffAt.comp x
    (contMDiffAt_const.add (hs.smul (contMDiff_circle_coe.contMDiffAt.comp x hu)))

theorem outerCappingAnnulusInverse_smooth :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ outerCappingAnnulusInverse.{u} := by
  apply ((planarAtlas 2).contMDiff_iff_subtype_val _).mpr
  intro y
  have hy := (outerCappingFunction_nonpos_iff_radius y.val.down).mp y.property
  have hne : y.val.down - ((-(12 / 35) : ℝ) : ℂ) ≠ 0 := by
    intro he
    rw [he, norm_zero] at hy
    norm_num at hy
  have hd : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞
      (fun z : outerCappingBaseSet.{u} => z.val.down - ((-(12 / 35) : ℝ) : ℂ)) y :=
    (contMDiff_planeLift_down.comp outerCappingBaseAtlas.contMDiff_subtype_val).contMDiffAt.sub
      contMDiffAt_const
  have hu := (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp y hd
  have hn := (contDiffAt_norm ℝ hne).contMDiffAt.comp y hd
  have hR := outerCappingOuterRadius_smooth.contMDiffAt.comp y hu
  have hs : ContMDiffAt (𝓡∂ 2) 𝓘(ℝ, ℝ) ∞
      (fun z : outerCappingBaseSet.{u} => outerCappingUnstretch
        (unitOf (z.val.down - ((-(12 / 35) : ℝ) : ℂ)))
        ‖z.val.down - ((-(12 / 35) : ℝ) : ℂ)‖) y :=
    contMDiffAt_const.add (((hn.sub contMDiffAt_const).mul contMDiffAt_const).div₀
      (hR.sub contMDiffAt_const) (ne_of_gt (by
        linarith [outerCappingOuterRadius_gt_inner
          (unitOf (y.val.down - ((-(12 / 35) : ℝ) : ℂ)))])))
  exact contMDiff_planeLift_up.contMDiffAt.comp y
    (hs.smul (contMDiff_circle_coe.contMDiffAt.comp y hu))

def outerCappingAnnulusDiffeomorph :
    planarSet.{u} 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ outerCappingBaseSet.{u} where
  toFun := outerCappingAnnulusForward
  invFun := outerCappingAnnulusInverse
  left_inv := outerCappingAnnulusInverse_forward
  right_inv := outerCappingAnnulusForward_inverse
  contMDiff_toFun := outerCappingAnnulusForward_smooth
  contMDiff_invFun := outerCappingAnnulusInverse_smooth

def outerCappingProductSet : Set (PlaneLift.{u} × Circle) :=
  {p | outerCappingFunction p.1.down ≤ 0}

theorem outerCappingProductFunction_smooth :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : PlaneLift.{u} × Circle => outerCappingFunction p.1.down) :=
  outerCappingBaseFunction_smooth.comp contMDiff_fst

theorem outerCappingProductFunction_regular (p : PlaneLift.{u} × Circle)
    (hp : outerCappingFunction p.1.down = 0) :
    mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ)
      (fun q : PlaneLift.{u} × Circle => outerCappingFunction q.1.down) p ≠ 0 := by
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ))
    (s := fun z : ℂ => ((ULift.up z : PlaneLift.{u}), p.2)) (y := p.1.down)
    (outerCappingProductFunction_smooth.mdifferentiableAt (by simp))
    ((contMDiff_planeLift_up.prodMk contMDiff_const).mdifferentiableAt (by simp)) ?_
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) outerCappingFunction p.1.down ≠ 0
  rw [mfderiv_eq_fderiv]
  exact outerCappingFunction_regular hp

def outerCappingProductAtlas : SmoothBoundaryAtlas
    (𝓘(ℝ, ℂ).prod (𝓡 1)) 3 outerCappingProductSet.{u} :=
  SmoothBoundaryAtlas.regularSublevel (𝓘(ℝ, ℂ).prod (𝓡 1)) (n := 2)
    finrank_planeCircleModel outerCappingProductFunction_smooth 0
      outerCappingProductFunction_regular

instance : ChartedSpace (EuclideanHalfSpace 3) outerCappingProductSet.{u} :=
  outerCappingProductAtlas.toChartedSpace

instance : IsManifold (𝓡∂ 3) ∞ outerCappingProductSet.{u} :=
  outerCappingProductAtlas.isManifold

def outerCappingProductDiffeomorph :
    (outerCappingBaseSet.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯
      outerCappingProductSet.{u} where
  toFun x := ⟨(x.1.val, x.2), x.1.property⟩
  invFun y := (⟨y.val.1, y.property⟩, y.val.2)
  left_inv x := by cases x; rfl
  right_inv y := by cases y; rfl
  contMDiff_toFun := (outerCappingProductAtlas.contMDiff_iff_subtype_val _).mpr
    ((outerCappingBaseAtlas.contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd)
  contMDiff_invFun :=
    ((outerCappingBaseAtlas.contMDiff_iff_subtype_val _).mpr
      (contMDiff_fst.comp outerCappingProductAtlas.contMDiff_subtype_val)).prodMk
        (contMDiff_snd.comp outerCappingProductAtlas.contMDiff_subtype_val)

def outerCappingAnnulusProductDiffeomorph :
    (planarSet.{u} 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯
      outerCappingProductSet.{u} :=
  (outerCappingAnnulusDiffeomorph.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans
    outerCappingProductDiffeomorph

theorem exists_outerCapping_annulusProduct :
    ∃ B : PlanarBase.{u} 2,
      Nonempty ((B.surface.Carrier × Circle) ≃ₘ⟮
        (SurfaceModel.model B.surface.kind).prod (𝓡 1), 𝓡∂ 3⟯
          outerCappingProductSet.{u}) :=
  ⟨annulusPlanarBase, ⟨outerCappingAnnulusProductDiffeomorph⟩⟩

theorem cappingUnitOf_circle_mul (t : Circle) (z : ℂ) (hz : z ≠ 0) :
    unitOf ((t : ℂ) * z) = t * unitOf z := by
  apply Circle.ext
  rw [coe_unitOf (mul_ne_zero (Circle.coe_ne_zero t) hz), Circle.coe_mul, coe_unitOf hz,
    norm_mul, Circle.norm_coe, one_mul, Complex.real_smul, Complex.real_smul]
  ring

def outerCappingCapPhase (q : ℤ) (x : UnitDisc.{u}) : Circle :=
  unitOf (3 - (3 / 2 : ℂ) * x.down.val) ^ (-q)

theorem outerCappingCapPhase_smooth (q : ℤ) :
    ContMDiff (𝓡∂ 2) (𝓡 1) ∞ (outerCappingCapPhase.{u} q) := by
  have ha : ContDiff ℝ ∞ (fun z : ℂ => 3 - (3 / 2 : ℂ) * z) :=
    contDiff_const.sub (contDiff_const.mul contDiff_id)
  intro x
  exact (contMDiff_circle_zpow (-q)).contMDiffAt.comp x
    ((contMDiffOn_unitOf.contMDiffAt
      (isOpen_ne.mem_nhds (cappingOuterDisc_denominator x))).comp x
        (ha.contMDiff.comp contMDiff_disc_val).contMDiffAt)

def outerCappingCapFibreChange (q : ℤ) :
    (UnitDisc.{u} × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), (𝓡∂ 2).prod (𝓡 1)⟯
      UnitDisc.{u} × Circle where
  toFun x := (x.1, outerCappingCapPhase q x.1 * x.2)
  invFun y := (y.1, (outerCappingCapPhase q y.1)⁻¹ * y.2)
  left_inv x := by simp
  right_inv y := by simp
  contMDiff_toFun := contMDiff_fst.prodMk
    (((outerCappingCapPhase_smooth q).comp contMDiff_fst).mul contMDiff_snd)
  contMDiff_invFun := contMDiff_fst.prodMk
    (((outerCappingCapPhase_smooth q).inv.comp contMDiff_fst).mul contMDiff_snd)

theorem outerCapping_phase_matching (q : ℤ) (t v : Circle) :
    unitOf ((3 : ℂ) * ((t⁻¹ : Circle) : ℂ) - (3 / 2 : ℂ)) ^ (-q) *
      (t ^ (-q) * v) = unitOf (3 - (3 / 2 : ℂ) * t) ^ (-q) * v := by
  have hd : 3 - (3 / 2 : ℂ) * t ≠ 0 := by
    exact cappingOuterDisc_denominator (outerCappingDiscBoundary.{0} t)
  have he : (3 : ℂ) * ((t⁻¹ : Circle) : ℂ) - (3 / 2 : ℂ) =
      ((t⁻¹ : Circle) : ℂ) * (3 - (3 / 2 : ℂ) * t) := by
    rw [Circle.coe_inv]
    field_simp
  rw [he, cappingUnitOf_circle_mul (t⁻¹) _ hd, mul_zpow, inv_zpow', neg_neg]
  calc
    t ^ q * unitOf (3 - (3 / 2 : ℂ) * t) ^ (-q) * (t ^ (-q) * v) =
        (t ^ q * t ^ (-q)) * unitOf (3 - (3 / 2 : ℂ) * t) ^ (-q) * v := by ac_rfl
    _ = unitOf (3 - (3 / 2 : ℂ) * t) ^ (-q) * v := by
      rw [← zpow_add, add_neg_cancel, zpow_zero, one_mul]

theorem outerCapping_host_phase_matching (B : PlanarBase.{u} 3)
    (q : ℤ) (t v : Circle) :
    fillingHostInnerChange B 1 (by decide) (-q)
      (B.collar 0 ((t⁻¹ : Circle), halfZero), t ^ (-q) * v) =
        (B.collar 0 ((t⁻¹ : Circle), halfZero),
          unitOf (3 - (3 / 2 : ℂ) * t) ^ (-q) * v) := by
  change (B.collar 0 ((t⁻¹ : Circle), halfZero),
    unitOf (B.embedding (B.collar 0 ((t⁻¹ : Circle), halfZero)) -
      planarCenter 3 1) ^ (-q) * (t ^ (-q) * v)) = _
  have he : (planarCenter 3 1 : ℂ) = (3 / 2 : ℂ) := by norm_num [planarCenter]
  rw [he, cappingHostPhase_outer, outerCapping_phase_matching]

def outerCappingHostPhase (q : ℤ) (x : planarSet.{u} 3) : Circle :=
  unitOf (x.val.down - (3 / 2 : ℂ)) ^ (-q)

theorem outerCappingHostPhase_smooth (q : ℤ) :
    ContMDiff (𝓡∂ 2) (𝓡 1) ∞ (outerCappingHostPhase.{u} q) := by
  have ha : ContDiff ℝ ∞ (fun z : ℂ => z - (3 / 2 : ℂ)) :=
    contDiff_id.sub contDiff_const
  intro x
  exact (contMDiff_circle_zpow (-q)).contMDiffAt.comp x
    ((contMDiffOn_unitOf.contMDiffAt
      (isOpen_ne.mem_nhds (cappingOuterHost_denominator x))).comp x
        (ha.contMDiff.comp (contMDiff_planarSet_down 3)).contMDiffAt)

def outerCappingHostProduct (q : ℤ) (x : planarSet.{u} 3 × Circle) :
    outerCappingProductSet.{u} :=
  outerCappingProductDiffeomorph (outerCappingHost x.1, outerCappingHostPhase q x.1 * x.2)

def outerCappingDiscProduct (q : ℤ) (x : UnitDisc.{u} × Circle) :
    outerCappingProductSet.{u} :=
  outerCappingProductDiffeomorph (outerCappingDisc x.1, outerCappingCapPhase q x.1 * x.2)

theorem outerCappingHostProduct_smooth (q : ℤ) :
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) ∞ (outerCappingHostProduct.{u} q) :=
  outerCappingProductDiffeomorph.contMDiff.comp
    ((outerCappingHost_smooth.comp contMDiff_fst).prodMk
      (((outerCappingHostPhase_smooth q).comp contMDiff_fst).mul contMDiff_snd))

theorem outerCappingDiscProduct_smooth (q : ℤ) :
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) ∞ (outerCappingDiscProduct.{u} q) :=
  outerCappingProductDiffeomorph.contMDiff.comp
    ((outerCappingDisc_smooth.comp contMDiff_fst).prodMk
      (((outerCappingCapPhase_smooth q).comp contMDiff_fst).mul contMDiff_snd))

theorem outerCappingProduct_matching (q : ℤ) (t v : Circle) :
    outerCappingHostProduct q
      (planarCollar.{u} 3 (Or.inr rfl) 0 ((t⁻¹ : Circle), halfZero), t ^ (-q) * v) =
        outerCappingDiscProduct q (outerCappingDiscBoundary t, v) := by
  apply congrArg outerCappingProductDiffeomorph
  apply Prod.ext
  · exact (outerCapping_boundary t).symm
  · change unitOf ((planarCollar.{u} 3 (Or.inr rfl) 0
      ((t⁻¹ : Circle), halfZero)).val.down - (3 / 2 : ℂ)) ^ (-q) *
        (t ^ (-q) * v) = unitOf (3 - (3 / 2 : ℂ) * t) ^ (-q) * v
    rw [planarCollar_zero_val]
    have he : planarCircleMap 3 0 (t⁻¹ : Circle) = (3 : ℂ) * ((t⁻¹ : Circle) : ℂ) := by
      simp [planarCircleMap, planarCenter, planarRadius]
    rw [he]
    exact outerCapping_phase_matching q t v

theorem outerCappingProduct_cover (q : ℤ) (y : outerCappingProductSet.{u}) :
    (∃ x : planarSet.{u} 3 × Circle, outerCappingHostProduct q x = y) ∨
      ∃ x : UnitDisc.{u} × Circle, outerCappingDiscProduct q x = y := by
  let p := outerCappingProductDiffeomorph.symm y
  rcases outerCapping_cover p.1 with ⟨x, hx⟩ | ⟨x, hx⟩
  · left
    refine ⟨(x, (outerCappingHostPhase q x)⁻¹ * p.2), ?_⟩
    change outerCappingProductDiffeomorph
      (outerCappingHost x, outerCappingHostPhase q x *
        ((outerCappingHostPhase q x)⁻¹ * p.2)) = y
    rw [hx, mul_inv_cancel_left]
    exact outerCappingProductDiffeomorph.apply_symm_apply y
  · right
    refine ⟨(x, (outerCappingCapPhase q x)⁻¹ * p.2), ?_⟩
    change outerCappingProductDiffeomorph
      (outerCappingDisc x, outerCappingCapPhase q x *
        ((outerCappingCapPhase q x)⁻¹ * p.2)) = y
    rw [hx, mul_inv_cancel_left]
    exact outerCappingProductDiffeomorph.apply_symm_apply y

end GC.Seifert.ElementaryPresentation
