import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.LensSeam

/-!
# Gluing two solid tori into a lens space

Let `L = L(p, q)` and `a p + b q = 1`. The quotient of the solid torus `‖z₁‖ ≤ ‖z₂‖` is the solid
torus `lensLeftCover.pieceSet = {h ≤ 0}` of `L` and the quotient of `‖z₂‖ ≤ ‖z₁‖` is
`lensRightCover.pieceSet = {h ≥ 0}`, where `h` is the descended Clifford height. In the disc and
circle coordinates of the two pieces the common boundary torus is identified by the linear map
`lensMatching`, `(x, y) ↦ (x^{-q} y^a, x^p y^b)` with matrix `!![-q, a; p, b]` of determinant
`-1`: the left seam at height `s` equals the right seam at height `-s` after `lensMatching`
(`lensRight_seamMap_lensMatching`).

The disjoint union of the two pieces maps to `L` by the two inclusions; we pull back the orientation
of `L` along this fold, build the boundary gluing, the homeomorphism from its quotient onto `L`, and
show that the two half collars induce opposite boundary orientations. The last step is a general
statement (`reversesBoundaryOrientation_of_seam`): two half collars which fold into one signed
collar through `s ↦ -s` and `s ↦ s` reverse the boundary orientation.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold

universe u

theorem mfderiv_congr_point {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] (f : M → M')
    (y₁ y₂ : M) (h : y₁ = y₂) (w : TangentSpace I y₁) :
    mfderiv I I' f y₁ w = mfderiv I I' f y₂ w := by
  subst h
  rfl

theorem reversesBoundaryOrientation_of_seam {C : CompactCarrier.{u}} {W : Type*}
    [TopologicalSpace W] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) W] [IsManifold (𝓡 3) ∞ W]
    {F : C.Carrier → W} (hF : ContMDiff C.model (𝓡 3) ∞ F)
    (hFb : ∀ x, Bijective (mfderiv C.model (𝓡 3) F x)) (O : ManifoldOrientation (𝓡 3) W 3)
    (hO : ∀ x, Orientation.map (Fin 3)
      (Manifold.differentialEquivOfBijective C.model (𝓡 3) F hFb x).toLinearEquiv
      (C.orientation.orientation x) = O.orientation (F x))
    {l r : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞}
    (hl : l.source = halfCollarSource) (hr : r.source = halfCollarSource)
    (m : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    {S : PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) W ∞}
    (hS : S.source = signedCollarSource)
    (hFl : ∀ y ∈ halfCollarSource, F (l y) = S (y.1, -y.2.val 0))
    (hFr : ∀ y ∈ halfCollarSource, F (r (m y.1, y.2)) = S (y.1, y.2.val 0)) :
    ReversesBoundaryOrientation C l (fun y => r (m y.1, y.2)) := by
  intro t
  let q0 : Torus × EuclideanHalfSpace 1 := (t, halfZero)
  let r' : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞ :=
    (m.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans r
  have hsrc : IsOpen halfCollarSource := by
    rw [← hl]
    exact l.open_source
  have hq0 : q0 ∈ halfCollarSource := halfZero_mem_halfCollarSource t
  have hq0l : q0 ∈ l.source := by
    rw [hl]
    exact hq0
  have hq0r : q0 ∈ r'.source := by
    refine ⟨mem_univ _, ?_⟩
    change (m t, halfZero) ∈ r.source
    rw [hr]
    exact halfZero_mem_halfCollarSource _
  have hL := l.isLocalDiffeomorphAt halfCollarModel C.model ∞ hq0l
  have hR := r'.isLocalDiffeomorphAt halfCollarModel C.model ∞ hq0r
  let L := (hL.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let R := (hR.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  refine ⟨L, R, fun v => rfl, fun v => rfl, ?_⟩
  let D : (x : C.Carrier) → EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fun x => (Manifold.differentialEquivOfBijective C.model (𝓡 3) F hFb x).toLinearEquiv
  have hOC : ∀ x : C.Carrier, C.orientation.orientation x =
      Orientation.map (Fin 3) (D x).symm (O.orientation (F x)) := by
    intro x
    rw [← hO x]
    exact (Equiv.symm_apply_apply (Orientation.map (Fin 3) (D x)) _).symm
  let y0 : Torus × ℝ := halfCollarHeight q0
  have hy0 : y0 ∈ S.source := by
    rw [hS]
    change -1 < halfZero.val 0 ∧ halfZero.val 0 < 1
    rw [show halfZero.val 0 = 0 from rfl]
    norm_num
  have hSd := S.isLocalDiffeomorphAt signedCollarModel (𝓡 3) ∞ hy0
  let dS := (hSd.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  have hFm : ∀ x, MDifferentiableAt C.model (𝓡 3) F x := fun x => hF.mdifferentiableAt (by simp)
  have hj : MDifferentiableAt halfCollarModel signedCollarModel halfCollarHeight q0 :=
    contMDiff_halfCollarHeight.mdifferentiableAt (by simp)
  have hρ : MDifferentiableAt signedCollarModel signedCollarModel seamReflection y0 :=
    contMDiff_seamReflection.mdifferentiableAt (by simp)
  have hSm : MDifferentiableAt signedCollarModel (𝓡 3) S y0 := S.mdifferentiableAt (by simp) hy0
  have hρy0 : seamReflection y0 = y0 := seamReflection_halfCollarHeight_zero t
  have hleft : ∀ v, D (l q0) (L v) = dS (mfderiv signedCollarModel signedCollarModel
      seamReflection y0 (mfderiv halfCollarModel signedCollarModel halfCollarHeight q0 v)) := by
    intro v
    have e1 := DFunLike.congr_fun
      (mfderiv_comp q0 (hFm (l q0)) (l.mdifferentiableAt (by simp) hq0l)) v
    have hev : F ∘ l =ᶠ[𝓝 q0] S ∘ seamReflection ∘ halfCollarHeight := by
      filter_upwards [hsrc.mem_nhds hq0] with y hy
      exact hFl y hy
    have e4 := DFunLike.congr_fun
      (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel) (I' := 𝓡 3) hev) v
    have hSm' : MDifferentiableAt signedCollarModel (𝓡 3) S (seamReflection y0) := by
      rw [hρy0]
      exact hSm
    have e2 := DFunLike.congr_fun (mfderiv_comp q0 hSm' (hρ.comp q0 hj)) v
    have e3 := DFunLike.congr_fun (mfderiv_comp q0 hρ hj) v
    exact (((e1.symm.trans e4).trans e2).trans (congrArg (mfderiv signedCollarModel (𝓡 3) S
      (seamReflection y0)) e3)).trans (mfderiv_congr_point S _ _ hρy0 _)
  have hright : ∀ v, D (r' q0) (R v) =
      dS (mfderiv halfCollarModel signedCollarModel halfCollarHeight q0 v) := by
    intro v
    have e1 := DFunLike.congr_fun
      (mfderiv_comp q0 (hFm (r' q0)) (r'.mdifferentiableAt (by simp) hq0r)) v
    have hev : F ∘ r' =ᶠ[𝓝 q0] S ∘ halfCollarHeight := by
      filter_upwards [hsrc.mem_nhds hq0] with y hy
      exact hFr y hy
    have e4 := DFunLike.congr_fun
      (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel) (I' := 𝓡 3) hev) v
    have e2 := DFunLike.congr_fun (mfderiv_comp q0 hSm hj) v
    exact (e1.symm.trans e4).trans e2
  let A := L.trans (D (l q0))
  let B := R.trans (D (r' q0))
  let J := B.trans dS.symm
  let P : (TangentSpace signedCollarModel y0) →ₗ[ℝ] (TangentSpace signedCollarModel y0) :=
    (LinearMap.id : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) →ₗ[ℝ] _).prodMap
      (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hJ : ∀ v, J v = mfderiv halfCollarModel signedCollarModel halfCollarHeight q0 v := by
    intro v
    apply dS.injective
    exact (dS.apply_symm_apply (B v)).trans (hright v)
  have hdet : LinearMap.det ((A.trans B.symm : _ ≃ₗ[ℝ] _) :
      TangentSpace halfCollarModel q0 →ₗ[ℝ] TangentSpace halfCollarModel q0) < 0 := by
    let Sₗ : TangentSpace signedCollarModel y0 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) := dS.toLinearMap
    rw [det_trans_symm_eq_det A B J P Sₗ]
    · rw [show LinearMap.det P = -1 from
        det_prodMap_id_neg (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))]
      norm_num
    · intro v
      change D (l q0) (L v) = Sₗ (P (J v))
      rw [hJ]
      exact (hleft v).trans (congrArg Sₗ (mfderiv_seamReflection_apply _ _))
    · intro v
      change D (r' q0) (R v) = Sₗ (J v)
      rw [hJ]
      exact hright v
  have hpt : F (r' q0) = F (l q0) := by
    have h1 : F (r' q0) = S (t, halfZero.val 0) := hFr q0 hq0
    rw [h1, hFl q0 hq0, show halfZero.val 0 = 0 from rfl, neg_zero]
  have hOS : ∀ w₁ w₂ : W, w₁ = w₂ → O.orientation w₁ = O.orientation w₂ := by
    rintro _ _ rfl
    rfl
  change Orientation.map (Fin 3) L.symm (C.orientation.orientation (l q0)) =
    -Orientation.map (Fin 3) R.symm (C.orientation.orientation (r' q0))
  rw [hOC, hOC, hOS _ _ hpt]
  let o := O.orientation (F (l q0))
  have key := orientation_map_symm_eq_neg_of_det_neg (finrank_halfCollarTangent q0) A B o hdet
  have hA' : A.symm = (D (l q0)).symm.trans L.symm := LinearEquiv.ext fun _ => rfl
  have hB' : B.symm = (D (r' q0)).symm.trans R.symm := LinearEquiv.ext fun _ => rfl
  rw [hA', hB'] at key
  exact (DifferentialGeometry.orientation_map_trans (D (l q0)).symm L.symm o).symm.trans
    (key.trans (congrArg Neg.neg (DifferentialGeometry.orientation_map_trans
      (D (r' q0)).symm R.symm o)))

namespace TwistedCover

variable {p : ℕ} [NeZero p] {e : ℤ} {W : Type} [TopologicalSpace W]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) W] (T : TwistedCover p e W)

instance instCompactSpacePiece [CompactSpace W] : CompactSpace T.pieceSet :=
  isCompact_iff_compactSpace.mp T.isClosed_pieceSet.isCompact

end TwistedCover

theorem lensMatching_pow_alg (p : ℕ) (x v : Circle) (b : ℤ) :
    (x * v ^ b) ^ p = x ^ (p : ℤ) * (v ^ p) ^ b := by
  rw [mul_pow, ← zpow_natCast (v ^ b), ← zpow_mul, mul_comm b, zpow_mul]
  simp only [zpow_natCast]

theorem lensMatching_first_alg (p : ℕ) (q : ℤ) (x v : Circle) {a b : ℤ}
    (h : a * p + b * q = 1) : x ^ (-q) * (v ^ p) ^ a * (x * v ^ b) ^ q = v := by
  rw [← zpow_natCast v p, ← zpow_mul, mul_zpow, ← zpow_mul, mul_comm (x ^ (-q)), mul_assoc,
    ← mul_assoc (x ^ (-q)) (x ^ q), ← zpow_add, neg_add_cancel, zpow_zero, one_mul, ← zpow_add,
    show (p : ℤ) * a + b * q = 1 by linarith, zpow_one]

section Lens

variable (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q)

theorem lensRight_height (w : LensCarrier p q hpq) :
    (lensRightCover p q hpq).height w = -(lensLeftCover p q hpq).height w := by
  obtain ⟨x, rfl⟩ := (lensRightCover p q hpq).surjective w
  rw [TwistedCover.height_cover, lensRightCover_cover]
  change cliffordHeight x = -(lensLeftCover p q hpq).height
    ((lensLeftCover p q hpq).cover (sphereSwap x))
  rw [TwistedCover.height_cover, cliffordHeight_sphereSwap, neg_neg]

def lensMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-q, lensCoeffP p q hpq; (p : ℤ), lensCoeffQ p q hpq]

omit [NeZero p] in
theorem lensMatrix_det : (lensMatrix p q hpq).det = -1 := by
  rw [lensMatrix, Matrix.det_fin_two_of]
  linear_combination -(lensCoeff_spec p q hpq)

def lensMatrixUnit : GL (Fin 2) ℤ :=
  GC.Seifert.PrimitiveSlope.unitOfDet (lensMatrix p q hpq) (Or.inr (lensMatrix_det p q hpq))

def lensMatching : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  GC.Seifert.linearTorusDiffeomorph (lensMatrixUnit p q hpq)

omit [NeZero p] in
theorem lensMatching_apply (t : Torus) :
    lensMatching p q hpq t = (t.1 ^ (-q) * t.2 ^ lensCoeffP p q hpq,
      t.1 ^ (p : ℤ) * t.2 ^ lensCoeffQ p q hpq) := rfl

theorem lensRight_seamMap_lensMatching (t : Torus) {s : ℝ} (h₁ : -1 ≤ s) (h₂ : s ≤ 1) :
    (lensRightCover p q hpq).seamMap (lensMatching p q hpq t, -s) =
      (lensLeftCover p q hpq).seamMap (t, s) := by
  have hu : (t.1 * circleRootOf p t.2 ^ lensCoeffQ p q hpq) ^ p =
      (lensMatching p q hpq t).2 := by
    rw [lensMatching_apply, lensMatching_pow_alg, circleRootOf_pow]
  rw [TwistedCover.seamMap_eq_cover _ (y := (lensMatching p q hpq t, -s)) hu]
  have hv : (lensMatching p q hpq t).1 * (t.1 * circleRootOf p t.2 ^ lensCoeffQ p q hpq) ^ q =
      circleRootOf p t.2 := by
    have h := lensMatching_first_alg p q t.1 (circleRootOf p t.2) (lensCoeff_spec p q hpq)
    rw [circleRootOf_pow] at h
    exact h
  change lensCover p q hpq (sphereSwap (cliffordSeamMap (((lensMatching p q hpq t).1 *
    (t.1 * circleRootOf p t.2 ^ lensCoeffQ p q hpq) ^ q,
    t.1 * circleRootOf p t.2 ^ lensCoeffQ p q hpq), -s))) =
    lensCover p q hpq (cliffordSeamMap ((t.1 * circleRootOf p t.2 ^ lensCoeffQ p q hpq,
      circleRootOf p t.2), s))
  rw [hv]
  exact congrArg (lensCover p q hpq)
    (sphereSwap_cliffordSeamMap_swap (t.1 * circleRootOf p t.2 ^ lensCoeffQ p q hpq,
      circleRootOf p t.2) h₁ h₂)

abbrev LensCut : Type := (lensLeftCover p q hpq).pieceSet ⊕ (lensRightCover p q hpq).pieceSet

def lensFold : LensCut p q hpq → LensCarrier p q hpq := Sum.elim Subtype.val Subtype.val

@[simp] theorem lensFold_inl (a : (lensLeftCover p q hpq).pieceSet) :
    lensFold p q hpq (Sum.inl a) = a.val := rfl

@[simp] theorem lensFold_inr (b : (lensRightCover p q hpq).pieceSet) :
    lensFold p q hpq (Sum.inr b) = b.val := rfl

theorem contMDiff_lensFold : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (lensFold p q hpq) :=
  ContMDiff.sumElim (lensLeftCover p q hpq).contMDiff_piece_val
    (lensRightCover p q hpq).contMDiff_piece_val

theorem mfderiv_lensFold_bijective (x : LensCut p q hpq) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (lensFold p q hpq) x) := by
  have hf : MDifferentiableAt (𝓡∂ 3) (𝓡 3) (lensFold p q hpq) x :=
    (contMDiff_lensFold p q hpq).mdifferentiableAt (by simp)
  rcases x with a | b
  · have hi : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3)
        (Sum.inl : (lensLeftCover p q hpq).pieceSet → LensCut p q hpq) a :=
      (ContMDiff.inl : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
        (Sum.inl : (lensLeftCover p q hpq).pieceSet → LensCut p q hpq)).mdifferentiableAt
          (by simp)
    have h := mfderiv_comp a hf hi
    rw [hasMFDerivAt_inl.mfderiv] at h
    have hb : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
        (lensFold p q hpq ∘ (Sum.inl : (lensLeftCover p q hpq).pieceSet → LensCut p q hpq)) a) :=
      (lensLeftCover p q hpq).mfderiv_piece_val_bijective a
    rw [h] at hb
    exact hb
  · have hi : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3)
        (Sum.inr : (lensRightCover p q hpq).pieceSet → LensCut p q hpq) b :=
      (ContMDiff.inr : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
        (Sum.inr : (lensRightCover p q hpq).pieceSet → LensCut p q hpq)).mdifferentiableAt
          (by simp)
    have h := mfderiv_comp b hf hi
    rw [hasMFDerivAt_inr.mfderiv] at h
    have hb : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
        (lensFold p q hpq ∘ (Sum.inr : (lensRightCover p q hpq).pieceSet → LensCut p q hpq)) b) :=
      (lensRightCover p q hpq).mfderiv_piece_val_bijective b
    rw [h] at hb
    exact hb

def lensCutOrientation : ManifoldOrientation (𝓡∂ 3) (LensCut p q hpq) 3 :=
  Manifold.manifoldOrientationPullback (𝓡∂ 3) (𝓡 3) finrank_euclideanSpace_fin (lensFold p q hpq)
    (contMDiff_lensFold p q hpq) (mfderiv_lensFold_bijective p q hpq)
    (GC.Seifert.lensSpaceFormGroup p q hpq).manifold.orientation

theorem orientation_map_lensCutOrientation (x : LensCut p q hpq) :
    Orientation.map (Fin 3) (Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (lensFold p q hpq)
      (mfderiv_lensFold_bijective p q hpq) x).toLinearEquiv
      ((lensCutOrientation p q hpq).orientation x) =
      (GC.Seifert.lensSpaceFormGroup p q hpq).manifold.orientation.orientation
        (lensFold p q hpq x) :=
  Manifold.orientation_map_manifoldOrientationPullback (𝓡∂ 3) (𝓡 3) finrank_euclideanSpace_fin
    (lensFold p q hpq) (contMDiff_lensFold p q hpq) (mfderiv_lensFold_bijective p q hpq)
    (GC.Seifert.lensSpaceFormGroup p q hpq).manifold.orientation x

theorem secondCountable_lensCarrier : SecondCountableTopology (LensCarrier p q hpq) :=
  ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) _

abbrev lensCutCarrier : CompactCarrier.{0} where
  kind := .withBoundary
  Carrier := LensCut p q hpq
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) (LensCut p q hpq))
  smooth := (inferInstance : IsManifold (𝓡∂ 3) ∞ (LensCut p q hpq))
  secondCountable := by
    have := secondCountable_lensCarrier p q hpq
    infer_instance
  orientation := lensCutOrientation p q hpq

def lensLeftTorus (t : Torus) : LensCut p q hpq := Sum.inl ((lensLeftCover p q hpq).torusPoint t)

def lensRightTorus (t : Torus) : LensCut p q hpq :=
  Sum.inr ((lensRightCover p q hpq).torusPoint t)

theorem isEmbedding_lensLeftTorus : _root_.Topology.IsEmbedding (lensLeftTorus p q hpq) :=
  ((continuous_inl.comp (lensLeftCover p q hpq).continuous_torusPoint).isClosedEmbedding
    (Sum.inl_injective.comp (lensLeftCover p q hpq).torusPoint_injective)).isEmbedding

theorem isEmbedding_lensRightTorus : _root_.Topology.IsEmbedding (lensRightTorus p q hpq) :=
  ((continuous_inr.comp (lensRightCover p q hpq).continuous_torusPoint).isClosedEmbedding
    (Sum.inr_injective.comp (lensRightCover p q hpq).torusPoint_injective)).isEmbedding

def lensLeftParam : Torus ≃ₜ range (lensLeftTorus p q hpq) :=
  (isEmbedding_lensLeftTorus p q hpq).toHomeomorph

def lensRightParam : Torus ≃ₜ range (lensRightTorus p q hpq) :=
  (isEmbedding_lensRightTorus p q hpq).toHomeomorph

def lensAttaching : range (lensLeftTorus p q hpq) ≃ₜ range (lensRightTorus p q hpq) :=
  (lensLeftParam p q hpq).symm.trans
    ((lensMatching p q hpq).toHomeomorph.trans (lensRightParam p q hpq))

theorem lensAttaching_leftParam (t : Torus) :
    lensAttaching p q hpq (lensLeftParam p q hpq t) =
      lensRightParam p q hpq (lensMatching p q hpq t) := by
  simp [lensAttaching]

theorem lensAttaching_val (t : Torus)
    (h : lensLeftTorus p q hpq t ∈ range (lensLeftTorus p q hpq)) :
    (lensAttaching p q hpq ⟨lensLeftTorus p q hpq t, h⟩ : LensCut p q hpq) =
      lensRightTorus p q hpq (lensMatching p q hpq t) := by
  have hl : (⟨lensLeftTorus p q hpq t, h⟩ : range (lensLeftTorus p q hpq)) =
      lensLeftParam p q hpq t := Subtype.ext rfl
  rw [hl, lensAttaching_leftParam]
  rfl

theorem lensAttaching_symm_val (t : Torus)
    (h : lensRightTorus p q hpq t ∈ range (lensRightTorus p q hpq)) :
    ((lensAttaching p q hpq).symm ⟨lensRightTorus p q hpq t, h⟩ : LensCut p q hpq) =
      lensLeftTorus p q hpq ((lensMatching p q hpq).symm t) := by
  have hr : (⟨lensRightTorus p q hpq t, h⟩ : range (lensRightTorus p q hpq)) =
      lensAttaching p q hpq (lensLeftParam p q hpq ((lensMatching p q hpq).symm t)) := by
    rw [lensAttaching_leftParam, Diffeomorph.apply_symm_apply]
    exact Subtype.ext rfl
  rw [hr, Homeomorph.symm_apply_apply]
  rfl

def lensGluing : BoundaryGluing (LensCut p q hpq) (Fin 1) where
  left _ := range (lensLeftTorus p q hpq)
  right _ := range (lensRightTorus p q hpq)
  attaching _ := lensAttaching p q hpq
  isClosed_left _ := isClosed_range_of_continuous_of_compactSpace
    (continuous_inl.comp (lensLeftCover p q hpq).continuous_torusPoint)
  isClosed_right _ := isClosed_range_of_continuous_of_compactSpace
    (continuous_inr.comp (lensRightCover p q hpq).continuous_torusPoint)
  disjoint_left_right _ := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨s, hs⟩
    cases hs
  disjoint_blocks i j h := (h (Subsingleton.elim i j)).elim

theorem lensFold_leftTorus (t : Torus) :
    lensFold p q hpq (lensLeftTorus p q hpq t) = (lensLeftCover p q hpq).seam (t, 0) :=
  (lensLeftCover p q hpq).torusPoint_val t

theorem lensFold_rightTorus_lensMatching (t : Torus) :
    lensFold p q hpq (lensRightTorus p q hpq (lensMatching p q hpq t)) =
      lensFold p q hpq (lensLeftTorus p q hpq t) := by
  change ((lensRightCover p q hpq).torusPoint (lensMatching p q hpq t)).val =
    ((lensLeftCover p q hpq).torusPoint t).val
  rw [TwistedCover.torusPoint_val, TwistedCover.torusPoint_val, TwistedCover.seam_apply,
    TwistedCover.seam_apply]
  have h := lensRight_seamMap_lensMatching p q hpq t (s := 0) (by norm_num) (by norm_num)
  rwa [neg_zero] at h

theorem lensGluing_rel_left_right (t : Torus) :
    (lensGluing p q hpq).rel (lensLeftTorus p q hpq t)
      (lensRightTorus p q hpq (lensMatching p q hpq t)) := by
  refine Or.inr ⟨0, Or.inl ⟨t, rfl⟩, ?_⟩
  rw [(lensGluing p q hpq).flip_of_mem_left ⟨t, rfl⟩]
  exact (lensAttaching_val p q hpq t _).symm

theorem lensFold_eq_of_rel {x y : LensCut p q hpq} (h : (lensGluing p q hpq).rel x y) :
    lensFold p q hpq x = lensFold p q hpq y := by
  rcases h with rfl | ⟨i, hx, rfl⟩
  · rfl
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    rcases hx with hx | hx
    · obtain ⟨t, rfl⟩ := id hx
      rw [(lensGluing p q hpq).flip_of_mem_left hx]
      have h1 := lensAttaching_val p q hpq t hx
      calc lensFold p q hpq (lensLeftTorus p q hpq t) =
            lensFold p q hpq (lensRightTorus p q hpq (lensMatching p q hpq t)) :=
          (lensFold_rightTorus_lensMatching p q hpq t).symm
        _ = _ := congrArg (lensFold p q hpq) h1.symm
    · obtain ⟨t, rfl⟩ := id hx
      rw [(lensGluing p q hpq).flip_of_mem_right hx]
      have h1 := lensAttaching_symm_val p q hpq t hx
      have h2 : lensFold p q hpq (lensRightTorus p q hpq t) =
          lensFold p q hpq (lensLeftTorus p q hpq ((lensMatching p q hpq).symm t)) := by
        rw [← lensFold_rightTorus_lensMatching, Diffeomorph.apply_symm_apply]
      exact h2.trans (congrArg (lensFold p q hpq) h1.symm)

theorem lensGluing_rel_inl_inr {a : (lensLeftCover p q hpq).pieceSet}
    {b : (lensRightCover p q hpq).pieceSet} (h : a.val = b.val) :
    (lensGluing p q hpq).rel (Sum.inl a) (Sum.inr b) := by
  have ha : (lensLeftCover p q hpq).height a.val = 0 := by
    have h₁ : (lensLeftCover p q hpq).height a.val ≤ 0 := a.2
    have h₂ : (lensRightCover p q hpq).height b.val ≤ 0 := b.2
    rw [lensRight_height, ← h] at h₂
    linarith
  obtain ⟨t, rfl⟩ := (lensLeftCover p q hpq).exists_torusPoint_eq ha
  have hb : b = (lensRightCover p q hpq).torusPoint (lensMatching p q hpq t) := by
    apply Subtype.ext
    rw [← h]
    exact (lensFold_rightTorus_lensMatching p q hpq t).symm
  rw [hb]
  exact lensGluing_rel_left_right p q hpq t

theorem lensGluing_rel_of_lensFold_eq {x y : LensCut p q hpq}
    (h : lensFold p q hpq x = lensFold p q hpq y) : (lensGluing p q hpq).rel x y := by
  rcases x with a | a <;> rcases y with b | b
  · exact Or.inl (congrArg Sum.inl (Subtype.ext h))
  · exact lensGluing_rel_inl_inr p q hpq h
  · exact (lensGluing p q hpq).isEquivalence_rel.symm (lensGluing_rel_inl_inr p q hpq h.symm)
  · exact Or.inl (congrArg Sum.inr (Subtype.ext h))

theorem surjective_lensFold : Surjective (lensFold p q hpq) := by
  intro w
  by_cases hw : (lensLeftCover p q hpq).height w ≤ 0
  · exact ⟨Sum.inl ⟨w, hw⟩, rfl⟩
  · have hw' : (lensRightCover p q hpq).height w ≤ 0 := by
      rw [lensRight_height]
      linarith [not_le.mp hw]
    exact ⟨Sum.inr ⟨w, hw'⟩, rfl⟩

def lensQuotientMap : Quotient (lensGluing p q hpq).setoid → LensCarrier p q hpq :=
  Quotient.lift (lensFold p q hpq) (fun _ _ h => lensFold_eq_of_rel p q hpq h)

theorem bijective_lensQuotientMap : Bijective (lensQuotientMap p q hpq) := by
  constructor
  · intro a b h
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y => exact Quotient.sound (lensGluing_rel_of_lensFold_eq p q hpq h)
  · intro w
    obtain ⟨x, hx⟩ := surjective_lensFold p q hpq w
    exact ⟨Quotient.mk _ x, hx⟩

def lensReconstruction : Quotient (lensGluing p q hpq).setoid ≃ₜ LensCarrier p q hpq :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ (bijective_lensQuotientMap p q hpq))
    (continuous_quot_lift _ (contMDiff_lensFold p q hpq).continuous)

theorem lensReconstruction_mk (x : LensCut p q hpq) :
    lensReconstruction p q hpq (Quotient.mk _ x) = lensFold p q hpq x := rfl

def lensLeftCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) (LensCut p q hpq) ∞ :=
  (lensLeftCover p q hpq).collar.trans partialDiffeomorphSumInl

def lensRightCollar :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) (LensCut p q hpq) ∞ :=
  (lensRightCover p q hpq).collar.trans partialDiffeomorphSumInr

theorem lensLeftCollar_source : (lensLeftCollar p q hpq).source = halfCollarSource := by
  change (lensLeftCover p q hpq).collar.source ∩ _ ⁻¹' univ = _
  rw [preimage_univ, inter_univ]
  rfl

theorem lensRightCollar_source : (lensRightCollar p q hpq).source = halfCollarSource := by
  change (lensRightCover p q hpq).collar.source ∩ _ ⁻¹' univ = _
  rw [preimage_univ, inter_univ]
  rfl

theorem lensFold_lensRightCollar (y : Torus × EuclideanHalfSpace 1) (hy : y ∈ halfCollarSource) :
    lensFold p q hpq (lensRightCollar p q hpq (lensMatching p q hpq y.1, y.2)) =
      (lensLeftCover p q hpq).seam (y.1, y.2.val 0) := by
  have hy' : y.2.val 0 < 1 := hy
  have h0 : 0 ≤ y.2.val 0 := y.2.2
  exact lensRight_seamMap_lensMatching p q hpq y.1 (by linarith) hy'.le

theorem lensReversing :
    ReversesBoundaryOrientation (lensCutCarrier p q hpq) (lensLeftCollar p q hpq)
      (fun y => lensRightCollar p q hpq (lensMatching p q hpq y.1, y.2)) :=
  reversesBoundaryOrientation_of_seam (C := lensCutCarrier p q hpq) (contMDiff_lensFold p q hpq)
    (mfderiv_lensFold_bijective p q hpq) _ (orientation_map_lensCutOrientation p q hpq)
    (lensLeftCollar_source p q hpq) (lensRightCollar_source p q hpq) (lensMatching p q hpq)
    (S := (lensLeftCover p q hpq).seam) rfl (fun _ _ => rfl)
    (lensFold_lensRightCollar p q hpq)

end Lens

end GC.GraphManifold
