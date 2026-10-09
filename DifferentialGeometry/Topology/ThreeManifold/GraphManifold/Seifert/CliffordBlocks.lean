import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TwoSolidTori
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Sphere
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# The Clifford solid tori as K06 blocks

`unitDiscPlanarBase : PlanarBase 1` is the closed unit disc `unitDiscSurface` with the embedding
`w ↦ 3 w` onto the K06 model `planarModel 1 = closedBall 0 3` (the inclusion of the regular
sublevel set composed with the scaling diffeomorphism `scaleThree`). Its collar
`cliffordDiscCollar` is read off the solid-torus collar through `solidTorusDiscCircle`:
`cliffordDiscCollarMap (t, s)` is the disc coordinate of `solidTorusCollar ((t, 1), s)`, which is
`√2 seamFirst (-s) t` (`cliffordDiscCollarMap_val`), equal to `t` at height `0`; the disc
coordinate does not depend on the second circle and the circle coordinate is the second circle
(`solidTorusDiscCircle_solidTorusCollar`), so `solidTorusCollar` is `cliffordDiscCollar × id` under
`solidTorusDiscCircle` (`solidTorusCollar_eq_symm`). The boundary of the disc is its unit circle
(`unitDisc_isBoundaryPoint_iff`).

Both pieces of the Clifford presentation `cliffordTorusPresentation` of the three-sphere are copies
of `solidTorusSet` in the cut carrier, with collars `Sum.inl ∘ solidTorusCollar` and
`Sum.inr ∘ solidTorusCollar` (the exchange of the circle factors only enters the gluing), so the
trivialisations `cliffordPieceTrivialization` make both solid-torus pieces
(`cliffordLeftSolidTorus`, `cliffordRightSolidTorus`) with the collar equality as above. By
`isPrime_of_twoSolidTori` the standard three-sphere is prime and has cyclic π₁ at every point
(`isPrime_standardThreeSphereLift_of_twoSolidTori`,
`isCyclic_fundamentalGroup_standardThreeSphereLift_of_twoSolidTori`).
-/

set_option autoImplicit false

noncomputable section
open Set Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

theorem solidTorusDiscCircle_apply (p : solidTorusSet.{u}) :
    solidTorusDiscCircle p = (discOfSolidTorus p, unitOf (sphereSecond p.val)) := rfl

theorem discOfSolidTorus_solidTorusCollar (v w : Circle) (h : EuclideanHalfSpace 1) :
    (discOfSolidTorus (solidTorusCollar.{u} ((v, w), h))).down.val =
      ((√2 : ℝ) * seamFirst (-h.val 0)) • (v : ℂ) := by
  rw [discOfSolidTorus_val, solidTorusCollar_apply, solidTorusCollarMap_val]
  change (√2 : ℝ) • sphereFirst (cliffordSeamMap ((v, w), -h.val 0)) = _
  rw [sphereFirst_cliffordSeamMap, smul_smul]

theorem solidTorusDiscCircle_solidTorusCollar (v w : Circle) (h : EuclideanHalfSpace 1) :
    solidTorusDiscCircle (solidTorusCollar.{u} ((v, w), h)) =
      ((solidTorusDiscCircle (solidTorusCollar.{u} ((v, 1), h))).1, w) := by
  refine Prod.ext ?_ ?_
  · apply ULift.ext
    apply Subtype.ext
    change (discOfSolidTorus (solidTorusCollar.{u} ((v, w), h))).down.val =
      (discOfSolidTorus (solidTorusCollar.{u} ((v, 1), h))).down.val
    rw [discOfSolidTorus_solidTorusCollar, discOfSolidTorus_solidTorusCollar]
  · change unitOf (sphereSecond (cliffordSeamMap ((v, w), -h.val 0))) = w
    rw [sphereSecond_cliffordSeamMap]
    exact unitOf_smul (seamSecond_pos (by linarith [h.2])) w

def cliffordDiscCollarMap (q : Circle × EuclideanHalfSpace 1) : UnitDisc.{u} :=
  (solidTorusDiscCircle (solidTorusCollar.{u} ((q.1, 1), q.2))).1

def cliffordDiscCollarInv (w : UnitDisc.{u}) : Circle × EuclideanHalfSpace 1 :=
  ((solidTorusCollar.{u}.symm (solidTorusDiscCircle.symm (w, 1))).1.1,
    (solidTorusCollar.{u}.symm (solidTorusDiscCircle.symm (w, 1))).2)

theorem cliffordDiscCollarMap_val (q : Circle × EuclideanHalfSpace 1) :
    (cliffordDiscCollarMap.{u} q).down.val = ((√2 : ℝ) * seamFirst (-q.2.val 0)) • (q.1 : ℂ) :=
  discOfSolidTorus_solidTorusCollar q.1 1 q.2

theorem solidTorusCollar_eq_symm (v w : Circle) (h : EuclideanHalfSpace 1) :
    solidTorusCollar.{u} ((v, w), h) =
      solidTorusDiscCircle.symm (cliffordDiscCollarMap (v, h), w) := by
  rw [← solidTorusDiscCircle.symm_apply_apply (solidTorusCollar.{u} ((v, w), h)),
    solidTorusDiscCircle_solidTorusCollar]
  rfl

theorem sphereFirst_solidTorusDiscCircle_symm (w : UnitDisc.{u}) (v : Circle) :
    sphereFirst (solidTorusDiscCircle.symm (w, v)).val = (√2 : ℝ)⁻¹ • w.down.val := by
  change sphereFirst (solidTorusOfDiscCircle (w, v)).val = _
  simp only [solidTorusOfDiscCircle, sphereFirst_sphereOfPair]

def cliffordDiscCollar : PartialDiffeomorph circleCollarModel (𝓡∂ 2) (Circle × EuclideanHalfSpace 1)
    UnitDisc.{u} ∞ where
  toFun := cliffordDiscCollarMap
  invFun := cliffordDiscCollarInv
  source := circleCollarSource
  target := {w | w.down.val ≠ 0}
  map_source' := by
    intro q hq
    change (cliffordDiscCollarMap q).down.val ≠ 0
    rw [cliffordDiscCollarMap_val]
    have hq' : q.2.val 0 < 1 := hq
    exact smul_ne_zero (mul_pos (by positivity) (seamFirst_pos (by linarith))).ne'
      (Circle.coe_ne_zero _)
  map_target' := by
    intro w hw
    have hmem : solidTorusDiscCircle.symm (w, 1) ∈ solidTorusCollar.{u}.target := by
      change sphereFirst (solidTorusDiscCircle.symm (w, 1)).val ≠ 0
      rw [sphereFirst_solidTorusDiscCircle_symm]
      exact smul_ne_zero (by positivity) hw
    exact solidTorusCollar.{u}.map_target' hmem
  left_inv' := by
    rintro ⟨v, h⟩ hq
    have hq' : ((v, (1 : Circle)), h) ∈ solidTorusCollar.{u}.source := hq
    change cliffordDiscCollarInv (cliffordDiscCollarMap (v, h)) = (v, h)
    have e : solidTorusCollar.{u}.symm (solidTorusCollar ((v, 1), h)) = ((v, 1), h) :=
      solidTorusCollar.{u}.left_inv' hq'
    unfold cliffordDiscCollarInv
    rw [← solidTorusCollar_eq_symm, e]
  right_inv' := by
    intro w hw
    have hmem : solidTorusDiscCircle.symm (w, 1) ∈ solidTorusCollar.{u}.target := by
      change sphereFirst (solidTorusDiscCircle.symm (w, 1)).val ≠ 0
      rw [sphereFirst_solidTorusDiscCircle_symm]
      exact smul_ne_zero (by positivity) hw
    set q := solidTorusCollar.{u}.symm (solidTorusDiscCircle.symm (w, 1)) with hq
    have hr : solidTorusCollar.{u} q = solidTorusDiscCircle.symm (w, 1) :=
      solidTorusCollar.{u}.right_inv' hmem
    change cliffordDiscCollarMap (q.1.1, q.2) = w
    have h := congrArg (fun p => (solidTorusDiscCircle p).1) hr
    simp only [Diffeomorph.apply_symm_apply] at h
    rw [← h]
    obtain ⟨⟨a, b⟩, c⟩ := q
    exact (congrArg Prod.fst (solidTorusDiscCircle_solidTorusCollar a b c)).symm
  open_source := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
  open_target := isOpen_ne_fun contMDiff_disc_val.continuous continuous_const
  contMDiffOn_toFun := by
    have hincl : ContMDiff circleCollarModel halfCollarModel ∞
        (fun q : Circle × EuclideanHalfSpace 1 => ((q.1, (1 : Circle)), q.2)) :=
      (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
    exact contMDiff_fst.comp_contMDiffOn (solidTorusDiscCircle.contMDiff.comp_contMDiffOn
      (solidTorusCollar.{u}.contMDiffOn.comp hincl.contMDiffOn fun q hq => hq))
  contMDiffOn_invFun := by
    have hpair : ContMDiff (𝓡∂ 2) ((𝓡∂ 2).prod (𝓡 1)) ∞
        (fun w : UnitDisc.{u} => (w, (1 : Circle))) := contMDiff_id.prodMk contMDiff_const
    have h := solidTorusCollar.{u}.symm.contMDiffOn.comp
      (solidTorusDiscCircle.symm.contMDiff.comp hpair).contMDiffOn (s := {w | w.down.val ≠ 0})
      fun w hw => by
        change sphereFirst (solidTorusDiscCircle.symm (w, 1)).val ≠ 0
        rw [sphereFirst_solidTorusDiscCircle_symm]
        exact smul_ne_zero (by positivity) hw
    exact (contMDiff_fst.comp contMDiff_fst).comp_contMDiffOn h |>.prodMk
      (contMDiff_snd.comp_contMDiffOn h)

theorem sqrt_two_mul_seamFirst_zero : (√2 : ℝ) * seamFirst (-0) = 1 := by
  rw [neg_zero, seamFirst, seamClamp_of_mem (by norm_num) (by norm_num),
    ← Real.sqrt_mul (by norm_num)]
  norm_num

theorem cliffordDiscCollarMap_zero_val (t : Circle) :
    (cliffordDiscCollarMap.{u} (t, halfZero)).down.val = t := by
  rw [cliffordDiscCollarMap_val]
  change ((√2 : ℝ) * seamFirst (-0)) • (t : ℂ) = t
  rw [sqrt_two_mul_seamFirst_zero, one_smul]

theorem unitDisc_isBoundaryPoint_iff (w : UnitDisc.{u}) :
    (𝓡∂ 2).IsBoundaryPoint w ↔ ‖w.down.val‖ ^ 2 = 1 :=
  (((uliftDiffeomorph (𝓡∂ 2) unitDiscSet).isLocalDiffeomorph w.down).isBoundaryPoint_iff
    (by simp)).symm.trans
    (SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff 𝓘(ℝ, ℂ) (n := 1)
      Complex.finrank_real_complex (contDiff_norm_sq ℝ).contMDiff 1 unitDisc_normSq_regular
      w.down)

theorem cliffordDiscCollarMap_zero_isBoundaryPoint (t : Circle) :
    (𝓡∂ 2).IsBoundaryPoint (cliffordDiscCollarMap.{u} (t, halfZero)) := by
  rw [unitDisc_isBoundaryPoint_iff, cliffordDiscCollarMap_zero_val, Circle.norm_coe, one_pow]

def scaleThree : ℂ ≃L[ℝ] ℂ :=
  (LinearEquiv.smulOfUnit (Units.mk0 (3 : ℝ) (by norm_num))).toContinuousLinearEquiv

def unitDiscPlanarBase : PlanarBase.{u} 1 where
  surface := unitDiscSurface
  collar _ := cliffordDiscCollar
  source_eq _ := rfl
  boundary_zero _ t := cliffordDiscCollarMap_zero_isBoundaryPoint t
  disjoint i j h := (h (Subsingleton.elim i j)).elim
  boundary_exhausted := by
    ext w
    simp only [mem_iUnion, mem_range]
    constructor
    · intro hw
      have hw' := (unitDisc_isBoundaryPoint_iff w).1 hw
      have hn : ‖w.down.val‖ = 1 := by
        have h0 := norm_nonneg w.down.val
        nlinarith
      refine ⟨0, ⟨w.down.val, mem_sphere_zero_iff_norm.2 hn⟩, ?_⟩
      apply ULift.ext
      apply Subtype.ext
      exact cliffordDiscCollarMap_zero_val _
    · rintro ⟨j, t, rfl⟩
      exact cliffordDiscCollarMap_zero_isBoundaryPoint t
  embedding w := (3 : ℝ) • w.down.val
  isSmoothEmbedding := by
    have h1 : Manifold.IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞ (Subtype.val : unitDiscSet → ℂ) :=
      SmoothBoundaryAtlas.isSmoothEmbedding_subtype_val unitDiscAtlas
    exact (h1.comp_diffeomorph (uliftDiffeomorph (𝓡∂ 2) unitDiscSet :
      unitDiscSet ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ UnitDisc.{u}).symm).diffeomorph_comp scaleThree.toDiffeomorph
  range_embedding := by
    rw [planarModel_one]
    ext z
    simp only [mem_range, mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨w, rfl⟩
      have hw : ‖w.down.val‖ ^ 2 ≤ 1 := w.down.2
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      nlinarith [norm_nonneg w.down.val]
    · intro hz
      have hmem : (3 : ℝ)⁻¹ • z ∈ unitDiscSet := by
        change ‖(3 : ℝ)⁻¹ • z‖ ^ 2 ≤ 1
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3⁻¹)]
        nlinarith [norm_nonneg z]
      refine ⟨ULift.up ⟨(3 : ℝ)⁻¹ • z, hmem⟩, ?_⟩
      change (3 : ℝ) • (3 : ℝ)⁻¹ • z = z
      rw [smul_smul, mul_inv_cancel₀ (by norm_num), one_smul]
  embedding_collar j t := by
    obtain rfl : j = 0 := Subsingleton.elim _ _
    change (3 : ℝ) • (cliffordDiscCollarMap.{u} (t, halfZero)).down.val = _
    rw [cliffordDiscCollarMap_zero_val]
    simp [planarCircleMap, planarCenter, planarRadius, Complex.real_smul]

abbrev cliffordTorusPresentation : TorusPresentation (NoCuts.carrier standardThreeSphereLift.{u}) :=
  standardThreeSphereLiftRawGraphPresentation.toTorusPresentation

def cliffordLeftPort :
    Fin 1 ≃ cliffordTorusPresentation.{u}.OwnedSide ⟨0, Nat.zero_lt_two⟩ where
  toFun _ := ⟨.inl ⟨0, Nat.zero_lt_one⟩, rfl⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv s := by
    obtain ⟨k | k | k, hs⟩ := s
    · exact Subtype.ext (congrArg Sum.inl (Fin.ext (Nat.lt_one_iff.mp (k.isLt : k.val < 1)).symm))
    · exact absurd (congrArg Fin.val hs : (1 : ℕ) = 0) one_ne_zero
    · exact k.elim0

def cliffordRightPort :
    Fin 1 ≃ cliffordTorusPresentation.{u}.OwnedSide ⟨1, Nat.one_lt_two⟩ where
  toFun _ := ⟨.inr (.inl ⟨0, Nat.zero_lt_one⟩), rfl⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv s := by
    obtain ⟨k | k | k, hs⟩ := s
    · exact absurd (congrArg Fin.val hs : (0 : ℕ) = 1) zero_ne_one
    · exact Subtype.ext (congrArg (Sum.inr ∘ Sum.inl)
        (Fin.ext (Nat.lt_one_iff.mp (k.isLt : k.val < 1)).symm))
    · exact k.elim0

def cliffordLeftSolidTorus :
    SolidTorusPiece cliffordTorusPresentation.{u} ⟨0, Nat.zero_lt_two⟩ where
  base := unitDiscPlanarBase
  port := cliffordLeftPort
  trivialization := (cliffordPieceTrivialization ⟨0, Nat.zero_lt_two⟩).symm
  collar_eq j p hp := by
    obtain rfl : j = 0 := Subsingleton.elim _ _
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
    change Sum.inl (solidTorusCollar p) =
      Sum.inl (solidTorusDiscCircle.symm (cliffordDiscCollarMap (p.1.1, p.2), p.1.2))
    obtain ⟨⟨v, w⟩, h⟩ := p
    exact congrArg Sum.inl (solidTorusCollar_eq_symm v w h)

def cliffordRightSolidTorus :
    SolidTorusPiece cliffordTorusPresentation.{u} ⟨1, Nat.one_lt_two⟩ where
  base := unitDiscPlanarBase
  port := cliffordRightPort
  trivialization := (cliffordPieceTrivialization ⟨1, Nat.one_lt_two⟩).symm
  collar_eq j p hp := by
    obtain rfl : j = 0 := Subsingleton.elim _ _
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
    change Sum.inr (solidTorusCollar p) =
      Sum.inr (solidTorusDiscCircle.symm (cliffordDiscCollarMap (p.1.1, p.2), p.1.2))
    obtain ⟨⟨v, w⟩, h⟩ := p
    exact congrArg Sum.inr (solidTorusCollar_eq_symm v w h)

def cliffordSolidTorusPiece : (i : Fin 2) → SolidTorusPiece cliffordTorusPresentation.{u} i
  | ⟨0, _⟩ => cliffordLeftSolidTorus
  | ⟨1, _⟩ => cliffordRightSolidTorus

theorem isPrime_standardThreeSphereLift_of_twoSolidTori : IsPrime standardThreeSphereLift.{u} :=
  isPrime_of_twoSolidTori cliffordTorusPresentation rfl cliffordSolidTorusPiece

theorem isCyclic_fundamentalGroup_standardThreeSphereLift_of_twoSolidTori
    (p : standardThreeSphereLift.{u}.Carrier) :
    IsCyclic (FundamentalGroup standardThreeSphereLift.{u}.Carrier p) :=
  have := isCyclic_fundamentalGroup_of_twoSolidTori cliffordTorusPresentation.{u} rfl
    cliffordSolidTorusPiece
  isCyclic_of_surjective (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
    (cliffordTorusPresentation.seamTorus ⟨0, Nat.zero_lt_one⟩ torusBase) p) (MulEquiv.surjective _)

end GC.Seifert
