import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeProof
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CliffordBlocks
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct

import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.AnnulusLongCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BundleOverAnnulus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockCharts

/-!
# Concrete systems and trivial product refinements

Product pieces retain their full external collars under the trivial piece refinement.
The examples distinguish the general closed-base cut system from planar elementary pieces.
A radial annulus fold gives an actual old self-seam on three circles, with two distinct ports.
-/

set_option autoImplicit false

noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)

def elementaryTrivialPieceSystem (i : Fin E.toTorus.components.count) :
    EmbeddedPieceSystem (E.toTorus.Component i) where
  count := 1
  count_pos := Nat.one_pos
  kind j := E.kind i
  kind_mem j := E.kind_mem i
  base j := (E.piece i).base
  map j := (E.piece i).trivialization
  smooth j := (E.piece i).trivialization.contMDiff
  mfderiv_bijective j q := bijective_mfderiv_of_isLocalDiffeomorphAt
    ((E.piece i).trivialization.isLocalDiffeomorph q)
  covers := eq_univ_of_forall fun q =>
    mem_iUnion.2 ⟨⟨0, Nat.one_pos⟩, (E.piece i).trivialization.surjective q⟩
  seamCount := 0
  side c := c.elim0
  externalCount := E.kind i
  externalSide l := ⟨⟨0, Nat.one_pos⟩, l⟩
  sides_bijective := by
    constructor
    · rintro (⟨c, b⟩ | l) (⟨c', b'⟩ | l') hs
      · exact c.elim0
      · exact c.elim0
      · exact c'.elim0
      · simp only [Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hs
        rw [hs]
    · rintro ⟨j, l⟩
      exact ⟨.inr l, by rw [Subsingleton.elim j ⟨0, Nat.one_pos⟩]; rfl⟩
  matching c := c.elim0
  seam c := c.elim0
  seam_source c := c.elim0
  seam_neg c := c.elim0
  seam_pos c := c.elim0
  seam_interior c := c.elim0
  external_local l t := (E.piece i).trivialization.isLocalDiffeomorph
    ((E.piece i).base.collar l (t.1, halfZero), t.2)
  overlap j j' q q' hs := by
    left
    obtain rfl : j = j' := Subsingleton.elim j j'
    rw [(E.piece i).trivialization.injective hs]

def elementaryTrivialPieceRefinement : E.toTorus.PieceRefinement where
  system := elementaryTrivialPieceSystem E
  port i := (E.piece i).port
  port_collar i l p hp := by
    change ((E.piece i).trivialization
      ((E.piece i).base.collar l (p.1.1, p.2), p.1.2)).val = _
    rw [← (E.piece i).collar_eq l p hp]
    exact E.toTorus.pieceCollar_apply i ((E.piece i).port l) hp

def elementaryTrivialPresentation : ElementaryPresentation W :=
  (elementaryTrivialPieceRefinement E).toProductRefinement.toElementaryPresentation

theorem elementaryTrivialPieceRefinement_seam (c : Fin E.toTorus.pairing.count) :
    (elementaryTrivialPieceRefinement E).toProductRefinement.toElementaryPresentation.toTorus.seam
      (finSumFinEquiv (.inr c)) = E.toTorus.seam c :=
  (elementaryTrivialPieceRefinement E).toProductRefinement.toRefinement.splice_seam_old c

theorem elementaryTrivialPieceRefinement_collar (m : Fin E.toTorus.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (elementaryTrivialPresentation E).toTorus.external.collar m p =
      E.toTorus.external.collar m p :=
  (elementaryTrivialPieceRefinement E).toProductRefinement.toElementaryPresentation_external_collar
    m hp


theorem elementaryTrivialPieceRefinement_counts :
    (elementaryTrivialPresentation E).toTorus.components.count = E.toTorus.components.count ∧
      (elementaryTrivialPresentation E).toTorus.pairing.count = E.toTorus.pairing.count ∧
      (elementaryTrivialPresentation E).toTorus.externalCount = E.toTorus.externalCount := by
  change (∑ i : Fin E.toTorus.components.count, 1) = E.toTorus.components.count ∧
    (∑ i : Fin E.toTorus.components.count, 0) + E.toTorus.pairing.count =
      E.toTorus.pairing.count ∧ E.toTorus.externalCount = E.toTorus.externalCount
  simp

def elementarySubCollarPresentation : ElementaryPresentation W :=
  E.toTorus.recollarReparam (fun _s => Diffeomorph.refl torusModel Torus ∞)
    E.kind E.kind_mem (fun i => (E.piece i).base) (fun i => (E.piece i).port)
    (fun i => (E.piece i).trivialization) one_pos le_rfl
    (fun i j p hp _hlt => (E.piece i).collar_eq j p hp)

theorem elementarySubCollar_pieceRefinement :
    ∃ (ψ : E.toRaw.toTorusPresentation.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
      Nonempty ((E.toRaw.toTorusPresentation.reparam ψ).shrink hδ hδ1).PieceRefinement := by
  refine ⟨fun _s => Diffeomorph.refl torusModel Torus ∞, 1, one_pos, le_rfl, ?_⟩
  exact ⟨elementaryTrivialPieceRefinement (elementarySubCollarPresentation E)⟩

theorem elementaryTrivialPieceRefinement_zero (m : Fin E.toTorus.externalCount) (t : Torus) :
    (elementaryTrivialPresentation E).toTorus.external.collar m (t, halfZero) =
      E.toTorus.external.collar m (t, halfZero) :=
  elementaryTrivialPieceRefinement_collar E m (zero_mem_halfCollarSource t)

namespace ElementarizeSelfSeam

abbrev Target := Torus × Circle

abbrev targetModel := torusModel.prod (𝓡 1)

def productCoordinates (m n : ℕ) :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m + n)) :=
  ((EuclideanSpace.equiv (Fin m) ℝ).prodCongr (EuclideanSpace.equiv (Fin n) ℝ)).trans
    (((LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin n) ℝ ℝ).symm
      ).toContinuousLinearEquiv.trans
      ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _i : Fin (m + n) => ℝ)
        (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))).trans
          (EuclideanSpace.equiv (Fin (m + n)) ℝ).symm))

def targetCoordinates :
    ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((productCoordinates 1 1).prodCongr (ContinuousLinearEquiv.refl ℝ _)).trans
    (productCoordinates 2 1)

abbrev targetCopy :=
  DifferentialGeometry.Geometry.Topology.standardModelCopy (I := targetModel) (M := Target)
    targetCoordinates

def targetOrientation : ManifoldOrientation targetModel Target 3 :=
  productOrientation torusModel (𝓡 1) (by norm_num) le_rfl
    productTorusOrientation circleOrientation

abbrev carrier : CompactCarrier where
  kind := .closed
  Carrier := targetCopy.Q
  charts := targetCopy.charted
  smooth := targetCopy.mfld
  compact := targetCopy.equiv.toHomeomorph.compactSpace
  secondCountable := targetCopy.equiv.symm.toHomeomorph.secondCountableTopology
  orientation := Manifold.manifoldOrientationPullback (𝓡 3) targetModel (by simp)
    targetCopy.equiv.symm targetCopy.equiv.symm.contMDiff
    (fun x =>
      ((targetCopy.equiv.symm.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv
        (by simp)).bijective) targetOrientation

def radialPhase (z : ℂ) : ℝ := (‖z‖ - 1 / 2) / (5 / 2)

def fold (q : planarSet.{u} 2 × Circle) : Target :=
  ((unitOf q.1.val.down, q.2), AnnulusStraightening.cexp (radialPhase q.1.val.down))

def seamMap (p : Torus × ℝ) : Target :=
  (p.1, AnnulusStraightening.cexp (p.2 / 10))

def collar (j : Fin 2) (p : Torus × EuclideanHalfSpace 1) :
    planarSet.{u} 2 × Circle :=
  (planarCollar 2 (Or.inl rfl) j (p.1.1, p.2), p.1.2)

def matching : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus := torusInvFirst

theorem fold_collar_outer (t : Torus) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    fold.{u} (collar 0 (t, halfPoint s hs)) =
      (t, AnnulusStraightening.cexp (-s / 10)) := by
  have hv := planarCollarMap_val.{u} (Or.inl rfl) (0 : Fin 2)
    (p := (t.1, halfPoint s hs)) (by exact hs1)
  change (planarCollar.{u} 2 (Or.inl rfl) 0 (t.1, halfPoint s hs)).val.down = _ at hv
  simp only [halfPoint_val_zero] at hv
  have hr : 0 < (3 : ℝ) - s / 4 := by linarith
  have hz : (planarCollar.{u} 2 (Or.inl rfl) 0 (t.1, halfPoint s hs)).val.down =
      (3 - s / 4) • (t.1 : ℂ) := by
    simpa [planarCollarFormula, planarCenter, planarRadius, planarSign, planarTwist,
      sub_eq_add_neg, neg_div] using hv
  dsimp only [fold, collar, matching, torusInvFirst_apply]
  change ((unitOf _, t.2), AnnulusStraightening.cexp (radialPhase _)) = _
  rw [hz, unitOf_smul hr]
  congr 1
  rw [radialPhase, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le]
  have he : ((3 - s / 4) - 1 / 2) / (5 / 2) = -s / 10 + (1 : ℤ) := by
    push_cast
    ring
  rw [he, AnnulusStraightening.cexp_add_int]

theorem fold_collar_inner (t : Torus) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    fold.{u} (collar 1 (matching t, halfPoint s hs)) =
      (t, AnnulusStraightening.cexp (s / 10)) := by
  have hv := planarCollarMap_val.{u} (Or.inl rfl) (1 : Fin 2)
    (p := (t.1⁻¹, halfPoint s hs)) (by exact hs1)
  change (planarCollar.{u} 2 (Or.inl rfl) 1 (t.1⁻¹, halfPoint s hs)).val.down = _ at hv
  simp only [halfPoint_val_zero] at hv
  have hr : 0 < (1 / 2 : ℝ) + s / 4 := by linarith
  have hz : (planarCollar.{u} 2 (Or.inl rfl) 1 (t.1⁻¹, halfPoint s hs)).val.down =
      (1 / 2 + s / 4) • (t.1 : ℂ) := by
    simp only [planarCollarFormula, planarCenter_two, Complex.ofReal_zero, zero_add,
      planarRadius, planarSign, planarTwist, Fin.val_one, one_ne_zero, ↓reduceIte,
      one_mul] at hv
    rw [Circle.coe_inv_eq_conj, Complex.conj_conj] at hv
    exact hv
  dsimp only [fold, collar, matching, torusInvFirst_apply]
  change ((unitOf _, t.2), AnnulusStraightening.cexp (radialPhase _)) = _
  rw [hz, unitOf_smul hr]
  congr 1
  rw [radialPhase, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le]
  congr 1
  ring

theorem seam_negative (t : Torus) {s : ℝ} (hs : s ≤ 0) (hs1 : -1 < s) :
    seamMap (t, s) = fold.{u} (collar 0 (t, halfPoint (-s) (neg_nonneg.mpr hs))) := by
  rw [fold_collar_outer t (neg_nonneg.mpr hs) (by linarith)]
  simp [seamMap]

theorem seam_positive (t : Torus) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    seamMap (t, s) = fold.{u} (collar 1 (matching t, halfPoint s hs)) := by
  rw [fold_collar_inner t hs hs1]
  rfl

theorem seam_zero (t : Torus) : seamMap (t, 0) = (t, 1) := by
  simp [seamMap, AnnulusStraightening.cexp_zero]

theorem fold_smooth :
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) targetModel ∞ fold.{u} := by
  intro q
  have hne : q.1.val.down ≠ 0 := by
    have h := planarSet_two_ne_zero (0 : Fin 2) q.1
    simpa only [planarCenter_two, Complex.ofReal_zero, sub_zero] using h
  have hd : ContMDiff ((𝓡∂ 2).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun q : planarSet.{u} 2 × Circle => q.1.val.down) :=
    (contMDiff_planarSet_down 2).comp contMDiff_fst
  have hu := (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp q
    hd.contMDiffAt
  have hn := (contDiffAt_norm ℝ hne).contMDiffAt.comp q hd.contMDiffAt
  have hp : ContMDiffAt ((𝓡∂ 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun q : planarSet.{u} 2 × Circle => radialPhase q.1.val.down) q :=
    (hn.sub contMDiffAt_const).div_const (5 / 2 : ℝ)
  exact (hu.prodMk contMDiffAt_snd).prodMk
    ((AnnulusStraightening.isLocalDiffeomorph_cexp _).contMDiffAt.comp q hp)

def phaseDiffeomorph : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toFun s := (s + 1) / 5
  invFun s := 5 * s - 1
  left_inv s := by dsimp; ring
  right_inv s := by dsimp; ring
  contMDiff_toFun := ((contDiff_id.add contDiff_const).div_const 5).contMDiff
  contMDiff_invFun := ((contDiff_const.mul contDiff_id).sub contDiff_const).contMDiff

def phaseMap (p : Torus × ℝ) : Target :=
  (p.1, AnnulusStraightening.cexp ((p.2 + 1) / 5))

theorem phaseMap_local : IsLocalDiffeomorph signedCollarModel targetModel ∞ phaseMap :=
  (Diffeomorph.refl torusModel Torus ∞).isLocalDiffeomorph.prodMap
    (DifferentialGeometry.isLocalDiffeomorph_comp
      AnnulusStraightening.isLocalDiffeomorph_cexp phaseDiffeomorph.isLocalDiffeomorph)

def ambientFold (q : ℂ × Circle) : Target := phaseMap (chartPolar 1 q)

theorem ambientFold_eq (q : planarSet.{u} 2 × Circle) :
    ambientFold (q.1.val.down, q.2) = fold q := by
  dsimp [ambientFold, phaseMap, chartPolar, fold, radialPhase, seamDepth]
  rw [norm_mul, Complex.norm_ofNat]
  congr 2
  simp only [pow_one, ULift.norm_def]
  ring

theorem ambientFold_local {q : ℂ × Circle} (hne : q.1 ≠ 0) :
    IsLocalDiffeomorphAt PlaneCircleModel targetModel ∞ ambientFold q :=
  _root_.IsLocalDiffeomorphAt.comp targetModel Target
    ((chartPolar 1).isLocalDiffeomorphAt PlaneCircleModel signedCollarModel ∞ hne)
    (phaseMap_local (chartPolar 1 q))

def planeDown (z : planarSet.{u} 2) : ℂ := z.val.down

theorem planeDown_bijective (z : planarSet.{u} 2) :
    Function.Bijective (mfderiv (𝓡∂ 2) 𝓘(ℝ, ℂ) planeDown z) := by
  let d : ℂ ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ PlaneLift.{u} := uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ
  have hdown := d.symm.isLocalDiffeomorph z.val
  have hd : (d.symm : PlaneLift.{u} → ℂ) = ULift.down := rfl
  rw [hd] at hdown
  have hval := (planarAtlas 2).mfderiv_subtypeVal_bijective z
  change Function.Bijective (mfderiv (𝓡∂ 2) 𝓘(ℝ, ℂ)
    (ULift.down ∘ (Subtype.val : planarSet.{u} 2 → PlaneLift.{u})) z)
  rw [mfderiv_comp z (hdown.mdifferentiableAt (by simp))
    ((planarAtlas 2).contMDiff_subtype_val.mdifferentiableAt (by simp))]
  exact ((hdown.mfderivToContinuousLinearEquiv (by simp)).bijective).comp hval

theorem fold_mfderiv_bijective (q : planarSet.{u} 2 × Circle) :
    Function.Bijective (mfderiv ((𝓡∂ 2).prod (𝓡 1)) targetModel fold q) := by
  have hne : q.1.val.down ≠ 0 := by
    have h := planarSet_two_ne_zero (0 : Fin 2) q.1
    simpa only [planarCenter_two, Complex.ofReal_zero, sub_zero] using h
  have hl := ambientFold_local (q := (q.1.val.down, q.2)) hne
  have hm : MDifferentiableAt ((𝓡∂ 2).prod (𝓡 1)) PlaneCircleModel
      (Prod.map planeDown id) q :=
    ((contMDiff_planarSet_down 2).mdifferentiableAt (by simp)).prodMap
      mdifferentiableAt_id
  have he : fold.{u} = ambientFold ∘ Prod.map planeDown id :=
    funext fun q => (ambientFold_eq q).symm
  have hpd : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ, ℂ) planeDown q.1 :=
    (contMDiff_planarSet_down 2).mdifferentiableAt (by simp)
  rw [he, mfderiv_comp q (hl.mdifferentiableAt (by simp)) hm,
    mfderiv_prodMap hpd
      mdifferentiableAt_id, mfderiv_id]
  exact ((hl.mfderivToContinuousLinearEquiv (by simp)).bijective).comp
    ((planeDown_bijective q.1).prodMap Function.bijective_id)

theorem radialPhase_bounds (z : planarSet.{u} 2) :
    0 ≤ radialPhase z.val.down ∧ radialPhase z.val.down ≤ 1 := by
  have hz := (mem_planarSet_iff (Or.inl rfl) z.val).mp z.property
  rw [mem_planarModel_two] at hz
  dsimp only [radialPhase]
  constructor <;> linarith

theorem fold_overlap (q q' : planarSet.{u} 2 × Circle) (he : fold q = fold q') :
    q = q' ∨ ∃ t : Torus, fold q = seamMap (t, 0) := by
  have hu : unitOf q.1.val.down = unitOf q'.1.val.down :=
    congrArg (fun p : Target => p.1.1) he
  have hf : q.2 = q'.2 := congrArg (fun p : Target => p.1.2) he
  have ht : AnnulusStraightening.cexp (radialPhase q.1.val.down) =
      AnnulusStraightening.cexp (radialPhase q'.1.val.down) := congrArg Prod.snd he
  by_cases hp : radialPhase q.1.val.down = radialPhase q'.1.val.down
  · left
    have hn : ‖q.1.val.down‖ = ‖q'.1.val.down‖ := by
      dsimp only [radialPhase] at hp
      linarith
    apply Prod.ext _ hf
    apply Subtype.ext
    apply ULift.ext
    calc
      q.1.val.down = ‖q.1.val.down‖ • (unitOf q.1.val.down : ℂ) :=
        (norm_smul_unitOf q.1.val.down).symm
      _ = ‖q'.1.val.down‖ • (unitOf q'.1.val.down : ℂ) := by rw [hu, hn]
      _ = q'.1.val.down := norm_smul_unitOf q'.1.val.down
  · obtain ⟨n, hn⟩ := AnnulusStraightening.cexp_eq_cexp_iff.mp ht
    have hb := radialPhase_bounds q.1
    have hb' := radialPhase_bounds q'.1
    have hlo : (-1 : ℝ) ≤ n := by linarith
    have hhi : (n : ℝ) ≤ 1 := by linarith
    have hlo' : (-1 : ℤ) ≤ n := by exact_mod_cast hlo
    have hhi' : n ≤ (1 : ℤ) := by exact_mod_cast hhi
    have hne : n ≠ 0 := by
      intro hz
      rw [hz, Int.cast_zero, add_zero] at hn
      exact hp hn
    have hc : n = -1 ∨ n = 1 := by omega
    have hp' : radialPhase q.1.val.down = 0 ∨ radialPhase q.1.val.down = 1 := by
      rcases hc with hneg | hpos
      · rw [hneg] at hn
        left
        norm_num at hn
        linarith
      · rw [hpos] at hn
        right
        norm_num at hn
        linarith
    right
    refine ⟨(unitOf q.1.val.down, q.2), ?_⟩
    rw [seam_zero]
    change ((unitOf q.1.val.down, q.2),
      AnnulusStraightening.cexp (radialPhase q.1.val.down)) = _
    congr 1
    rcases hp' with hzero | hone
    · rw [hzero, AnnulusStraightening.cexp_zero]
    · rw [hone]
      simpa only [Int.cast_one] using AnnulusStraightening.cexp_int 1

theorem fold_surjective : Function.Surjective fold.{u} := by
  rintro ⟨t, w⟩
  obtain ⟨v, hv⟩ := AnnulusStraightening.cexp_surjective w
  let r : ℝ := 1 / 2 + (5 / 2) * Int.fract v
  have hr : 0 < r := by
    dsimp only [r]
    linarith [Int.fract_nonneg v]
  have hn : ‖r • (t.1 : ℂ)‖ = r := by
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le]
  have hmem : r • (t.1 : ℂ) ∈ planarModel 2 := by
    rw [mem_planarModel_two, hn]
    dsimp only [r]
    constructor <;> linarith [Int.fract_nonneg v, Int.fract_lt_one v]
  let z : planarSet.{u} 2 :=
    ⟨ULift.up (r • (t.1 : ℂ)), (mem_planarSet_iff (Or.inl rfl) _).mpr hmem⟩
  refine ⟨(z, t.2), ?_⟩
  change ((unitOf (r • (t.1 : ℂ)), t.2),
    AnnulusStraightening.cexp (radialPhase (r • (t.1 : ℂ)))) = (t, w)
  rw [unitOf_smul hr]
  congr 1
  have hphase : radialPhase (r • (t.1 : ℂ)) = Int.fract v := by
    rw [radialPhase, hn]
    dsimp only [r]
    ring
  rw [hphase]
  have he : Int.fract v = v + ((-⌊v⌋ : ℤ) : ℝ) := by
    simp [Int.fract, sub_eq_add_neg]
  rw [he, AnnulusStraightening.cexp_add_int, hv]

def side (c : Fin 1) (b : Bool) : Σ _j : Fin 1, Fin 2 :=
  ⟨c, if b then 0 else 1⟩

theorem side_bijective : Function.Bijective (Function.uncurry side) := by decide

def seamPhaseDiffeomorph : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toFun s := s / 10
  invFun s := 10 * s
  left_inv s := by dsimp; ring
  right_inv s := by dsimp; ring
  contMDiff_toFun := (contDiff_id.div_const 10).contMDiff
  contMDiff_invFun := (contDiff_const.mul contDiff_id).contMDiff

theorem seamMap_local : IsLocalDiffeomorph signedCollarModel targetModel ∞ seamMap :=
  (Diffeomorph.refl torusModel Torus ∞).isLocalDiffeomorph.prodMap
    (DifferentialGeometry.isLocalDiffeomorph_comp
      AnnulusStraightening.isLocalDiffeomorph_cexp seamPhaseDiffeomorph.isLocalDiffeomorph)

theorem seamMap_injOn : Set.InjOn seamMap signedCollarSource := by
  rintro ⟨t, s⟩ hs ⟨t', s'⟩ hs' he
  have htt : t = t' := congrArg Prod.fst he
  have hphase : AnnulusStraightening.cexp (s / 10) =
      AnnulusStraightening.cexp (s' / 10) := congrArg Prod.snd he
  obtain ⟨n, hn⟩ := AnnulusStraightening.cexp_eq_cexp_iff.mp hphase
  have hlo : (-1 : ℝ) < n := by
    change -1 < s ∧ s < 1 at hs
    change -1 < s' ∧ s' < 1 at hs'
    linarith
  have hhi : (n : ℝ) < 1 := by
    change -1 < s ∧ s < 1 at hs
    change -1 < s' ∧ s' < 1 at hs'
    linarith
  have hlo' : (-1 : ℤ) < n := by exact_mod_cast hlo
  have hhi' : n < (1 : ℤ) := by exact_mod_cast hhi
  have hnzero : n = 0 := by omega
  rw [hnzero, Int.cast_zero, add_zero] at hn
  exact Prod.ext htt (by linarith)

def actualFold (q : planarSet 2 × Circle) : carrier.Carrier := targetCopy.equiv (fold q)

def actualSeamMap (p : Torus × ℝ) : carrier.Carrier := targetCopy.equiv (seamMap p)

theorem actualSeamMap_local :
    IsLocalDiffeomorph signedCollarModel carrier.model ∞ actualSeamMap :=
  DifferentialGeometry.isLocalDiffeomorph_comp targetCopy.equiv.isLocalDiffeomorph seamMap_local

theorem actualSeamMap_injOn : Set.InjOn actualSeamMap signedCollarSource :=
  fun _p hp _p' hp' he => seamMap_injOn hp hp' (targetCopy.equiv.injective he)

theorem exists_actualSeam : ∃ Φ : PartialDiffeomorph signedCollarModel carrier.model
    (Torus × ℝ) carrier.Carrier ∞,
    Φ.source = signedCollarSource ∧ Φ.target = actualSeamMap '' signedCollarSource ∧
      Φ.toFun = actualSeamMap := by
  apply IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (actualSeamMap_local.isLocalDiffeomorphOn signedCollarSource)
    isOpen_signedCollarSource'
  · exact ⟨((1, 1), 0), by constructor <;> norm_num⟩
  · exact actualSeamMap_injOn

def actualSeam : PartialDiffeomorph signedCollarModel carrier.model
    (Torus × ℝ) carrier.Carrier ∞ := Classical.choose exists_actualSeam

theorem actualSeam_source : actualSeam.source = signedCollarSource :=
  (Classical.choose_spec exists_actualSeam).1

theorem actualSeam_apply (p : Torus × ℝ) : actualSeam p = actualSeamMap p :=
  congrFun (Classical.choose_spec exists_actualSeam).2.2 p

theorem actualFold_smooth :
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) carrier.model ∞ actualFold :=
  targetCopy.equiv.contMDiff.comp fold_smooth

theorem actualFold_mfderiv_bijective (q : planarSet 2 × Circle) :
    Function.Bijective (mfderiv ((𝓡∂ 2).prod (𝓡 1)) carrier.model actualFold q) := by
  change Function.Bijective (mfderiv ((𝓡∂ 2).prod (𝓡 1)) carrier.model
    (targetCopy.equiv ∘ fold) q)
  rw [mfderiv_comp q (targetCopy.equiv.contMDiff.mdifferentiableAt (by simp))
    (fold_smooth.mdifferentiableAt (by simp))]
  exact ((targetCopy.equiv.isLocalDiffeomorph (fold q)).mfderivToContinuousLinearEquiv
    (by simp)).bijective.comp (fold_mfderiv_bijective q)

theorem actualSeam_neg (t : Torus) {s : ℝ} (hs : s ≤ 0) (hs1 : -1 < s) :
    actualSeam (t, s) = actualFold (collar.{0} 0 (t, halfPoint (-s) (neg_nonneg.mpr hs))) := by
  rw [actualSeam_apply]
  exact congrArg targetCopy.equiv (seam_negative t hs hs1)

theorem actualSeam_pos (t : Torus) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    actualSeam (t, s) = actualFold (collar.{0} 1 (matching t, halfPoint s hs)) := by
  rw [actualSeam_apply]
  exact congrArg targetCopy.equiv (seam_positive t hs hs1)

theorem actualFold_overlap (q q' : planarSet.{0} 2 × Circle)
    (he : actualFold q = actualFold q') :
    q = q' ∨ ∃ t : Torus, actualFold q = actualSeam (t, 0) := by
  have hf : fold q = fold q' := targetCopy.equiv.injective he
  rcases fold_overlap q q' hf with hq | ⟨t, ht⟩
  · exact Or.inl hq
  · right
    refine ⟨t, ?_⟩
    rw [actualSeam_apply]
    exact congrArg targetCopy.equiv ht

def system : EmbeddedPieceSystem carrier where
  count := 1
  count_pos := Nat.one_pos
  kind i := 2
  kind_mem i := by decide
  base i := annulusPlanarBase.{0}
  map i := actualFold
  smooth i := actualFold_smooth
  mfderiv_bijective i := actualFold_mfderiv_bijective
  covers := eq_univ_of_forall fun x => by
    obtain ⟨q, hq⟩ := fold_surjective (targetCopy.equiv.symm x)
    refine mem_iUnion.mpr ⟨⟨0, Nat.one_pos⟩, q, ?_⟩
    exact (congrArg targetCopy.equiv hq).trans (targetCopy.equiv.apply_symm_apply x)
  seamCount := 1
  side := side
  externalCount := 0
  externalSide l := l.elim0
  sides_bijective := by
    constructor
    · rintro (p | l) (p' | l') he
      · exact congrArg Sum.inl (side_bijective.injective he)
      · exact l'.elim0
      · exact l.elim0
      · exact l.elim0
    · intro s
      obtain ⟨p, hp⟩ := side_bijective.surjective s
      exact ⟨Sum.inl p, hp⟩
  matching c := matching
  seam c := actualSeam
  seam_source c := actualSeam_source
  seam_neg c t s hs hs1 := actualSeam_neg t hs hs1
  seam_pos c t s hs hs1 := actualSeam_pos t hs hs1
  seam_interior c x hx := BoundarylessManifold.isInteriorPoint
  external_local l := l.elim0
  overlap j j' q q' he := by
    obtain rfl : j = j' := Subsingleton.elim j j'
    rcases actualFold_overlap q q' he with hq | ⟨t, ht⟩
    · left
      exact congrArg (Sigma.mk j) hq
    · right
      refine ⟨⟨0, Nat.one_pos⟩, t, ?_⟩
      exact ht

end ElementarizeSelfSeam

def acceptanceSelfSeamSystem : EmbeddedPieceSystem ElementarizeSelfSeam.carrier :=
  ElementarizeSelfSeam.system

def acceptanceSelfSeam : ElementaryPresentation ElementarizeSelfSeam.carrier :=
  acceptanceSelfSeamSystem.toElementaryPresentation

def acceptanceSelfSeamRefinement : acceptanceSelfSeam.toTorus.PieceRefinement :=
  elementaryTrivialPieceRefinement acceptanceSelfSeam

theorem acceptanceSelfSeam_counts :
    acceptanceSelfSeam.toTorus.components.count = 1 ∧
      acceptanceSelfSeam.toTorus.pairing.count = 1 ∧
      acceptanceSelfSeam.toTorus.externalCount = 0 := ⟨rfl, rfl, rfl⟩

theorem acceptanceSelfSeam_owner (c : Fin 1) :
    acceptanceSelfSeam.toTorus.leftPiece c = acceptanceSelfSeam.toTorus.rightPiece c := rfl

theorem acceptanceSelfSeam_ports_distinct (c : Fin 1) :
    acceptanceSelfSeamSystem.side c true ≠ acceptanceSelfSeamSystem.side c false :=
  acceptanceSelfSeamSystem.toCutSystem.side_ne c

theorem acceptanceSelfSeam_matching (c : Fin 1) :
    acceptanceSelfSeam.toTorus.pairing.matching c = torusInvFirst := rfl

theorem acceptanceSelfSeam_seam (c : Fin 1) :
    acceptanceSelfSeam.toTorus.seam c = ElementarizeSelfSeam.actualSeam := rfl

theorem acceptanceSelfSeam_negative (c : Fin 1) (t : Torus) {s : ℝ}
    (hs : s ≤ 0) (hs1 : -1 < s) :
    acceptanceSelfSeam.toTorus.seam c (t, s) = ElementarizeSelfSeam.actualFold
      (ElementarizeSelfSeam.collar 0 (t, halfPoint (-s) (neg_nonneg.mpr hs))) :=
  ElementarizeSelfSeam.actualSeam_neg t hs hs1

theorem acceptanceSelfSeam_positive (c : Fin 1) (t : Torus) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) :
    acceptanceSelfSeam.toTorus.seam c (t, s) = ElementarizeSelfSeam.actualFold
      (ElementarizeSelfSeam.collar 1 (torusInvFirst t, halfPoint s hs)) :=
  ElementarizeSelfSeam.actualSeam_pos t hs hs1

theorem acceptanceSelfSeam_zero_fibre (c : Fin 1) (t : Torus) :
    acceptanceSelfSeamSystem.toCutSystem.fold
        (acceptanceSelfSeamSystem.toCutSystem.leftPt c t) =
      acceptanceSelfSeamSystem.toCutSystem.fold
        (acceptanceSelfSeamSystem.toCutSystem.rightPt c t) :=
  (acceptanceSelfSeamSystem.toCutSystem.fold_leftPt c t).trans
    (acceptanceSelfSeamSystem.toCutSystem.fold_rightPt c t).symm

theorem acceptanceSelfSeam_refinement_counts :
    (elementaryTrivialPresentation acceptanceSelfSeam).toTorus.components.count = 1 ∧
      (elementaryTrivialPresentation acceptanceSelfSeam).toTorus.pairing.count = 1 ∧
      (elementaryTrivialPresentation acceptanceSelfSeam).toTorus.externalCount = 0 :=
  elementaryTrivialPieceRefinement_counts acceptanceSelfSeam

theorem acceptanceSelfSeam_refinement_seam (c : Fin 1) :
    (elementaryTrivialPresentation acceptanceSelfSeam).toTorus.seam
      (finSumFinEquiv (.inr c)) = ElementarizeSelfSeam.actualSeam :=
  elementaryTrivialPieceRefinement_seam acceptanceSelfSeam c

theorem acceptanceSelfSeam_refinement_matching (c : Fin 1) :
    (elementaryTrivialPresentation acceptanceSelfSeam).toTorus.pairing.matching
      (finSumFinEquiv (.inr c)) = torusInvFirst :=
  acceptanceSelfSeamRefinement.toProductRefinement.toRefinement.splice_matching_old c

theorem acceptanceSelfSeam_refinement_piece_counts
    (i : Fin acceptanceSelfSeam.toTorus.components.count) :
    (acceptanceSelfSeamRefinement.system i).count = 1 ∧
      (acceptanceSelfSeamRefinement.system i).seamCount = 0 ∧
      (acceptanceSelfSeamRefinement.system i).externalCount = 2 := ⟨rfl, rfl, rfl⟩

def acceptanceClifford : ElementaryPresentation (NoCuts.carrier standardThreeSphereLift.{u}) where
  toTorus := cliffordTorusPresentation
  kind i := 1
  kind_mem i := by decide
  piece := cliffordSolidTorusPiece

def acceptanceCliffordSystem := acceptanceClifford.{u}.toPieceSystem

theorem acceptanceClifford_counts :
    acceptanceCliffordSystem.{u}.toElementaryPresentation.toTorus.components.count = 2 ∧
      acceptanceCliffordSystem.{u}.toElementaryPresentation.toTorus.pairing.count = 1 ∧
      acceptanceCliffordSystem.{u}.toElementaryPresentation.toTorus.externalCount = 0 := by
  exact ⟨rfl, rfl, rfl⟩

theorem acceptanceClifford_seam (c : Fin 1) :
    acceptanceCliffordSystem.{u}.toElementaryPresentation.toTorus.seam c =
      cliffordTorusPresentation.{u}.seam c := rfl

def acceptanceMobius : ElementaryPresentation mobiusBundleCarrier.{u} where
  toTorus := mobiusPresentation
  kind := Fin.cases 3 (fun m => 1)
  kind_mem i := by
    fin_cases i <;> decide
  piece := Fin.cases mobiusProductPiece mobiusSolidPiece

def acceptanceMobiusSystem := acceptanceMobius.{u}.toPieceSystem

theorem acceptanceMobius_counts :
    acceptanceMobiusSystem.{u}.toElementaryPresentation.toTorus.components.count = 3 ∧
      acceptanceMobiusSystem.{u}.toElementaryPresentation.toTorus.pairing.count = 2 ∧
      acceptanceMobiusSystem.{u}.toElementaryPresentation.toTorus.externalCount = 1 := by
  exact ⟨rfl, rfl, rfl⟩

theorem acceptanceMobius_collar (m : Fin 1) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    acceptanceMobiusSystem.{u}.toElementaryPresentation.toTorus.external.collar m p =
      mobiusPresentation.{u}.external.collar m p :=
  acceptanceMobius.toPieceSystem_external_collar m hp

def acceptanceAnnulus : ElementaryPresentation annulusCircleCarrier.{u} where
  toTorus := annulusCirclePresentation
  kind i := 2
  kind_mem i := by decide
  piece i := by
    obtain rfl : i = ⟨0, Nat.one_pos⟩ :=
      @Subsingleton.elim (Fin 1) inferInstance i ⟨0, Nat.one_pos⟩
    exact annulusCirclePiece

def acceptanceAnnulusSystem := acceptanceAnnulus.{u}.toPieceSystem

theorem acceptanceAnnulus_counts :
    acceptanceAnnulusSystem.{u}.toElementaryPresentation.toTorus.components.count = 1 ∧
      acceptanceAnnulusSystem.{u}.toElementaryPresentation.toTorus.pairing.count = 0 ∧
      acceptanceAnnulusSystem.{u}.toElementaryPresentation.toTorus.externalCount = 2 := by
  exact ⟨rfl, rfl, rfl⟩

def acceptanceClosedBaseSystem :=
  sphereTwoTimesCircleRawGraphPresentation.toTorusPresentation.cutSystem

theorem acceptanceClosedBase_counts :
    acceptanceClosedBaseSystem.toTorusPresentation.components.count = 1 ∧
      acceptanceClosedBaseSystem.toTorusPresentation.pairing.count = 0 ∧
      acceptanceClosedBaseSystem.toTorusPresentation.externalCount = 0 := by
  exact ⟨rfl, rfl, rfl⟩

def acceptanceCliffordRefinement := elementaryTrivialPieceRefinement acceptanceClifford.{u}

def acceptanceMobiusRefinement := elementaryTrivialPieceRefinement acceptanceMobius.{u}

def acceptanceAnnulusRefinement := elementaryTrivialPieceRefinement acceptanceAnnulus.{u}

def acceptanceExternalSystem := elementaryTrivialPieceSystem acceptanceClifford.{u} (0 : Fin 2)

def acceptanceExternalRefinement :=
  elementaryTrivialPieceRefinement acceptanceExternalSystem.{u}.toElementaryPresentation

theorem acceptanceExternal_counts :
    acceptanceExternalSystem.{u}.toElementaryPresentation.toTorus.components.count = 1 ∧
      acceptanceExternalSystem.{u}.toElementaryPresentation.toTorus.pairing.count = 0 ∧
      acceptanceExternalSystem.{u}.toElementaryPresentation.toTorus.externalCount = 1 := by
  exact ⟨rfl, rfl, rfl⟩

theorem acceptanceExternal_collar (m : Fin 1) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    acceptanceExternalSystem.{u}.toElementaryPresentation.toTorus.external.collar m p =
      acceptanceClifford.{u}.toTorus.pieceCollar (0 : Fin 2)
        ((acceptanceClifford.{u}.piece (0 : Fin 2)).port m) p := by
  exact (acceptanceExternalSystem.{u}.toElementaryPresentation_external_collar m p).trans
    (((acceptanceClifford.{u}.piece (0 : Fin 2)).collar_eq m p hp).symm)

theorem acceptanceClifford_two_piece_seam (c : Fin 1) :
    acceptanceCliffordSystem.{u}.toElementaryPresentation.toTorus.leftPiece c ≠
      acceptanceCliffordSystem.{u}.toElementaryPresentation.toTorus.rightPiece c := by
  change (0 : Fin 2) ≠ 1
  decide

theorem acceptanceMobius_two_piece_seam (c : Fin 2) :
    acceptanceMobiusSystem.{u}.toElementaryPresentation.toTorus.leftPiece c ≠
      acceptanceMobiusSystem.{u}.toElementaryPresentation.toTorus.rightPiece c := by
  change c.succ ≠ (0 : Fin 3)
  exact Fin.succ_ne_zero c

theorem acceptanceMobius_seam (c : Fin 2) :
    acceptanceMobiusSystem.{u}.toElementaryPresentation.toTorus.seam c =
      mobiusPresentation.{u}.seam c := rfl

theorem acceptanceClifford_ports_distinct (c : Fin 1) :
    acceptanceCliffordSystem.{u}.side c true ≠ acceptanceCliffordSystem.{u}.side c false :=
  acceptanceCliffordSystem.toCutSystem.side_ne c

theorem acceptanceMobius_ports_distinct (c : Fin 2) :
    acceptanceMobiusSystem.{u}.side c true ≠ acceptanceMobiusSystem.{u}.side c false :=
  acceptanceMobiusSystem.toCutSystem.side_ne c

theorem acceptanceClifford_matching (c : Fin 1) :
    acceptanceCliffordSystem.{u}.toElementaryPresentation.toTorus.pairing.matching c =
      cliffordTorusPresentation.{u}.pairing.matching c := rfl

theorem acceptanceMobius_matching (c : Fin 2) :
    acceptanceMobiusSystem.{u}.toElementaryPresentation.toTorus.pairing.matching c =
      mobiusPresentation.{u}.pairing.matching c := rfl

theorem acceptanceClifford_refinement_counts :
    (elementaryTrivialPresentation acceptanceClifford.{u}).toTorus.components.count = 2 ∧
      (elementaryTrivialPresentation acceptanceClifford.{u}).toTorus.pairing.count = 1 ∧
      (elementaryTrivialPresentation acceptanceClifford.{u}).toTorus.externalCount = 0 :=
  elementaryTrivialPieceRefinement_counts acceptanceClifford

theorem acceptanceMobius_refinement_counts :
    (elementaryTrivialPresentation acceptanceMobius.{u}).toTorus.components.count = 3 ∧
      (elementaryTrivialPresentation acceptanceMobius.{u}).toTorus.pairing.count = 2 ∧
      (elementaryTrivialPresentation acceptanceMobius.{u}).toTorus.externalCount = 1 :=
  elementaryTrivialPieceRefinement_counts acceptanceMobius

theorem acceptanceAnnulus_refinement_counts :
    (elementaryTrivialPresentation acceptanceAnnulus.{u}).toTorus.components.count = 1 ∧
      (elementaryTrivialPresentation acceptanceAnnulus.{u}).toTorus.pairing.count = 0 ∧
      (elementaryTrivialPresentation acceptanceAnnulus.{u}).toTorus.externalCount = 2 :=
  elementaryTrivialPieceRefinement_counts acceptanceAnnulus

theorem acceptanceAnnulus_subCollar_pieceRefinement :
    ∃ (ψ : acceptanceAnnulus.{u}.toRaw.toTorusPresentation.Side →
        (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
      Nonempty (TorusPresentation.PieceRefinement
        ((acceptanceAnnulus.toRaw.toTorusPresentation.reparam ψ).shrink hδ hδ1)) :=
  elementarySubCollar_pieceRefinement acceptanceAnnulus

theorem acceptanceClifford_zero_fibre (c : Fin 1) (t : Torus) :
    acceptanceCliffordSystem.{u}.toCutSystem.fold
        (acceptanceCliffordSystem.toCutSystem.leftPt c t) =
      acceptanceCliffordSystem.toCutSystem.fold
        (acceptanceCliffordSystem.toCutSystem.rightPt c t) :=
  (acceptanceCliffordSystem.toCutSystem.fold_leftPt c t).trans
    (acceptanceCliffordSystem.toCutSystem.fold_rightPt c t).symm

theorem acceptanceMobius_zero_fibre (c : Fin 2) (t : Torus) :
    acceptanceMobiusSystem.{u}.toCutSystem.fold
        (acceptanceMobiusSystem.toCutSystem.leftPt c t) =
      acceptanceMobiusSystem.toCutSystem.fold
        (acceptanceMobiusSystem.toCutSystem.rightPt c t) :=
  (acceptanceMobiusSystem.toCutSystem.fold_leftPt c t).trans
    (acceptanceMobiusSystem.toCutSystem.fold_rightPt c t).symm

theorem acceptanceMobius_refinement_collar (m : Fin 1) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    (elementaryTrivialPresentation acceptanceMobius.{u}).toTorus.external.collar m p =
      mobiusPresentation.{u}.external.collar m p :=
  elementaryTrivialPieceRefinement_collar acceptanceMobius m hp

theorem acceptanceClosedBase_noProductCertificate :
    ¬Nonempty acceptanceClosedBaseSystem.ProductCertificate := by
  rintro ⟨C⟩
  have hk := C.kind_mem ⟨0, Nat.one_pos⟩
  change (0 : ℕ) ∈ ({1, 2, 3} : Finset ℕ) at hk
  norm_num at hk

end GC.Seifert
