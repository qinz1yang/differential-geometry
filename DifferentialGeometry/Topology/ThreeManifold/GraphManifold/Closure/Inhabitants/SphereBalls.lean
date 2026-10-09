import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces
import DifferentialGeometry.Topology.Manifold.StereographicHemisphere
import DifferentialGeometry.Topology.Manifold.StereographicClosedBall
import DifferentialGeometry.Topology.Manifold.StereographicChart
import DifferentialGeometry.Topology.Manifold.StereographicCylinder
import DifferentialGeometry.Topology.Manifold.ClosedCellOrientation
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.StandardSphere

/-!
Actual closed hemisphere ball pieces and the equatorial sphere collar in the standard three-sphere.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff InnerProductSpace

universe u

namespace GC.GraphManifold.Assembly

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold
attribute [local instance] uliftChartedSpace isManifold_ulift

local instance sphereBallsDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

local instance sphereBallsConnected : ConnectedSpace (ClosedCell 3) :=
  closedCell_three_connectedSpace

local instance sphereBallsLiftConnected : ConnectedSpace (ULift.{u} (ClosedCell 3)) :=
  Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1

private def sphereBallsPole : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩

private def sphereBallsScale : E3 ≃L[ℝ] E3 :=
  (LinearEquiv.smulOfNeZero ℝ E3 (2 : ℝ) (by norm_num)).toContinuousLinearEquiv

private def sphereBallsMap (x : ClosedCell 3) : S3 :=
  (stereographic' 3 sphereBallsPole).symm (sphereBallsScale x.val)

private theorem sphereBallsMap_smooth : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ sphereBallsMap :=
  (stereographicInverse_isLocalDiffeomorph (n := 3) sphereBallsPole).contMDiff.comp
    (sphereBallsScale.contDiff.contMDiff.comp
      (isSmoothEmbedding_closedCell_inclusion 2).contMDiff)

private theorem sphereBallsMap_bijective (x : ClosedCell 3) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3) sphereBallsMap x) := by
  have hs := stereographicInverse_isLocalDiffeomorph (n := 3) sphereBallsPole
  change Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
    ((stereographic' 3 sphereBallsPole).symm ∘ (sphereBallsScale ∘ Subtype.val)) x)
  rw [mfderiv_comp x ((hs.contMDiff).mdifferentiableAt (by simp))
    ((sphereBallsScale.contDiff.contMDiff.comp
      (isSmoothEmbedding_closedCell_inclusion 2).contMDiff).mdifferentiableAt (by simp))]
  have hsc : ContMDiff (𝓡 3) (𝓡 3) ∞ sphereBallsScale :=
    sphereBallsScale.contDiff.contMDiff
  rw [mfderiv_comp x (hsc.mdifferentiableAt (by simp))
    ((isSmoothEmbedding_closedCell_inclusion 2).contMDiff.mdifferentiableAt (by simp))]
  exact ((hs (sphereBallsScale x.val)).mfderivToContinuousLinearEquiv (by simp)).bijective.comp
    (sphereBallsScale.toDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x.val).bijective
      |>.comp (closedCell_inclusion_mfderiv_bijective 2 x)

private theorem sphereBallsMap_injective : Injective sphereBallsMap :=
  ((stereographic' 3 sphereBallsPole).symm.isOpenEmbedding (by simp)).injective.comp
    (sphereBallsScale.injective.comp Subtype.val_injective)

private def sphereBallsAntipodal (b : Bool) : S3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ S3 :=
  if b then sphereAntipodalDiffeomorph else Diffeomorph.refl (𝓡 3) S3 ∞

def standardS3HemispherePiece (b : Bool) :
    PieceEmbedding (NoCuts.carrier standardThreeSphereLift.{u}) where
  Piece := ULift.{u} (ClosedCell 3)
  map := uliftDiffeomorph (𝓡 3) S3 ∘ sphereBallsAntipodal b ∘ sphereBallsMap ∘
    (uliftDiffeomorph (𝓡∂ 3) (ClosedCell 3)).symm
  smooth := (uliftDiffeomorph (𝓡 3) S3).contMDiff.comp
    ((sphereBallsAntipodal b).contMDiff.comp
      (sphereBallsMap_smooth.comp (uliftDiffeomorph (𝓡∂ 3) (ClosedCell 3)).symm.contMDiff))
  mfderiv_bijective x := by
    let D := (uliftDiffeomorph (𝓡∂ 3) (ClosedCell 3)).symm
    let A := sphereBallsAntipodal b
    let L := uliftDiffeomorph (𝓡 3) S3
    change Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (L ∘ A ∘ sphereBallsMap ∘ D) x)
    rw [mfderiv_comp x (L.contMDiff.mdifferentiableAt (by simp))
      ((A.contMDiff.comp (sphereBallsMap_smooth.comp D.contMDiff)).mdifferentiableAt (by simp)),
      mfderiv_comp x (A.contMDiff.mdifferentiableAt (by simp))
        ((sphereBallsMap_smooth.comp D.contMDiff).mdifferentiableAt (by simp)),
      mfderiv_comp x (sphereBallsMap_smooth.mdifferentiableAt (by simp))
        (D.contMDiff.mdifferentiableAt (by simp))]
    exact (L.mfderivToContinuousLinearEquiv (by simp) (A (sphereBallsMap (D x)))).bijective.comp
      ((A.mfderivToContinuousLinearEquiv (by simp) (sphereBallsMap (D x))).bijective.comp
        ((sphereBallsMap_bijective (D x)).comp
          (D.mfderivToContinuousLinearEquiv (by simp) x).bijective))
  injective := (uliftDiffeomorph (𝓡 3) S3).injective.comp
    ((sphereBallsAntipodal b).injective.comp
      (sphereBallsMap_injective.comp (uliftDiffeomorph (𝓡∂ 3) (ClosedCell 3)).symm.injective))

def standardS3HemisphereBall (b : Bool) :
    (standardS3HemispherePiece.{u} b).Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 :=
  (uliftDiffeomorph (𝓡∂ 3) (ClosedCell 3)).symm

private theorem sphereBallsStereo_height (x : E3) :
    (((stereographic' 3 sphereBallsPole).symm x).val : E4) 0 =
      (‖x‖ ^ 2 + 4)⁻¹ * (‖x‖ ^ 2 - 4) := by
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 3
    (ne_zero_of_mem_unit_sphere sphereBallsPole)).repr
  have ho : inner ℝ (sphereBallsPole : E4) (U.symm x : E4) = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (U.symm x).property
  have hn : ‖(U.symm x : E4)‖ = ‖x‖ := U.symm.norm_map x
  have hh (y : E4) : inner ℝ (sphereBallsPole : E4) y = y 0 := by
    simp [sphereBallsPole, EuclideanSpace.inner_single_left]
  rw [← hh, stereographic'_symm_apply]
  change inner ℝ (sphereBallsPole : E4)
    ((‖(U.symm x : E4)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (U.symm x : E4) +
      (‖(U.symm x : E4)‖ ^ 2 + 4)⁻¹ •
        (‖(U.symm x : E4)‖ ^ 2 - 4) • sphereBallsPole.val) = _
  rw [hn]
  simp only [inner_add_right, inner_smul_right, ho, mul_zero, zero_add]
  have hp : inner ℝ (sphereBallsPole : E4) sphereBallsPole = 1 := by
    simp [sphereBallsPole]
  rw [hp, mul_one]

private theorem sphereBallsMap_range :
    range sphereBallsMap = (stereographic' 3 sphereBallsPole).symm ''
      Metric.closedBall (0 : E3) 2 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(2 : ℝ) • x.val, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs]
    norm_num
    linarith [x.property]
  · rintro ⟨x, hx, rfl⟩
    have hn : ‖x‖ ≤ 2 := mem_closedBall_zero_iff.mp hx
    let z : ClosedCell 3 := ⟨(2 : ℝ)⁻¹ • x, by
      rw [norm_smul, Real.norm_eq_abs]
      norm_num
      linarith⟩
    refine ⟨z, ?_⟩
    change (stereographic' 3 sphereBallsPole).symm ((2 : ℝ) • ((2 : ℝ)⁻¹ • x)) = _
    rw [smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0)]

private theorem sphereBallsMap_hemisphere :
    range sphereBallsMap = {x : S3 | (x.val : E4) 0 ≤ 0} := by
  rw [sphereBallsMap_range]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (((stereographic' 3 sphereBallsPole).symm x).val : E4) 0 ≤ 0
    rw [sphereBallsStereo_height]
    have hn : ‖x‖ ≤ 2 := mem_closedBall_zero_iff.mp hx
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (by positivity))
      (by nlinarith [norm_nonneg x])
  · intro hy
    have hne : y ≠ sphereBallsPole := by
      intro he
      subst y
      norm_num [sphereBallsPole] at hy
    let x := stereographic' 3 sphereBallsPole y
    have hx : (stereographic' 3 sphereBallsPole).symm x = y :=
      (stereographic' 3 sphereBallsPole).left_inv
        (by simpa only [stereographic'_source, mem_compl_iff, mem_singleton_iff] using hne)
    refine ⟨x, ?_, hx⟩
    change (y.val : E4) 0 ≤ 0 at hy
    rw [← hx, sphereBallsStereo_height] at hy
    have hi : 0 < (‖x‖ ^ 2 + 4)⁻¹ := inv_pos.mpr (by positivity)
    have hs : ‖x‖ ^ 2 - 4 ≤ 0 := by nlinarith
    rw [mem_closedBall_zero_iff]
    nlinarith [norm_nonneg x]

theorem standardS3HemispherePiece_range (b : Bool) :
    range (standardS3HemispherePiece.{u} b).map =
      {x | if b then 0 ≤ (x.down.val : E4) 0 else (x.down.val : E4) 0 ≤ 0} := by
  have hmap : range (standardS3HemispherePiece.{u} b).map =
      ULift.up '' ((sphereBallsAntipodal b) '' range sphereBallsMap) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨sphereBallsAntipodal b (sphereBallsMap x.down),
        ⟨sphereBallsMap x.down, ⟨x.down, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, ⟨w, rfl⟩, rfl⟩, rfl⟩
      exact ⟨ULift.up w, rfl⟩
  rw [hmap, sphereBallsMap_hemisphere]
  cases b
  · ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact hz
    · intro hx
      exact ⟨x.down, ⟨x.down, hx, rfl⟩, rfl⟩
  · ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      change (z.val : E4) 0 ≤ 0 at hz
      change 0 ≤ -(z.val : E4) 0
      exact neg_nonneg.mpr hz
    · intro hx
      change 0 ≤ (x.down.val : E4) 0 at hx
      refine ⟨x.down, ⟨-x.down, ?_, ?_⟩, rfl⟩
      · change -(x.down.val : E4) 0 ≤ 0
        exact neg_nonpos.mpr hx
      · change -(-x.down) = x.down
        exact neg_neg x.down

theorem exists_standardS3HemisphereBall :
    ∃ P : PieceEmbedding (NoCuts.carrier standardThreeSphereLift.{u}),
      Nonempty (P.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) ∧
        range P.map = {x | (x.down.val : E4) 0 ≤ 0} :=
  ⟨standardS3HemispherePiece false, ⟨standardS3HemisphereBall false⟩,
    standardS3HemispherePiece_range false⟩

def standardS3EquatorMap (z : ClosureSphere.{u}) :
    (NoCuts.carrier standardThreeSphereLift.{u}).Carrier :=
  ULift.up ((stereographic' 3 sphereBallsPole).symm ((2 : ℝ) • z.down.val))

def standardS3Equator : Set (NoCuts.carrier standardThreeSphereLift.{u}).Carrier :=
  range standardS3EquatorMap

private theorem sphereBallsMap_height_zero {x : ClosedCell 3} :
    (sphereBallsMap x).val 0 = 0 ↔ ‖x.val‖ = 1 := by
  change (((stereographic' 3 sphereBallsPole).symm ((2 : ℝ) • x.val)).val : E4) 0 = 0 ↔ _
  rw [sphereBallsStereo_height]
  have hn : ‖(2 : ℝ) • x.val‖ = 2 * ‖x.val‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
  rw [hn, mul_eq_zero]
  have hi : ((2 * ‖x.val‖) ^ 2 + 4)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  simp only [hi, false_or]
  constructor <;> intro h <;> nlinarith [norm_nonneg x.val]

private theorem sphereBallsPiece_height_zero {b : Bool}
    {x : (standardS3HemispherePiece.{u} b).Piece} :
    ((standardS3HemispherePiece b).map x).down.val 0 = 0 ↔ ‖x.down.val‖ = 1 := by
  cases b
  · exact sphereBallsMap_height_zero (x := x.down)
  · change -(sphereBallsMap x.down).val 0 = 0 ↔ _
    rw [neg_eq_zero]
    exact sphereBallsMap_height_zero (x := x.down)

theorem standardS3Equator_eq :
    standardS3Equator.{u} = {x | (x.down.val : E4) 0 = 0} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    change (sphereBallsMap (⟨z.down.val, (norm_eq_of_mem_sphere z.down).le⟩ :
      ClosedCell 3)).val 0 = 0
    exact (sphereBallsMap_height_zero).mpr (norm_eq_of_mem_sphere z.down)
  · intro hy
    have hm : y ∈ range (standardS3HemispherePiece.{u} false).map := by
      rw [standardS3HemispherePiece_range]
      exact le_of_eq hy
    obtain ⟨x, rfl⟩ := hm
    have hn : ‖x.down.val‖ = 1 := (sphereBallsPiece_height_zero (b := false) (x := x)).mp hy
    exact ⟨ULift.up ⟨x.down.val, mem_sphere_zero_iff_norm.mpr hn⟩, rfl⟩

theorem standardS3HemispherePiece_boundary (b : Bool) :
    (standardS3HemispherePiece.{u} b).map ''
      (𝓡∂ 3).boundary (standardS3HemispherePiece b).Piece = standardS3Equator := by
  have hboundary (x : (standardS3HemispherePiece.{u} b).Piece) :
      (𝓡∂ 3).IsBoundaryPoint x ↔ ‖x.down.val‖ = 1 := by
    have h := ((standardS3HemisphereBall b).isLocalDiffeomorph x).isBoundaryPoint_iff
      (by simp)
    change (𝓡∂ 3).IsBoundaryPoint x ↔ _
    rw [h]
    change x.down ∈ (𝓡∂ 3).boundary (ClosedCell 3) ↔ _
    rw [closedCell_boundary_eq_sphere]
    rfl
  rw [standardS3Equator_eq]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (sphereBallsPiece_height_zero (b := b) (x := x)).mpr ((hboundary x).mp hx)
  · intro hy
    have hm : y ∈ range (standardS3HemispherePiece.{u} b).map := by
      rw [standardS3HemispherePiece_range]
      change (y.down.val : E4) 0 = 0 at hy
      cases b
      · exact hy.le
      · exact hy.ge
    obtain ⟨x, rfl⟩ := hm
    exact ⟨x, (hboundary x).mpr ((sphereBallsPiece_height_zero (b := b) (x := x)).mp hy), rfl⟩

private theorem sphereBallsEquator_injective : Injective standardS3EquatorMap.{u} := by
  intro z w h
  have he := congrArg ULift.down h
  have hc := ((stereographic' 3 sphereBallsPole).symm.isOpenEmbedding (by simp)).injective he
  have hv := (smul_right_injective E3 (by norm_num : (2 : ℝ) ≠ 0)) hc
  exact ULift.ext (Subtype.ext hv)

def standardS3EquatorHomeomorph :
    standardS3Equator.{u} ≃ₜ Metric.sphere (0 : E3) 1 := by
  have hscale : Continuous (fun z : ClosureSphere.{u} => (2 : ℝ) • z.down.val) :=
    (continuous_subtype_val.comp continuous_uliftDown).const_smul (2 : ℝ)
  have hc : Continuous standardS3EquatorMap.{u} :=
    continuous_uliftUp.comp ((stereographicInverse_isLocalDiffeomorph
      (n := 3) sphereBallsPole).contMDiff.continuous.comp hscale)
  exact (hc.isClosedEmbedding sphereBallsEquator_injective).isEmbedding.toHomeomorph.symm.trans
    Homeomorph.ulift

private def sphereBallsCylinderParameters :
    (ClosureSphere.{u} × ℝ) ≃ₘ⟮sphereSignedCollarModel, (𝓡 2).prod 𝓘(ℝ)⟯
      (Metric.sphere (0 : E3) 1 × ℝ) where
  toFun p := (p.1.down, Real.log 2 + p.2)
  invFun p := (ULift.up p.1, p.2 - Real.log 2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  contMDiff_toFun := ((uliftDiffeomorph (𝓡 2) (Metric.sphere (0 : E3) 1)).symm.contMDiff.comp
    contMDiff_fst).prodMk (contMDiff_const.add contMDiff_snd)
  contMDiff_invFun := ((uliftDiffeomorph (𝓡 2) (Metric.sphere (0 : E3) 1)).contMDiff.comp
    contMDiff_fst).prodMk (contMDiff_snd.sub contMDiff_const)

def standardS3SphereTubeMap (p : ClosureSphere.{u} × ℝ) :
    (NoCuts.carrier standardThreeSphereLift.{u}).Carrier :=
  uliftDiffeomorph (𝓡 3) S3
    (stereographicCylinderMap sphereBallsPole (sphereBallsCylinderParameters p))

private theorem sphereBallsTube_local :
    IsLocalDiffeomorph sphereSignedCollarModel (𝓡 3) ∞ standardS3SphereTubeMap.{u} := by
  intro p
  exact ((sphereBallsCylinderParameters.isLocalDiffeomorph p).comp _ _
    (stereographicCylinderMap_isLocalDiffeomorph sphereBallsPole
      (sphereBallsCylinderParameters p))).comp _ _
        ((uliftDiffeomorph (𝓡 3) S3).isLocalDiffeomorph _)

private theorem sphereBallsTube_injective : Injective standardS3SphereTubeMap.{u} :=
  (uliftDiffeomorph (𝓡 3) S3).injective.comp
    ((stereographicCylinderMap_isOpenEmbedding sphereBallsPole).injective.comp
      sphereBallsCylinderParameters.injective)

private theorem sphereBallsTube_exists :
    ∃ D : PartialDiffeomorph sphereSignedCollarModel (𝓡 3)
        (ClosureSphere.{u} × ℝ) (NoCuts.carrier standardThreeSphereLift.{u}).Carrier ∞,
      D.source = sphereSignedCollarSource ∧
        ∀ p, D p = standardS3SphereTubeMap p := by
  have ho : IsOpen (sphereSignedCollarSource : Set (ClosureSphere.{u} × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  let z : ClosureSphere.{u} := ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩
  have hn : (sphereSignedCollarSource : Set (ClosureSphere.{u} × ℝ)).Nonempty :=
    ⟨(z, 0), ⟨mem_univ z, by constructor <;> norm_num⟩⟩
  obtain ⟨D, hD, ht, he⟩ :=
    (sphereBallsTube_local.isLocalDiffeomorphOn _).exists_partialDiffeomorph_of_injOn
      ho hn sphereBallsTube_injective.injOn
  exact ⟨D, hD, fun p => congrFun he p⟩

def standardS3EquatorSeam : SphereSeam (NoCuts.carrier standardThreeSphereLift.{u}) where
  collar := sphereBallsTube_exists.choose
  source_eq := sphereBallsTube_exists.choose_spec.1
  target_interior := by
    intro y hy
    exact BoundarylessManifold.isInteriorPoint

theorem standardS3EquatorSeam_apply (p : ClosureSphere.{u} × ℝ) :
    standardS3EquatorSeam.collar p = standardS3SphereTubeMap p :=
  sphereBallsTube_exists.choose_spec.2 p

theorem standardS3SphereTubeMap_formula (z : ClosureSphere.{u}) (s : ℝ) :
    standardS3SphereTubeMap (z, s) = ULift.up
      ((stereographic' 3 sphereBallsPole).symm ((2 * Real.exp s) • z.down.val)) := by
  change ULift.up ((stereographic' 3 sphereBallsPole).symm
    (Real.exp (Real.log 2 + s) • z.down.val)) = _
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem standardS3EquatorSeam_zero (z : ClosureSphere.{u}) :
    standardS3EquatorSeam.collar (z, 0) = standardS3EquatorMap z := by
  rw [standardS3EquatorSeam_apply, standardS3SphereTubeMap_formula]
  simp only [Real.exp_zero, mul_one]
  rfl

private theorem sphereBallsPiece_image (b : Bool) :
    range (standardS3HemispherePiece.{u} b).map =
      (Homeomorph.ulift.symm : S3 ≃ₜ ULift.{u} S3) ''
        ((sphereBallsAntipodal b) ''
          ((stereographic' 3 sphereBallsPole).symm '' closedBall (0 : E3) 2)) := by
  rw [← sphereBallsMap_range]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨sphereBallsAntipodal b (sphereBallsMap x.down),
      ⟨sphereBallsMap x.down, ⟨x.down, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, ⟨w, rfl⟩, rfl⟩, rfl⟩
    exact ⟨ULift.up w, rfl⟩

theorem standardS3HemispherePiece_interiors_disjoint :
    Disjoint (interior (range (standardS3HemispherePiece.{u} false).map))
      (interior (range (standardS3HemispherePiece.{u} true).map)) := by
  let L : S3 ≃ₜ (NoCuts.carrier standardThreeSphereLift.{u}).Carrier :=
    Homeomorph.ulift.symm
  have hfalse : range (standardS3HemispherePiece.{u} false).map =
      L '' ((stereographic' 3 sphereBallsPole).symm '' closedBall (0 : E3) 2) := by
    rw [sphereBallsPiece_image]
    change L '' (id '' _) = L '' _
    rw [image_id]
  have htrue : range (standardS3HemispherePiece.{u} true).map =
      L '' (Neg.neg '' ((stereographic' 3 sphereBallsPole).symm '' closedBall (0 : E3) 2)) := by
    rw [sphereBallsPiece_image]
    rfl
  have hneg : Neg.neg '' ((stereographic' 3 sphereBallsPole).symm '' closedBall (0 : E3) 2) =
      ((stereographic' 3 sphereBallsPole).symm '' ball (0 : E3) 2)ᶜ := by
    convert antipodal_image_stereographic_symm_closedBall sphereBallsPole
      (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  rw [hfalse, ← L.image_interior, interior_image_stereographic_symm_closedBall
    sphereBallsPole (by norm_num : (2 : ℝ) ≠ 0), htrue, hneg, L.image_compl]
  exact disjoint_compl_right.mono_right interior_subset

theorem standardS3HemispherePiece_cover :
    range (standardS3HemispherePiece.{u} false).map ∪
      range (standardS3HemispherePiece.{u} true).map = univ := by
  rw [standardS3HemispherePiece_range, standardS3HemispherePiece_range]
  ext y
  change ((y.down.val : E4) 0 ≤ 0 ∨ 0 ≤ (y.down.val : E4) 0) ↔ True
  exact iff_true_intro (le_total _ _)

theorem standardS3EquatorSeam_neg (z : ClosureSphere.{u}) (s : ℝ) (hs : s ≤ 0) :
    standardS3EquatorSeam.collar (z, s) ∈ range (standardS3HemispherePiece.{u} false).map := by
  rw [standardS3EquatorSeam_apply, standardS3SphereTubeMap_formula,
    standardS3HemispherePiece_range]
  change (((stereographic' 3 sphereBallsPole).symm ((2 * Real.exp s) • z.down.val)).val : E4)
    0 ≤ 0
  rw [sphereBallsStereo_height]
  have hn : ‖(2 * Real.exp s) • z.down.val‖ = 2 * Real.exp s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      norm_eq_of_mem_sphere, mul_one]
  rw [hn]
  have he : Real.exp s ≤ 1 := Real.exp_le_one_iff.mpr hs
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (by nlinarith [Real.exp_pos s])

theorem standardS3EquatorSeam_pos (z : ClosureSphere.{u}) (s : ℝ) (hs : 0 ≤ s) :
    standardS3EquatorSeam.collar (z, s) ∈ range (standardS3HemispherePiece.{u} true).map := by
  rw [standardS3EquatorSeam_apply, standardS3SphereTubeMap_formula,
    standardS3HemispherePiece_range]
  change 0 ≤ (((stereographic' 3 sphereBallsPole).symm ((2 * Real.exp s) • z.down.val)).val : E4)
    0
  rw [sphereBallsStereo_height]
  have hn : ‖(2 * Real.exp s) • z.down.val‖ = 2 * Real.exp s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      norm_eq_of_mem_sphere, mul_one]
  rw [hn]
  have he : 1 ≤ Real.exp s := Real.one_le_exp_iff.mpr hs
  exact mul_nonneg (by positivity) (by nlinarith)

end GC.GraphManifold.Assembly
