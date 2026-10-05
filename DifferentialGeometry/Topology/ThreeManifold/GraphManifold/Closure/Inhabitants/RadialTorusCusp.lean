import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusHeight
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance sphereSecondCountable_X135 : SecondCountableTopology SphereCarrier.{0} :=
  secondCountableTopology_sphereCarrier


local instance carrierCharts_CuspX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_CuspX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def cuspSet : Set SphereCarrier.{0} := {p | bandDefiner (-(1 / 4 : ℝ)) 0 p ≤ 0}

def cuspAtlas : SmoothBoundaryAtlas (𝓡 3) 3 cuspSet :=
  SmoothBoundaryAtlas.regularSublevel (𝓡 3) (n := 2) finrank_euclideanSpace_fin
    (bandDefiner_smooth (-(1 / 4 : ℝ)) 0) 0
    (bandDefiner_regular (-(1 / 4 : ℝ)) 0 (by norm_num) (by norm_num) (by norm_num))

instance cuspCharts : ChartedSpace (EuclideanHalfSpace 3) cuspSet := cuspAtlas.toChartedSpace

instance cuspSmooth : IsManifold (𝓡∂ 3) ∞ cuspSet := cuspAtlas.isManifold

instance cuspCompact : CompactSpace cuspSet :=
  isCompact_iff_compactSpace.mp
    (isClosed_le (bandDefiner_smooth (-(1 / 4 : ℝ)) 0).continuous continuous_const).isCompact

instance cuspSecondCountable : SecondCountableTopology cuspSet := inferInstance

def cuspToCarrier (p : cuspSet) : carrier.Carrier :=
  ⟨p.val, (bandDefiner_nonpos_iff (by norm_num)).mp p.property |>.2⟩

theorem cuspToCarrier_smooth : ContMDiff (𝓡∂ 3) carrier.model ∞ cuspToCarrier :=
  (solidTorusAtlas.contMDiff_iff_subtype_val cuspToCarrier).mpr cuspAtlas.contMDiff_subtype_val

theorem cuspToCarrier_injective : Injective cuspToCarrier := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg (Subtype.val : carrier.Carrier → SphereCarrier.{0}) hpq

theorem cuspToCarrier_range : range cuspToCarrier = {p | -(1 / 4 : ℝ) ≤ height p} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact (bandDefiner_nonpos_iff (by norm_num)).mp q.property |>.1
  · intro hp
    let q : cuspSet := ⟨p.val, (bandDefiner_nonpos_iff (by norm_num)).mpr ⟨hp, p.property⟩⟩
    exact ⟨q, Subtype.ext rfl⟩

theorem cuspToCarrier_mfderiv (p : cuspSet) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) cuspToCarrier p) := by
  have hw : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : carrier.Carrier → SphereCarrier.{0}) (cuspToCarrier p)) :=
    solidTorusAtlas.mfderiv_subtypeVal_bijective (cuspToCarrier p)
  have hc : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      ((Subtype.val : carrier.Carrier → SphereCarrier.{0}) ∘ cuspToCarrier) p) :=
    cuspAtlas.mfderiv_subtypeVal_bijective p
  have hchain := mfderiv_comp p (contMDiff_solidTorus_val.mdifferentiableAt (by simp))
    (cuspToCarrier_smooth.mdifferentiableAt (by simp))
  have hcomp := hchain ▸ hc
  exact Function.Bijective.of_comp_left
    (f := mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : carrier.Carrier → SphereCarrier.{0}) (cuspToCarrier p))
    (g := mfderiv (𝓡∂ 3) (𝓡∂ 3) cuspToCarrier p) hcomp hw.1

def cuspInternalPoint : cuspSet := ⟨internalPoint.val, by
  have hh : cliffordHeight internalPoint.val = -(1 / 4 : ℝ) := internalPoint_height
  change bandDefiner (-(1 / 4 : ℝ)) 0 internalPoint.val ≤ 0
  simp only [bandDefiner, hh, sub_self, zero_mul, le_refl]⟩

theorem cuspInternalPoint_map : cuspToCarrier cuspInternalPoint = internalPoint :=
  Subtype.ext rfl

theorem cusp_boundary_iff {p : cuspSet} :
    (𝓡∂ 3).IsBoundaryPoint p ↔
      cliffordHeight p.val = -(1 / 4 : ℝ) ∨ cliffordHeight p.val = 0 := by
  erw [SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓡 3) (n := 2)
    finrank_euclideanSpace_fin (bandDefiner_smooth (-(1 / 4 : ℝ)) 0) 0
    (bandDefiner_regular (-(1 / 4 : ℝ)) 0 (by norm_num) (by norm_num) (by norm_num))]
  exact bandDefiner_zero_iff

def cuspProductParam (q : Torus × Icc (0 : ℝ) 1) : Torus × ℝ :=
  (q.1, -(q.2.val / 4))

theorem cuspProductParam_source (q : Torus × Icc (0 : ℝ) 1) :
    cuspProductParam q ∈ cliffordSeam.{0}.source := by
  change -1 < -(q.2.val / 4) ∧ -(q.2.val / 4) < 1
  constructor <;> linarith [q.2.property.1, q.2.property.2]

theorem cuspProductPoint_height (q : Torus × Icc (0 : ℝ) 1) :
    cliffordHeight (cliffordSeam.{0} (cuspProductParam q)) = -(q.2.val / 4) := by
  rw [cliffordSeam_apply, cliffordHeight_cliffordSeamMap]
  exact seamClamp_of_mem (by dsimp [cuspProductParam]; linarith [q.2.property.2])
    (by dsimp [cuspProductParam]; linarith [q.2.property.1])

def cuspProductMap (q : Torus × Icc (0 : ℝ) 1) : cuspSet :=
  ⟨cliffordSeam.{0} (cuspProductParam q), by
    apply (bandDefiner_nonpos_iff (by norm_num)).mpr
    rw [cuspProductPoint_height]
    constructor <;> linarith [q.2.property.1, q.2.property.2]⟩

def cuspProductInv (p : cuspSet) : Torus × Icc (0 : ℝ) 1 :=
  ((cliffordSeamInv p.val).1, ⟨-4 * cliffordHeight p.val, by
    have h := (bandDefiner_nonpos_iff (by norm_num)).mp p.property
    constructor <;> linarith [h.1, h.2]⟩)

theorem cusp_first_ne_zero (p : cuspSet) : sphereFirst p.val ≠ 0 := by
  intro hzero
  have h := norm_sphereFirst_sq_eq p.val
  rw [hzero, norm_zero, zero_pow (by decide)] at h
  have hb := (bandDefiner_nonpos_iff (by norm_num)).mp p.property
  linarith [hb.1]

theorem cusp_second_ne_zero (p : cuspSet) : sphereSecond p.val ≠ 0 :=
  sphereSecond_ne_zero_of_mem (cuspToCarrier p).property

theorem cuspProduct_left_inv (q : Torus × Icc (0 : ℝ) 1) :
    cuspProductInv (cuspProductMap q) = q := by
  have h := cliffordSeam.{0}.left_inv' (cuspProductParam_source q)
  apply Prod.ext
  · change (cliffordSeamInv (cliffordSeam.{0} (cuspProductParam q))).1 = q.1
    exact congrArg (fun z : Torus × ℝ => z.1) h
  · apply Subtype.ext
    change -4 * cliffordHeight (cliffordSeam.{0} (cuspProductParam q)) = q.2.val
    rw [cuspProductPoint_height]
    ring

theorem cuspProduct_right_inv (p : cuspSet) : cuspProductMap (cuspProductInv p) = p := by
  apply Subtype.ext
  change cliffordSeam.{0} (cuspProductParam (cuspProductInv p)) = p.val
  have h : cuspProductParam (cuspProductInv p) = cliffordSeamInv p.val := by
    apply Prod.ext
    · rfl
    change -((-4 * cliffordHeight p.val) / 4) = cliffordHeight p.val
    ring
  rw [h]
  exact cliffordSeam.{0}.right_inv' ⟨cusp_first_ne_zero p, cusp_second_ne_zero p⟩

theorem cuspProductMap_smooth :
    ContMDiff (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) ∞ cuspProductMap := by
  apply (cuspAtlas.contMDiff_iff_subtype_val cuspProductMap).mpr
  have hs : ContMDiff (torusModel.prod (𝓡∂ 1)) signedCollarModel ∞ cuspProductParam :=
    contMDiff_fst.prodMk ((contMDiff_subtypeVal_Icc.comp contMDiff_snd).div_const 4).neg
  exact cliffordSeam.{0}.contMDiffOn_toFun.comp_contMDiff hs cuspProductParam_source

theorem cuspProductInv_smooth :
    ContMDiff (𝓡∂ 3) (torusModel.prod (𝓡∂ 1)) ∞ cuspProductInv := by
  have hfirst : ContMDiff (𝓡∂ 3) (𝓡 1) ∞
      (fun p : cuspSet => unitOf (sphereFirst p.val)) := by
    intro p
    exact (contMDiffOn_unitOf.contMDiffAt
      (isOpen_ne.mem_nhds (cusp_first_ne_zero p))).comp p
      ((contMDiff_sphereFirst.comp cuspAtlas.contMDiff_subtype_val) p)
  have hsecond : ContMDiff (𝓡∂ 3) (𝓡 1) ∞
      (fun p : cuspSet => unitOf (sphereSecond p.val)) := by
    intro p
    exact (contMDiffOn_unitOf.contMDiffAt
      (isOpen_ne.mem_nhds (cusp_second_ne_zero p))).comp p
      ((contMDiff_sphereSecond.comp cuspAtlas.contMDiff_subtype_val) p)
  have htime : ContMDiff (𝓡∂ 3) (𝓡∂ 1) ∞
      (fun p : cuspSet => (cuspProductInv p).2) := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    have hs : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞
        (fun p : cuspSet => -4 * cliffordHeight p.val) :=
      contMDiff_const.mul (contMDiff_cliffordHeight.comp cuspAtlas.contMDiff_subtype_val)
    exact ⟨hs.continuous.subtype_mk _, hs⟩
  exact (hfirst.prodMk hsecond).prodMk htime

def cuspProduct :
    (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ cuspSet where
  toFun := cuspProductMap
  invFun := cuspProductInv
  left_inv := cuspProduct_left_inv
  right_inv := cuspProduct_right_inv
  contMDiff_toFun := cuspProductMap_smooth
  contMDiff_invFun := cuspProductInv_smooth

instance cuspConnected : ConnectedSpace cuspSet :=
  cuspProduct.toHomeomorph.connectedSpace_iff.mp inferInstance

def cuspPiece : Assembly.PieceEmbedding carrier where
  Piece := cuspSet
  map := cuspToCarrier
  smooth := cuspToCarrier_smooth
  mfderiv_bijective := cuspToCarrier_mfderiv
  injective := cuspToCarrier_injective

def cuspPieceProduct :
    (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ cuspPiece.Piece :=
  cuspProduct

end GC.GraphManifold.Assembly.FC39P0.X135Radial
