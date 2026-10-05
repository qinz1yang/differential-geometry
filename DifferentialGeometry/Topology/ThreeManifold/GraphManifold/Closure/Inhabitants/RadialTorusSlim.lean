import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialTorusCores

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance sphereSecondCountable_SlimX135 : SecondCountableTopology SphereCarrier.{0} :=
  secondCountableTopology_sphereCarrier

local instance carrierCharts_SlimX135 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_SlimX135 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

def slimSet : Set SphereCarrier.{0} :=
  {p | bandDefiner (-(1 / 2 : ℝ)) (-(1 / 4 : ℝ)) p ≤ 0}

def slimAtlas : SmoothBoundaryAtlas (𝓡 3) 3 slimSet :=
  SmoothBoundaryAtlas.regularSublevel (𝓡 3) (n := 2) finrank_euclideanSpace_fin
    (bandDefiner_smooth (-(1 / 2 : ℝ)) (-(1 / 4 : ℝ))) 0
    (bandDefiner_regular (-(1 / 2 : ℝ)) (-(1 / 4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num))

instance slimCharts : ChartedSpace (EuclideanHalfSpace 3) slimSet := slimAtlas.toChartedSpace

instance slimSmooth : IsManifold (𝓡∂ 3) ∞ slimSet := slimAtlas.isManifold

instance slimCompact : CompactSpace slimSet :=
  isCompact_iff_compactSpace.mp
    (isClosed_le (bandDefiner_smooth (-(1 / 2 : ℝ)) (-(1 / 4 : ℝ))).continuous
      continuous_const).isCompact

instance slimSecondCountable : SecondCountableTopology slimSet := inferInstance

def slimToCarrier (p : slimSet) : carrier.Carrier :=
  ⟨p.val, by
    have hb := (bandDefiner_nonpos_iff (by norm_num)).mp p.property
    exact le_trans hb.2 (by norm_num)⟩

theorem slimToCarrier_smooth : ContMDiff (𝓡∂ 3) carrier.model ∞ slimToCarrier :=
  (solidTorusAtlas.contMDiff_iff_subtype_val slimToCarrier).mpr slimAtlas.contMDiff_subtype_val

theorem slimToCarrier_injective : Injective slimToCarrier := by
  intro p q h
  exact Subtype.ext (congrArg (Subtype.val : carrier.Carrier → SphereCarrier.{0}) h)

theorem slimToCarrier_range : range slimToCarrier =
    {p | -(1 / 2 : ℝ) ≤ height p ∧ height p ≤ -(1 / 4 : ℝ)} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact (bandDefiner_nonpos_iff (by norm_num)).mp q.property
  · intro hp
    exact ⟨⟨p.val, (bandDefiner_nonpos_iff (by norm_num)).mpr hp⟩, Subtype.ext rfl⟩

theorem slimToCarrier_mfderiv (p : slimSet) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) slimToCarrier p) := by
  have hw : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : carrier.Carrier → SphereCarrier.{0}) (slimToCarrier p)) :=
    solidTorusAtlas.mfderiv_subtypeVal_bijective (slimToCarrier p)
  have hc : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      ((Subtype.val : carrier.Carrier → SphereCarrier.{0}) ∘ slimToCarrier) p) :=
    slimAtlas.mfderiv_subtypeVal_bijective p
  have hchain := mfderiv_comp p (contMDiff_solidTorus_val.mdifferentiableAt (by simp))
    (slimToCarrier_smooth.mdifferentiableAt (by simp))
  have hcomp := hchain ▸ hc
  exact Function.Bijective.of_comp_left
    (f := mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : carrier.Carrier → SphereCarrier.{0}) (slimToCarrier p))
    (g := mfderiv (𝓡∂ 3) (𝓡∂ 3) slimToCarrier p) hcomp hw.1

def slimParameter (q : Torus × Icc (0 : ℝ) 1) : Torus × ℝ :=
  (q.1, -(1 / 4 : ℝ) - q.2.val / 4)

theorem slimParameter_source (q : Torus × Icc (0 : ℝ) 1) :
    slimParameter q ∈ cliffordSeam.{0}.source := by
  change -1 < -(1 / 4 : ℝ) - q.2.val / 4 ∧ -(1 / 4 : ℝ) - q.2.val / 4 < 1
  constructor <;> linarith [q.2.property.1, q.2.property.2]

theorem slimParameter_height (q : Torus × Icc (0 : ℝ) 1) :
    cliffordHeight (cliffordSeam.{0} (slimParameter q)) = -(1 / 4 : ℝ) - q.2.val / 4 := by
  rw [cliffordSeam_apply, cliffordHeight_cliffordSeamMap]
  exact seamClamp_of_mem (by dsimp [slimParameter]; linarith [q.2.property.2])
    (by dsimp [slimParameter]; linarith [q.2.property.1])

def slimProductMap (q : Torus × Icc (0 : ℝ) 1) : slimSet :=
  ⟨cliffordSeam.{0} (slimParameter q), by
    apply (bandDefiner_nonpos_iff (by norm_num)).mpr
    rw [slimParameter_height]
    constructor <;> linarith [q.2.property.1, q.2.property.2]⟩

def slimProductInverse (p : slimSet) : Torus × Icc (0 : ℝ) 1 :=
  ((cliffordSeamInv p.val).1, ⟨-1 - 4 * cliffordHeight p.val, by
    have hb := (bandDefiner_nonpos_iff (by norm_num)).mp p.property
    constructor <;> linarith [hb.1, hb.2]⟩)

theorem slim_first_nonzero (p : slimSet) : sphereFirst p.val ≠ 0 := by
  intro hzero
  have hn := norm_sphereFirst_sq_eq p.val
  rw [hzero, norm_zero, zero_pow (by decide)] at hn
  have hb := (bandDefiner_nonpos_iff (by norm_num)).mp p.property
  linarith [hb.1]

theorem slim_second_nonzero (p : slimSet) : sphereSecond p.val ≠ 0 :=
  sphereSecond_ne_zero_of_mem (slimToCarrier p).property

theorem slimProduct_left (q : Torus × Icc (0 : ℝ) 1) :
    slimProductInverse (slimProductMap q) = q := by
  apply Prod.ext
  · exact congrArg (fun z : Torus × ℝ => z.1)
      (cliffordSeam.{0}.left_inv' (slimParameter_source q))
  · apply Subtype.ext
    change -1 - 4 * cliffordHeight (cliffordSeam.{0} (slimParameter q)) = q.2.val
    rw [slimParameter_height]
    ring

theorem slimProduct_right (p : slimSet) : slimProductMap (slimProductInverse p) = p := by
  apply Subtype.ext
  change cliffordSeam.{0} (slimParameter (slimProductInverse p)) = p.val
  have h : slimParameter (slimProductInverse p) = cliffordSeamInv p.val := by
    apply Prod.ext
    · rfl
    change -(1 / 4 : ℝ) - (-1 - 4 * cliffordHeight p.val) / 4 = cliffordHeight p.val
    ring
  rw [h]
  exact cliffordSeam.{0}.right_inv' ⟨slim_first_nonzero p, slim_second_nonzero p⟩

theorem slimProductMap_smooth :
    ContMDiff (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) ∞ slimProductMap := by
  apply (slimAtlas.contMDiff_iff_subtype_val slimProductMap).mpr
  have hs : ContMDiff (torusModel.prod (𝓡∂ 1)) signedCollarModel ∞ slimParameter :=
    contMDiff_fst.prodMk
      (contMDiff_const.sub ((contMDiff_subtypeVal_Icc.comp contMDiff_snd).div_const 4))
  exact cliffordSeam.{0}.contMDiffOn_toFun.comp_contMDiff hs slimParameter_source

theorem slimProductInverse_smooth :
    ContMDiff (𝓡∂ 3) (torusModel.prod (𝓡∂ 1)) ∞ slimProductInverse := by
  have hf : ContMDiff (𝓡∂ 3) (𝓡 1) ∞
      (fun p : slimSet => unitOf (sphereFirst p.val)) := by
    intro p
    exact (contMDiffOn_unitOf.contMDiffAt
      (isOpen_ne.mem_nhds (slim_first_nonzero p))).comp p
      ((contMDiff_sphereFirst.comp slimAtlas.contMDiff_subtype_val) p)
  have hg : ContMDiff (𝓡∂ 3) (𝓡 1) ∞
      (fun p : slimSet => unitOf (sphereSecond p.val)) := by
    intro p
    exact (contMDiffOn_unitOf.contMDiffAt
      (isOpen_ne.mem_nhds (slim_second_nonzero p))).comp p
      ((contMDiff_sphereSecond.comp slimAtlas.contMDiff_subtype_val) p)
  have ht : ContMDiff (𝓡∂ 3) (𝓡∂ 1) ∞
      (fun p : slimSet => (slimProductInverse p).2) := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    have hs : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞
        (fun p : slimSet => -1 - 4 * cliffordHeight p.val) :=
      contMDiff_const.sub
        (contMDiff_const.mul (contMDiff_cliffordHeight.comp slimAtlas.contMDiff_subtype_val))
    exact ⟨hs.continuous.subtype_mk _, hs⟩
  exact (hf.prodMk hg).prodMk ht

def slimProduct :
    (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ slimSet where
  toFun := slimProductMap
  invFun := slimProductInverse
  left_inv := slimProduct_left
  right_inv := slimProduct_right
  contMDiff_toFun := slimProductMap_smooth
  contMDiff_invFun := slimProductInverse_smooth

instance slimConnected : ConnectedSpace slimSet :=
  slimProduct.toHomeomorph.connectedSpace_iff.mp inferInstance

def slimPiece : Assembly.PieceEmbedding carrier where
  Piece := slimSet
  map := slimToCarrier
  smooth := slimToCarrier_smooth
  mfderiv_bijective := slimToCarrier_mfderiv
  injective := slimToCarrier_injective

end GC.GraphManifold.Assembly.FC39P0.X135Radial
