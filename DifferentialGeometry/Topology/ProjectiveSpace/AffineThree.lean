import DifferentialGeometry.Topology.ProjectiveSpace.PuncturedThreeManifold
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion

noncomputable section

open scoped Manifold ContDiff
open TopologicalSpace

namespace DifferentialGeometry

open private realProjectiveThreeSplit realProjectiveThreeScalarLine
  realProjectiveThreeScalarLine_apply realProjectiveThreeScalarLine_ext
  realProjectiveThreeScalarLine_smul
  from DifferentialGeometry.Topology.ProjectiveSpace.PuncturedThree

local instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

private def realProjectiveThreeAffineVector (v : EuclideanSpace Real (Fin 3)) :
    EuclideanSpace Real (Fin 4) :=
  realProjectiveThreeSplit.symm (v, realProjectiveThreeScalarLine 1)

private def realProjectiveThreeHeight : EuclideanSpace Real (Fin 4) →L[Real] Real :=
  (PiLp.proj 2 (fun _ : Fin 1 => Real) 0).comp
    ((ContinuousLinearMap.snd Real (EuclideanSpace Real (Fin 3))
      (EuclideanSpace Real (Fin 1))).comp
        realProjectiveThreeSplit.toContinuousLinearMap)

private theorem realProjectiveThreeHeight_affineVector (v : EuclideanSpace Real (Fin 3)) :
    realProjectiveThreeHeight (realProjectiveThreeAffineVector v) = 1 := by
  change (realProjectiveThreeSplit (realProjectiveThreeSplit.symm
    (v, realProjectiveThreeScalarLine 1))).2 0 = 1
  rw [realProjectiveThreeSplit.apply_symm_apply]
  rfl

private theorem realProjectiveThreeAffineVector_ne_zero (v : EuclideanSpace Real (Fin 3)) :
    realProjectiveThreeAffineVector v ≠ 0 := by
  intro h
  have hh := realProjectiveThreeHeight_affineVector v
  rw [h, map_zero] at hh
  exact zero_ne_one hh

def realProjectiveThreeAffineLift (v : EuclideanSpace Real (Fin 3)) :
    Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 :=
  ⟨NormedSpace.normalize (realProjectiveThreeAffineVector v),
    mem_sphere_zero_iff_norm.mpr
      (NormedSpace.norm_normalize (realProjectiveThreeAffineVector_ne_zero v))⟩

def realProjectiveThreeAffineChart (v : EuclideanSpace Real (Fin 3)) :
    RealProjectiveThreeSpace :=
  realProjectiveSpaceQuotientMap (realProjectiveThreeAffineLift v)

private theorem realProjectiveThreeAffineLift_coe (v : EuclideanSpace Real (Fin 3)) :
    (realProjectiveThreeAffineLift v : EuclideanSpace Real (Fin 4)) =
      ‖realProjectiveThreeAffineVector v‖⁻¹ • realProjectiveThreeAffineVector v :=
  rfl

private theorem realProjectiveThreeHeight_affineLift (v : EuclideanSpace Real (Fin 3)) :
    realProjectiveThreeHeight (realProjectiveThreeAffineLift v) =
      ‖realProjectiveThreeAffineVector v‖⁻¹ := by
  rw [realProjectiveThreeAffineLift_coe, map_smul,
    realProjectiveThreeHeight_affineVector, smul_eq_mul, mul_one]

private theorem realProjectiveThreeHeight_affineLift_pos (v : EuclideanSpace Real (Fin 3)) :
    0 < realProjectiveThreeHeight (realProjectiveThreeAffineLift v) := by
  rw [realProjectiveThreeHeight_affineLift]
  exact inv_pos.mpr (norm_pos_iff.mpr (realProjectiveThreeAffineVector_ne_zero v))

private def realProjectiveThreePositiveHemisphere :
    Opens (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) :=
  ⟨{z | 0 < realProjectiveThreeHeight z.1},
    isOpen_lt continuous_const
      (realProjectiveThreeHeight.continuous.comp continuous_subtype_val)⟩

private def realProjectiveThreeAffineLiftPositive (v : EuclideanSpace Real (Fin 3)) :
    realProjectiveThreePositiveHemisphere :=
  ⟨realProjectiveThreeAffineLift v, realProjectiveThreeHeight_affineLift_pos v⟩

private def realProjectiveThreeAffineInverse (z : realProjectiveThreePositiveHemisphere) :
    EuclideanSpace Real (Fin 3) :=
  (realProjectiveThreeHeight z.1.1)⁻¹ • (realProjectiveThreeSplit z.1.1).1

private theorem realProjectiveThreeAffineInverse_left_inv (v : EuclideanSpace Real (Fin 3)) :
    realProjectiveThreeAffineInverse (realProjectiveThreeAffineLiftPositive v) = v := by
  change (realProjectiveThreeHeight (realProjectiveThreeAffineLift v))⁻¹ •
    (realProjectiveThreeSplit (realProjectiveThreeAffineLift v)).1 = v
  rw [realProjectiveThreeHeight_affineLift, realProjectiveThreeAffineLift_coe,
    map_smul, realProjectiveThreeAffineVector,
    realProjectiveThreeSplit.apply_symm_apply]
  change (‖realProjectiveThreeAffineVector v‖⁻¹)⁻¹ •
    (‖realProjectiveThreeAffineVector v‖⁻¹ • v) = v
  rw [inv_inv, smul_smul, mul_inv_cancel₀
    (norm_ne_zero_iff.mpr (realProjectiveThreeAffineVector_ne_zero v)), one_smul]

private theorem realProjectiveThreeAffineInverse_right_inv
    (z : realProjectiveThreePositiveHemisphere) :
    realProjectiveThreeAffineLiftPositive (realProjectiveThreeAffineInverse z) = z := by
  have hv : realProjectiveThreeAffineVector (realProjectiveThreeAffineInverse z) =
      (realProjectiveThreeHeight z.1.1)⁻¹ • z.1.1 := by
    apply realProjectiveThreeSplit.injective
    rw [realProjectiveThreeAffineVector, realProjectiveThreeSplit.apply_symm_apply, map_smul]
    apply Prod.ext
    · rfl
    · change realProjectiveThreeScalarLine 1 =
        (realProjectiveThreeHeight z.1.1)⁻¹ • (realProjectiveThreeSplit z.1.1).2
      rw [← realProjectiveThreeScalarLine_ext (realProjectiveThreeSplit z.1.1).2,
        ← realProjectiveThreeScalarLine_smul]
      change realProjectiveThreeScalarLine 1 =
        realProjectiveThreeScalarLine
          ((realProjectiveThreeHeight z.1.1)⁻¹ * realProjectiveThreeHeight z.1.1)
      rw [inv_mul_cancel₀ (ne_of_gt z.2)]
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.normalize
    (realProjectiveThreeAffineVector (realProjectiveThreeAffineInverse z)) = z.1.1
  rw [hv, NormedSpace.normalize_smul_of_pos (inv_pos.mpr z.2),
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere z.1)]

private theorem realProjectiveThreeAffineLift_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞ realProjectiveThreeAffineLift := by
  have hv : ContMDiff (𝓡 3) 𝓘(Real, EuclideanSpace Real (Fin 4)) ∞
      realProjectiveThreeAffineVector :=
    realProjectiveThreeSplit.symm.contDiff.contMDiff.comp
      (contMDiff_id.prodMk_space contMDiff_const)
  have hn : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞
      (fun v => ‖realProjectiveThreeAffineVector v‖⁻¹) := by
    intro v
    exact ((contDiffAt_norm Real (realProjectiveThreeAffineVector_ne_zero v)).comp_contMDiffAt
      hv.contMDiffAt).inv₀ (norm_ne_zero_iff.mpr (realProjectiveThreeAffineVector_ne_zero v))
  have hmem (v) : ‖realProjectiveThreeAffineVector v‖⁻¹ • realProjectiveThreeAffineVector v ∈
      Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 :=
    (realProjectiveThreeAffineLift v).2
  exact (hn.smul hv).codRestrict_sphere (n := 3) hmem

private theorem realProjectiveThreeAffineInverse_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞ realProjectiveThreeAffineInverse := by
  have hsphere : ContMDiff (𝓡 3) (𝓡 3) ∞
      (Subtype.val : realProjectiveThreePositiveHemisphere →
        Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) :=
    contMDiff_subtype_val (U := realProjectiveThreePositiveHemisphere)
  have he : ContMDiff (𝓡 3) 𝓘(Real, EuclideanSpace Real (Fin 4)) ∞
      (fun z : realProjectiveThreePositiveHemisphere => z.1.1) :=
    contMDiff_coe_sphere.comp hsphere
  have ht : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞
      (fun z : realProjectiveThreePositiveHemisphere => realProjectiveThreeHeight z.1.1) :=
    realProjectiveThreeHeight.contDiff.contMDiff.comp he
  have hu : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun z : realProjectiveThreePositiveHemisphere => (realProjectiveThreeSplit z.1.1).1) :=
    (ContinuousLinearMap.fst Real (EuclideanSpace Real (Fin 3))
      (EuclideanSpace Real (Fin 1))).contDiff.contMDiff.comp
        (realProjectiveThreeSplit.contDiff.contMDiff.comp he)
  exact (ht.inv₀ (fun z => ne_of_gt z.2)).smul hu

private def realProjectiveThreeAffineDiffeomorph :
    EuclideanSpace Real (Fin 3) ≃ₘ⟮𝓡 3, 𝓡 3⟯ realProjectiveThreePositiveHemisphere where
  toFun := realProjectiveThreeAffineLiftPositive
  invFun := realProjectiveThreeAffineInverse
  left_inv := realProjectiveThreeAffineInverse_left_inv
  right_inv := realProjectiveThreeAffineInverse_right_inv
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff realProjectiveThreePositiveHemisphere _).mp
      realProjectiveThreeAffineLift_contMDiff
  contMDiff_invFun := realProjectiveThreeAffineInverse_contMDiff

theorem realProjectiveThreeAffineChart_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ realProjectiveThreeAffineChart := by
  have hlift : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ realProjectiveThreeAffineLift :=
    isLocalDiffeomorph_comp
      (isLocalDiffeomorph_subtype_val realProjectiveThreePositiveHemisphere)
      realProjectiveThreeAffineDiffeomorph.isLocalDiffeomorph
  exact isLocalDiffeomorph_comp realProjectiveSpaceQuotientMap_isLocalDiffeomorph hlift

theorem realProjectiveThreeAffineChart_injective :
    Function.Injective realProjectiveThreeAffineChart := by
  intro v w h
  rcases realProjectiveSpaceQuotientMap_eq_iff.mp h with hsame | hneg
  · apply realProjectiveThreeAffineDiffeomorph.injective
    exact Subtype.ext hsame
  · have he := congrArg realProjectiveThreeHeight hneg
    rw [map_neg] at he
    have hv := realProjectiveThreeHeight_affineLift_pos v
    have hw := realProjectiveThreeHeight_affineLift_pos w
    linarith

theorem realProjectiveThreeAffineChart_isSmoothEmbedding :
    Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ realProjectiveThreeAffineChart :=
  Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
    realProjectiveThreeAffineChart_isLocalDiffeomorph realProjectiveThreeAffineChart_injective

def realProjectiveThreeAffinePartialDiffeomorph :
    PartialDiffeomorph (𝓡 3) (𝓡 3)
      (EuclideanSpace Real (Fin 3)) RealProjectiveThreeSpace ∞ := by
  let U := realProjectiveThreeAffineChart_isLocalDiffeomorph.image
  let _ : Nonempty U := ⟨⟨realProjectiveThreeAffineChart 0, ⟨0, rfl⟩⟩⟩
  exact PartialDiffeomorph.liftTargetOpen
    (Topology.Manifold.diffeomorphOntoImage realProjectiveThreeAffineChart
      realProjectiveThreeAffineChart_isLocalDiffeomorph
      realProjectiveThreeAffineChart_injective).toPartialDiffeomorph rfl

@[simp] theorem realProjectiveThreeAffinePartialDiffeomorph_apply
    (v : EuclideanSpace Real (Fin 3)) :
    realProjectiveThreeAffinePartialDiffeomorph v = realProjectiveThreeAffineChart v :=
  rfl

@[simp] theorem realProjectiveThreeAffinePartialDiffeomorph_source :
    realProjectiveThreeAffinePartialDiffeomorph.source = Set.univ :=
  rfl

@[simp] theorem realProjectiveThreeAffinePartialDiffeomorph_target :
    realProjectiveThreeAffinePartialDiffeomorph.target = Set.range realProjectiveThreeAffineChart :=
  rfl

end DifferentialGeometry
