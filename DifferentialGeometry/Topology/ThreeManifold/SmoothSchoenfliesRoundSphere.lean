import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.Diffeomorph.Radial

open scoped ContDiff Manifold
open Set Metric

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : ℝ³) 1

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [Module.finrank_fin_fun]⟩

theorem isSmoothEmbedding_sphereTwo_subtype :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (Subtype.val : S² → ℝ³) :=
  isSmoothEmbedding_coe_sphere (E := ℝ³) (n := 2)

theorem exists_diffeomorph_image_sphereTwo_subtype :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' S² = Set.range (Subtype.val : S² → ℝ³) := by
  refine ⟨Diffeomorph.refl 𝓘(ℝ, ℝ³) ℝ³ ∞, ?_⟩
  rw [Diffeomorph.coe_refl, Set.image_id, Subtype.range_coe]

private abbrev closedBallComplement : TopologicalSpace.Opens ℝ³ :=
  ⟨(closedBall (0 : ℝ³) 1)ᶜ, isClosed_closedBall.isOpen_compl⟩

private abbrev aboveOne : TopologicalSpace.Opens ℝ :=
  ⟨Set.Ioi (1 : ℝ), isOpen_Ioi⟩

private theorem one_lt_norm (x : closedBallComplement) : 1 < ‖(x : ℝ³)‖ := by
  have hx : (x : ℝ³) ∈ (closedBall (0 : ℝ³) 1)ᶜ := x.property
  simpa only [mem_compl_iff, mem_closedBall_zero_iff, not_le] using hx

private theorem norm_smul_sphereTwo {r : ℝ} (hr : 1 < r) (u : S²) :
    ‖r • (u : ℝ³)‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hr),
    norm_eq_of_mem_sphere u, mul_one]

private noncomputable def toComplement (p : S² × aboveOne) : closedBallComplement :=
  ⟨(p.2 : ℝ) • (p.1 : ℝ³), by
    change (p.2 : ℝ) • (p.1 : ℝ³) ∈ (closedBall (0 : ℝ³) 1)ᶜ
    rw [mem_compl_iff, mem_closedBall_zero_iff, not_le,
      norm_smul_sphereTwo p.2.2 p.1]
    exact p.2.2⟩

private noncomputable def unitNormalize (x : closedBallComplement) : S² :=
  ⟨‖(x : ℝ³)‖⁻¹ • (x : ℝ³), by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one (one_lt_norm x)))]⟩

private noncomputable def normAboveOne (x : closedBallComplement) : aboveOne :=
  ⟨‖(x : ℝ³)‖, by
    change (1 : ℝ) < ‖(x : ℝ³)‖
    exact one_lt_norm x⟩

private noncomputable def fromComplement (x : closedBallComplement) : S² × aboveOne :=
  (unitNormalize x, normAboveOne x)

private theorem toComplement_contMDiff :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ³) ∞
      (fun p : S² × aboveOne => (p.2 : ℝ) • (p.1 : ℝ³)) :=
  (contMDiff_subtype_val.comp contMDiff_snd).smul
    (contMDiff_coe_sphere.comp contMDiff_fst)

private theorem unitNormalize_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun x : closedBallComplement => ‖(x : ℝ³)‖⁻¹ • (x : ℝ³)) := by
  have hpos : ∀ x : closedBallComplement, (0 : ℝ) < ‖(x : ℝ³)‖ :=
    fun x => lt_trans zero_lt_one (one_lt_norm x)
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun x : closedBallComplement => ‖(x : ℝ³)‖) := by
    intro x
    refine contMDiffAt_subtype_iff.mpr ?_
    exact (contDiffAt_norm ℝ (norm_ne_zero_iff.mp (ne_of_gt (hpos x)))).contMDiffAt
  exact (hn.inv₀ (fun x => ne_of_gt (hpos x))).smul contMDiff_subtype_val

private theorem normAboveOne_contMDiff :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ normAboveOne := by
  have hpos : ∀ x : closedBallComplement, (0 : ℝ) < ‖(x : ℝ³)‖ :=
    fun x => lt_trans zero_lt_one (one_lt_norm x)
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun x : closedBallComplement => ‖(x : ℝ³)‖) := by
    intro x
    refine contMDiffAt_subtype_iff.mpr ?_
    exact (contDiffAt_norm ℝ (norm_ne_zero_iff.mp (ne_of_gt (hpos x)))).contMDiffAt
  exact (ContMDiff.subtypeVal_comp_iff (M := closedBallComplement) (I := 𝓡 3)
    (I' := 𝓘(ℝ, ℝ)) aboveOne normAboveOne).mp hn

private theorem fromComplement_contMDiff :
    ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ fromComplement := by
  have hpos : ∀ x : closedBallComplement, (0 : ℝ) < ‖(x : ℝ³)‖ :=
    fun x => lt_trans zero_lt_one (one_lt_norm x)
  have hsph : ContMDiff (𝓡 3) (𝓡 2) ∞
      (fun x : closedBallComplement =>
        (⟨‖(x : ℝ³)‖⁻¹ • (x : ℝ³), by
          rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
            inv_mul_cancel₀ (ne_of_gt (hpos x))]⟩ : S²)) :=
    unitNormalize_contMDiff.codRestrict_sphere (fun x => by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (ne_of_gt (hpos x))])
  exact hsph.prodMk normAboveOne_contMDiff

noncomputable def closedBallComplementDiffeomorph :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      (S² × aboveOne) closedBallComplement ∞ where
  toFun := toComplement
  invFun := fromComplement
  left_inv p := by
    have hnorm := norm_smul_sphereTwo p.2.2 p.1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change ‖(p.2 : ℝ) • (p.1 : ℝ³)‖⁻¹ • ((p.2 : ℝ) • (p.1 : ℝ³)) = (p.1 : ℝ³)
      rw [hnorm, smul_smul,
        inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one p.2.2)), one_smul]
    · change ‖(p.2 : ℝ) • (p.1 : ℝ³)‖ = (p.2 : ℝ)
      rw [hnorm]
  right_inv x := by
    refine Subtype.ext ?_
    change ‖(x : ℝ³)‖ • (‖(x : ℝ³)‖⁻¹ • (x : ℝ³)) = (x : ℝ³)
    rw [smul_smul,
      mul_inv_cancel₀ (ne_of_gt (lt_trans zero_lt_one (one_lt_norm x))), one_smul]
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff (M := S² × aboveOne) (I := (𝓡 2).prod 𝓘(ℝ, ℝ))
      (I' := 𝓡 3) closedBallComplement toComplement).mp toComplement_contMDiff
  contMDiff_invFun := fromComplement_contMDiff

end DifferentialGeometry.Topology.ThreeManifold
