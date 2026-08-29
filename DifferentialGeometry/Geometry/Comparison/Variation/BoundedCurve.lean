import DifferentialGeometry.Geometry.Comparison.Variation.ChartVariation

noncomputable section

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem exists_smooth_curve
    (y : M) (V : TangentSpace I y) (U : Set M)
    (hU : IsOpen U) (hy : y ∈ U) :
    ∃ η : Real → M,
      ContMDiff 𝓘(Real, Real) I ∞ η ∧
      (∀ u, η u ∈ U) ∧
      η 0 = y ∧
      mfderiv 𝓘(Real, Real) I η 0 (1 : Real) = V := by
  let φ : E := extChartAt I y y
  let W : Set M := U ∩ (extChartAt I y).source
  have hW_nhds : W ∈ 𝓝 y := by
    apply (hU.inter (isOpen_extChartAt_source y)).mem_nhds
    exact ⟨hy, mem_extChartAt_source y⟩
  have hcoord_nhds : extChartAt I y '' W ∈ 𝓝 φ := by
    exact extChartAt_image_nhds_mem_nhds_of_boundaryless hW_nhds
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hcoord_nhds
  let w : E := V
  let B : Real := ‖w‖ + 1
  have hB : 0 < B := by
    dsimp [B]
    positivity
  let ρ : Real := r / (2 * B)
  have hρ : 0 < ρ := div_pos hr (mul_pos (by norm_num) hB)
  let θ : Real → Real := fun u => ρ * Real.sin (u / ρ)
  have hθsmooth : ContDiff Real ∞ θ := by
    exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const ρ))
  have hθ0 : θ 0 = 0 := by simp [θ]
  have hθ'0 : HasDerivAt θ 1 0 := by
    have hinner : HasDerivAt (fun u : Real => u / ρ) (1 / ρ) 0 := by
      simpa using (hasDerivAt_id (0 : Real)).div_const ρ
    have hsin : HasDerivAt Real.sin (Real.cos (0 / ρ)) (0 / ρ) :=
      Real.hasDerivAt_sin _
    have hmul := (hsin.comp 0 hinner).const_mul ρ
    simpa [θ, hρ.ne'] using hmul
  have hθbound : ∀ u, |θ u| ≤ ρ := by
    intro u
    change |ρ * Real.sin (u / ρ)| ≤ ρ
    rw [abs_mul, abs_of_pos hρ]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hρ.le).trans_eq
      (mul_one ρ)
  have hwB : ‖w‖ < B := by
    exact lt_add_one ‖w‖
  have hpert : ∀ u, ‖θ u • w‖ < r := by
    intro u
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |θ u| * ‖w‖ ≤ ρ * ‖w‖ :=
        mul_le_mul_of_nonneg_right (hθbound u) (norm_nonneg _)
      _ < ρ * B := mul_lt_mul_of_pos_left hwB hρ
      _ = r / 2 := by simp only [ρ]; field_simp
      _ < r := half_lt_self hr
  have hmem : ∀ u, φ + θ u • w ∈ extChartAt I y '' W := by
    intro u
    apply hrsub
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hpert u
  have htgt : ∀ u, φ + θ u • w ∈ (extChartAt I y).target := by
    intro u
    obtain ⟨z, hzW, hz⟩ := hmem u
    rw [← hz]
    exact (extChartAt I y).map_source hzW.2
  let η : Real → M :=
    fun u => (extChartAt I y).symm (φ + θ u • w)
  have hθM : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ θ := by
    rw [contMDiff_iff_contDiff]
    exact hθsmooth
  have hcurveE : ContMDiff 𝓘(Real, Real) 𝓘(Real, E) ∞
      (fun u : Real => φ + θ u • w) :=
    contMDiff_const.add (hθM.smul contMDiff_const)
  have hηsmooth : ContMDiff 𝓘(Real, Real) I ∞ η := by
    exact (contMDiffOn_extChartAt_symm (I := I) (n := ∞) y).comp_contMDiff
      hcurveE htgt
  have hηU : ∀ u, η u ∈ U := by
    intro u
    obtain ⟨z, hzW, hz⟩ := hmem u
    change (extChartAt I y).symm (φ + θ u • w) ∈ U
    rw [← hz, (extChartAt I y).left_inv hzW.2]
    exact hzW.1
  have hη0 : η 0 = y := by
    simp only [η, hθ0, zero_smul, add_zero, φ]
    exact (extChartAt I y).left_inv (mem_extChartAt_source y)
  have hline : HasMFDerivAt 𝓘(Real, Real) 𝓘(Real, E)
      (fun u : Real => φ + θ u • w) 0
      (modelLinearMapToTangent
        (A := (1 : Real →L[Real] Real).smulRight w)) := by
    have hsmul : HasDerivAt (fun u : Real => θ u • w) ((1 : Real) • w) 0 := by
      simpa using hθ'0.smul_const w
    have hadd : HasDerivAt (fun u : Real => φ + θ u • w)
        (0 + (1 : Real) • w) 0 :=
      (hasDerivAt_const (0 : Real) φ).add hsmul
    rw [zero_add, one_smul] at hadd
    exact HasFDerivAt.hasMFDerivAt_model hadd.hasFDerivAt
  have hsymmD : HasMFDerivAt 𝓘(Real, E) I (extChartAt I y).symm φ
      (tangentLinearMapOfModel (I := 𝓘(Real, E)) (I' := I)
        (x := φ) (y := (extChartAt I y).symm φ)
        (ContinuousLinearMap.id Real E)) := by
    have hmemφ : φ ∈ (extChartAt I y).target := by
      exact mem_extChartAt_target y
    have hdiff : MDifferentiableWithinAt 𝓘(Real, E) I
        (extChartAt I y).symm univ φ := by
      have h := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := y) hmemφ
      rwa [I.range_eq_univ] at h
    have heq : tangentLinearMapToModel
        (mfderivWithin 𝓘(Real, E) I (extChartAt I y).symm univ φ) =
          ContinuousLinearMap.id Real E := by
      rw [← I.range_eq_univ]
      have hraw := mfderivWithin_range_extChartAt_symm (I := I) (x := y)
      have hmap := congrArg tangentLinearMapToModel hraw
      exact hmap.trans (by
        apply ContinuousLinearMap.ext
        intro v
        rfl)
    have heqNative :
        mfderivWithin 𝓘(Real, E) I (extChartAt I y).symm univ φ =
          tangentLinearMapOfModel (I := 𝓘(Real, E)) (I' := I)
            (x := φ) (y := (extChartAt I y).symm φ)
            (ContinuousLinearMap.id Real E) := by
      apply tangentLinearMapToModel_injective
      rw [heq, tangentLinearMapToModel_ofModel]
    rw [← hasMFDerivWithinAt_univ]
    exact heqNative ▸ hdiff.hasMFDerivWithinAt
  have hηderiv : HasMFDerivAt 𝓘(Real, Real) I η 0
      (tangentLinearMapOfModel (I := 𝓘(Real, Real)) (I' := I)
        (x := 0) (y := η 0) ((1 : Real →L[Real] Real).smulRight w)) := by
    have hsymmD' : HasMFDerivAt 𝓘(Real, E) I (extChartAt I y).symm
        (φ + θ 0 • w)
        (tangentLinearMapOfModel (I := 𝓘(Real, E)) (I' := I)
          (x := φ + θ 0 • w)
          (y := (extChartAt I y).symm (φ + θ 0 • w))
          (ContinuousLinearMap.id Real E)) := by
      have hbase : φ + θ 0 • w = φ := by
        rw [hθ0, zero_smul, add_zero]
      rw [hbase]
      exact hsymmD
    have hcomp := hsymmD'.comp 0 hline
    rw [Function.comp_def] at hcomp
    have hmap :
        (tangentLinearMapOfModel (I := 𝓘(Real, E)) (I' := I)
          (x := φ + θ 0 • w)
          (y := (extChartAt I y).symm (φ + θ 0 • w))
          (ContinuousLinearMap.id Real E)).comp
            (modelLinearMapToTangent
              (A := (1 : Real →L[Real] Real).smulRight w)) =
          tangentLinearMapOfModel (I := 𝓘(Real, Real)) (I' := I)
            (x := 0) (y := (extChartAt I y).symm (φ + θ 0 • w))
            ((1 : Real →L[Real] Real).smulRight w) := by
      apply tangentLinearMapToModel_injective
      rw [tangentLinearMapToModel_comp, tangentLinearMapToModel_ofModel,
        tangentLinearMapToModel_modelLinearMapToTangent,
        ContinuousLinearMap.id_comp, tangentLinearMapToModel_ofModel]
    rw [hmap] at hcomp
    simpa only [η] using hcomp
  refine ⟨η, hηsmooth, hηU, hη0, ?_⟩
  rw [hηderiv.mfderiv]
  change (1 : Real) • V = V
  exact one_smul Real V

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
