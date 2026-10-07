/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Analysis.Calculus.Quasiconformal.DerivativeEccentricity
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.ChartAction

noncomputable section

open Set Filter MeasureTheory Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology ContDiff

namespace DifferentialGeometry.BoundaryChartConformal

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary BoundaryTopology
open MobiusBoundary Horospherical EuclideanBoundary GeodesicFlow BoundaryChartAction

variable {m : ℕ}

local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) :=
  poBoundaryMulAction (by omega)

theorem rawImage_eq_denominator_smul (A : LorGrp (m + 1)) {x : Horizontal m}
    (hx : x ∈ chartDomain (QuotientGroup.mk' _ A)) :
    rawImage A x = denominator A x •
      horoVec (fun i => chartAction (QuotientGroup.mk' _ A) x i) := by
  let y := chartAction (QuotientGroup.mk' _ A) x
  have he : boundaryRep (rawImage A x) = boundaryRep (horoVec (fun i => y i)) := by
    have h := congrArg BoundaryH.val (embed_chartAction (QuotientGroup.mk' _ A) hx)
    rw [action_mk_val] at h
    exact h.symm
  have hd := congrArg vHeight he
  simp only [boundaryRep, vHeight_smul, vHeight_horoVec, mul_one] at hd
  change (tc (rawImage A x))⁻¹ * denominator A x = (tc (horoVec (fun i => y i)))⁻¹ at hd
  have hd' : tc (rawImage A x) * (tc (horoVec (fun i => y i)))⁻¹ = denominator A x := by
    rw [← hd, ← mul_assoc, mul_inv_cancel₀ (rawImage_time_ne_zero A x), one_mul]
  calc
    rawImage A x = tc (rawImage A x) • boundaryRep (rawImage A x) := by
      rw [boundaryRep, smul_smul, mul_inv_cancel₀ (rawImage_time_ne_zero A x), one_smul]
    _ = tc (rawImage A x) • boundaryRep (horoVec (fun i => y i)) := by rw [he]
    _ = denominator A x • horoVec (fun i => y i) := by
      rw [boundaryRep, smul_smul, hd']

theorem lorB_horoVec_horizontal (x y : Horizontal m) :
    lorB (horoVec (fun i => x i)) (horoVec (fun i => y i)) = -dist x y ^ 2 / 2 := by
  rw [lorB_horoVec_horoVec]
  have hs : normSq ((fun i => x i) - (fun i => y i)) = dist x y ^ 2 := by
    change normSq (fun i => (x - y) i) = _
    rw [normSq_horizontal, dist_eq_norm]
  rw [hs]

theorem dist_sq_mul_denominator (A : LorGrp (m + 1)) {x y : Horizontal m}
    (hx : x ∈ chartDomain (QuotientGroup.mk' _ A))
    (hy : y ∈ chartDomain (QuotientGroup.mk' _ A)) :
    dist (chartAction (QuotientGroup.mk' _ A) x) (chartAction (QuotientGroup.mk' _ A) y) ^ 2 *
        denominator A x * denominator A y = dist x y ^ 2 := by
  have h := lorB_matOf_mulVec A (horoVec (fun i => x i)) (horoVec (fun i => y i))
  change lorB (rawImage A x) (rawImage A y) = _ at h
  rw [rawImage_eq_denominator_smul A hx, rawImage_eq_denominator_smul A hy,
    lorB_smul_left, lorB_smul_right, lorB_horoVec_horizontal, lorB_horoVec_horizontal] at h
  nlinarith

theorem norm_fderiv_sq_mul_denominator (A : LorGrp (m + 1)) {x : Horizontal m}
    (hx : x ∈ chartDomain (QuotientGroup.mk' _ A)) (v : Horizontal m) :
    ‖fderiv ℝ (chartAction (QuotientGroup.mk' _ A)) x v‖ ^ 2 * denominator A x ^ 2 =
      ‖v‖ ^ 2 := by
  let g : IsometryGroup m := QuotientGroup.mk' _ A
  have hf := (differentiableAt_chartAction g hx).hasFDerivAt
  have hs := (hf.hasLineDerivAt v).tendsto_slope_zero_right.norm
  have hp : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hd := (contDiff_denominator A 0).continuous.continuousAt.tendsto.comp hp
  have ht := (hs.pow 2).mul (hd.mul_const (denominator A x))
  have he : (fun t : ℝ =>
      ‖t⁻¹ • (chartAction g (x + t • v) - chartAction g x)‖ ^ 2 *
        (denominator A (x + t • v) * denominator A x)) =ᶠ[𝓝[>] 0] fun _ => ‖v‖ ^ 2 := by
    filter_upwards [hp ((isOpen_chartDomain g).mem_nhds hx), self_mem_nhdsWithin]
      with t htx ht
    have htpos : 0 < t := ht
    have hb := dist_sq_mul_denominator A htx hx
    simp only [dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg htpos.le, mul_pow] at hb
    simp only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htpos.le), mul_pow]
    calc
      _ = t⁻¹ ^ 2 * (‖chartAction g (x + t • v) - chartAction g x‖ ^ 2 *
          denominator A (x + t • v) * denominator A x) := by ring
      _ = t⁻¹ ^ 2 * (t ^ 2 * ‖v‖ ^ 2) := by rw [hb]
      _ = ‖v‖ ^ 2 := by field_simp
  have heq := tendsto_nhds_unique (ht.congr' he) tendsto_const_nhds
  simpa only [pow_two] using heq

theorem norm_fderiv_eq (A : LorGrp (m + 1)) {x : Horizontal m}
    (hx : x ∈ chartDomain (QuotientGroup.mk' _ A)) (v : Horizontal m) :
    ‖fderiv ℝ (chartAction (QuotientGroup.mk' _ A)) x v‖ =
      |denominator A x|⁻¹ * ‖v‖ := by
  have hd : |denominator A x| ≠ 0 := abs_ne_zero.mpr ((denominator_ne_zero_iff A x).mpr hx)
  have hs := norm_fderiv_sq_mul_denominator A hx v
  have hn : |denominator A x| * ‖fderiv ℝ (chartAction (QuotientGroup.mk' _ A)) x v‖ = ‖v‖ := by
    apply (sq_eq_sq₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow, sq_abs, mul_comm]
    exact hs
  calc
    _ = |denominator A x|⁻¹ *
        (|denominator A x| * ‖fderiv ℝ (chartAction (QuotientGroup.mk' _ A)) x v‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    _ = _ := by rw [hn]

theorem isConformalMap_fderiv_chartAction (g : IsometryGroup m) {x : Horizontal m}
    (hx : x ∈ chartDomain g) : IsConformalMap (fderiv ℝ (chartAction g) x) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hd : |denominator A x| ≠ 0 := abs_ne_zero.mpr ((denominator_ne_zero_iff A x).mpr hx)
  let L : Horizontal m →ₗᵢ[ℝ] Horizontal m :=
    { toLinearMap := (|denominator A x| • fderiv ℝ (chartAction (QuotientGroup.mk' _ A)) x).toLinearMap
      norm_map' v := by
        change ‖|denominator A x| • fderiv ℝ (chartAction (QuotientGroup.mk' _ A)) x v‖ = ‖v‖
        rw [norm_smul, Real.norm_eq_abs, abs_abs, norm_fderiv_eq A hx v,
          ← mul_assoc, mul_inv_cancel₀ hd, one_mul] }
  refine ⟨|denominator A x|⁻¹, inv_ne_zero hd, L, ?_⟩
  ext1 v
  change fderiv ℝ (chartAction (QuotientGroup.mk' _ A)) x v =
    |denominator A x|⁻¹ • (|denominator A x| • fderiv ℝ (chartAction (QuotientGroup.mk' _ A)) x v)
  rw [smul_smul, inv_mul_cancel₀ hd, one_smul]

variable [Nonempty (Fin m)]

theorem ae_chartEccentricity_conjugacy (g h : IsometryGroup m)
    (ψ : BoundaryH (m + 1) → BoundaryH (m + 1)) (F : Horizontal m ≃ₜ Horizontal m)
    (hF : ∀ x, embed (F x) = ψ (embed x))
    (heq : ∀ v, ψ (g • v) = h • ψ v)
    (hdiff : ∀ᵐ x ∂(volume : Measure (Horizontal m)), DifferentiableAt ℝ F x)
    (hinverse : ∀ᵐ x ∂(volume : Measure (Horizontal m)),
      (fderiv ℝ F.symm (F x)).comp (fderiv ℝ F x) = ContinuousLinearMap.id ℝ (Horizontal m) ∧
      (fderiv ℝ F x).comp (fderiv ℝ F.symm (F x)) = ContinuousLinearMap.id ℝ (Horizontal m)) :
    ∀ᵐ x ∂(volume : Measure (Horizontal m)),
      DerivativeEccentricity.chartEccentricity F (chartAction g x) =
        DerivativeEccentricity.chartEccentricity F x := by
  filter_upwards [ae_fderiv_conjugacy g h ψ F hF heq hdiff, hinverse,
    (quasiMeasurePreserving_chartAction g).ae hinverse] with x hchain hix higx
  exact DerivativeEccentricity.eccentricity_conjugacy _ _ _ _ _ _ _ _
    hix.2 higx.1
    (inverse_fderiv_chartAction g hchain.1) (fderiv_inverse_chartAction g hchain.1)
    (inverse_fderiv_chartAction h hchain.2.1) (fderiv_inverse_chartAction h hchain.2.1)
    (isConformalMap_fderiv_chartAction g hchain.1)
    (isConformalMap_fderiv_chartAction h hchain.2.1) hchain.2.2

end DifferentialGeometry.BoundaryChartConformal
