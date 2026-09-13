import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatPotential.Estimate
import DifferentialGeometry.Analysis.Parabolic.Euclidean.Duhamel.Frozen
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Topology.ContinuousMap.CompactlySupported

open MeasureTheory Set
open scoped NNReal

namespace DifferentialGeometry.Analysis

open Parabolic.Euclidean Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem norm_fderiv_le_of_bounded_laplacian
    {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (x : V) :
    ‖fderiv ℝ (u : V → F) x‖ ≤ (Real.sqrt t)⁻¹ * heatC1 V * ‖u‖ +
      2 * ‖coreLap d2u‖ * heatC1 V * Real.sqrt t := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · let : Subsingleton V := hV
    have hz : fderiv ℝ (u : V → F) x = 0 := by
      ext v
      rw [Subsingleton.elim v 0]
      simp
    rw [hz, norm_zero]
    have hC := heatC1_nonneg (V := V)
    positivity
  · let : Nontrivial V := hV
    have hulip : LipschitzWith ‖du‖₊ (u : V → F) := by
      apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      · exact fun y => (hu y).differentiableAt
      · intro y
        rw [(hu y).fderiv]
        exact_mod_cast du.norm_coe_le_norm y
    have huzero : HolderWith (2 * ‖u‖₊) 0 (u : V → F) :=
      holderWith_zero_of_norm_le u.norm_coe_le_norm
    have huhalf : HolderWith (max (2 * ‖u‖₊) ‖du‖₊) (1 / 2 : NNReal) (u : V → F) :=
      huzero.of_le_of_le hulip.holderWith (by positivity) (by norm_num)
    have hsource : ContinuousOn (fun q : ℝ × V => coreLap d2u q.2)
        (Ioo (0 : ℝ) t ×ˢ (Set.univ : Set V)) :=
      ((coreLap d2u).continuous.comp continuous_snd).continuousOn
    have hmeas0 (z : V) : AEStronglyMeasurable
        (fun s : ℝ => heatSup (t - s) (coreLap d2u) z)
        (volume.restrict (uIoc (0 : ℝ) t)) :=
      heatSup_timeSource_aestronglyMeasurable_of_continuousOn ht.le
        (fun _ => coreLap d2u) hsource z
    have hmeas1 (z : V) : AEStronglyMeasurable
        (fun s : ℝ => heatSupGradient (t - s) (coreLap d2u) z)
        (volume.restrict (uIoc (0 : ℝ) t)) :=
      heatSupGradient_timeSource_aestronglyMeasurable_of_continuousOn ht.le
        (fun _ => coreLap d2u) hsource z
    have hb : ∀ s ∈ Icc (0 : ℝ) t, ‖coreLap d2u‖ ≤ ‖coreLap d2u‖₊ := by simp
    have hrep : (u : V → F) =
        (fun y => heatSup t u y) - heatDuhamel t (fun _ => coreLap d2u) := by
      funext y
      rw [Pi.sub_apply, heatDuhamel_const_eq_integral_heatSup,
        heatSup_primitive ht u du d2u hu hdu huhalf y]
      abel
    have heq : fderiv ℝ (u : V → F) x = heatSupGradient t u x -
        fderiv ℝ (heatDuhamel t (fun _ => coreLap d2u)) x := by
      conv_lhs => rw [hrep]
      rw [fderiv_sub (heatSup_hasFDerivAt ht u x).differentiableAt
        (heatDuhamel_hasFDerivAt ht _ hb hmeas0 hmeas1 x).differentiableAt,
        (heatSup_hasFDerivAt ht u x).fderiv]
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add (heatSupGradient_norm_le ht u x)
      (heatDuhamel_fderiv_norm_le ht _ hb hmeas0 hmeas1 x))

omit [MeasurableSpace V] [BorelSpace V] [CompleteSpace F] in
private theorem coreLap_eq_laplacian
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (x : V) : coreLap d2u x = Laplacian.laplacian (u : V → F) x := by
  have he : fderiv ℝ (u : V → F) = (du : V → V →L[ℝ] F) :=
    funext fun y => (hu y).fderiv
  simp only [coreLap_apply, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, he, (hdu x).fderiv]

private theorem norm_fderiv_le_of_bounded_laplacian_bound
    {t B : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (hbound : ∀ x : V, ‖Laplacian.laplacian (u : V → F) x‖ ≤ B)
    (x : V) :
    ‖fderiv ℝ (u : V → F) x‖ ≤ (Real.sqrt t)⁻¹ * heatC1 V * ‖u‖ +
      2 * B * heatC1 V * Real.sqrt t := by
  have hB : 0 ≤ B := (norm_nonneg (Laplacian.laplacian (u : V → F) 0)).trans (hbound 0)
  have hb : ‖coreLap d2u‖ ≤ B := (BoundedContinuousFunction.norm_le hB).2 (fun y => by
    rw [coreLap_eq_laplacian u du d2u hu hdu y]
    exact hbound y)
  have h := norm_fderiv_le_of_bounded_laplacian ht u du d2u hu hdu x
  have hC := heatC1_nonneg (V := V)
  have hcoef : 0 ≤ 2 * heatC1 V * Real.sqrt t := by positivity
  have hm := mul_le_mul_of_nonneg_right hb hcoef
  nlinarith only [h, hm]

theorem norm_fderiv_le_of_laplacian_bound
    {f : V → F} (hf : ContDiff ℝ 2 f) (hcs : HasCompactSupport f)
    {t M B : ℝ} (ht : 0 < t)
    (hM : ∀ x : V, ‖f x‖ ≤ M)
    (hB : ∀ x : V, ‖Laplacian.laplacian f x‖ ≤ B) (x : V) :
    ‖fderiv ℝ f x‖ ≤ (Real.sqrt t)⁻¹ * heatC1 V * M +
      2 * B * heatC1 V * Real.sqrt t := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  let u : BoundedContinuousFunction V F :=
    (⟨⟨f, hf.continuous⟩, hcs⟩ : CompactlySupportedContinuousMap V F).toBoundedContinuousFunction
  let du : BoundedContinuousFunction V (V →L[ℝ] F) :=
    (⟨⟨fderiv ℝ f, hdf.continuous⟩, hcs.fderiv ℝ⟩ :
      CompactlySupportedContinuousMap V (V →L[ℝ] F)).toBoundedContinuousFunction
  let d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F) :=
    (⟨⟨fderiv ℝ (fderiv ℝ f), hdf.continuous_fderiv (by norm_num)⟩,
      (hcs.fderiv ℝ).fderiv ℝ⟩ :
      CompactlySupportedContinuousMap V (V →L[ℝ] V →L[ℝ] F)).toBoundedContinuousFunction
  have hu (y : V) : HasFDerivAt (u : V → F) (du y) y :=
    (hf.differentiable (by norm_num) y).hasFDerivAt
  have hdu (y : V) : HasFDerivAt (du : V → V →L[ℝ] F) (d2u y) y :=
    (hdf.differentiable (by norm_num) y).hasFDerivAt
  have h := norm_fderiv_le_of_bounded_laplacian_bound ht u du d2u hu hdu hB x
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have hnorm : ‖u‖ ≤ M := (BoundedContinuousFunction.norm_le hM0).2 hM
  have hcoef : 0 ≤ (Real.sqrt t)⁻¹ * heatC1 V :=
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg t)) (heatC1_nonneg (V := V))
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hnorm hcoef) le_rfl)

end DifferentialGeometry.Analysis
