import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatPotential.Estimate
import DifferentialGeometry.Analysis.Parabolic.Euclidean.Duhamel.Laplacian
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

private theorem fderiv_eq_heatSupGradient_sub_heatDuhamelGradientMap [Nontrivial V]
    {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (x : V) :
    fderiv ℝ (u : V → F) x = heatSupGradient t u x -
      heatDuhamelGradientMap t (fun _ => coreLap d2u) x := by
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
  have hrep := eq_heatSup_sub_heatDuhamel ht u du d2u hu hdu
  have he := (heatSup_hasFDerivAt ht u x).sub
    (heatDuhamel_hasFDerivAt ht _ hb hmeas0 hmeas1 x)
  rw [← hrep] at he
  exact he.fderiv

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
    have hsource : ContinuousOn (fun q : ℝ × V => coreLap d2u q.2)
        (Ioo (0 : ℝ) t ×ˢ (Set.univ : Set V)) :=
      ((coreLap d2u).continuous.comp continuous_snd).continuousOn
    have hmeas := heatSupGradient_timeSource_aestronglyMeasurable_of_continuousOn
      ht.le (fun _ => coreLap d2u) hsource x
    have hb : ∀ s ∈ Icc (0 : ℝ) t, ‖coreLap d2u‖ ≤ ‖coreLap d2u‖₊ := by simp
    rw [fderiv_eq_heatSupGradient_sub_heatDuhamelGradientMap ht u du d2u hu hdu x]
    exact (norm_sub_le _ _).trans (add_le_add (heatSupGradient_norm_le ht u x)
      (heatDuhamelGradientMap_norm_le ht _ hb x hmeas))

private theorem norm_fderiv_sub_le_of_bounded_laplacian
    {alpha : NNReal} (halpha : alpha < 1) {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (x y : V) :
    ‖fderiv ℝ (u : V → F) x - fderiv ℝ (u : V → F) y‖ ≤
      (heatC2 V + 2 * heatC1 V) *
        (‖u‖ * t ^ (-(1 + (alpha : ℝ)) / 2) +
          2 * ‖coreLap d2u‖ / (1 - (alpha : ℝ)) * t ^ ((1 - (alpha : ℝ)) / 2)) *
        ‖x - y‖ ^ (alpha : ℝ) := by
  have ha : (alpha : ℝ) < 1 := by exact_mod_cast halpha
  have hC1 := heatC1_nonneg (V := V)
  have hC2 := heatC2_nonneg (V := V)
  rcases subsingleton_or_nontrivial V with hV | hV
  · let : Subsingleton V := hV
    rw [Subsingleton.elim x y, sub_self, norm_zero]
    positivity
  · let : Nontrivial V := hV
    have hsource : ContinuousOn (fun q : ℝ × V => coreLap d2u q.2)
        (Ioo (0 : ℝ) t ×ˢ (Set.univ : Set V)) :=
      ((coreLap d2u).continuous.comp continuous_snd).continuousOn
    have hmeas := heatSupGradient_timeSource_aestronglyMeasurable_of_continuousOn
      ht.le (fun _ => coreLap d2u) hsource
    have hb : ∀ s ∈ Icc (0 : ℝ) t, ‖coreLap d2u‖ ≤ ‖coreLap d2u‖₊ := by simp
    have h1 := (heatSupGradient_holderWith halpha.le ht u).dist_le x y
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h2 := heatDuhamelGradientMap_norm_sub_le halpha ht
      (fun _ => coreLap d2u) hb hmeas x y
    rw [fderiv_eq_heatSupGradient_sub_heatDuhamelGradientMap ht u du d2u hu hdu x,
      fderiv_eq_heatSupGradient_sub_heatDuhamelGradientMap ht u du d2u hu hdu y,
      sub_sub_sub_comm]
    refine ((norm_sub_le _ _).trans (add_le_add h1 h2)).trans_eq ?_
    change ((heatC2 V + 2 * heatC1 V) * ‖u‖ * t ^ (-(1 + (alpha : ℝ)) / 2)) *
      ‖x - y‖ ^ (alpha : ℝ) +
      ((2 / (1 - (alpha : ℝ))) * (heatC2 V + 2 * heatC1 V) * ‖coreLap d2u‖ *
        t ^ ((1 - (alpha : ℝ)) / 2)) * ‖x - y‖ ^ (alpha : ℝ) = _
    ring

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

theorem norm_fderiv_sub_le_of_laplacian_bound
    {f : V → F} (hf : ContDiff ℝ 2 f) (hcs : HasCompactSupport f)
    {alpha : NNReal} (halpha : alpha < 1) {t M B : ℝ} (ht : 0 < t)
    (hM : ∀ x : V, ‖f x‖ ≤ M)
    (hB : ∀ x : V, ‖Laplacian.laplacian f x‖ ≤ B) (x y : V) :
    ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤
      (heatC2 V + 2 * heatC1 V) *
        (M * t ^ (-(1 + (alpha : ℝ)) / 2) +
          2 * B / (1 - (alpha : ℝ)) * t ^ ((1 - (alpha : ℝ)) / 2)) *
        ‖x - y‖ ^ (alpha : ℝ) := by
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
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have hB0 : 0 ≤ B := (norm_nonneg (Laplacian.laplacian f 0)).trans (hB 0)
  have hnorm : ‖u‖ ≤ M := (BoundedContinuousFunction.norm_le hM0).2 hM
  have hnormΔ : ‖coreLap d2u‖ ≤ B := (BoundedContinuousFunction.norm_le hB0).2
    (fun z => by
      rw [coreLap_eq_laplacian u du d2u hu hdu z]
      exact hB z)
  have h := norm_fderiv_sub_le_of_bounded_laplacian halpha ht u du d2u hu hdu x y
  have ha : (alpha : ℝ) < 1 := by exact_mod_cast halpha
  have hC1 := heatC1_nonneg (V := V)
  have hC2 := heatC2_nonneg (V := V)
  refine h.trans ?_
  gcongr

end DifferentialGeometry.Analysis
