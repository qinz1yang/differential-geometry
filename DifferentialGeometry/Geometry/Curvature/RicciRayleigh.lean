import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.NonnegativeCurvatureOperator
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.Geometry.Curvature
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

def upperRicciTensorAt (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3) :
    Tensor02At (I := 𝓡 3) (M := E3) x :=
  (metricScalarAt g x / 2) • metricTensorField g x - metricRicciAt g x

def upperRicciRayleighAt (g : SmoothRiemannianMetric (𝓡 3) E3) (x v : E3) : ℝ :=
  ((metricScalarAt g x / 2) * g.inner x v v - ricciTensor g x v v) /
    g.inner x v v

def leastUpperRicciAt (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3) : ℝ :=
  sInf (Set.range fun v : ↥(Metric.sphere (0 : E3) 1) => upperRicciRayleighAt g x v.val)

private theorem unitSphere_univ_nonempty :
    (Set.univ : Set ↥(Metric.sphere (0 : E3) 1)).Nonempty := by
  obtain ⟨v, hv⟩ :=
    (NormedSpace.sphere_nonempty (E := E3) (x := (0 : E3)) (r := 1)).mpr
      (by norm_num)
  exact ⟨⟨v, hv⟩, Set.mem_univ _⟩

theorem upperRicciTensorAt_apply
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3) (v w : E3) :
    upperRicciTensorAt g x (vec2 (I := 𝓡 3) v w) =
      (metricScalarAt g x / 2) * g.inner x v w - ricciTensor g x v w := by
  change (metricScalarAt g x / 2) * g.inner x v w -
    metricRicciAt g x (vec2 (I := 𝓡 3) v w) = _
  rw [metricRicciAt_apply_eq_ricciTensor g x v w]

theorem continuous_upperRicciRayleighAt_unitSphere
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3) :
    Continuous (fun v : ↥(Metric.sphere (0 : E3) 1) => upperRicciRayleighAt g x v.val) := by
  have hv : Continuous (fun v : ↥(Metric.sphere (0 : E3) 1) => (v : E3)) :=
    continuous_subtype_val
  have hd : Continuous (fun v : ↥(Metric.sphere (0 : E3) 1) =>
      g.inner x (v : E3) (v : E3)) :=
    ((continuous_const (y := g.inner x)).clm_apply hv).clm_apply hv
  have hRic : Continuous (fun v : ↥(Metric.sphere (0 : E3) 1) =>
      ricciTensor g x (v : E3) (v : E3)) :=
    ((continuous_const (y := ricciTensor g x)).clm_apply hv).clm_apply hv
  exact ((continuous_const.mul hd).sub hRic).div hd
    (fun v => ne_of_gt (g.pos x v.val (Metric.ne_of_mem_sphere v.property one_ne_zero)))

theorem exists_unitSphere_minimizer_upperRicciRayleighAt
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3) :
    ∃ v : ↥(Metric.sphere (0 : E3) 1),
      leastUpperRicciAt g x = upperRicciRayleighAt g x v.val ∧
      ∀ w : ↥(Metric.sphere (0 : E3) 1),
        upperRicciRayleighAt g x v.val ≤ upperRicciRayleighAt g x w.val := by
  obtain ⟨v, _hv, hval, hmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set ↥(Metric.sphere (0 : E3) 1))).exists_sInf_image_eq_and_le unitSphere_univ_nonempty
        (continuous_upperRicciRayleighAt_unitSphere g x).continuousOn
  refine ⟨v, ?_, fun w => hmin w (Set.mem_univ w)⟩
  simpa only [leastUpperRicciAt, Set.image_univ] using hval

theorem upperRicciRayleighAt_smul
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (v : E3) (c : ℝ) (hc : c ≠ 0) :
    upperRicciRayleighAt g x (c • v) = upperRicciRayleighAt g x v := by
  have hscale (B : E3 →L[ℝ] E3 →L[ℝ] ℝ) :
      B (c • v) (c • v) = c ^ 2 * B v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner x
  let Ric : E3 →L[ℝ] E3 →L[ℝ] ℝ := ricciTensor g x
  change (metricScalarAt g x / 2 * B (c • v) (c • v) -
    Ric (c • v) (c • v)) / B (c • v) (c • v) =
    (metricScalarAt g x / 2 * B v v - Ric v v) / B v v
  rw [hscale B, hscale Ric]
  rw [show metricScalarAt g x / 2 * (c ^ 2 * B v v) -
      c ^ 2 * Ric v v =
      c ^ 2 * (metricScalarAt g x / 2 * B v v - Ric v v) by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hc)

theorem leastUpperRicciAt_le_rayleigh
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (v : E3) (hv : v ≠ 0) :
    leastUpperRicciAt g x ≤ upperRicciRayleighAt g x v := by
  let w : ↥(Metric.sphere (0 : E3) 1) :=
    ⟨‖v‖⁻¹ • v, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hv)⟩
  obtain ⟨z, hz, hmin⟩ := exists_unitSphere_minimizer_upperRicciRayleighAt g x
  have h := hmin w
  rw [← hz] at h
  change leastUpperRicciAt g x ≤ upperRicciRayleighAt g x (‖v‖⁻¹ • v) at h
  rwa [upperRicciRayleighAt_smul g x v _ (inv_ne_zero (norm_ne_zero_iff.mpr hv))]
    at h

theorem leastUpperRicciAt_nonneg_of_ricci_upper
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (hupper : ∀ v : E3,
      ricciTensor g x v v ≤ (metricScalarAt g x / 2) * g.inner x v v) :
    0 ≤ leastUpperRicciAt g x := by
  obtain ⟨v, hv, _hmin⟩ := exists_unitSphere_minimizer_upperRicciRayleighAt g x
  rw [hv]
  exact div_nonneg (sub_nonneg.mpr (hupper v.val))
    (g.pos x v.val (Metric.ne_of_mem_sphere v.property one_ne_zero)).le

theorem ricci_upper_of_leastUpperRicciAt_nonneg
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (hmin : 0 ≤ leastUpperRicciAt g x) :
    ∀ v : E3, ricciTensor g x v v ≤ (metricScalarAt g x / 2) * g.inner x v v := by
  intro v
  by_cases hv : v = 0
  · subst v
    let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner x
    let Ric : E3 →L[ℝ] E3 →L[ℝ] ℝ := ricciTensor g x
    change Ric 0 0 ≤ metricScalarAt g x / 2 * B 0 0
    simp only [map_zero, mul_zero, le_refl]
  · have hq := hmin.trans (leastUpperRicciAt_le_rayleigh g x v hv)
    have hd : 0 < g.inner x v v := g.pos x v hv
    have hn := mul_nonneg hq hd.le
    change 0 ≤
      (((metricScalarAt g x / 2) * g.inner x v v - ricciTensor g x v v) /
        g.inner x v v) * g.inner x v v at hn
    rw [div_mul_cancel₀ _ (ne_of_gt hd)] at hn
    exact sub_nonneg.mp hn

theorem leastUpperRicciAt_of_ordered_eigenframe
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (horth : OrthonormalBasisAt (I := 𝓡 3) g x basis)
    (r1 r2 r3 : ℝ) (h21 : r2 ≤ r1) (h32 : r3 ≤ r2)
    (hdiag : ∀ i j : Fin 3,
      metricRicciAt g x (vec2 (I := 𝓡 3) (basis i) (basis j)) =
        ricciDiag3 r1 r2 r3 i j) :
    leastUpperRicciAt g x = metricScalarAt g x / 2 - r1 ∧
    g.inner x (basis 0) (basis 0) = 1 ∧
    upperRicciRayleighAt g x (basis 0) = leastUpperRicciAt g x ∧
    (∀ w : E3,
      upperRicciTensorAt g x (vec2 (I := 𝓡 3) (basis 0) w) =
        leastUpperRicciAt g x * g.inner x (basis 0) w) ∧
    (∀ w : E3,
      upperRicciTensorAt g x (vec2 (I := 𝓡 3) w (basis 0)) =
        leastUpperRicciAt g x * g.inner x w (basis 0)) := by
  classical
  have hRdiag (i j : Fin 3) :
      ricciTensor g x (basis i) (basis j) = ricciDiag3 r1 r2 r3 i j := by
    rw [← metricRicciAt_apply_eq_ricciTensor]
    exact hdiag i j
  have hON : ∀ i j : Fin 3,
      g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    simpa only [OrthonormalBasisAt, delta3] using horth
  have hgexp (w : E3) :
      g.inner x w w =
        (basis.repr w 0) ^ 2 + (basis.repr w 1) ^ 2 + (basis.repr w 2) ^ 2 := by
    have h := inner_sum_orthonormal g x basis hON (fun i => basis.repr w i)
    have hsum : (∑ i : Fin 3, basis.repr w i • basis i) = w := basis.sum_repr w
    rw [hsum] at h
    simpa only [Fin.sum_univ_three] using h
  have hRexp (w : E3) :
      ricciTensor g x w w =
        (basis.repr w 0) ^ 2 * r1 +
        (basis.repr w 1) ^ 2 * r2 + (basis.repr w 2) ^ 2 * r3 := by
    rw [← metricRicciAt_apply_eq_ricciTensor g x w w,
      ricci_quad_sum_repr (metricRicciAt g x) basis w]
    simp [hdiag, ricciDiag3, Fin.sum_univ_three, pow_two]
  have hRupper (w : E3) : ricciTensor g x w w ≤ r1 * g.inner x w w := by
    rw [hRexp, hgexp]
    nlinarith [mul_nonneg (sub_nonneg.mpr h21) (sq_nonneg (basis.repr w 1)),
      mul_nonneg (sub_nonneg.mpr (h32.trans h21)) (sq_nonneg (basis.repr w 2))]
  have hunit : g.inner x (basis 0) (basis 0) = 1 := by
    simpa [delta3] using horth 0 0
  have hvalue :
      upperRicciRayleighAt g x (basis 0) = metricScalarAt g x / 2 - r1 := by
    unfold upperRicciRayleighAt
    rw [hunit, hRdiag 0 0]
    simp [ricciDiag3]
  have hlower (w : E3) (hw : w ≠ 0) :
      metricScalarAt g x / 2 - r1 ≤ upperRicciRayleighAt g x w := by
    unfold upperRicciRayleighAt
    apply (le_div_iff₀ (g.pos x w hw)).mpr
    nlinarith only [hRupper w]
  obtain ⟨w, hw, _hmin⟩ := exists_unitSphere_minimizer_upperRicciRayleighAt g x
  have hminlower : metricScalarAt g x / 2 - r1 ≤ leastUpperRicciAt g x := by
    rw [hw]
    exact hlower w.val (Metric.ne_of_mem_sphere w.property one_ne_zero)
  have hminupper :=
    leastUpperRicciAt_le_rayleigh g x (basis 0) (basis.ne_zero 0)
  rw [hvalue] at hminupper
  have hmin : leastUpperRicciAt g x = metricScalarAt g x / 2 - r1 :=
    le_antisymm hminupper hminlower
  have hRicFirst (w : E3) :
      ricciTensor g x (basis 0) w = r1 * g.inner x (basis 0) w := by
    have hwexp : w = ∑ i : Fin 3, basis.repr w i • basis i :=
      (basis.sum_repr w).symm
    rw [hwexp]
    simp [map_smul, smul_eq_mul, hRdiag, hON,
      ricciDiag3, Fin.sum_univ_three, mul_comm]
  have hRicLast (w : E3) :
      ricciTensor g x w (basis 0) = r1 * g.inner x w (basis 0) := by
    rw [ricciTensor_symm g x w (basis 0), g.symm x w (basis 0)]
    exact hRicFirst w
  refine ⟨hmin, hunit, hvalue.trans hmin.symm, ?_, ?_⟩
  · intro z
    rw [upperRicciTensorAt_apply g x (basis 0) z, hRicFirst, hmin]
    ring
  · intro z
    rw [upperRicciTensorAt_apply g x z (basis 0), hRicLast, hmin]
    ring

theorem exists_ordered_ricci_frame_leastUpperRicciAt
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3) :
    ∃ basis : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x),
      ∃ r1 r2 r3 : ℝ,
        OrthonormalBasisAt (I := 𝓡 3) g x basis ∧ r2 ≤ r1 ∧ r3 ≤ r2 ∧
        (∀ i j : Fin 3,
          metricRicciAt g x (vec2 (I := 𝓡 3) (basis i) (basis j)) =
            ricciDiag3 r1 r2 r3 i j) ∧
        leastUpperRicciAt g x = metricScalarAt g x / 2 - r1 ∧
        g.inner x (basis 0) (basis 0) = 1 ∧
        upperRicciRayleighAt g x (basis 0) = leastUpperRicciAt g x ∧
        (∀ w : E3,
          upperRicciTensorAt g x (vec2 (I := 𝓡 3) (basis 0) w) =
            leastUpperRicciAt g x * g.inner x (basis 0) w) ∧
        (∀ w : E3,
          upperRicciTensorAt g x (vec2 (I := 𝓡 3) w (basis 0)) =
            leastUpperRicciAt g x * g.inner x w (basis 0)) := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 :=
    finrank_euclideanSpace_fin
  have hsymm : RicciSymAt (I := 𝓡 3) (metricRicciAt g x) := by
    intro v w
    rw [metricRicciAt_apply_eq_ricciTensor, metricRicciAt_apply_eq_ricciTensor]
    exact ricciTensor_symm g x v w
  obtain ⟨basis, r1, r2, r3, horth, h21, h32, hdiag⟩ :=
    ricciEigen3_ordered g (metricRicciAt g x) hdim hsymm
  have hcomp : ∀ i j : Fin 3,
      metricRicciAt g x (vec2 (I := 𝓡 3) (basis i) (basis j)) =
        ricciDiag3 r1 r2 r3 i j := by
    intro i j
    simpa only [ricciCompAt_apply] using hdiag.2 i j
  exact ⟨basis, r1, r2, r3, horth, h21, h32, hcomp,
    leastUpperRicciAt_of_ordered_eigenframe g x basis horth r1 r2 r3 h21 h32 hcomp⟩

theorem ricciEigenvalue_abs_le_three_mul_of_rm
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3) (K : ℝ)
    (hRm : Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ K)
    (basis : Module.Basis (Fin 3) ℝ (TangentSpace (𝓡 3) x))
    (horth : OrthonormalBasisAt (I := 𝓡 3) g x basis)
    (r : ℝ)
    (hr : metricRicciAt g x (vec2 (I := 𝓡 3) (basis 0) (basis 0)) = r) :
    |r| ≤ 3 * K := by
  have hON : ∀ i j : Fin 3,
      g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    simpa only [OrthonormalBasisAt, delta3] using horth
  have h := metricRicciComp_le g basis hON 0 0
  rw [hr] at h
  have hRmAt : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ K := by
    simpa only [metricRm04_apply] using hRm
  have h' : |r| ≤ 3 * Real.sqrt (normSq0S g x 4 (metricRm04At g x)) := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using h
  exact h'.trans (mul_le_mul_of_nonneg_left hRmAt (by norm_num))

theorem abs_leastUpperRicciAt_le_eight_mul_of_rm
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (K : ℝ)
    (hRm : Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ K) :
    |leastUpperRicciAt g x| ≤ 8 * K := by
  have hK : 0 ≤ K := (Real.sqrt_nonneg _).trans hRm
  obtain ⟨basis, r1, r2, r3, horth, _h21, _h32, hdiag, hmin, _hrest⟩ :=
    exists_ordered_ricci_frame_leastUpperRicciAt g x
  have hr1 : |r1| ≤ 3 * K :=
    ricciEigenvalue_abs_le_three_mul_of_rm g x K hRm basis horth r1
      (by simpa [ricciDiag3] using hdiag 0 0)
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 :=
    finrank_euclideanSpace_fin
  have hs := scalar_abs_le_rm g x
  norm_num only [hdim] at hs
  have hRmAt : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ K := by
    simpa only [metricRm04_apply] using hRm
  have hsK : |metricScalarAt g x| ≤ 9 * K :=
    hs.trans (mul_le_mul_of_nonneg_left hRmAt (by norm_num))
  rcases abs_le.mp hsK with ⟨hslo, hshi⟩
  rcases abs_le.mp hr1 with ⟨hrlo, hrhi⟩
  rw [hmin]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem shifted_upperRicciRayleighAt_eq
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (v : E3) (hv : v ≠ 0) (ell : ℝ) :
    ell + (upperRicciTensorAt g x (vec2 (I := 𝓡 3) v v) -
        ell * g.inner x v v) / g.inner x v v =
      upperRicciRayleighAt g x v := by
  have hd : g.inner x v v ≠ 0 := ne_of_gt (g.pos x v hv)
  rw [upperRicciTensorAt_apply]
  unfold upperRicciRayleighAt
  field_simp [hd]
  ring
end DifferentialGeometry.Geometry.Curvature
