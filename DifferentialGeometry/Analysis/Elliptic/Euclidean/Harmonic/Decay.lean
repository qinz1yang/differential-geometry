import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.HarmonicDecay
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Laplacian
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.Harmonic
import DifferentialGeometry.Analysis.Integration.Integral.Laplacian
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace InnerProductSpace

theorem HarmonicOnNhd.comp_linearIsometryEquiv
    {E G F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : G → F} {U : Set G} (hf : HarmonicOnNhd f U) (e : E ≃ₗᵢ[ℝ] G) :
    HarmonicOnNhd (f ∘ e) (e ⁻¹' U) := by
  intro x hx
  refine ⟨(hf (e x) hx).1.comp x e.toContinuousLinearEquiv.contDiff.contDiffAt, ?_⟩
  have hh := e.continuous.continuousAt.preimage_mem_nhds (hf (e x) hx).2
  filter_upwards [hh] with y hy
  rw [LinearIsometryEquiv.laplacian_comp e f y]
  exact hy

end InnerProductSpace

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem harmonic_integral_gradient_sq_le_radius_ratio_sq
    {f : V → ℝ} {c : V} {r R : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 2)
    (hf : HarmonicOnNhd f (Metric.ball c R))
    (hi : IntegrableOn (fun x => ∑ j : Fin 2,
      (fderiv ℝ f x (EuclideanSpace.single j 1)) ^ 2) (Metric.ball c R)) :
    (∫ x in Metric.ball c r, ∑ j : Fin 2, (fderiv ℝ f x (EuclideanSpace.single j 1)) ^ 2) ≤
      16 * (r / R) ^ 2 * ∫ x in Metric.ball c R,
        ∑ j : Fin 2, (fderiv ℝ f x (EuclideanSpace.single j 1)) ^ 2 := by
  let e := Complex.orthonormalBasisOneI.repr
  let g := f ∘ e
  have hpre (s : ℝ) : e ⁻¹' Metric.ball c s = Metric.ball (e.symm c) s := by
    ext x
    simp only [mem_preimage, Metric.mem_ball]
    rw [← e.dist_map, e.apply_symm_apply]
  have hg : HarmonicOnNhd g (Metric.ball (e.symm c) R) := by
    simpa only [hpre] using hf.comp_linearIsometryEquiv e
  have hrepr (j : Fin 2) : e (Complex.orthonormalBasisOneI j) = EuclideanSpace.single j 1 :=
    Complex.orthonormalBasisOneI.repr_self j
  have hd (j : Fin 2) (z : ℂ) : fderiv ℝ g z (Complex.orthonormalBasisOneI j) =
      fderiv ℝ f (e z) (EuclideanSpace.single j 1) := by
    rw [show g = f ∘ e.toContinuousLinearEquiv by rfl, e.toContinuousLinearEquiv.comp_right_fderiv]
    change fderiv ℝ f (e z) (e (Complex.orthonormalBasisOneI j)) = _
    rw [hrepr]
  let D := fun x => ∑ j : Fin 2, (fderiv ℝ f x (EuclideanSpace.single j 1)) ^ 2
  have hsum (z : ℂ) : (fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z Complex.I) ^ 2 = D (e z) := by
    have h0 := hd 0 z
    have h1 := hd 1 z
    simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    dsimp only [D]
    rw [Fin.sum_univ_two, h0, h1]
  have hmp (s : ℝ) : MeasurePreserving e (volume.restrict (Metric.ball (e.symm c) s))
      (volume.restrict (Metric.ball c s)) := by
    have hh := e.measurePreserving.restrict_preimage
      (s := Metric.ball c s) Metric.isOpen_ball.measurableSet
    rwa [hpre] at hh
  have hgi : IntegrableOn (fun z => (fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z Complex.I) ^ 2)
      (Metric.ball (e.symm c) R) := by
    simp_rw [hsum]
    exact (hmp R).integrable_comp_of_integrable hi
  have hint (s : ℝ) : (∫ z in Metric.ball (e.symm c) s,
      (fderiv ℝ g z 1) ^ 2 + (fderiv ℝ g z Complex.I) ^ 2) = ∫ x in Metric.ball c s, D x := by
    simp_rw [hsum]
    exact (hmp s).integral_comp e.toMeasurableEquiv.measurableEmbedding D
  have hh := harmonic_integral_derivative_sq_le_radius_ratio_sq hR hr hrR hg hgi
  rwa [hint r, hint R] at hh

end DifferentialGeometry.Analysis

end

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem harmonic_integral_gradient_sub_center_sq_le_radius_ratio_pow_four
    {f : V → ℝ} {c : V} {r R : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 4)
    (hf : HarmonicOnNhd f (Metric.ball c R)) (p : V)
    (hi : IntegrableOn (fun x => ∑ j : Fin 2,
      (fderiv ℝ f x (EuclideanSpace.single j 1) - p j) ^ 2) (Metric.ball c R)) :
    (∫ x in Metric.ball c r, ∑ j : Fin 2,
      (fderiv ℝ f x (EuclideanSpace.single j 1) - fderiv ℝ f c (EuclideanSpace.single j 1)) ^ 2) ≤
      256 * (r / R) ^ 4 * ∫ x in Metric.ball c R,
        ∑ j : Fin 2, (fderiv ℝ f x (EuclideanSpace.single j 1) - p j) ^ 2 := by
  let e := Complex.orthonormalBasisOneI.repr
  let g := f ∘ e
  have hpre (s : ℝ) : e ⁻¹' Metric.ball c s = Metric.ball (e.symm c) s := by
    ext x
    simp only [mem_preimage, Metric.mem_ball]
    rw [← e.dist_map, e.apply_symm_apply]
  have hg : HarmonicOnNhd g (Metric.ball (e.symm c) R) := by
    simpa only [hpre] using hf.comp_linearIsometryEquiv e
  have hrepr (j : Fin 2) : e (Complex.orthonormalBasisOneI j) = EuclideanSpace.single j 1 :=
    Complex.orthonormalBasisOneI.repr_self j
  have hd (j : Fin 2) (z : ℂ) : fderiv ℝ g z (Complex.orthonormalBasisOneI j) =
      fderiv ℝ f (e z) (EuclideanSpace.single j 1) := by
    rw [show g = f ∘ e.toContinuousLinearEquiv by rfl, e.toContinuousLinearEquiv.comp_right_fderiv]
    change fderiv ℝ f (e z) (e (Complex.orthonormalBasisOneI j)) = _
    rw [hrepr]
  let D := fun x => ∑ j : Fin 2, (fderiv ℝ f x (EuclideanSpace.single j 1) - p j) ^ 2
  have hsum (z : ℂ) :
      (fderiv ℝ g z 1 - p 0) ^ 2 + (fderiv ℝ g z Complex.I - p 1) ^ 2 = D (e z) := by
    have h0 := hd 0 z
    have h1 := hd 1 z
    simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    dsimp only [D]
    rw [Fin.sum_univ_two, h0, h1]
  have hmp (s : ℝ) : MeasurePreserving e (volume.restrict (Metric.ball (e.symm c) s))
      (volume.restrict (Metric.ball c s)) := by
    have hh := e.measurePreserving.restrict_preimage
      (s := Metric.ball c s) Metric.isOpen_ball.measurableSet
    rwa [hpre] at hh
  have hgi : IntegrableOn (fun z => (fderiv ℝ g z 1 - p 0) ^ 2 + (fderiv ℝ g z Complex.I - p 1) ^ 2)
      (Metric.ball (e.symm c) R) := by
    simp_rw [hsum]
    exact (hmp R).integrable_comp_of_integrable hi
  have hint (s : ℝ) : (∫ z in Metric.ball (e.symm c) s,
      (fderiv ℝ g z 1 - p 0) ^ 2 + (fderiv ℝ g z Complex.I - p 1) ^ 2) =
      ∫ x in Metric.ball c s, D x := by
    simp_rw [hsum]
    exact (hmp s).integral_comp e.toMeasurableEquiv.measurableEmbedding D
  let Dc := fun x => ∑ j : Fin 2,
    (fderiv ℝ f x (EuclideanSpace.single j 1) - fderiv ℝ f c (EuclideanSpace.single j 1)) ^ 2
  have hdiff (z : ℂ) :
      (fderiv ℝ g z 1 - fderiv ℝ g (e.symm c) 1) ^ 2 +
        (fderiv ℝ g z Complex.I - fderiv ℝ g (e.symm c) Complex.I) ^ 2 = Dc (e z) := by
    have h0 := hd 0 z
    have h1 := hd 1 z
    have hc0 := hd 0 (e.symm c)
    have hc1 := hd 1 (e.symm c)
    simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
      e.apply_symm_apply] at h0 h1 hc0 hc1
    dsimp only [Dc]
    rw [Fin.sum_univ_two, h0, h1, hc0, hc1]
  have hintdiff : (∫ z in Metric.ball (e.symm c) r,
      (fderiv ℝ g z 1 - fderiv ℝ g (e.symm c) 1) ^ 2 +
        (fderiv ℝ g z Complex.I - fderiv ℝ g (e.symm c) Complex.I) ^ 2) =
      ∫ x in Metric.ball c r, Dc x := by
    simp_rw [hdiff]
    exact (hmp r).integral_comp e.toMeasurableEquiv.measurableEmbedding Dc
  have hh := harmonic_integral_derivative_sub_center_sq_le_radius_ratio_pow_four
    hR hr hrR hg (p 0) (p 1) hgi
  rwa [hintdiff, hint R] at hh

end DifferentialGeometry.Analysis

end

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)


private theorem integral_mul_laplacian_eq_zero_of_weakly_harmonic
    {Ω : Set E} {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hEuler : ∀ φ : E → ℝ, DeGiorgi.IsSmoothTestOn Ω φ →
      (∫ x in Ω, inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0)
    {φ : E → ℝ} (hφ : DeGiorgi.IsSmoothTestOn Ω φ) :
    (∫ x in Ω, u x * Laplacian.laplacian φ x) = 0 := by
  let D (j : Fin d) (x : E) := fderiv ℝ φ x (EuclideanSpace.single j 1)
  have hD (j : Fin d) : ContDiff ℝ ∞ (D j) :=
    (hφ.1.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc (j : Fin d) : HasCompactSupport (D j) := hφ.2.1.fderiv_apply ℝ _
  have hDs (j : Fin d) : tsupport (D j) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ _).trans hφ.2.2
  have hweak (j : Fin d) := hu.isWeakGrad j (D j) (hD j) (hDc j) (hDs j)
  have hleftI (j : Fin d) : IntegrableOn
      (fun x => u x * fderiv ℝ (D j) x (EuclideanSpace.single j 1)) Ω := by
    exact (hu.memLp.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      (((hD j).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hDc j).fderiv_apply ℝ _)
  have hrightI (j : Fin d) : IntegrableOn (fun x => hu.weakGrad x j * D j x) Ω := by
    have hi := (hu.weakGrad_component_memLp j).locallyIntegrable (by norm_num)
    exact hi.integrable_smul_right_of_hasCompactSupport (hD j).continuous (hDc j)
  have hEq : (∫ x in Ω, u x * Laplacian.laplacian φ x) =
      -∫ x in Ω, inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x) := by
    simp_rw [laplacian_eq_sum_euclidean_fderiv (hφ.1.contDiffAt.of_le (by norm_cast)),
      Finset.mul_sum]
    rw [integral_finsetSum _ (fun j _ => hleftI j)]
    simp_rw [hweak]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => hrightI j)]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      DeGiorgi.smoothGradField, D, mul_comm]
  rw [hEq, hEuler φ hφ, neg_zero]

theorem harmonicOnNhd_of_contDiffOn_ae_eq_weakly_harmonic
    {Ω U : Set E} (hU : IsOpen U) (hUΩ : U ⊆ Ω) {u f : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω) (hf : ContDiffOn ℝ 2 f U)
    (hfu : f =ᵐ[volume.restrict U] u)
    (hEuler : ∀ φ : E → ℝ, DeGiorgi.IsSmoothTestOn Ω φ →
      (∫ x in Ω, inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) :
    HarmonicOnNhd f U := by
  have hΔcont : ContinuousOn (Laplacian.laplacian f) U := by
    intro x hx
    exact ((hf.contDiffAt (hU.mem_nhds hx)).continuousAt_laplacian).continuousWithinAt
  have hΔAE : ∀ᵐ x ∂volume, x ∈ U → Laplacian.laplacian f x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hΔcont.locallyIntegrableOn hU.measurableSet)
    intro φ hφ hφc hφU
    have hφΩ : DeGiorgi.IsSmoothTestOn Ω φ := ⟨hφ, hφc, hφU.trans hUΩ⟩
    have hzero := integral_mul_laplacian_eq_zero_of_weakly_harmonic hu hEuler hφΩ
    have hΔsupp : tsupport (Laplacian.laplacian φ) ⊆ U := (tsupport_laplacian_subset φ).trans hφU
    rw [DifferentialGeometry.Analysis.integral_smul_laplacian_eq_integral_laplacian_smul
      (hφ.of_le (by norm_cast)) hφc (fun x hx => hf.contDiffAt (hU.mem_nhds (hφU hx)))]
    have hrestrict : (∫ x, Laplacian.laplacian φ x * f x) =
        ∫ x in U, Laplacian.laplacian φ x * f x := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hΔsupp h)), zero_mul]
    simp only [smul_eq_mul]
    rw [hrestrict]
    have heq := integral_congr_ae
      (hfu.mono fun x hx => congrArg (fun v => Laplacian.laplacian φ x * v) hx)
    rw [heq]
    have hset : (∫ x in U, Laplacian.laplacian φ x * u x) =
        ∫ x in Ω, u x * Laplacian.laplacian φ x := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      · apply integral_congr_ae
        exact Eventually.of_forall fun x => mul_comm _ _
      · intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hUΩ (hΔsupp h))), mul_zero]
      · intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hΔsupp h)), zero_mul]
    exact hset.trans hzero
  have hΔeq : EqOn (Laplacian.laplacian f) 0 U := volume.eqOn_open_of_ae_eq
    ((ae_restrict_iff' hU.measurableSet).mpr hΔAE) hU hΔcont continuousOn_const
  intro x hx
  refine ⟨hf.contDiffAt (hU.mem_nhds hx), ?_⟩
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hΔeq hy

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem integral_weakGrad_sq_le_radius_ratio_sq_of_harmonic
    {u : E → ℝ} {c : E} {r R : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 4)
    (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball c R))
    (hEuler : ∀ φ : E → ℝ, DeGiorgi.IsSmoothTestOn (Metric.ball c R) φ →
      (∫ x in Metric.ball c R, inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) :
    (∫ x in Metric.ball c r, ‖hu.weakGrad x‖ ^ 2) ≤
      64 * (r / R) ^ 2 * ∫ x in Metric.ball c R, ‖hu.weakGrad x‖ ^ 2 := by
  let S := Metric.ball c (3 * R / 4)
  have hS : IsOpen S := Metric.isOpen_ball
  have hSpos : 0 < 3 * R / 4 := by positivity
  have hSR : 3 * R / 4 < R := by linarith
  have hSc : IsCompact (closure S) := by
    rw [closure_ball c hSpos.ne']
    exact isCompact_closedBall _ _
  have hSsub : closure S ⊆ Metric.ball c R := by
    rw [closure_ball c hSpos.ne']
    exact Metric.closedBall_subset_ball hSR
  obtain ⟨f, hf, hueq⟩ := exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero
    Metric.isOpen_ball hS hSc hSsub hu hEuler
  have hharm : HarmonicOnNhd f S := harmonicOnNhd_of_contDiffOn_ae_eq_weakly_harmonic
    hS (subset_closure.trans hSsub) hu (hf.of_le (by norm_cast)) hueq.symm hEuler
  have hhalfS : Metric.closedBall c (R / 2) ⊆ S := Metric.closedBall_subset_ball (by linarith)
  have hhalfR : Metric.ball c (R / 2) ⊆ Metric.ball c R := Metric.ball_subset_ball (by linarith)
  have hhalfS' : Metric.ball c (R / 2) ⊆ S := Metric.ball_subset_closedBall.trans hhalfS
  have hderEq (j : Fin 2) : (fun x => hu.weakGrad x j) =ᵐ[volume.restrict
      (Metric.ball c (R / 2))] (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) := by
    have hweakf := hasWeakPartialDeriv_of_contDiffOn Metric.isOpen_ball
      ((hf.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by norm_cast)).mono hhalfS') j
    have hweakU := DeGiorgi.HasWeakPartialDeriv.restrict Metric.isOpen_ball hhalfR (hu.isWeakGrad j)
    have hEq := ae_restrict_of_ae_restrict_of_subset hhalfS' hueq
    have hweakU' := hweakU.congr_ae hEq Filter.EventuallyEq.rfl
    have hc : ContinuousOn (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) S :=
      (hf.continuousOn_fderiv_of_isOpen hS (by norm_cast)).clm_apply continuousOn_const
    have hi : IntegrableOn (fun x => fderiv ℝ f x (EuclideanSpace.single j 1))
        (Metric.closedBall c (R / 2)) :=
      (hc.mono hhalfS).integrableOn_compact (isCompact_closedBall _ _)
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq Metric.isOpen_ball hweakU' hweakf
      (((hu.weakGrad_component_memLp j).mono_measure
        (Measure.restrict_mono_set volume hhalfR)).locallyIntegrable (by norm_num))
      (hi.mono_set Metric.ball_subset_closedBall).locallyIntegrable
  let D := fun x => ∑ j : Fin 2, (fderiv ℝ f x (EuclideanSpace.single j 1)) ^ 2
  have hnormEq : (fun x => ‖hu.weakGrad x‖ ^ 2) =ᵐ[volume.restrict
      (Metric.ball c (R / 2))] D := by
    filter_upwards [ae_all_iff.mpr hderEq] with x hx
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun j _ => congrArg (fun t : ℝ => t ^ 2) (hx j)
  have huInt : IntegrableOn (fun x => ‖hu.weakGrad x‖ ^ 2) (Metric.ball c R) :=
    hu.weakGrad_memLp.norm.integrable_sq
  have hDi : IntegrableOn D (Metric.ball c (R / 2)) :=
    (huInt.mono_set hhalfR).congr hnormEq
  have hdecay := DifferentialGeometry.Analysis.harmonic_integral_gradient_sq_le_radius_ratio_sq
    (half_pos hR) hr (by linarith : r ≤ R / 2 / 2) (hharm.mono hhalfS') hDi
  have hrhalf : Metric.ball c r ⊆ Metric.ball c (R / 2) := Metric.ball_subset_ball (by linarith)
  have heqr := integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hrhalf hnormEq)
  have heqhalf := integral_congr_ae hnormEq
  rw [← heqr, ← heqhalf] at hdecay
  have hmono : (∫ x in Metric.ball c (R / 2), ‖hu.weakGrad x‖ ^ 2) ≤
      ∫ x in Metric.ball c R, ‖hu.weakGrad x‖ ^ 2 :=
    setIntegral_mono_set huInt (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall hhalfR)
  have ht := hdecay.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
  have hc : 16 * (r / (R / 2)) ^ 2 = 64 * (r / R) ^ 2 := by ring
  rwa [hc] at ht

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem exists_integral_weakGrad_sub_sq_le_radius_ratio_pow_four_of_harmonic
    {u : E → ℝ} {c : E} {r R : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 8)
    (hu : DeGiorgi.MemW1pWitness 2 u (Metric.ball c R)) (p : E)
    (hEuler : ∀ φ : E → ℝ, DeGiorgi.IsSmoothTestOn (Metric.ball c R) φ →
      (∫ x in Metric.ball c R, inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) :
    ∃ v : E, (∫ x in Metric.ball c r, ‖hu.weakGrad x - v‖ ^ 2) ≤
      4096 * (r / R) ^ 4 * ∫ x in Metric.ball c R, ‖hu.weakGrad x - p‖ ^ 2 := by
  let S := Metric.ball c (3 * R / 4)
  have hS : IsOpen S := Metric.isOpen_ball
  have hSpos : 0 < 3 * R / 4 := by positivity
  have hSR : 3 * R / 4 < R := by linarith
  have hSc : IsCompact (closure S) := by
    rw [closure_ball c hSpos.ne']
    exact isCompact_closedBall _ _
  have hSsub : closure S ⊆ Metric.ball c R := by
    rw [closure_ball c hSpos.ne']
    exact Metric.closedBall_subset_ball hSR
  obtain ⟨f, hf, hueq⟩ := exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero
    Metric.isOpen_ball hS hSc hSsub hu hEuler
  have hharm : HarmonicOnNhd f S := harmonicOnNhd_of_contDiffOn_ae_eq_weakly_harmonic
    hS (subset_closure.trans hSsub) hu (hf.of_le (by norm_cast)) hueq.symm hEuler
  have hhalfS : Metric.closedBall c (R / 2) ⊆ S := Metric.closedBall_subset_ball (by linarith)
  have hhalfR : Metric.ball c (R / 2) ⊆ Metric.ball c R := Metric.ball_subset_ball (by linarith)
  have hhalfS' : Metric.ball c (R / 2) ⊆ S := Metric.ball_subset_closedBall.trans hhalfS
  have hderEq (j : Fin 2) : (fun x => hu.weakGrad x j) =ᵐ[volume.restrict
      (Metric.ball c (R / 2))] (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) := by
    have hweakf := hasWeakPartialDeriv_of_contDiffOn Metric.isOpen_ball
      ((hf.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by norm_cast)).mono hhalfS') j
    have hweakU := DeGiorgi.HasWeakPartialDeriv.restrict Metric.isOpen_ball hhalfR (hu.isWeakGrad j)
    have hEq := ae_restrict_of_ae_restrict_of_subset hhalfS' hueq
    have hweakU' := hweakU.congr_ae hEq Filter.EventuallyEq.rfl
    have hc : ContinuousOn (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) S :=
      (hf.continuousOn_fderiv_of_isOpen hS (by norm_cast)).clm_apply continuousOn_const
    have hi : IntegrableOn (fun x => fderiv ℝ f x (EuclideanSpace.single j 1))
        (Metric.closedBall c (R / 2)) :=
      (hc.mono hhalfS).integrableOn_compact (isCompact_closedBall _ _)
    exact DeGiorgi.HasWeakPartialDeriv.ae_eq Metric.isOpen_ball hweakU' hweakf
      (((hu.weakGrad_component_memLp j).mono_measure
        (Measure.restrict_mono_set volume hhalfR)).locallyIntegrable (by norm_num))
      (hi.mono_set Metric.ball_subset_closedBall).locallyIntegrable
  let D := fun x => ∑ j : Fin 2, (fderiv ℝ f x (EuclideanSpace.single j 1) - p j) ^ 2
  have hnormEq : (fun x => ‖hu.weakGrad x - p‖ ^ 2) =ᵐ[volume.restrict
      (Metric.ball c (R / 2))] D := by
    filter_upwards [ae_all_iff.mpr hderEq] with x hx
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j hj
    change (hu.weakGrad x j - p j) ^ 2 = _
    rw [hx j]
  let : IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have huInt : IntegrableOn (fun x => ‖hu.weakGrad x - p‖ ^ 2) (Metric.ball c R) :=
    (hu.weakGrad_memLp.sub (memLp_const p)).norm.integrable_sq
  have hDi : IntegrableOn D (Metric.ball c (R / 2)) :=
    (huInt.mono_set hhalfR).congr hnormEq
  have hdecay :=
    DifferentialGeometry.Analysis.harmonic_integral_gradient_sub_center_sq_le_radius_ratio_pow_four
      (half_pos hR) hr (by linarith : r ≤ R / 2 / 4) (hharm.mono hhalfS') p hDi
  let v : E := WithLp.toLp 2 (fun j => fderiv ℝ f c (EuclideanSpace.single j 1))
  have hrhalf : Metric.ball c r ⊆ Metric.ball c (R / 2) := Metric.ball_subset_ball (by linarith)
  have hdiffEq : (fun x => ‖hu.weakGrad x - v‖ ^ 2) =ᵐ[volume.restrict (Metric.ball c r)]
      (fun x => ∑ j : Fin 2,
        (fderiv ℝ f x (EuclideanSpace.single j 1) -
          fderiv ℝ f c (EuclideanSpace.single j 1)) ^ 2) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hrhalf (ae_all_iff.mpr hderEq)]
      with x hx
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j hj
    change (hu.weakGrad x j - fderiv ℝ f c (EuclideanSpace.single j 1)) ^ 2 = _
    rw [hx j]
  have heqr := integral_congr_ae hdiffEq
  have heqhalf := integral_congr_ae hnormEq
  rw [← heqr, ← heqhalf] at hdecay
  have hmono : (∫ x in Metric.ball c (R / 2), ‖hu.weakGrad x - p‖ ^ 2) ≤
      ∫ x in Metric.ball c R, ‖hu.weakGrad x - p‖ ^ 2 :=
    setIntegral_mono_set huInt (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall hhalfR)
  have ht := hdecay.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
  have hc : 256 * (r / (R / 2)) ^ 4 = 4096 * (r / R) ^ 4 := by ring
  rw [hc] at ht
  exact ⟨v, ht⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
