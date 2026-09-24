import DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.Energy
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Locality
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Density
import DifferentialGeometry.Analysis.Integration.Integral.BallDecomposition
import DifferentialGeometry.Analysis.Integration.BallBoundary

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace DifferentialGeometry.Analysis

private theorem integral_complex_annulus_eq_euclidean_annulus
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (r R : ℝ) :
    (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, f (Complex.orthonormalBasisOneI.repr z)) =
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.closedBall 0 r, f x := by
  let e := Complex.orthonormalBasisOneI.repr
  let S : Set (EuclideanSpace ℝ (Fin 2)) := {x | ‖x‖ ∈ Icc r R}
  have hpre : e ⁻¹' S = {z : ℂ | ‖z‖ ∈ Icc r R} := by
    ext z
    simp only [mem_preimage, S, mem_ofPred_eq, LinearIsometryEquiv.norm_map]
  have h := e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding f S
  rw [hpre] at h
  apply h.trans
  apply setIntegral_congr_set
  have hrzero := measure_eq_zero_iff_ae_notMem.mp
    (Measure.addHaar_sphere volume (0 : EuclideanSpace ℝ (Fin 2)) r)
  have hRzero := measure_eq_zero_iff_ae_notMem.mp
    (Measure.addHaar_sphere volume (0 : EuclideanSpace ℝ (Fin 2)) R)
  filter_upwards [hrzero, hRzero] with x hxr hxR
  apply propext
  have hne_r : ‖x‖ ≠ r := by simpa only [Metric.mem_sphere, dist_zero_right] using hxr
  have hne_R : ‖x‖ ≠ R := by simpa only [Metric.mem_sphere, dist_zero_right] using hxR
  change (r ≤ ‖x‖ ∧ ‖x‖ ≤ R) ↔ (x ∈ Metric.ball 0 R ∧ x ∉ Metric.closedBall 0 r)
  simp only [Metric.mem_ball, Metric.mem_closedBall, dist_zero_right, not_le]
  exact ⟨fun hx => ⟨lt_of_le_of_ne hx.2 hne_R, lt_of_le_of_ne hx.1 hne_r.symm⟩,
    fun hx => ⟨hx.2.le, hx.1.le⟩⟩

private theorem integral_complex_collar_eq_euclidean_collar
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (r R : ℝ) :
    (∫ z in Metric.ball (0 : ℂ) R \ Metric.closedBall 0 r,
      f (Complex.orthonormalBasisOneI.repr z)) =
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.closedBall 0 r, f x := by
  let e := Complex.orthonormalBasisOneI.repr
  let S := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.closedBall 0 r
  have hpre : e ⁻¹' S = Metric.ball (0 : ℂ) R \ Metric.closedBall 0 r := by
    ext z
    simp only [S, mem_preimage, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall,
      dist_zero_right, LinearIsometryEquiv.norm_map]
  have h := e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding f S
  rwa [hpre] at h




variable {ι : Type*} [Fintype ι]

theorem weak_energy_ball_le_annulus_of_minimal
    {K U : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (T : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (hT : ContDiff ℝ ∞ T)
    (hTK : MapsTo T U K) (hfix : ∀ y ∈ K, T y = y) {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L)
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω)
    {w : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι}
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) Ω)
    (hwK : ∀ᵐ x ∂volume.restrict Ω, w x ∈ K)
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ Ω)
    {r R η : ℝ} (hr : 0 < r) (hrR : r < R) (hR1 : R < 1) (hη : 0 < η)
    (htube : ∀ p ∈ K, Metric.ball p η ⊆ U)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : ContinuousOn A K) (hpos : ∀ y ∈ K, ∀ v, 0 ≤ A y v v)
    {Λ : ℝ} (hΛ : ∀ y ∈ K, ‖A y‖ ≤ Λ) (hΛ0 : 0 ≤ Λ)
    (hsmall : (4 * Real.pi * R / (R - r)) *
      (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.closedBall 0 r,
        ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad x 0) : EuclideanSpace ℝ ι)‖ ^ 2 +
        ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad x 1) : EuclideanSpace ℝ ι)‖ ^ 2) < η ^ 2)
    (hmin : ∀ (q : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι)
      (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball 0 1)),
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1), q x ∈ K) →
      (q =ᵐ[volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 \ Metric.closedBall 0 R)] w) →
      (∑ j : Fin 2, ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
        A (w x) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
      ∑ j : Fin 2, ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
        A (q x) (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))) :
    (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r,
      ∑ j : Fin 2, A (w x) (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
      4 * Λ * ((5 * Real.pi ^ 2 * R / (R - r)) * L ^ 2) *
        (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.closedBall 0 r,
          ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad x 0) : EuclideanSpace ℝ ι)‖ ^ 2 +
          ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad x 1) : EuclideanSpace ℝ ι)‖ ^ 2) := by
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
  let S := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R
  have hBΩ : B ⊆ Ω := Metric.ball_subset_closedBall.trans hball
  have hSB : S ⊆ B := Metric.closedBall_subset_ball hR1
  have hwKB : ∀ᵐ x ∂volume.restrict B, w x ∈ K :=
    ae_restrict_of_ae_restrict_of_subset hBΩ hwK
  have hsmallC := hsmall
  rw [← integral_complex_annulus_eq_euclidean_annulus] at hsmallC
  obtain ⟨q, hq, hqK, hqw, hqE⟩ := exists_original_weak_replacement_energy_le
    hK hU hKU T hT hTK hfix hL hΩ hw hwK hball hr hrR hR1 hη htube
    A hA hpos hΛ hΛ0 hsmallC
  let ew := weakMapMetricDensity A hw
  let eq := weakMapMetricDensity A hq
  have hiw : IntegrableOn ew B := integrable_weakMapMetricDensity hBΩ hw hK A hA hwKB
  have hiq : IntegrableOn eq B := integrable_weakMapMetricDensity (Subset.rfl) hq hK A hA hqK
  have hminR : (∫ x in S, ew x) ≤ ∫ x in S, eq x := by
    rw [weakMapMetricDensity_integral_eq_sum (hSB.trans hBΩ) hw hK A hA
      (ae_restrict_of_ae_restrict_of_subset hSB hwKB) hpos,
      weakMapMetricDensity_integral_eq_sum hSB hq hK A hA
      (ae_restrict_of_ae_restrict_of_subset hSB hqK) hpos]
    exact hmin q hq hqK hqw
  let hwB (i : ι) := DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hBΩ (hw i)
  have hcoll := Sobolev.Euclidean.quadratic_weakGrad_columns_ae_eq_of_ae_eq
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (Metric.isOpen_ball.sdiff Metric.isClosed_closedBall) sdiff_subset
    hq hwB hqw (fun _ y => A y)
  have hcoll' : eq =ᵐ[volume.restrict (B \ S)] ew :=
    hcoll.mono fun x hx => Finset.sum_congr rfl fun j _ => hx j
  have hminB : (∫ x in B, ew x) ≤ ∫ x in B, eq x := by
    have h := integral_congr_ae hcoll'
    rw [setIntegral_sdiff Metric.isClosed_closedBall.measurableSet hiq hSB,
      setIntegral_sdiff Metric.isClosed_closedBall.measurableSet hiw hSB] at h
    linarith
  have hsumq := weakMapMetricDensity_integral_eq_sum (Subset.rfl) hq hK A hA hqK hpos
  rw [← hsumq, integral_complex_annulus_eq_euclidean_annulus (fun x =>
    ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad x 0) : EuclideanSpace ℝ ι)‖ ^ 2 +
    ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad x 1) : EuclideanSpace ℝ ι)‖ ^ 2) r R] at hqE
  have hcollEq : (2 * ∫ z in Metric.ball (0 : ℂ) 1 \ Metric.closedBall 0 r,
      (A (w (Complex.orthonormalBasisOneI.repr z))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad (Complex.orthonormalBasisOneI.repr z) 0))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad (Complex.orthonormalBasisOneI.repr z) 0)) +
        A (w (Complex.orthonormalBasisOneI.repr z))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad (Complex.orthonormalBasisOneI.repr z) 1))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad (Complex.orthonormalBasisOneI.repr z) 1))) / 2) =
      ∫ x in B \ Metric.closedBall 0 r, ew x := by
    rw [integral_div, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    simpa only [ew, weakMapMetricDensity, Fin.sum_univ_two] using
      integral_complex_collar_eq_euclidean_collar ew r 1
  rw [hcollEq] at hqE
  have hsplit := integral_ball_add_collar ew (hrR.le.trans hR1.le) hiw
  change (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r, ew x) ≤ _
  linarith

end DifferentialGeometry.Analysis

end
