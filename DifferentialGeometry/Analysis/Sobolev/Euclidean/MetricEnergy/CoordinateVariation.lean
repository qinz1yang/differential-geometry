import DifferentialGeometry.Analysis.Sobolev.Euclidean.Variation
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MetricEnergy.FirstVariation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d m n : ℕ} [NeZero d]
local notation "P" => EuclideanSpace ℝ (Fin d)
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin n)

private theorem restrict_ball_eq_restrict_closedBall (x₀ : P) (a : ℝ) :
    volume.restrict (Metric.ball x₀ a) = volume.restrict (Metric.closedBall x₀ a) := by
  apply Measure.restrict_congr_set
  have hz : ∀ᵐ x : P ∂volume, x ∉ Metric.sphere x₀ a :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume x₀ a)
  filter_upwards [hz] with x hx
  apply propext
  change dist x x₀ < a ↔ dist x x₀ ≤ a
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hx⟩

theorem integral_metric_energy_variation_eq_zero_of_coordinate_replacement
    {Ω : Set P} (hΩ : IsOpen Ω) {x₀ : P} {a c : ℝ}
    (hac : a < c) (hball : Metric.closedBall x₀ c ⊆ Ω)
    {z : P → E} (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) Ω)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hzK : ∀ᵐ x ∂volume.restrict Ω, z x ∈ K)
    (β : E → F) (hβ : ContDiffOn ℝ ∞ β U)
    {f : P → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hβz : (fun x => β (z x)) =ᵐ[volume.restrict Ω] f)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ 1 B U) (hsym : ∀ y ∈ K, ∀ v w, B y v w = B y w v)
    {T : Set F} (hβT : MapsTo β U T)
    (hmetric : ∀ y ∈ U, ∀ v w, A (β y) (fderiv ℝ β y v) (fderiv ℝ β y w) = B y v w)
    (hbase : ∀ᵐ x ∂volume.restrict Ω, ∀ j : Fin d,
      A (f x) (DeGiorgi.weakGradientColumn hf x j) (DeGiorgi.weakGradientColumn hf x j) =
        B (z x) (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j))
    (hmin : ∀ (q : P → F)
      (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball x₀ c)),
      (∀ᵐ x ∂volume.restrict (Metric.ball x₀ c), q x ∈ T) →
      q =ᵐ[volume.restrict (Metric.ball x₀ c \ Metric.closedBall x₀ a)] f →
      (∑ j : Fin d, ∫ x in Metric.closedBall x₀ a,
        A (f x) (DeGiorgi.weakGradientColumn hf x j) (DeGiorgi.weakGradientColumn hf x j)) ≤
      ∑ j : Fin d, ∫ x in Metric.closedBall x₀ a,
        A (q x) (DeGiorgi.weakGradientColumn hq x j) (DeGiorgi.weakGradientColumn hq x j))
    {φ : P → E} (hφ : ContDiff ℝ ∞ φ) (hφa : tsupport φ ⊆ Metric.ball x₀ a) :
    (∫ x in Metric.ball x₀ a, ∑ j : Fin d,
      ((fderiv ℝ B (z x) (φ x)) (DeGiorgi.weakGradientColumn hz x j)
          (DeGiorgi.weakGradientColumn hz x j) +
        2 * B (z x) (DeGiorgi.weakGradientColumn hz x j)
          (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0 := by
  classical
  have haΩ : Metric.ball x₀ a ⊆ Ω :=
    (Metric.ball_subset_ball hac.le).trans (Metric.ball_subset_closedBall.trans hball)
  let hza (i : Fin m) := DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball haΩ (hz i)
  have hzKa : ∀ᵐ x ∂volume.restrict (Metric.ball x₀ a), z x ∈ K :=
    ae_mono (Measure.restrict_mono_set volume haΩ) hzK
  have hφs : HasCompactSupport φ :=
    (isCompact_closedBall x₀ a).of_isClosed_subset (isClosed_tsupport φ)
      (hφa.trans Metric.ball_subset_closedBall)
  obtain ⟨δ₁, hδ₁, hq⟩ := Euclidean.exists_coordinate_affine_variation_memW1p
    hΩ hz hK hU hKU hzK β hβ hball hφ hφs
  obtain ⟨P₀, hP₀⟩ := hφ.continuous.bounded_above_of_compact_support hφs
  let Cφ := max P₀ 0
  have hCφ : 0 ≤ Cφ := le_max_right _ _
  have hφbound (x : P) : ‖φ x‖ ≤ Cφ := (hP₀ x).trans (le_max_left _ _)
  obtain ⟨δ₂, hδ₂, C, _, hbound⟩ := exists_compact_metric_range_bounds hU hB hK hKU Cφ hCφ
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have haffmin : ∀ᶠ t in 𝓝 (0 : ℝ), metricDirichletEnergy B hza ≤
      metricDirichletEnergy B
        (DeGiorgi.componentAffineVariationWitness Metric.isOpen_ball hza hφ hφs t) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have ht' : |t| < min δ₁ δ₂ := by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht
    obtain ⟨hqt, hqU, hqgrad, hqoff⟩ := hq t (ht'.trans_le (min_le_left _ _))
    let qt : P → F := fun x => β (z x + t • φ x)
    have hqT : ∀ᵐ x ∂volume.restrict (Metric.ball x₀ c), qt x ∈ T :=
      hqU.mono fun x hx => hβT hx
    have hsub : Metric.ball x₀ c \ Metric.closedBall x₀ a ⊆ Ω :=
      sdiff_subset.trans (Metric.ball_subset_closedBall.trans hball)
    have hqf : qt =ᵐ[volume.restrict (Metric.ball x₀ c \ Metric.closedBall x₀ a)] f := by
      filter_upwards [ae_mono (Measure.restrict_mono_set volume hsub) hβz,
        ae_restrict_mem (Metric.isOpen_ball.measurableSet.diff measurableSet_closedBall)]
        with x hx hxS
      exact (hqoff x (fun hxφ => hxS.2
        (Metric.ball_subset_closedBall (hφa hxφ)))).trans hx
    have hcomparison := hmin qt hqt hqT hqf
    let haff := DeGiorgi.componentAffineVariationWitness Metric.isOpen_ball hza hφ hφs t
    have hbaseEq (j : Fin d) : (∫ x in Metric.closedBall x₀ a,
        A (f x) (DeGiorgi.weakGradientColumn hf x j) (DeGiorgi.weakGradientColumn hf x j)) =
        ∫ x in Metric.ball x₀ a,
          B (z x) (DeGiorgi.weakGradientColumn hza x j) (DeGiorgi.weakGradientColumn hza x j) := by
      rw [← restrict_ball_eq_restrict_closedBall]
      apply integral_congr_ae
      filter_upwards [ae_mono (Measure.restrict_mono_set volume haΩ) hbase] with x hx
      exact hx j
    have hvarEq (j : Fin d) : (∫ x in Metric.closedBall x₀ a,
        A (qt x) (DeGiorgi.weakGradientColumn hqt x j) (DeGiorgi.weakGradientColumn hqt x j)) =
        ∫ x in Metric.ball x₀ a, B (z x + t • φ x)
          (DeGiorgi.weakGradientColumn haff x j) (DeGiorgi.weakGradientColumn haff x j) := by
      rw [← restrict_ball_eq_restrict_closedBall]
      apply integral_congr_ae
      filter_upwards [ae_mono (Measure.restrict_mono_set volume
        (Metric.ball_subset_ball hac.le)) hqgrad,
        ae_mono (Measure.restrict_mono_set volume (Metric.ball_subset_ball hac.le)) hqU]
        with x hx hxU
      rw [hx j]
      change A (β (z x + t • φ x))
        (fderiv ℝ β (z x + t • φ x) _) (fderiv ℝ β (z x + t • φ x) _) = _
      rw [hmetric _ hxU]
      change B (z x + t • φ x) _ _ = B (z x + t • φ x)
        (DeGiorgi.weakGradientColumn
          (DeGiorgi.componentAffineVariationWitness Metric.isOpen_ball hza hφ hφs t) x j)
        (DeGiorgi.weakGradientColumn
          (DeGiorgi.componentAffineVariationWitness Metric.isOpen_ball hza hφ hφs t) x j)
      rw [DeGiorgi.weakGradientColumn_componentAffineVariationWitness]
      rfl
    have hbaseInt (j : Fin d) := integrable_metric_weakGradientColumn_of_compact_range
      hza hK hzKa B (hB.continuousOn.mono hKU) j
    have hBm : Measurable (U.piecewise B 0) :=
      hB.continuousOn.measurable_piecewise continuous_zero.continuousOn hU.measurableSet
    have haffM : MemLp (fun x => z x + t • φ x) 2 (volume.restrict (Metric.ball x₀ a)) :=
      MemLp.of_eval_piLp fun i => (haff i).memLp
    have hBaff : AEStronglyMeasurable (fun x => B (z x + t • φ x))
        (volume.restrict (Metric.ball x₀ a)) := by
      apply (hBm.comp_aemeasurable haffM.aemeasurable).aestronglyMeasurable.congr
      filter_upwards [hzKa] with x hx
      exact Set.piecewise_eq_of_mem U B 0
        (hbound (z x) hx (φ x) (hφbound x) t (ht'.trans_le (min_le_right _ _))).1
    have hBbound : ∀ᵐ x ∂volume.restrict (Metric.ball x₀ a), ‖B (z x + t • φ x)‖ ≤ C :=
      hzKa.mono fun x hx =>
        (hbound (z x) hx (φ x) (hφbound x) t (ht'.trans_le (min_le_right _ _))).2.1
    have hvarInt (j : Fin d) := integrable_quadratic_weakGradientColumn haff
      (fun x => B (z x + t • φ x)) hBaff hBbound j
    simp_rw [hbaseEq, hvarEq] at hcomparison
    unfold metricDirichletEnergy
    rw [integral_finsetSum _ (fun j _ => hbaseInt j), integral_finsetSum _ (fun j _ => hvarInt j)]
    exact hcomparison
  exact integral_metric_energy_variation_eq_zero_of_eventually_energy_le
    Metric.isOpen_ball hza hU hB hK hKU hzKa hsym hφ hφs haffmin

end DifferentialGeometry.Analysis.Sobolev

end
