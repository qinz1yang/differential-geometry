import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakFormulation
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Divergence
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ClassicalDivergence
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical

section

noncomputable section
open Set Filter MeasureTheory

namespace DeGiorgi

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem isSupersolution_of_hasWeakDiv_nonpos
    {Ω : Set V} (hΩ : IsOpen Ω) {A : EllipticCoeff d Ω} {u g : V → ℝ}
    (hu : MemW1pWitness 2 u Ω) (hg : MemLp g 2 (volume.restrict Ω))
    (hdiv : HasWeakDiv g (fun x => matMulE (A.a x) (hu.weakGrad x)) Ω)
    (hg0 : ∀ᵐ x ∂volume.restrict Ω, g x ≤ 0) : IsSupersolution A u := by
  have hweak := (bilinFormOfCoeff_eq_integral_iff_hasWeakDiv hΩ hu hg.neg).mpr
    (by simpa only [Pi.neg_apply, neg_neg] using hdiv)
  refine ⟨hu.memW1p, ?_⟩
  intro hw φ hφ0 hφ hφpos
  rw [bilinFormOfCoeff_eq_left hΩ A hw hu hφ, hweak φ hφ0 hφ]
  exact integral_nonneg_of_ae (hg0.mono fun x hx => mul_nonneg (neg_nonneg.mpr hx) (hφpos x))

end DeGiorgi

end

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace DeGiorgi
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem isSupersolution_on_ball_of_divergence_nonpos
    {N : Set V} (hN : IsOpen N) {c : V} {R : ℝ} (hball : Metric.closedBall c R ⊆ N)
    (A : EllipticCoeff d (Metric.ball c R)) (a : V → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) N)
    (hAa : EqOn A.a a (Metric.ball c R)) {u : V → ℝ} (hu : ContDiffOn ℝ 2 u N)
    (hdiv : ∀ x ∈ Metric.ball c R,
      (∑ i, fderiv ℝ (fun y => matMulE (a y) (smoothGradField u y) i) x
        (EuclideanSpace.single i 1)) ≤ 0) : IsSupersolution A u := by
  let F := fun x => matMulE (a x) (smoothGradField u x)
  let g := fun x => ∑ i, fderiv ℝ (fun y => F y i) x (EuclideanSpace.single i 1)
  have hF (i : Fin d) : ContDiffOn ℝ 1 (fun x => F x i) N := by
    change ContDiffOn ℝ 1 (fun x => ∑ j,
      a x i j * fderiv ℝ u x (EuclideanSpace.single j 1)) N
    apply ContDiffOn.sum
    intro j _
    exact (ha i j).mul ((hu.fderiv_of_isOpen hN (by norm_num)).clm_apply contDiffOn_const)
  have hgc : ContinuousOn g (Metric.closedBall c R) := by
    apply (continuousOn_finsetSum _ (fun i _ =>
      ((hF i).continuousOn_fderiv_of_isOpen hN le_rfl).clm_apply continuousOn_const)).mono hball
  have hgLp : MemLp g 2 (volume.restrict (Metric.ball c R)) := by
    let : IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    obtain ⟨C, hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hgc
    apply MemLp.of_bound
      ((hgc.mono Metric.ball_subset_closedBall).aestronglyMeasurable
        Metric.isOpen_ball.measurableSet) C
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hC x (Metric.ball_subset_closedBall hx)
  obtain ⟨hw, hgrad⟩ := exists_memW1pWitness_of_contDiffOn_closedBall hN
    (hu.of_le (by norm_num)) hball 2
  have hdivF : HasWeakDiv g F (Metric.ball c R) := hasWeakDiv_of_contDiffOn Metric.isOpen_ball
    (fun i => (hF i).mono (Metric.ball_subset_closedBall.trans hball))
  have hflux : F =ᵐ[volume.restrict (Metric.ball c R)]
      (fun x => matMulE (A.a x) (hw.weakGrad x)) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hgx : hw.weakGrad x = smoothGradField u x := by ext j; exact hgrad x j
    change matMulE (a x) (smoothGradField u x) = _
    rw [hAa hx, hgx]
  exact isSupersolution_of_hasWeakDiv_nonpos Metric.isOpen_ball hw hgLp
    (hdivF.congr_ae EventuallyEq.rfl hflux)
    ((ae_restrict_mem Metric.isOpen_ball.measurableSet).mono (fun x hx => hdiv x hx))

end DeGiorgi

end

end
