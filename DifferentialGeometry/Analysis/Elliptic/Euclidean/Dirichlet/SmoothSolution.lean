import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.SmoothRepresentative
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.ClassicalDivergence
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical
import DifferentialGeometry.Analysis.Elliptic.Coefficients
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory

section

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace DeGiorgi

open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem exists_smooth_dirichlet_solution_of_posDef
    (hd : 2 ≤ d) (B : SmoothEllipticBilinearForm d (univ : Set V))
    (hpos : ∀ x, (B.a x).PosDef) (p : V) (R : ℝ) (v₀ : V) (b : ℝ) :
    ∃ (A : EllipticCoeff d (Metric.ball p R)) (u v : V → ℝ),
      A.a = B.a ∧ A.lam = B.lam ∧ IsHomogeneousWeakSolution A u ∧
      MemW01p 2 (fun x => u x - (inner ℝ v₀ x + b)) (Metric.ball p R) ∧
      ContDiffOn ℝ ∞ v (Metric.ball p R) ∧
      u =ᵐ[volume.restrict (Metric.ball p R)] v ∧
      HasWeakDiv 0 (fun x => matMulE (B.a x) (smoothGradField v x)) (Metric.ball p R) ∧
      ∀ x ∈ Metric.ball p R, (∑ i : Fin d,
        fderiv ℝ (fun y => (matMulE (B.a y) (smoothGradField v y)) i) x
          (EuclideanSpace.single i 1)) = 0 := by
  obtain ⟨A₀, hA₀⟩ := ellipticCoeff_of_continuous_posDef_on_compact
    Metric.isOpen_ball.measurableSet Metric.ball_subset_closedBall (isCompact_closedBall p R)
    B.a (fun i j => (B.smooth_a i j).continuous.measurable)
    (fun i j => (B.smooth_a i j).continuous.continuousOn) (fun x _ => hpos x)
  let A : EllipticCoeff d (Metric.ball p R) :=
    { a := B.a
      lam := B.lam
      Λ := max B.lam A₀.Λ
      measurable_comp := fun i j => (B.smooth_a i j).continuous.measurable
      hlam := B.ellipticity_pos
      hΛ := le_max_left _ _
      coercive := Eventually.of_forall fun x ξ => B.coercive x (mem_univ _) ξ
      coercive_inv := by
        filter_upwards [A₀.coercive_inv] with x hx
        intro ξ
        have hle : (max B.lam A₀.Λ)⁻¹ ≤ A₀.Λ⁻¹ :=
          (inv_le_inv₀ (lt_of_lt_of_le A₀.Λ_pos (le_max_right _ _)) A₀.Λ_pos).mpr
            (le_max_right _ _)
        have h := (mul_le_mul_of_nonneg_right hle (sq_nonneg ‖ξ‖)).trans (hx ξ)
        simpa only [hA₀] using h }
  have hA : A.a = B.a := rfl
  have hℓ : ContDiff ℝ 1 (fun x : V => inner ℝ v₀ x + b) :=
    (innerSL ℝ v₀).contDiff.add contDiff_const
  obtain ⟨hℓw, _⟩ := exists_memW1pWitness_of_contDiffOn_closedBall isOpen_univ
    hℓ.contDiffOn (subset_univ (Metric.closedBall p R)) 2
  obtain ⟨u, hu, htrace⟩ := aHarmonic_replacement_exists hd Metric.isOpen_ball
    Metric.isBounded_ball A hℓw.memW1p
  obtain ⟨v, hv, huv⟩ := (isHomogeneousWeakSolution_isSolution hu).exists_contDiffOn_ae_eq
    Metric.isOpen_ball B (fun x _ => congrFun hA x)
  let hw := hu.1.someWitness
  let hwv : MemW1pWitness 2 v (Metric.ball p R) :=
    { memLp := hw.memLp.ae_eq huv
      weakGrad := hw.weakGrad
      weakGrad_component_memLp := hw.weakGrad_component_memLp
      isWeakGrad := fun i => (hw.isWeakGrad i).congr_ae huv EventuallyEq.rfl }
  have hgrad := hwv.weakGrad_ae_eq_smoothGradField (by norm_num)
    Metric.isOpen_ball (hv.of_le (by norm_cast))
  have hdiv := (bilinFormOfCoeff_eq_integral_iff_hasWeakDiv Metric.isOpen_ball hw
    (MemLp.zero : MemLp (0 : V → ℝ) 2 (volume.restrict (Metric.ball p R)))).mp
    (fun φ hφ hφw => by
      simpa only [Pi.zero_apply, zero_mul, integral_zero] using hu.2 hw φ hφ hφw)
  have hdivv : HasWeakDiv 0 (fun x => matMulE (B.a x) (smoothGradField v x))
      (Metric.ball p R) := by
    apply hdiv.congr_ae (Eventually.of_forall fun _ => neg_zero)
    filter_upwards [hgrad] with x hx
    change matMulE (A.a x) (hwv.weakGrad x) = _
    rw [hA, hx]
  have hflux : ContDiffOn ℝ ∞ (fun x => matMulE (B.a x) (smoothGradField v x))
      (Metric.ball p R) := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    change ContDiffOn ℝ ∞ (fun x => ∑ j, B.a x i j *
      fderiv ℝ v x (EuclideanSpace.single j 1)) (Metric.ball p R)
    apply ContDiffOn.sum
    intro j _
    exact (B.smooth_a i j).contDiffOn.mul
      ((hv.fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_const)
  exact ⟨A, u, v, hA, rfl, hu, htrace, hv, huv, hdivv,
    hdivv.sum_fderiv_eq_zero Metric.isOpen_ball (hflux.of_le (by norm_cast))⟩

end DeGiorgi

end

end
