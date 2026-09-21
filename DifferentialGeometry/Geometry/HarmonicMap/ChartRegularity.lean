import DifferentialGeometry.Analysis.Sobolev.Euclidean.MetricEnergy.GradientRegularity
import DifferentialGeometry.Geometry.Metric.Pullback.ConvexBounds
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Locality
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MetricEnergy.FirstVariation
import DifferentialGeometry.Geometry.HarmonicMap.ChartEquation
import DifferentialGeometry.Analysis.Elliptic.Euclidean.System.QuadraticRegularity
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates

section

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem exists_contDiffOn_one_of_chart_metric_minimality
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m)) {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hKsource : MapsTo L.symm (closedBall (0 : EuclideanSpace ℝ (Fin m)) a) Φ.source)
    {z : V → EuclideanSpace ℝ (Fin m)}
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : V) R))
    (hzc : ContinuousOn z (ball (0 : V) R)) (hz0 : z 0 = 0)
    (hzrange : MapsTo z (ball (0 : V) R) (closedBall (0 : EuclideanSpace ℝ (Fin m)) a))
    (hmin : let ψ := fun y => Φ (L.symm y)
      ∀ s : ℝ, 0 < s → s < R → ∀ q : V → EuclideanSpace ℝ (Fin m),
        ∀ hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (ball (0 : V) s),
        (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (ball (0 : V) s)) →
        (∀ᵐ x ∂volume.restrict (ball (0 : V) s), q x ∈ closedBall 0 a) →
        (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : V) s,
          pullbackMetricCoefficients g ψ (z x)
            (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
          (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : V) s,
            pullbackMetricCoefficients g ψ (q x)
              (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
              (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)))) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ContDiffOn ℝ 1 z (ball (0 : V) r) ∧
      ∃ (G : Fin m → V → V) (C : Fin m → ℝ),
        (∀ i, 0 ≤ C i) ∧
        (∀ i, G i =ᵐ[volume.restrict (ball (0 : V) r)] (hz i).weakGrad) ∧
        (∀ i, ∀ x ∈ ball (0 : V) r, HasFDerivAt (fun y => z y i) (innerSL ℝ (G i x)) x) ∧
        ∀ i, ∀ x ∈ ball (0 : V) r, ∀ y ∈ ball (0 : V) r,
          ‖G i x - G i y‖ ≤ C i * ‖x - y‖ ^ ((1 : ℝ) / 8) := by
  let ψ := fun y => Φ (L.symm y)
  let B := pullbackMetricCoefficients g ψ
  have hK := isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) a
  obtain ⟨lam, C, hlam, hcoerce, hBLip⟩ := exists_pullback_metric_bounds_on_convex_chart
    g Φ L.symm hK (convex_closedBall 0 a) hKsource
  have hzK : ∀ᵐ x ∂volume.restrict (ball (0 : V) R), z x ∈ closedBall 0 a := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hzrange hx
  exact exists_contDiffOn_one_of_continuous_metric_minimizer hR ha hz hzc hz0 B hBLip
    (fun y _ v w => g.symm _ _ _) hlam hcoerce
    (fun c s hs hcs q hq hqz hqK =>
      quadratic_weakGrad_energy_le_on_subball_of_concentric_minimality
        hz hK hzK B hBLip.continuousOn hmin hs hcs q hq hqz hqK)

end DifferentialGeometry.Geometry

end

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_smooth_centered_chart_of_local_minimality
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) (y₀ : H)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞)
    (hΦ : ∀ y : H, Φ ((toEuclidean (E := E)).symm y) =
      (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm (y + y₀)))
    {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hKsource : MapsTo (toEuclidean (E := E)).symm (closedBall (0 : H) a) Φ.source)
    {z : V → H} (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (ball (0 : V) R))
    (hzc : ContinuousOn z (ball (0 : V) R)) (hz0 : z 0 = 0)
    (hzrange : MapsTo z (ball (0 : V) R) (ball (0 : H) a))
    (hmap : MapsTo (fun x => z x + y₀) (ball (0 : V) R)
      (chartTargetEuclid (I := 𝓘(ℝ, E)) p))
    (hmin : let ψ := fun y => Φ ((toEuclidean (E := E)).symm y)
      ∀ s : ℝ, 0 < s → s < R → ∀ q : V → H,
        ∀ hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (ball (0 : V) s),
        (∀ i, DeGiorgi.MemW01p 2 (fun x => q x i - z x i) (ball (0 : V) s)) →
        (∀ᵐ x ∂volume.restrict (ball (0 : V) s), q x ∈ closedBall (0 : H) a) →
        (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : V) s,
          pullbackMetricCoefficients g ψ (z x)
            (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
          (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball (0 : V) s,
            pullbackMetricCoefficients g ψ (q x)
              (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
              (WithLp.toLp 2 (fun i => (hq i).weakGrad x j)))) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ContDiffOn ℝ ∞ z (ball (0 : V) r) ∧
      (∀ k, DeGiorgi.HasWeakDiv (fun x => -(∑ j : Fin 2, ∑ i, ∑ l,
        chartChristoffel g p i l k ((toEuclidean (E := E)).symm (z x + y₀)) *
          (hz i).weakGrad x j * (hz l).weakGrad x j)) (hz k).weakGrad (ball (0 : V) r)) := by
  let ψ : H → M := fun y => Φ ((toEuclidean (E := E)).symm y)
  let Ψc : H → M := fun y =>
    (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm (y + y₀))
  have hψeq : ψ = Ψc := funext hΦ
  let U := (toEuclidean (E := E)).symm ⁻¹' Φ.source
  have hU : IsOpen U := Φ.open_source.preimage (toEuclidean (E := E)).symm.continuous
  have hψ : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ ψ U :=
    Φ.contMDiffOn_toFun.comp (toEuclidean (E := E)).symm.contDiff.contMDiff.contMDiffOn
      (fun _ hy => hy)
  let B := pullbackMetricCoefficients g ψ
  have hB : ContDiffOn ℝ 1 B U :=
    (contDiffOn_pullback_metric_coefficients g hU hψ).of_le (by simp)
  obtain ⟨r₀, hr₀, hr₀R, hz1, G, C, hC, hG, _, hHolder⟩ :=
    exists_contDiffOn_one_of_chart_metric_minimality g Φ (toEuclidean (E := E)) hR ha
      hKsource hz hzc hz0 (fun x hx => ball_subset_closedBall (hzrange hx)) hmin
  let s := r₀ / 2
  have hs : 0 < s := half_pos hr₀
  have hsr₀ : s < r₀ := half_lt_self hr₀
  have hsR : s < R := hsr₀.trans hr₀R
  have hclosed : closedBall (0 : V) s ⊆ ball 0 R := closedBall_subset_ball hsR
  have hsub : ball (0 : V) s ⊆ ball 0 R := ball_subset_ball hsR.le
  have hsub₀ : ball (0 : V) s ⊆ ball 0 r₀ := ball_subset_ball hsr₀.le
  let hzs (i : Fin (Module.finrank ℝ E)) := (hz i).restrict isOpen_ball hsub
  have hEL : ∀ φ : V → H, ContDiff ℝ ∞ φ → tsupport φ ⊆ ball (0 : V) s →
      (∫ x in ball (0 : V) s, ∑ j : Fin 2,
        ((fderiv ℝ (pullbackMetricCoefficients g Ψc) (z x) (φ x))
            (DeGiorgi.weakGradientColumn hzs x j) (DeGiorgi.weakGradientColumn hzs x j) +
          2 * pullbackMetricCoefficients g Ψc (z x) (DeGiorgi.weakGradientColumn hzs x j)
            (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0 := by
    intro φ hφ hφsupp
    have h := Analysis.Sobolev.integral_metric_energy_variation_eq_zero_of_ball_minimality
      hz hzc hzrange hU hKsource B hB (fun y _ v w => g.symm _ _ _)
      hmin hs hsR hφ hφsupp
    simpa only [B, hψeq, hzs, DeGiorgi.MemW1pWitness.restrict, DeGiorgi.weakGradientColumn] using h
  obtain ⟨_, _, _, hPDE⟩ := exists_weak_chart_equation_of_centered_metric_variation g p y₀
    (hzc.mono hclosed) (hmap.mono_left hclosed) hzs hEL
  let A (k i l : Fin (Module.finrank ℝ E)) (y : H) :=
    chartChristoffel g p i l k ((toEuclidean (E := E)).symm (y + y₀))
  let W := (fun y : H => y + y₀) ⁻¹' chartTargetEuclid (I := 𝓘(ℝ, E)) p
  have hW : IsOpen W := (chartTargetEuclid_isOpen p).preimage (continuous_id.add continuous_const)
  have hA (k i l : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞ (A k i l) W := by
    have hh := chartChristoffel_contDiffOn_interior g p i l k
    have ht : ContDiffOn ℝ ∞ (chartChristoffel g p i l k) (extChartAt 𝓘(ℝ, E) p).target := by
      simpa only [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).interior_eq] using hh
    exact ht.comp ((toEuclidean (E := E)).symm.contDiff.comp
      (contDiff_id.add contDiff_const)).contDiffOn
      (fun y hy => toEuclidean_symm_mem_target hy)
  have hdiv (k : Fin (Module.finrank ℝ E)) : DeGiorgi.HasWeakDiv
      (fun x => -(∑ j : Fin 2, ∑ i, ∑ l, A k i l (z x) *
        (hzs i).weakGrad x j * (hzs l).weakGrad x j)) (hzs k).weakGrad (ball (0 : V) s) := by
    intro φ hφ hφc hφsupp
    have h := hPDE k φ hφ hφsupp
    simp only [neg_mul, integral_neg, neg_neg]
    simpa only [DeGiorgi.weakGradientColumn, PiLp.toLp_apply, mul_comm, A] using h
  have hGeq (i : Fin (Module.finrank ℝ E)) :
      G i =ᵐ[volume.restrict (ball (0 : V) s)] (hzs i).weakGrad :=
    ae_restrict_of_ae_restrict_of_subset hsub₀ (hG i)
  obtain ⟨r, hr, hrs, hzsm⟩ := exists_contDiffOn_of_quadratic_weak_system hs hzs
    (hz1.mono hsub₀) hGeq (by norm_num : (0 : ℝ≥0) < 1 / 8)
    (by norm_num : (1 / 8 : ℝ≥0) < 1) C hC
    (fun i x hx y hy => by
      norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
      exact hHolder i x (hsub₀ hx) y (hsub₀ hy))
    hW (hmap.mono_left hsub) A hA hdiv
  refine ⟨r, hr, hrs.trans hsR, hzsm, ?_⟩
  intro k
  exact (hdiv k).restrict (ball_subset_ball hrs.le)

end DifferentialGeometry.Geometry

end

end
