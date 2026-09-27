import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartCutoff
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalSecondDerivative

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem ae_memWkp_succ_of_cutoff_gradient
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₁ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₁ : IsOpen Ω₁) (hsub : Ω₁ ⊆ Ω)
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (u : Z → H1ComplDirichlet q) (v : Fin (Module.finrank ℝ EuN) → Z → H1ComplDirichlet q)
    {η : EuStd → ℝ} (hηone : ∀ z ∈ Ω₁, η z = 1)
    (hv : ∀ i, ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v i t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α
          (fun z => η z * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z))
    {k : ℕ} (hW : ∀ i, ∀ᵐ t ∂μ,
      MemWkp k 2
        (fun z => H1ComplDirichletToLp q (v i t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁) :
    ∀ᵐ t ∂μ,
      MemWkp (k + 1) 2
        (fun z => H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁ := by
  have hallv := ae_all_iff.mpr hv
  have hallW := ae_all_iff.mpr hW
  filter_upwards [hallv, hallW] with t hvt hWt
  apply DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.memWkp_succ_chartInverse_of_cutoff_localWeakPartial q α hΩ hΩc hΩs hΩ₁ hsub (u t)
    (fun i => (H1ComplDirichletToLp q (v i t) : M → ℝ)) hηone hvt
  intro i
  exact hWt i

theorem ae_memWkp_three_of_cutoff_gradient_timeH1
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b c d : ℝ} (hab : a ≤ b) (hreg : Icc a b ⊆ D.regular)
    (hac : a < c) (hdb : d < b)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₁ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₁ : IsOpen Ω₁) (hΩ₁Ω : closure Ω₁ ⊆ Ω)
    {η : EuStd → ℝ} (hηone : ∀ z ∈ Ω₁, η z = 1)
    (u : ℝ → H1ComplDirichlet q)
    {μ : Measure ℝ} (hμ : μ = volume.restrict (Icc a b))
    (v : Fin (Module.finrank ℝ EuN) → Lp (H1ComplDirichlet q) 2 μ)
    (f : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (ℓ β : Fin (Module.finrank ℝ EuN) → Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (w : Fin (Module.finrank ℝ EuN) → timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a))
    (hrep : ∀ i, ∀ᵐ t ∂μ.restrict (Icc c d),
      (H1ComplDirichletToLp q (v i t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α
          (fun z => η z * dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z))
    (hwmass : ∀ i, ∀ᵐ s ∂timeMeasure (b - a), ∀ z,
      (w i).toFun s z = inner ℝ (H1ComplDirichletToLp q (v i (a + s)))
        (H1ComplDirichletToLp q z))
    (hwderiv : ∀ i, (w i).deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ i (a + s))
    (hpair : ∀ i, ∀ z : Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, ℓ i t (z t) ∂μ) = (∫ t, β i t (z t) ∂μ) -
        ∫ t, (∑ j, ∑ k, ∫ y in Ω,
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (v i t) y *
            (densityOnEuclid q α y * invGramOnEuclid (G.metric t) α j k y) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (z t) y) ∂μ)
    (hsource : ∀ i, ∀ z : Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, β i t (z t) ∂μ) = ∫ t, (∫ y in Ω,
        f i (t, y) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))) ∂μ) :
    ∀ᵐ t ∂μ.restrict (Icc c d),
      MemWkp 3 2
        (fun z => H1ComplDirichletToLp q (u t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁ := by
  have hW : ∀ i, ∀ᵐ t ∂μ.restrict (Icc c d),
      MemWkp 2 2
        (fun z => H1ComplDirichletToLp q (v i t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₁ := by
    intro i
    obtain ⟨H, _, hH⟩ := exists_local_dirichlet_second_weak_derivative_of_timeH1_of_measure_eq_volume
      hG hab hreg q α hΩ hΩc hΩs hac hdb hμ
      (v i) (f i) (ℓ i) (β i) (w i)
      (hwmass i) (hwderiv i) (hpair i) (hsource i) hΩ₁ hΩ₁Ω
    simpa only [hμ] using hH
  exact ae_memWkp_succ_of_cutoff_gradient (k := 2) q α hΩ hΩc hΩs hΩ₁
    (subset_closure.trans hΩ₁Ω) u (fun i => v i) hηone hrep hW

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
