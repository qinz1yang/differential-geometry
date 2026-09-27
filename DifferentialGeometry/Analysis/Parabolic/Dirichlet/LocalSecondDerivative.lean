import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalSecondDerivative
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartDensityCutoff
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalNirenbergInteriorTime

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
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

theorem exists_local_dirichlet_second_weak_derivative_of_timeH1
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a ≤ b) (hreg : Icc a b ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ Icc a b, ∀ y ∈ Ω, ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, invGramOnEuclid (G.metric t) α i j y * ξ i * ξ j)
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    (v : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)))
    (f : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (ℓ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 (volume.restrict (Icc a b)))
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a))
    (hwmass : ∀ᵐ s ∂timeMeasure (b - a), ∀ z,
      w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (a + s))) (H1ComplDirichletToLp q z))
    (hwderiv : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (hpair : ∀ z : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)),
      (∫ t in Icc a b, ℓ t (z t)) = (∫ t in Icc a b, β t (z t)) -
        ∫ t in Icc a b, (∑ i, ∑ j, ∫ y in Ω,
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) y *
            (densityOnEuclid q α y * invGramOnEuclid (G.metric t) α i j y) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) y))
    (hsource : ∀ z : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)),
      (∫ t in Icc a b, β t (z t)) = ∫ t in Icc a b, (∫ y in Ω,
        f (t,y) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))))
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hηone : ∀ z ∈ Ω₀, η z = 1) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (((volume.restrict (Icc a b)).restrict (Icc c d)).prod (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂(volume.restrict (Icc a b)).restrict (Icc c d),
        DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀) ∧
      ∀ᵐ t ∂(volume.restrict (Icc a b)).restrict (Icc c d),
        Sobolev.Euclidean.MemWkp 2 2
          (fun z => H1ComplDirichletToLp q (v t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  obtain ⟨δ, hδ, C, _, hroom, hbound⟩ :=
    exists_local_dirichlet_nirenberg_integral_Icc_bound hG hab hreg q α hΩ hΩc hΩs
      φ hφ hη hηc hηs hηb hlam hcoer hac hdb
  exact DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_second_weak_derivative_of_local_diffQuot_bound_restrict q α hΩ hΩc hΩs
    (Icc c d) v (hη.of_le (by simp)) hηc hΩ₀ hηone hδ hroom
    (fun k h _ hh => hbound v f ℓ β w hwmass hwderiv hpair hsource k h hh)


omit [T2Space M] [CompactSpace M] in
private theorem exists_uniform_inv_gram_sum_lower_bound
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {K : Set EuStd} (hKc : IsCompact K)
    (hKs : K ⊆ chartTargetEuclid (I := I_hs) α) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ t ∈ J, ∀ y ∈ K,
      ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
        lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, invGramOnEuclid (G.metric t) α i j y * ξ i * ξ j := by
  obtain ⟨lam, hlam, hcoer⟩ := exists_uniform_inv_gram_quadratic_lower_bound hG hJc hJ α hKc hKs
  refine ⟨lam, hlam, ?_⟩
  intro t ht y hy ξ
  have hb := hcoer t ht y hy (WithLp.toLp 2 ξ)
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
    PiLp.inner_apply, DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Real.inner_apply] at hb
  convert hb using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem exists_local_dirichlet_second_weak_derivative_of_timeH1_interior
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a ≤ b) (hreg : Icc a b ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    (v : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)))
    (f : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
    (ℓ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 (volume.restrict (Icc a b)))
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a))
    (hwmass : ∀ᵐ s ∂timeMeasure (b - a), ∀ z,
      w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (a + s))) (H1ComplDirichletToLp q z))
    (hwderiv : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (hpair : ∀ z : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)),
      (∫ t in Icc a b, ℓ t (z t)) = (∫ t in Icc a b, β t (z t)) -
        ∫ t in Icc a b, (∑ i, ∑ j, ∫ y in Ω,
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) y *
            (densityOnEuclid q α y * invGramOnEuclid (G.metric t) α i j y) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) y))
    (hsource : ∀ z : Lp (H1ComplDirichlet q) 2 (volume.restrict (Icc a b)),
      (∫ t in Icc a b, β t (z t)) = ∫ t in Icc a b, (∫ y in Ω,
        f (t,y) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))))
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (((volume.restrict (Icc a b)).restrict (Icc c d)).prod (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂(volume.restrict (Icc a b)).restrict (Icc c d),
        DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀) ∧
      ∀ᵐ t ∂(volume.restrict (Icc a b)).restrict (Icc c d),
        Sobolev.Euclidean.MemWkp 2 2
          (fun z => H1ComplDirichletToLp q (v t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨δ, η, _, _, hη, hηc, hηrange, hηone, hηs⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      hΩ₀c hΩ hΩ₀Ω
  have hηb : ∀ z, |η z| ≤ 1 := by
    intro z
    have hz := hηrange (mem_range_self z)
    exact (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩)
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  obtain ⟨φ, _, hφ0⟩ := DifferentialGeometry.Analysis.Sobolev.Chart.exists_smoothMap_mul_chartDensity_eq_one
    q α hU (Subset.rfl : U ⊆ U) hΩc hΩs
  have hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1 := by
    intro z hz
    exact hφ0 z (subset_closure hz)
  obtain ⟨lam, hlam, hcoer⟩ := exists_uniform_inv_gram_sum_lower_bound
    hG isCompact_Icc hreg α hΩc (hΩs.trans (image_mono interior_subset))
  exact exists_local_dirichlet_second_weak_derivative_of_timeH1
    hG hab hreg q α hΩ hΩc hΩs φ hφ hη hηc hηs hηb hlam (fun t ht y hy => hcoer t ht y (subset_closure hy)) hac hdb
    v f ℓ β w hwmass hwderiv hpair hsource hΩ₀
    (fun z hz => hηone z (Metric.self_subset_cthickening (closure Ω₀) (subset_closure hz)))

theorem exists_local_dirichlet_second_weak_derivative_of_timeH1_of_measure_eq_volume
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a ≤ b) (hreg : Icc a b ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    {μ : Measure ℝ} (hμ : μ = volume.restrict (Icc a b))
    (v : Lp (H1ComplDirichlet q) 2 μ)
    (f : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (ℓ β : Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a))
    (hwmass : ∀ᵐ s ∂timeMeasure (b - a), ∀ z,
      w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (a + s)))
        (H1ComplDirichletToLp q z))
    (hwderiv : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (hpair : ∀ z : Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
        ∫ t, (∑ i, ∑ j, ∫ y in Ω,
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) y *
            (densityOnEuclid q α y * invGramOnEuclid (G.metric t) α i j y) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) y) ∂μ)
    (hsource : ∀ z : Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, β t (z t) ∂μ) = ∫ t, (∫ y in Ω,
        f (t, y) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))) ∂μ)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (((volume.restrict (Icc a b)).restrict (Icc c d)).prod
          (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂(volume.restrict (Icc a b)).restrict (Icc c d),
        DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀) ∧
      ∀ᵐ t ∂(volume.restrict (Icc a b)).restrict (Icc c d),
        Sobolev.Euclidean.MemWkp 2 2
          (fun z => H1ComplDirichletToLp q (v t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  cases hμ
  exact exists_local_dirichlet_second_weak_derivative_of_timeH1_interior
    hG hab hreg q α hΩ hΩc hΩs hac hdb v f ℓ β w hwmass hwderiv hpair hsource
      hΩ₀ hΩ₀Ω

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
