import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletChartMassPairing
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEquationLocal

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem integral_mass_inner_eq_integral_spacetime_weak_partial
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω)
    {T a b : ℝ} (u : timeL2 (H1ComplDirichlet q) T)
    (v : Lp (H1ComplDirichlet q) 2 ((timeMeasure T).restrict (Icc a b)))
    (k : Fin (Module.finrank ℝ EuN))
    (hv : ∀ᵐ t ∂((timeMeasure T).restrict (Icc a b)),
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      chartPullback I_hs α (fun x => η x *
        dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) x)) :
    ∀ (τ : Lp ℝ 2 ((timeMeasure T).restrict (Icc a b))) (z : H1ComplDirichlet q),
      (∫ t, τ t * inner ℝ (H1ComplDirichletToLp q (v t))
        (H1ComplDirichletToLp q z) ∂((timeMeasure T).restrict (Icc a b))) =
      ∫ p, τ p.1 * η p.2 * MetricExtension.densityOnEuclid q α p.2 *
        dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) k u p *
        H1ComplDirichletToLp q z ((extChartAt I_hs α).symm
          ((toEuclidean (E := EuN)).symm p.2))
        ∂((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω) := by
  let μ := (timeMeasure T).restrict (Icc a b)
  let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k
  let V := dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) k u
  have huμ : MemLp (fun t => u t) 2 μ := (Lp.memLp u).mono_measure Measure.restrict_le_self
  let uμ := huμ.toLp (fun t => u t)
  let P : Lp (Lp ℝ 2 (volume.restrict Ω)) 2 μ := D.compLpL 2 μ uμ
  have hVμ : MemLp (fun p => V p) 2 (μ.prod (volume.restrict Ω)) :=
    (Lp.memLp V).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  let F := hVμ.toLp (fun p => V p)
  have hPt : ∀ᵐ t ∂μ, P t = D (u t) := by
    filter_upwards [D.coeFn_compLpL uμ, huμ.coeFn_toLp] with t hPt hut
    change P t = D (uμ t) at hPt
    exact hPt.trans (congrArg D hut)
  have hVt : ∀ᵐ t ∂μ, (fun x => V (t, x)) =ᵐ[volume.restrict Ω] (D (u t) : EuStd → ℝ) :=
    ae_mono Measure.restrict_le_self
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) k u)
  have hFt : ∀ᵐ t ∂μ, (fun x => F (t, x)) =ᵐ[volume.restrict Ω] (P t : EuStd → ℝ) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hVμ.coeFn_toLp, hVt, hPt] with t hFt hVt hPt
    change (fun x => F (t, x)) =ᵐ[volume.restrict Ω] (fun x => V (t, x)) at hFt
    have hDP : (D (u t) : EuStd → ℝ) =ᵐ[volume.restrict Ω] (P t : EuStd → ℝ) :=
      Eventually.of_forall (fun x => congrArg (fun L : Lp ℝ 2 (volume.restrict Ω) => L x) hPt.symm)
    exact Filter.EventuallyEq.trans hFt (hVt.trans hDP)
  have hvP : ∀ᵐ t ∂μ, (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      chartPullback I_hs α (fun x => η x * P t x) := by
    filter_upwards [hv, hPt] with t hvt hpt
    rw [hpt]
    exact hvt
  intro τ z
  have h := integral_mass_inner_eq_integral_chart_prod q α hΩ hΩc hΩs
    hη hηc hηs τ v P F hFt z hvP
  apply h.trans
  apply integral_congr_ae
  filter_upwards [hVμ.coeFn_toLp] with p hp
  rw [hp]

theorem integral_mass_inner_eq_integral_spacetime_weak_partial_of_subset
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hsub : Ω₀ ⊆ Ω)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω₀)
    {T a b : ℝ} (u : timeL2 (H1ComplDirichlet q) T)
    (v : Lp (H1ComplDirichlet q) 2 ((timeMeasure T).restrict (Icc a b)))
    (k : Fin (Module.finrank ℝ EuN))
    (hv : ∀ᵐ t ∂((timeMeasure T).restrict (Icc a b)),
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      chartPullback I_hs α (fun x => η x *
        dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) x)) :
    ∀ (τ : Lp ℝ 2 ((timeMeasure T).restrict (Icc a b))) (z : H1ComplDirichlet q),
      (∫ t, τ t * inner ℝ (H1ComplDirichletToLp q (v t))
        (H1ComplDirichletToLp q z) ∂((timeMeasure T).restrict (Icc a b))) =
      ∫ p, τ p.1 * η p.2 * MetricExtension.densityOnEuclid q α p.2 *
        dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) k u p *
        H1ComplDirichletToLp q z ((extChartAt I_hs α).symm
          ((toEuclidean (E := EuN)).symm p.2))
        ∂((timeMeasure T).restrict (Icc a b)).prod (volume.restrict Ω₀) := by
  let μ := (timeMeasure T).restrict (Icc a b)
  let V := dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs (timeMeasure T) k u
  let V₀ := dirichletLocalSpacetimeWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s (timeMeasure T) k u
  have hVt : ∀ᵐ t ∂μ, (fun x => V (t, x)) =ᵐ[volume.restrict Ω]
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) : EuStd → ℝ) :=
    ae_mono Measure.restrict_le_self
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs (timeMeasure T) k u)
  have hV₀t : ∀ᵐ t ∂μ, (fun x => V₀ (t, x)) =ᵐ[volume.restrict Ω₀]
      (dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) : EuStd → ℝ) :=
    ae_mono Measure.restrict_le_self
      (dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ₀ hΩ₀c hΩ₀s (timeMeasure T) k u)
  have hVV : (V₀ : ℝ × EuStd → ℝ) =ᵐ[μ.prod (volume.restrict Ω₀)] V := by
    apply (Measure.ae_prod_iff_ae_ae
      ((Lp.stronglyMeasurable V₀).measurableSet_eq_fun (Lp.stronglyMeasurable V))).mpr
    filter_upwards [hVt, hV₀t] with t hVt hV₀t
    have hrestrict := dirichletLocalWeakPartialLp_restrict_ae q α hΩ hΩc hΩs
      hΩ₀ hΩ₀c hΩ₀s hsub k (u t)
    have hVt₀ : (fun x => V (t, x)) =ᵐ[volume.restrict Ω₀]
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) : EuStd → ℝ) :=
      ae_mono (Measure.restrict_mono hsub le_rfl) hVt
    exact hV₀t.trans (hrestrict.symm.trans hVt₀.symm)
  intro τ z
  apply (integral_mass_inner_eq_integral_spacetime_weak_partial q α hΩ₀ hΩ₀c hΩ₀s
    hη hηc hηs u v k hv τ z).trans
  apply integral_congr_ae
  filter_upwards [hVV] with p hp
  change τ p.1 * η p.2 * MetricExtension.densityOnEuclid q α p.2 * V₀ p * _ = _
  rw [hp]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
