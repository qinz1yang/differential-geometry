import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartCutoff
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalForm

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev.Euclidean
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

theorem ae_cutoff_gradient_flux_eq_density_ratio
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (g : Z → SmoothRiemannianMetric I_hs M)
    (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hsub : Ω₀ ⊆ Ω) (u v : Z → H1ComplDirichlet q)
    (k : Fin (Module.finrank ℝ EuN))
    (H : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω₀)))
    {η : EuStd → ℝ}
    (hv : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α
          (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) z))
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i (fun z => H i (t, z))
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t)) Ω₀)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    let ρ := fun p : Z × EuStd => MetricExtension.densityOnEuclid (g p.1) α p.2
    let σ := fun p : Z × EuStd => MetricExtension.densityOnEuclid q α p.2
    let r := fun p => ρ p / σ p
    let A := fun i j (p : Z × EuStd) => MetricExtension.weightedInvGramOnEuclid (g p.1) α i j p.2
    let c := fun i j (p : Z × EuStd) => σ p * MetricExtension.invGramOnEuclid (g p.1) α i j p.2
    ∀ j, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume.restrict Ω₀,
      (∑ i, (η z / r (t, z)) * A i j (t, z) * H i (t, z)) =
        (∑ i, c i j (t, z) * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s i (v t) z) -
          ∑ i, c i j (t, z) * fderiv ℝ η z (EuclideanSpace.single i 1) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) z := by
  intro ρ σ r A c j
  have h := ae_cutoff_gradient_flux_eq q α hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀s hsub
    u v k H A r hv hweak hη hηc j
  filter_upwards [h] with t ht
  filter_upwards [ht, ae_restrict_mem hΩ₀.measurableSet] with z hz hzm
  have hcoeff (i) : A i j (t, z) / r (t, z) = c i j (t, z) :=
    DifferentialGeometry.Analysis.Parabolic.Dirichlet.weightedInvGramOnEuclid_div_density_ratio
      q (g t) α i j z (hΩ₀s.trans (image_mono interior_subset) (subset_closure hzm))
  simpa only [hcoeff] using hz

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
