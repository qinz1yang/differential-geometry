import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffMetricEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffTimeEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CutoffScalarSource
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalSecondDerivative
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartFlux
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SliceWkp

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Geometry.Connection
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

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_local_second_weak_derivative_of_metric_divergence_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {c d : ℝ} (hac : a < c) (hdb : d < b) :
    let μ := volume.restrict (Icc a b)
    let ν := μ.prod (volume.restrict Ω)
    let ρ := fun p : ℝ × EuStd => densityOnEuclid (I := I_hs) (g p.1) α p.2
    let A := fun i j (p : ℝ × EuStd) => weightedInvGramOnEuclid (I := I_hs) (g p.1) α i j p.2
    ∀ U S : Lp ℝ 2 ν, ∀ K : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i
        (fun z => K i (t, z)) (fun z => U (t, z)) Ω) →
      (∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ p, ρ p * U p * fderiv ℝ φ p (1, 0) ∂ν) =
          (∑ i, ∑ j, ∫ p, A i j p * K i p * fderiv ℝ φ p (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ p, S p * φ p ∂ν) →
      let μ₀ := μ.restrict (Icc c d)
      ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Lp ℝ 2 (μ₀.prod (volume.restrict Ω₀)),
        (∀ i j, ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
          (fun z => H i j (t, z)) (fun z => K i (t, z)) Ω₀) ∧
        (∀ᵐ t ∂μ₀, MemWkp 2 2 (fun z => U (t, z)) Ω₀) ∧
        MemLp (fun t => (iteratedWeakSobolevNorm 2 2 (fun z => U (t, z)) Ω₀).toReal) 2 μ₀ := by
  intro μ ν ρ A U S K hK hweak μ₀
  let q := g a
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨δ, η, _, _, hη, _, _, hηone, hηs⟩ :=
    exists_smooth_cutoff_with_neighborhood hΩ₀c hΩ hΩ₀Ω
  have hηc : HasCompactSupport η :=
    hΩc.of_isClosed_subset (isClosed_tsupport _) (hηs.trans subset_closure)
  have hηone' : ∀ z ∈ Ω₀, η z = 1 := fun z hz =>
    hηone z (Metric.self_subset_cthickening (closure Ω₀) (subset_closure hz))
  obtain ⟨v, hv⟩ := exists_lp_h1ComplDirichlet_chartPullback_mul_of_joint_weak_partials
    q α hΩ hΩc hΩs hη hηc hηs U K hK
  let W := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hW : IsOpen W := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  let σ := fun p : ℝ × EuStd => densityOnEuclid q α p.2
  let r := fun p => ρ p / σ p
  let C := fun p => (r p)⁻¹ * S p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * U p)
  let Q := fun j p => ∑ i, (η p.2 / r p) * A i j p * K i p
  let B := fun p => η p.2 * C p -
    ∑ i, ∑ j, A i j p * K i p * fderiv ℝ (fun z => η z.2 / r z) p (0, EuclideanSpace.single j 1)
  obtain ⟨hQ, hB, ⟨ℓ, hℓ⟩, htensor⟩ := exists_lp_dual_of_cutoff_metric_divergence_equation
    (μ₀ := volume) hG q α hW Subset.rfl hΩ hΩc hΩs hreg hη hηs
    (Lp.memLp U) (Lp.memLp S) (fun i => Lp.memLp (K i)) hweak
  obtain ⟨w, hw, hd⟩ := exists_timeH1_of_cutoff_tensor_identity α hΩ hΩc hΩs hη hηs
    hab μ rfl U v ℓ Q B hv hℓ htensor
  have hflux := ae_cutoff_flux_eq_density_ratio q g α hΩ hΩc hΩs U
    (fun j p => K j p) (Lp.memLp U) (fun j => Lp.memLp (K j))
    (fun t => v t) hv hK hη
  obtain ⟨β, f, _, hpair, _, hsource⟩ := exists_lp_scalar_source_of_cutoff_flux q hG
    isCompact_Icc hreg α hΩ hΩc hΩs (μ := μ) le_rfl U K v ℓ hη hηs hK Q B hQ hB hℓ hflux
  obtain ⟨H, hH, _⟩ := exists_local_dirichlet_second_weak_derivative_of_timeH1_of_measure_eq_volume
    (G := G) hG hab.le hreg q α hΩ hΩc hΩs hac hdb rfl
    v f ℓ β w hw hd hpair hsource hΩ₀ hΩ₀Ω
  have hsub : Ω₀ ⊆ Ω := subset_closure.trans hΩ₀Ω
  have hmeasure : μ₀.prod (volume.restrict Ω₀) ≤ ν :=
    Measure.prod_mono Measure.restrict_le_self (Measure.restrict_mono hsub le_rfl)
  have hK₀ (i) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv i
      (fun z => K i (t, z)) (fun z => U (t, z)) Ω₀ := by
    filter_upwards [ae_restrict_of_ae (s := Icc c d) (hK i)] with t ht
    exact ht.restrict hΩ₀ hsub
  have halign (i) : ∀ᵐ t ∂μ₀,
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) : EuStd → ℝ)
        =ᵐ[volume.restrict Ω₀] fun z => K i (t, z) := by
    apply ae_dirichletLocalWeakPartialLp_eq_of_chartPullback_mul_eq_one q α
      hΩ hΩc hΩs hΩ₀ hsub (fun t => v t) (fun t z => U (t, z)) i
      (fun t z => K i (t, z)) hηone' (ae_restrict_of_ae hv) ?_ (hK₀ i)
    exact (((Lp.memLp (K i)).mono_measure hmeasure).prodMk_left (by norm_num)).mono
      (fun _ ht => ht.locallyIntegrable (by norm_num))
  have hH₀ (i j) : ∀ᵐ t ∂μ₀, DeGiorgi.HasWeakPartialDeriv j
      (fun z => H i j (t, z)) (fun z => K i (t, z)) Ω₀ := by
    filter_upwards [hH i j, halign i] with t ht he
    exact hasWeakPartialDeriv_congr_ae hΩ₀ j he ht
  have hKreg (i) := ae_memWkp_one_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num)
    ((Lp.memLp (K i)).mono_measure hmeasure) (fun j => Lp.memLp (H i j)) (hH₀ i)
  have hUreg := ae_memWkp_succ_and_memLp_wkpNorm_of_weak_partials
    hΩ₀ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num)
    ((Lp.memLp U).mono_measure hmeasure) (fun i => (hKreg i).1) (fun i => (hKreg i).2) hK₀
  exact ⟨H, hH₀, hUreg.1, hUreg.2⟩

end DifferentialGeometry.Analysis.Parabolic
