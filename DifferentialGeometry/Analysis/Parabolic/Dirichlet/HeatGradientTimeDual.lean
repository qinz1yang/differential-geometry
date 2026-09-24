import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatTimeRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GradientTimeDual

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
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

theorem exists_timeH1_weighted_gradient_dual_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T) (hab : a < b)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z))
    {c : EuStd → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcc : HasCompactSupport c) (hcs : tsupport c ⊆ Ω₀) (k : Fin (Module.finrank ℝ EuN)) :
    ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a),
      ∀ᵐ s ∂timeMeasure (b - a), ∀ v : H1ComplDirichlet q,
        w.toFun s v = ∫ z in Ω₀,
          dirichletLocalWeakPartialLp q α hΩ₀
            (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
            (hΩ₀Ω.trans (subset_closure.trans hΩs)) k (u (a + s)) z * c z *
            H1ComplDirichletToLp q v ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) := by
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  obtain ⟨z, hz⟩ := exists_timeH1_chartInverse_of_heat_timeH1 hG hT hreg q hCg hequiv Cv hCv0
    hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv
  exact exists_timeH1_dual_weak_partial q α hΩ₀ hΩ₀c hΩ₀s (fun s => u (a + s)) hc hcc hcs k z hz

theorem exists_timeH1_cutoff_gradient_mass_dual_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω Ω₀ : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω)
    {a b : ℝ} (ha : 0 < a) (hb : b < T) (hab : a < b)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
      w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
        hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
        (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
          inner ℝ (f t) (H1ComplDirichletToLp q z))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω₀) (k : Fin (Module.finrank ℝ EuN)) :
    ∃ v : Lp (H1ComplDirichlet q) 2 ((timeMeasure T).restrict (Icc a b)),
      ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a),
        (∀ᵐ t ∂(timeMeasure T).restrict (Icc a b),
          (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
            DifferentialGeometry.Analysis.Sobolev.Chart.chartPullback I_hs α
              (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀
                (hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure))
                (hΩ₀Ω.trans (subset_closure.trans hΩs)) k (u t) z)) ∧
        ∀ᵐ s ∂timeMeasure (b - a), ∀ z : H1ComplDirichlet q,
          w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v (a + s))) (H1ComplDirichletToLp q z) := by
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  let c : EuStd → ℝ := fun x => densityOnEuclid q α x * η x
  have hcs : tsupport c ⊆ Ω₀ := tsupport_mul_subset_right.trans hηs
  have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
    (((densityOnEuclid_contDiffOn q α).mono
      (subset_closure.trans (hΩ₀s.trans (image_mono interior_subset)))).mul
        hη.contDiffOn).contDiff_of_tsupport_subset hΩ₀ hcs
  have hcc : HasCompactSupport c := hηc.mul_left
  obtain ⟨z, hz⟩ := exists_timeH1_weighted_gradient_dual_of_heat_timeH1 hG hT hreg q hCg hequiv
    Cv hCv0 hCvtop hvol α hΩ hΩc hΩs hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv hc hcc hcs k
  obtain ⟨v, hv⟩ := exists_lp_h1_gradient_chartPullback_mul_of_heat_timeH1 hG hT hreg q hCg
    hequiv Cv hCv0 hCvtop hvol α hΩ₀ hΩ₀c hΩ₀s ha hb u f w hwmass hwderiv hη hηc hηs k
  refine ⟨v, z, hv, ?_⟩
  have hI : Icc a b ⊆ Icc (0 : ℝ) T := fun t ht => ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
  have hshift : MeasurePreserving (fun s : ℝ => a + s) (timeMeasure (b - a))
      ((timeMeasure T).restrict (Icc a b)) := measurePreserving_add_right_timeMeasure_restrict hI
  filter_upwards [hz, hshift.quasiMeasurePreserving.ae hv] with t ht hvt
  intro z
  exact (ht z).trans (inner_eq_integral_chartPullback_mul q α hΩ₀s hη hηs
    (dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u (a + t))) (v (a + t)) z hvt).symm

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
