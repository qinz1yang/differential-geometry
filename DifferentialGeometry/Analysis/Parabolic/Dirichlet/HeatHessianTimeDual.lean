import DifferentialGeometry.Analysis.Parabolic.Dirichlet.HeatGradientTimeRegularity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakSpatialDerivative
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartCutoff

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
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

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_timeH1_cutoff_hessian_mass_dual_of_heat_timeH1
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
    (hηs : tsupport η ⊆ Ω₀) :
    let F := Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (((chartRestrictionLp q α hΩ.measurableSet hΩc
        (hΩs.trans (image_mono interior_subset)) 2).compLpL 2 (timeMeasure T)) f)
    ∀ Df : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 ((timeMeasure T).prod (volume.restrict Ω)),
      (∀ k, ∀ᵐ t ∂timeMeasure T, DeGiorgi.HasWeakPartialDeriv k (fun z => Df k (t, z))
        (fun z => F (t, z)) Ω) →
    let μ := (timeMeasure T).restrict (Icc a b)
    ∀ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        Lp ℝ 2 (μ.prod (volume.restrict Ω₀)),
      (∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
        (fun z => H i j (t, z))
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀) →
      ∃ v : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
          Lp (H1ComplDirichlet q) 2 μ,
        (∀ i j, ∀ᵐ t ∂μ,
          (H1ComplDirichletToLp q (v i j t) : M → ℝ) =ᵐ[
            riemannianVolumeMeasure (I := I_hs) (M := M) q]
            Sobolev.Chart.chartPullback I_hs α (fun z => η z * H i j (t, z))) ∧
        ∀ i j, ∃ w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a),
          ∀ᵐ s ∂timeMeasure (b - a), ∀ z : H1ComplDirichlet q,
            w.toFun s z = inner ℝ (H1ComplDirichletToLp q (v i j (a + s)))
              (H1ComplDirichletToLp q z) := by
  intro F Df hDf μ H hH
  classical
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  have hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target :=
    hΩ₀Ω.trans (subset_closure.trans hΩs)
  have hηc : HasCompactSupport η :=
    hΩ₀c.of_isClosed_subset (isClosed_tsupport η) (hηs.trans subset_closure)
  obtain ⟨K, hK⟩ := exists_local_third_weak_derivative_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab.le u f w hwmass hwderiv Df hDf H hH
  choose v hv using fun i j =>
    exists_lp_h1ComplDirichlet_chartPullback_mul_of_joint_weak_partials
      q α hΩ₀ hΩ₀c hΩ₀s hη hηc hηs (H i j) (K i j) (hK i j)
  refine ⟨v, hv, ?_⟩
  intro i j
  obtain ⟨z, hz⟩ := exists_timeH1_localWeakPartial_of_heat_timeH1
    hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol α hΩ hΩc hΩs
    hΩ₀ hΩ₀Ω ha hb hab u f w hwmass hwderiv Df hDf i
  have hI : Icc a b ⊆ Icc (0 : ℝ) T := Icc_subset_Icc ha.le hb.le
  have hshift : MeasurePreserving (fun s : ℝ => a + s)
      (timeMeasure (b - a)) μ := measurePreserving_add_right_timeMeasure_restrict hI
  have hweak : ∀ᵐ s ∂timeMeasure (b - a), DeGiorgi.HasWeakPartialDeriv j
      (fun x => H i j (a + s, x)) (z.toFun s) Ω₀ := by
    filter_upwards [hz, hshift.quasiMeasurePreserving.ae (hH i j)] with s hzs hHs
    intro φ hφ hφc hφs
    refine (integral_congr_ae ?_).trans (hHs φ hφ hφc hφs)
    filter_upwards [hzs] with x hx
    exact congrArg (· * fderiv ℝ φ x (EuclideanSpace.single j 1)) hx
  exact exists_timeH1_mass_dual_of_chartPullback_weak_partial q α hΩ₀ hΩ₀c hΩ₀s
    hη hηs j z (fun p => H i j (a + p.1, p.2))
    (hshift.quasiMeasurePreserving.ae ((Lp.memLp (H i j)).prodMk_left (by norm_num)))
    hweak (fun s => v i j (a + s)) (hshift.quasiMeasurePreserving.ae (hv i j))

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
