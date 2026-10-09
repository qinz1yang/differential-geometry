import DifferentialGeometry.Analysis.Parabolic.ClosedCell.WeakEquation
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakDensity.TimeDerivatives
import DifferentialGeometry.Topology.Attachment.Basic

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Matrix Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Handle

private local instance (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

private local instance (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  closedCellIsManifold m

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin (m + 1))
local notation "W" => EuclideanSpace ℝ (Fin (Module.finrank ℝ V))

private local instance : T2Space V := inferInstance

private local instance : MeasurableSpace W :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ V)) → ℝ)

theorem exists_closedCell_time_weak_partial_trees
    (k l : ℕ) (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (Ω : Set W) (hΩ : IsOpen Ω) :
    let z : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun y => Φ ((toEuclidean (E := V)).symm y)
    let Q : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    let Ωh := (fun x => z + r • x) ⁻¹' Ω
    IsCompact (closure Ωh) →
    closure Ωh ⊆ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target →
    ∀ (U : Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω)))
      (K : Fin (Module.finrank ℝ V) →
        Lp ℝ 2 ((volume.restrict (Icc a b)).prod (volume.restrict Ω))),
      (∀ i, ∀ᵐ t ∂volume.restrict (Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => K i (t, x)) (fun x => U (t, x)) Ω) →
      (∀ φ : ℝ × W → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * U q * fderiv ℝ φ q (1, 0)
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
          ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) * K i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1)
              ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) →
      ∀ {a' b' : ℝ}, a < a' → b' < b → ∀ {Ω₀ : Set W},
        IsOpen Ω₀ → closure Ω₀ ⊆ Ωh →
        let ν := (volume.restrict (Icc a' b')).prod (volume.restrict Ω₀)
        let e : Fin 0 → Fin (Module.finrank ℝ V) := fun i => Fin.elim0 i
        ∃ X : Fin (l + 2) → ∀ n : ℕ,
            (Fin n → Fin (Module.finrank ℝ V)) → Lp ℝ 2 ν,
          (X 0 0 e =ᵐ[ν] fun q => U (q.1, z + r • q.2)) ∧
          (∀ i, X 0 1 (Fin.cons i e) =ᵐ[ν] fun q => r * K i (q.1, z + r • q.2)) ∧
          (∀ j n, n < k + 2 * (l + 1 - j.val) → ∀ β i,
            ∀ᵐ t ∂volume.restrict (Icc a' b'), DeGiorgi.HasWeakPartialDeriv i
              (fun x => X j (n + 1) (Fin.cons i β) (t, x)) (fun x => X j n β (t, x)) Ω₀) ∧
          (let G := closedCellPullbackMetricFamily D g Φ c hr hsource
           let ρ := fun q : ℝ × W => MetricExtension.densityOnEuclid (G.metric q.1) α q.2
           let A := fun i j (q : ℝ × W) =>
             MetricExtension.weightedInvGramOnEuclid (G.metric q.1) α i j q.2
           X 1 0 e =ᵐ[ν] fun q => (ρ q)⁻¹ *
             ((∑ i, ∑ j, (A i j q * X 0 2 (Fin.cons j (Fin.cons i e)) q +
               fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1) *
                 X 0 1 (Fin.cons i e) q)) - fderiv ℝ ρ q (1, 0) * X 0 0 e q)) ∧
          ∀ j : Fin (l + 1), ∀ n, n ≤ k + 2 * (l - j.val) →
            ∀ β (φ : ℝ × W → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
            HasCompactSupport φ → tsupport φ ⊆ Ioo a' b' ×ˢ Ω₀ →
            (∫ q, X j.castSucc n β q * fderiv ℝ φ q (1, 0) ∂ν) =
              -∫ q, X j.succ n β q * φ q ∂ν := by
  intro z Ψ Q Ωh hΩhc hΩhs U K hspatial hweak a' b' haa hbb Ω₀ hΩ₀ hΩ₀Ω ν e
  classical
  let μ := volume.restrict (Icc a b)
  let νh := μ.prod (volume.restrict Ωh)
  let F : Lp ℝ 2 (μ.prod (volume.restrict Ω)) := 0
  have hFzero : F =ᵐ[μ.prod (volume.restrict Ω)] fun _ => (0 : ℝ) :=
    Lp.coeFn_zero ℝ 2 (μ.prod (volume.restrict Ω))
  have hweakF (φ : ℝ × W → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ Ω) :
      (∫ q, Real.sqrt (Q q).det * U q * fderiv ℝ φ q (1, 0)
        ∂μ.prod (volume.restrict Ω)) =
        (∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) * K i q) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω)) -
          ∫ q, F q * φ q ∂μ.prod (volume.restrict Ω) := by
    have hz : (∫ q, F q * φ q ∂μ.prod (volume.restrict Ω)) = 0 := by
      calc
        _ = ∫ q, (0 : ℝ) ∂μ.prod (volume.restrict Ω) := by
          apply integral_congr_ae
          filter_upwards [hFzero] with q hq
          rw [hq, zero_mul]
        _ = 0 := integral_zero _ _
    simpa only [hz, sub_zero] using hweak φ hφ hφc hφs
  obtain ⟨Uh, Fh, Kh, hU, hF, hK, hspatialH, hweakH⟩ :=
    exists_closedCell_lp_weighted_weak_equation D g Φ c hr hsource α hα μ (Ioo a b) Ω
      (subset_closure.trans hΩhs) U F K hspatial hweakF
  have hFhzero : Fh =ᵐ[νh] fun _ => (0 : ℝ) := by
    have hmap := quasiMeasurePreserving_prod_add_smul_restrict μ volume z hr.ne' Ω
    filter_upwards [hF, hmap.ae hFzero] with q hq hz
    change Fh q = r ^ Module.finrank ℝ V * F (q.1, z + r • q.2) at hq
    rw [hz, mul_zero] at hq
    exact hq
  let G := closedCellPullbackMetricFamily D g Φ c hr hsource
  have hweakZero (φ : ℝ × W → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ Ωh) :
      (∫ q, MetricExtension.densityOnEuclid (G.metric q.1) α q.2 * Uh q *
        fderiv ℝ φ q (1, 0) ∂νh) =
        ∑ j, ∫ q, (∑ i, MetricExtension.weightedInvGramOnEuclid
          (G.metric q.1) α i j q.2 * Kh i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂νh := by
    have hz : (∫ q, Fh q * φ q ∂νh) = 0 := by
      calc
        _ = ∫ q, (0 : ℝ) ∂νh := by
          apply integral_congr_ae
          filter_upwards [hFhzero] with q hq
          rw [hq, zero_mul]
        _ = 0 := integral_zero _ _
    have h := hweakH φ hφ hφc hφs
    change (∫ q, MetricExtension.densityOnEuclid (G.metric q.1) α q.2 * Uh q *
      fderiv ℝ φ q (1, 0) ∂νh) =
        (∑ j, ∫ q, (∑ i, MetricExtension.weightedInvGramOnEuclid
          (G.metric q.1) α i j q.2 * Kh i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂νh) -
              ∫ q, Fh q * φ q ∂νh at h
    simpa only [hz, sub_zero] using h
  have hΩh : IsOpen Ωh := hΩ.preimage (by fun_prop)
  obtain ⟨X, hXzero, hXone, hXweak, hXformula, hXtime⟩ :=
    Dirichlet.exists_local_lp_time_weak_partial_trees_of_homogeneous_weighted_weak_equation
      k l (metricFamilySmoothOn_closedCellPullbackMetricFamily D g Φ c hr hsource hg)
      hab hreg α hΩh hΩhc hΩhs Uh Kh hspatialH hweakZero haa hbb hΩ₀ hΩ₀Ω
  have hν : ν ≤ νh := Measure.prod_mono
    (Measure.restrict_mono (Icc_subset_Icc haa.le hbb.le) le_rfl)
    (Measure.restrict_mono (subset_closure.trans hΩ₀Ω) le_rfl)
  refine ⟨X, hXzero.trans (hU.filter_mono (ae_mono hν)), ?_,
    hXweak, hXformula, hXtime⟩
  intro i
  exact (hXone i).trans ((hK i).filter_mono (ae_mono hν))

end DifferentialGeometry.Analysis.Parabolic
