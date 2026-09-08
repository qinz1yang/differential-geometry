import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakChartPullback
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuant
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

omit [NeZero n] [CompactSpace M] [T2Space M] [IsManifold I_hs ∞ M] in
private theorem exists_wkpNorm_cutoff_bound
    {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ∃ K : ℝ, 0 < K ∧ ∀ {f : EuStd → ℝ}, MemWkp 1 2 f Ω →
      MemWkp 1 2 (fun z => η z * f z) Ω ∧
      (iteratedWeakSobolevNorm 1 2 (fun z => η z * f z) Ω).toReal ≤
        K * (iteratedWeakSobolevNorm 1 2 f Ω).toReal := by
  obtain ⟨C₀, hC₀⟩ := hΩc.exists_bound_of_continuousOn hη.continuous.continuousOn
  obtain ⟨C₁, hC₁⟩ := hΩc.exists_bound_of_continuousOn
    (hη.continuous_fderiv (by simp)).continuousOn
  let C := max (max C₀ C₁) 0
  have hC : 0 ≤ C := le_max_right _ _
  have hηb : ∀ j ≤ 1, ∀ z ∈ Ω, ‖iteratedFDeriv ℝ j η z‖ ≤ C := by
    intro j hj z hz
    have hc0 : C₀ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
    have hc1 : C₁ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · rw [norm_iteratedFDeriv_zero]
      exact (hC₀ z (subset_closure hz)).trans hc0
    · rw [norm_iteratedFDeriv_one]
      exact (hC₁ z (subset_closure hz)).trans hc1
  obtain ⟨K, hK, hmul⟩ := wkpNorm_smul_smooth_bounded_le_one 1 le_rfl
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hΩ hη hC hηb
  refine ⟨K, hK, ?_⟩
  intro f hf
  refine ⟨MemWkp.smul_smooth_bounded 1 (by norm_num) hΩ hη hηb hf, ?_⟩
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) (wkpNorm_lt_top_of_memWkp hf).ne) (hmul hf)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le] using hr

theorem exists_norm_h1ComplDirichlet_chartPullback_mul_le_wkpNorm
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : EuStd → ℝ}, MemWkp 1 2 f Ω →
      ∃ e : H1ComplDirichlet q,
        (H1ComplDirichletToLp q e : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I_hs) (M := M) q]
          chartPullback I_hs α (fun z => η z * f z) ∧
        ‖e‖ ≤ A * (iteratedWeakSobolevNorm 1 2 f Ω).toReal := by
  obtain ⟨K, hK, hmul⟩ := exists_wkpNorm_cutoff_bound hΩ hΩc hη
  obtain ⟨B, hB, hpb⟩ := exists_h1ComplDirichlet_chartPullback (n := n) (M := M) q α hΩ hΩc hΩs
  refine ⟨B*K, mul_nonneg hB hK.le, ?_⟩
  intro f hf
  have hs : tsupport (fun z => η z * f z) ⊆ Ω :=
    (tsupport_mul_subset_left (f := η) (g := f)).trans hηs
  obtain ⟨e, he, hne⟩ := hpb (fun z => η z * f z) (hmul hf).1 hs
  have hh := mul_le_mul_of_nonneg_left (hmul hf).2 hB
  exact ⟨e, he, hne.trans (by simpa only [mul_assoc] using hh)⟩


theorem exists_norm_h1ComplDirichlet_lift_chartPullback_mul
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : tsupport η ⊆ Ω)
    (L : Lp ℝ 2 (volume.restrict Ω) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q))
    (hL : ∀ f, (L f : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      chartPullback I_hs α (fun z => η z * f z)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : Lp ℝ 2 (volume.restrict Ω), MemWkp 1 2 f Ω →
      ∃ e : H1ComplDirichlet q, H1ComplDirichletToLp q e = L f ∧
        ‖e‖ ≤ A * (iteratedWeakSobolevNorm 1 2 f Ω).toReal := by
  obtain ⟨A, hA, hpb⟩ := exists_norm_h1ComplDirichlet_chartPullback_mul_le_wkpNorm q α hΩ hΩc hΩs hη hηs
  refine ⟨A, hA, ?_⟩
  intro f hf
  obtain ⟨e, he, hne⟩ := hpb hf
  exact ⟨e, Lp.ext (he.trans (hL f).symm), hne⟩

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
