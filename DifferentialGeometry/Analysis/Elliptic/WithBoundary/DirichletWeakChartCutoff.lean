import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivativeLift
import DifferentialGeometry.Analysis.Sobolev.Chart.CutoffPullbackLp
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSeparability
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

private theorem exists_chartPullback_mul_lift
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) :
    ∃ L : Lp ℝ 2 (volume.restrict Ω) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q),
      (∀ f, (L f : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * f z)) ∧
      ∃ A : ℝ, ∀ f : Lp ℝ 2 (volume.restrict Ω), MemWkp 1 2 f Ω →
        ∃ e : H1ComplDirichlet q, H1ComplDirichletToLp q e = L f ∧
          ‖e‖ ≤ A * (iteratedWeakSobolevNorm 1 2 f Ω).toReal := by
  obtain ⟨L, hL⟩ := exists_continuousLinearMap_chartPullback_mul q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) hη.continuous hηc hηs
  obtain ⟨A, _, hA⟩ := exists_norm_h1ComplDirichlet_lift_chartPullback_mul q α hΩ hΩc hΩs hη hηs L hL
  exact ⟨L, hL, A, hA⟩

theorem exists_lp_h1ComplDirichlet_chartPullback_mul_of_weak_partials
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω)
    (P : Lp (Lp ℝ 2 (volume.restrict Ω)) 2 μ)
    (W : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i (fun z => W i (t, z))
      (P t : EuStd → ℝ) Ω) :
    ∃ v : Lp (H1ComplDirichlet q) 2 μ, ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (fun z => η z * P t z) := by
  obtain ⟨L, hL, A, hA⟩ := exists_chartPullback_mul_lift q α hΩ hΩc hΩs hη hηc hηs
  obtain ⟨v, hv⟩ := exists_lp_lift_of_weak_partials hΩ (H1ComplDirichletToLp q).continuous
    (H1ComplDirichletToLp_injective q) L A hA P W hweak
  refine ⟨v, ?_⟩
  filter_upwards [hv] with t ht
  have he : (H1ComplDirichletToLp q (v t) : M → ℝ) = (L (P t) : M → ℝ) :=
    congrArg (fun f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q) => (f : M → ℝ)) ht
  exact Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => congrFun he x) (hL (P t))

theorem ae_dirichletLocalWeakPartialLp_eq_of_chartPullback_mul_localWeakPartial
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hsub : Ω₀ ⊆ Ω) (u v : Z → H1ComplDirichlet q)
    (k j : Fin (Module.finrank ℝ EuN))
    (H : Lp ℝ 2 (μ.prod (volume.restrict Ω₀))) {η : EuStd → ℝ}
    (hv : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α
          (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) z))
    (hweak : ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j (fun z => H (t, z))
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t)) Ω₀)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    ∀ᵐ t ∂μ,
      (dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s j (v t) : EuStd → ℝ) =ᵐ[volume.restrict Ω₀]
        (fun z => η z * H (t, z) + fderiv ℝ η z (EuclideanSpace.single j 1) *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) z) := by
  filter_upwards [hv, hweak, (Lp.memLp H).prodMk_left (by norm_num)] with t hvt hwt hHt
  exact dirichletLocalWeakPartialLp_eq_ae_of_chartPullback_mul_localWeakPartial q α
    hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀s hsub (u t) (v t) k j hvt hHt hwt hη hηc

theorem ae_cutoff_gradient_flux_eq
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω₀ : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ₀ : IsOpen Ω₀) (hΩ₀c : IsCompact (closure Ω₀))
    (hΩ₀s : closure Ω₀ ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hsub : Ω₀ ⊆ Ω) (u v : Z → H1ComplDirichlet q)
    (k : Fin (Module.finrank ℝ EuN))
    (H : Fin (Module.finrank ℝ EuN) → Lp ℝ 2 (μ.prod (volume.restrict Ω₀)))
    (A : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) → Z × EuStd → ℝ)
    (r : Z × EuStd → ℝ) {η : EuStd → ℝ}
    (hv : ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α
          (fun z => η z * dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s k (u t) z))
    (hweak : ∀ i, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv i (fun z => H i (t, z))
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t)) Ω₀)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    ∀ j, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume.restrict Ω₀,
      (∑ i, (η z / r (t, z)) * A i j (t, z) * H i (t, z)) =
        (∑ i, (A i j (t, z) / r (t, z)) *
          dirichletLocalWeakPartialLp q α hΩ₀ hΩ₀c hΩ₀s i (v t) z) -
        ∑ i, (A i j (t, z) / r (t, z)) * fderiv ℝ η z (EuclideanSpace.single i 1) *
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k (u t) z := by
  classical
  intro j
  have hpartial (i) := ae_dirichletLocalWeakPartialLp_eq_of_chartPullback_mul_localWeakPartial
    q α hΩ hΩc hΩs hΩ₀ hΩ₀c hΩ₀s hsub u v k i (H i) hv (hweak i) hη hηc
  filter_upwards [ae_all_iff.mpr hpartial] with t ht
  filter_upwards [ae_all_iff.mpr ht] with z hz
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hz i]
  simp only [div_eq_mul_inv]
  ring

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
