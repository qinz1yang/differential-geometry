import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.OfMetricDerivNorm
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.CompactExtension
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.PartialDiffeomorph
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Pairwise

set_option autoImplicit false
noncomputable section
universe u uQ uE uF uH uH'
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness
open Set Filter
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {H' : Type uH'} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
variable {Q : Type uQ} [TopologicalSpace Q] [ChartedSpace H Q] [T2Space Q] [IsManifold I ∞ Q]
variable {M N : Type u} [TopologicalSpace M] [ChartedSpace H' M] [T2Space M]
  [IsManifold J ∞ M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [T2Space N]
  [IsManifold J ∞ N] [SigmaCompactSpace N]

omit [T2Space N] [SigmaCompactSpace N] in
theorem exists_relative_map_metric_approximation_of_pullback_bound
    (Φ : PartialDiffeomorph I J Q M ∞) (Ψ : PartialDiffeomorph I J Q N ∞)
    (U : TopologicalSpace.Opens Q) [SigmaCompactSpace U]
    (hΦ : (U : Set Q) ⊆ Φ.source) (hΨ : (U : Set Q) ⊆ Ψ.source)
    (g : SmoothRiemannianMetric J M) (h : SmoothRiemannianMetric J N)
    (GΦ GΨ : SmoothRiemannianMetric I U)
    (hGΦ : ∀ (z : U) (v w : TangentSpace I z),
      GΦ.inner z v w = g.inner ((Φ : Q → M) z)
        (mfderiv I J (Φ : Q → M) (z : Q) v) (mfderiv I J (Φ : Q → M) (z : Q) w))
    (hGΨ : ∀ (z : U) (v w : TangentSpace I z),
      GΨ.inner z v w = h.inner ((Ψ : Q → N) z)
        (mfderiv I J (Ψ : Q → N) (z : Q) v) (mfderiv I J (Ψ : Q → N) (z : Q) w))
    {K K' : Set M} {L : Set U} (hK' : IsCompact K') (hKK' : K ⊆ interior K')
    (hsrc : K' ⊆ (Φ.symm.trans Ψ).source)
    (hcapture : K ⊆ (fun z : U => (Φ : Q → M) z) '' L)
    {p : ℕ} {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1)
    (hbound : ∀ a ≤ p, ∀ z ∈ L, metricDerivNorm (I := I) a GΨ GΦ GΦ z ≤ eps) :
    Nonempty (MapMetricApproximationOn (I := J) K eps p (Φ.symm.trans Ψ : M → N) g h) := by
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hKK : K ⊆ K' := hKK'.trans interior_subset
  have hKsrc : K ⊆ (Φ.symm.trans Ψ).source := hKK.trans hsrc
  obtain ⟨P, A, hPA, hA, hP⟩ :=
    exists_metric_tensor_field_eq_pullback_on_compact (I := J) (Φ.symm.trans Ψ) hK' hsrc h g
  refine ⟨MapMetricApproximationOn.ofMetricDerivNorm A g h heps heps1
    ((Φ.symm.trans Ψ).contMDiffOn_toFun.mono hKsrc) ?_ ?_⟩
  · intro y hy v
    rw [← hPA]
    exact hP y (hKK hy) v
  · intro a ha y hy
    obtain ⟨z, hz, rfl⟩ := hcapture hy
    have hnear : ∀ᶠ y in nhds ((Φ : Q → M) z), ∀ v w : TangentSpace J y,
        A.inner y v w = h.inner ((Φ.symm.trans Ψ) y)
          (mfderiv J J (Φ.symm.trans Ψ : M → N) y v)
          (mfderiv J J (Φ.symm.trans Ψ : M → N) y w) := by
      filter_upwards [isOpen_interior.mem_nhds (hKK' hy)] with y hy
      exact hA y (interior_subset hy)
    rw [metricDerivNorm_relative_pullback Φ Ψ U hΦ hΨ g h GΦ GΨ hGΦ hGΨ A a z hnear]
    exact hbound a ha z hz

theorem exists_relative_partial_diffeomorph_metric_approximation_of_pullback_bounds
    (Φ : PartialDiffeomorph I J Q M ∞) (Ψ : PartialDiffeomorph I J Q N ∞)
    (U : TopologicalSpace.Opens Q) [SigmaCompactSpace U]
    (hΦ : (U : Set Q) ⊆ Φ.source) (hΨ : (U : Set Q) ⊆ Ψ.source)
    (g : SmoothRiemannianMetric J M) (h : SmoothRiemannianMetric J N)
    (GΦ GΨ : SmoothRiemannianMetric I U)
    (hGΦ : ∀ (z : U) (v w : TangentSpace I z),
      GΦ.inner z v w = g.inner ((Φ : Q → M) z)
        (mfderiv I J (Φ : Q → M) (z : Q) v) (mfderiv I J (Φ : Q → M) (z : Q) w))
    (hGΨ : ∀ (z : U) (v w : TangentSpace I z),
      GΨ.inner z v w = h.inner ((Ψ : Q → N) z)
        (mfderiv I J (Ψ : Q → N) (z : Q) v) (mfderiv I J (Ψ : Q → N) (z : Q) w))
    {K K' : Set M} {L : Set U} (hK' : IsCompact K') (hKK' : K ⊆ interior K')
    (hsrc : K' ⊆ (Φ.symm.trans Ψ).source)
    (hcapture : K ⊆ (fun z : U => (Φ : Q → M) z) '' L)
    {p : ℕ} {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1)
    (hforward : ∀ a ≤ p, ∀ z ∈ L, metricDerivNorm (I := I) a GΨ GΦ GΦ z ≤ eps)
    (hreverse : ∀ a ≤ p, ∀ z ∈ L, metricDerivNorm (I := I) a GΦ GΨ GΨ z ≤ eps) :
    Nonempty (PartialDiffeomorphMetricApproximation (I := J) K eps p (Φ.symm.trans Ψ) g h) := by
  let R := Φ.symm.trans Ψ
  obtain ⟨hfwd⟩ := exists_relative_map_metric_approximation_of_pullback_bound Φ Ψ U hΦ hΨ
    g h GΦ GΨ hGΦ hGΨ hK' hKK' hsrc hcapture heps heps1 hforward
  have hKK : K ⊆ K' := hKK'.trans interior_subset
  have hRK' : IsCompact ((R : M → N) '' K') :=
    hK'.image_of_continuousOn (R.contMDiffOn_toFun.continuousOn.mono hsrc)
  have hRinterior : (R : M → N) '' K ⊆ interior ((R : M → N) '' K') := by
    apply (Set.image_mono hKK').trans
    exact interior_maximal (Set.image_mono interior_subset)
      (R.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior
        (interior_subset.trans hsrc))
  have hRsrc : (R : M → N) '' K' ⊆ (Ψ.symm.trans Φ).source := by
    rintro y ⟨x, hx, rfl⟩
    change R x ∈ R.target
    exact R.map_source (hsrc hx)
  have hRcapture : (R : M → N) '' K ⊆ (fun z : U => (Ψ : Q → N) z) '' L := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hcapture hx
    refine ⟨z, hz, ?_⟩
    change Ψ z = (Φ.symm.trans Ψ) (Φ z)
    rw [_root_.PartialDiffeomorph.trans_apply,
      _root_.PartialDiffeomorph.symm_apply_apply Φ (hΦ z.property)]
  obtain ⟨hrev⟩ := exists_relative_map_metric_approximation_of_pullback_bound Ψ Φ U hΨ hΦ
    h g GΨ GΦ hGΨ hGΦ hRK' hRinterior hRsrc hRcapture heps heps1 hreverse
  exact ⟨{ source_sub := hKK.trans hsrc, forward := hfwd, reverse := hrev }⟩


theorem MetricCInfConvergenceOnCompacts.eventually_relative_partial_diffeomorph_metric_approximation
    {Y : ℕ → Type u} [∀ k, TopologicalSpace (Y k)] [∀ k, ChartedSpace H' (Y k)]
    [∀ k, T2Space (Y k)] [∀ k, IsManifold J ∞ (Y k)] [∀ k, SigmaCompactSpace (Y k)]
    (U : TopologicalSpace.Opens Q) [SigmaCompactSpace U]
    (G : ℕ → SmoothRiemannianMetric I U) (gInf : SmoothRiemannianMetric I U)
    (hconv : MetricCInfConvergenceOnCompacts (I := I) G gInf gInf)
    (g : ∀ k, SmoothRiemannianMetric J (Y k))
    {L : Set U} (hL : IsCompact L) (p : ℕ) {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ n₀ : ℕ, ∀ k : ℕ, n₀ ≤ k → ∀ l : ℕ, n₀ ≤ l →
      ∀ (Φ : PartialDiffeomorph I J Q (Y k) ∞)
        (Ψ : PartialDiffeomorph I J Q (Y l) ∞),
      (U : Set Q) ⊆ Φ.source → (U : Set Q) ⊆ Ψ.source →
      (∀ (z : U) (v w : TangentSpace I z),
        (G k).inner z v w = (g k).inner ((Φ : Q → Y k) z)
          (mfderiv I J (Φ : Q → Y k) (z : Q) v)
          (mfderiv I J (Φ : Q → Y k) (z : Q) w)) →
      (∀ (z : U) (v w : TangentSpace I z),
        (G l).inner z v w = (g l).inner ((Ψ : Q → Y l) z)
          (mfderiv I J (Ψ : Q → Y l) (z : Q) v)
          (mfderiv I J (Ψ : Q → Y l) (z : Q) w)) →
      ∀ K K' : Set (Y k), IsCompact K' → K ⊆ interior K' →
        K' ⊆ (Φ.symm.trans Ψ).source →
        K ⊆ (fun z : U => (Φ : Q → Y k) z) '' L →
        Nonempty (PartialDiffeomorphMetricApproximation (I := J) K eps p
          (Φ.symm.trans Ψ) (g k) (g l)) := by
  obtain ⟨n₀, hn₀⟩ := hconv.eventually_pairwise_metric_deriv_norm G gInf hL p heps
  refine ⟨n₀, ?_⟩
  intro k hk l hl Φ Ψ hΦ hΨ hGΦ hGΨ K K' hK' hKK' hsrc hcapture
  exact exists_relative_partial_diffeomorph_metric_approximation_of_pullback_bounds Φ Ψ U
    hΦ hΨ (g k) (g l) (G k) (G l) hGΦ hGΨ hK' hKK' hsrc hcapture heps heps1
    (fun a ha z hz => (hn₀ l hl k hk a ha z hz).le)
    (fun a ha z hz => (hn₀ k hk l hl a ha z hz).le)

end DifferentialGeometry.CheegerGromovCompactness
