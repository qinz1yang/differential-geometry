import DifferentialGeometry.Geometry.Metric.Convergence.Window.AllOrders

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open scoped Manifold ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_metric_subsequence_tendsto_uniformly_on_time_interval_of_eventual_pointwise_lower
    {a b : ℝ} (hab : a ≤ b)
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (hind : ∀ i, ∀ K : Set M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeq i s) (gSeq i t) gRef x ≤ L * |s - t|)
    (hlip : ∀ K : Set M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ i in atTop, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeq i s) (gSeq i t) gRef x ≤ L * |s - t|)
    (hcov : ∀ t ∈ Icc a b, ∀ q : ℕ, ∀ K : Set M, IsCompact K →
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ K, metricCovDerivNorm q (gSeq i t) gRef x ≤ C)
    (hlower : ∀ t ∈ Icc a b, ∀ x : M, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop, ∀ v : TangentSpace I x,
        c * gRef.inner x v v ≤ (gSeq i t).inner x v v) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ g : ℝ → SmoothRiemannianMetric I M,
      ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ Icc a b,
          metricDerivNormSupOn K p (gSeq (f i) t) (g t) gRef < epsilon := by
  classical
  rcases isEmpty_or_nonempty M with hM | hne
  · let _ : IsEmpty M := hM
    refine ⟨id, strictMono_id, fun _ => gRef, fun K _ p epsilon hepsilon =>
      ⟨0, fun i _ t _ => ?_⟩⟩
    simpa [metricDerivNormSupOn] using hepsilon
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hfull : ∀ K : Set M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeq i s) (gSeq i t) gRef x ≤ L * |s - t| := by
    intro K hK p
    obtain ⟨Lt, hLt, htail⟩ := hlip K hK p
    obtain ⟨N, hN⟩ := eventually_atTop.mp htail
    have hprefix : ∀ n : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ i < n,
        ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeq i s) (gSeq i t) gRef x ≤ L * |s - t| := by
      intro n
      induction n with
      | zero => exact ⟨0, le_rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      | succ n ih =>
        obtain ⟨L, hL, hbound⟩ := ih
        obtain ⟨Li, hLi, hbi⟩ := hind n K hK p
        refine ⟨max L Li, hL.trans (le_max_left _ _), fun i hi s hs t ht q hq x hx => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact (hbound i hi s hs t ht q hq x hx).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
        · exact (hbi s hs t ht q hq x hx).trans
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
    obtain ⟨Lp, hLp, hp⟩ := hprefix N
    refine ⟨max Lp Lt, hLp.trans (le_max_left _ _), fun i s hs t ht q hq x hx => ?_⟩
    rcases lt_or_ge i N with hi | hi
    · exact (hp i hi s hs t ht q hq x hx).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    · exact (hN i hi s hs t ht q hq x hx).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
  have hbounded : ∀ rho : ℕ → ℕ, StrictMono rho → ∀ t ∈ Icc a b,
      ∀ q : ℕ, ∀ K : Set M, IsCompact K → ∃ C : ℝ,
        ∀ i, ∀ x ∈ K, metricCovDerivNorm q (gSeq (rho i) t) gRef x ≤ C := by
    intro rho _hrho t ht q K hK
    obtain ⟨C, hc⟩ := hcov t ht q K hK
    obtain ⟨N, hN⟩ := eventually_atTop.mp hc
    obtain ⟨C', hC'⟩ := cov_bdd_of_eventual hK q (fun i => gSeq i t) gRef ⟨N, C, hN⟩
    exact ⟨C', fun i x hx => hC' (rho i) x hx⟩
  let T := {t : ℝ // t ∈ Icc a b}
  let _ : Nonempty T := ⟨⟨a, le_rfl, hab⟩⟩
  let e : ℕ → ℝ := fun n => (TopologicalSpace.denseSeq T n).val
  have he : ∀ n, e n ∈ Icc a b := fun n => (TopologicalSpace.denseSeq T n).property
  have hdense : ∀ t ∈ Icc a b, ∀ delta : ℝ, 0 < delta → ∃ n, |t - e n| < delta := by
    intro t ht delta hd
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq T).exists_dist_lt (⟨t, ht⟩ : T) hd
    refine ⟨n, ?_⟩
    simpa [T, Subtype.dist_eq, Real.dist_eq, e] using hn
  exact exists_metric_subsequence_tendsto_uniformly_on_compacts_and_time_of_eventual_pointwise_lower
    hne a b gRef gSeq e he hdense hfull hbounded
    (fun rho hrho t ht x => by
      obtain ⟨c, hc, hlow⟩ := hlower t ht x
      exact ⟨c, hc, hrho.tendsto_atTop.eventually hlow⟩)

theorem exists_metric_subsequence_tendsto_uniformly_on_time_interval_of_eventual_compact_lower
    {a b : ℝ} (hab : a ≤ b)
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (hind : ∀ i, ∀ K : Set M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeq i s) (gSeq i t) gRef x ≤ L * |s - t|)
    (hlip : ∀ K : Set M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ i in atTop, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeq i s) (gSeq i t) gRef x ≤ L * |s - t|)
    (hcov : ∀ t ∈ Icc a b, ∀ q : ℕ, ∀ K : Set M, IsCompact K →
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ K, metricCovDerivNorm q (gSeq i t) gRef x ≤ C)
    (hlower : ∀ t ∈ Icc a b, ∀ K : Set M, IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in atTop, ∀ x ∈ K, ∀ v : TangentSpace I x,
        c * gRef.inner x v v ≤ (gSeq i t).inner x v v) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ g : ℝ → SmoothRiemannianMetric I M,
      ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ Icc a b,
          metricDerivNormSupOn K p (gSeq (f i) t) (g t) gRef < epsilon := by
  apply exists_metric_subsequence_tendsto_uniformly_on_time_interval_of_eventual_pointwise_lower
    hab gRef gSeq hind hlip hcov
  intro t ht x
  obtain ⟨c, hc, hbound⟩ := hlower t ht {x} isCompact_singleton
  exact ⟨c, hc, hbound.mono fun i hi => hi x (Set.mem_singleton x)⟩

theorem exists_metric_subsequence_tendsto_uniformly_on_time_interval_of_eventual_bounds
    {a b : ℝ} (hab : a ≤ b)
    (gRef : SmoothRiemannianMetric I M) (gSeq : ℕ → ℝ → SmoothRiemannianMetric I M)
    (hind : ∀ i, ∀ K : Set M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeq i s) (gSeq i t) gRef x ≤ L * |s - t|)
    (hlip : ∀ K : Set M, IsCompact K → ∀ p : ℕ,
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ i in atTop, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        ∀ q ≤ p, ∀ x ∈ K,
          metricDerivNorm q (gSeq i s) (gSeq i t) gRef x ≤ L * |s - t|)
    (hcov : ∀ t ∈ Icc a b, ∀ q : ℕ, ∀ K : Set M, IsCompact K →
      ∃ C : ℝ, ∀ᶠ i in atTop, ∀ x ∈ K, metricCovDerivNorm q (gSeq i t) gRef x ≤ C)
    (hlower : ∀ t ∈ Icc a b, ∃ c : ℝ, 0 < c ∧
      ∀ i, ∀ x : M, ∀ v : TangentSpace I x,
        c * gRef.inner x v v ≤ (gSeq i t).inner x v v) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ g : ℝ → SmoothRiemannianMetric I M,
      ∀ K : Set M, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ Icc a b,
          metricDerivNormSupOn K p (gSeq (f i) t) (g t) gRef < epsilon := by
  apply exists_metric_subsequence_tendsto_uniformly_on_time_interval_of_eventual_pointwise_lower
    hab gRef gSeq hind hlip hcov
  intro t ht x
  obtain ⟨c, hc, hbound⟩ := hlower t ht
  exact ⟨c, hc, Filter.Eventually.of_forall fun i v => hbound i x v⟩

end DifferentialGeometry.CheegerGromovCompactness
