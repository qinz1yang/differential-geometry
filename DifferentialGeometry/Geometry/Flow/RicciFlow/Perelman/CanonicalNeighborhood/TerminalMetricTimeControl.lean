import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCovariantBounds
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

local instance terminalMetricTimeC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
local instance terminalMetricTimeC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [SigmaCompactSpace M] in
theorem metric_time_lipschitz_of_local_bounds
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hreg : Set.Ico a b ⊆ D.regular)
    {U K : Set M} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (gRef : SmoothRiemannianMetric I M) {B : ℝ} (hB : 1 ≤ B)
    (heq : ∀ t ∈ Set.Ico a b,
      MetricUniformEquivalentOn (I := I) U gRef (S.base.metric t) B)
    (N : ℕ) (C : ℕ → ℝ)
    (hC : ∀ q ≤ N, ∀ t ∈ Set.Ico a b, ∀ x ∈ U,
      metricCovDerivNorm (I := I) q (S.base.metric t) gRef x ≤ C q)
    {KShi : ℝ} (hKShi : 0 ≤ KShi)
    (hShi : ∀ ψ ∈ Set.Ico a b,
      MovingShiBoundOn (I := I) U a ψ (fun _ t => S.base.metric t) N KShi) :
    ∀ q ≤ N, ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Set.Ico a b, ∀ t ∈ Set.Ico a b,
      ∀ x ∈ K, metricDerivNorm (I := I) q (S.base.metric s) (S.base.metric t) gRef x
        ≤ L * |s - t| := by
  let gSeq : ℕ → ℝ → SmoothRiemannianMetric I M := fun _ t => S.base.metric t
  intro q hq
  have hev (ψ : ℝ) (hψ : ψ ∈ Set.Ico a b) :
      ∀ x : M, ∀ r ∈ Set.Icc a ψ, ∀ v : Fin (q + 2) → TangentSpace I x,
        HasDerivAt (fun t => metricCovDeriv (I := I) (S.base.metric t) gRef q x v)
          (((-2 : ℝ) • nablaRicReal (I := I) gSeq gRef q 0 r x) v) r := by
    exact (hevComp_of_solutions (I := I) (β := a) (ψ := ψ) (N := q)
      (fun _ => D) (fun _ => S) (fun _ => hS) (fun _ _ => rfl)
      (fun _ t ht => hreg ⟨ht.1, ht.2.trans_lt hψ.2⟩)
      (fun _ p hp V x₀ => solutionTowerSwap_regularity (I := I) gRef S hS q
        (fun {_t} ht => D.regular_isOpen.mem_nhds ht) p hp V x₀)) 0
  have hric : ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Set.Ico a b, ∀ x ∈ K,
      Real.sqrt (normSq0S (I := I) gRef x (q + 2)
        ((-2 : ℝ) • nablaRicReal (I := I) gSeq gRef q 0 t x)) ≤ L := by
    by_cases hzero : q = 0
    · subst q
      refine ⟨2 * (Real.sqrt (B ^ 2) * KShi), by positivity, ?_⟩
      intro t ht x hx
      have hsym := metricUniformEquivalentOn_symm (I := I) (heq t ht)
      have hcomp := sqrt_normSq0S_le_of_metric_equiv (I := I)
        (g := S.base.metric t) (h := gRef) x 2 hB
        (fun v => hsym.2 x (hKU hx) v)
        (ricCovTower (I := I) (S.base.metric t) gRef 0 x)
      have hmove := hShi t ht 0 (Nat.zero_le N) 0 t ⟨ht.1, le_rfl⟩ x (hKU hx)
      rw [sqrt_normSq0S_smul, nablaRicReal_normSq]
      norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left
        (hcomp.trans (mul_le_mul_of_nonneg_left hmove (Real.sqrt_nonneg _))) (by norm_num)
    · obtain ⟨A, B₀, hA, hB₀, hbound⟩ := ric_bound_const (I := I)
        hK hU hKU q (by omega) B hB C KShi hKShi
      refine ⟨2 * (A * max (C q) 0 + B₀), by positivity, ?_⟩
      intro t ht x hx
      have hb := hbound (β := a) (ψ := t) (gSeq := gSeq) (fun _ => B)
        (fun _ r hr => heq r ⟨hr.1, hr.2.trans_lt ht.2⟩)
        (fun _ _ => le_rfl)
        (fun r _ hr _ s hs y hy => hC r (by omega) s
          ⟨hs.1, hs.2.trans_lt ht.2⟩ y hy)
        (fun r hr => hShi t ht r (hr.trans hq)) 0 t ⟨ht.1, le_rfl⟩ x hx
      rw [sqrt_normSq0S_smul]
      norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left
        (hb.trans (add_le_add (mul_le_mul_of_nonneg_left
          ((hC q hq t ht x (hKU hx)).trans (le_max_left _ _)) hA) le_rfl)) (by norm_num)
  obtain ⟨L, hL, hric⟩ := hric
  refine ⟨L, hL, ?_⟩
  intro s hs t ht x hx
  let ψ := max s t
  have hψ : ψ ∈ Set.Ico a b :=
    ⟨hs.1.trans (le_max_left _ _), max_lt hs.2 ht.2⟩
  exact timeLipschitz_of_hasDerivAt (I := I) gRef q (fun r => S.base.metric r)
    (fun r y => (-2 : ℝ) • nablaRicReal (I := I) gSeq gRef q 0 r y) K a ψ L
    (fun y _ r hr => hev ψ hψ y r hr)
    (fun y hy r hr => hric r ⟨hr.1, hr.2.trans_lt hψ.2⟩ y hy)
    s ⟨hs.1, le_max_left _ _⟩ t ⟨ht.1, le_max_right _ _⟩ x hx

theorem exists_local_metric_time_lipschitz_before_terminal
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (p : M) :
    ∃ (U : Set M) (c : ℝ) (L : ℕ → ℝ), IsOpen U ∧ p ∈ U ∧
      IsCompact (closure U) ∧ a < c ∧ c < b ∧ (∀ q, 0 ≤ L q) ∧
      ∀ q : ℕ, ∀ s ∈ Set.Ico c b, ∀ t ∈ Set.Ico c b, ∀ x ∈ closure U,
        metricDerivNorm (I := I) q (S.base.metric s) (S.base.metric t) (S.base.metric c) x
          ≤ L q * |s - t| := by
  classical
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨V, d, C₀, hV, hpV, hVc, had, hdb, hcurv⟩ :=
    exists_local_curvature_derivative_bounds_before_terminal S hS hab hslab hreg p
  obtain ⟨K₁, hK₁, hpK₁, hK₁V⟩ := exists_compact_between isCompact_singleton hV
    (Set.singleton_subset_iff.mpr hpV)
  obtain ⟨K₂, hK₂, hpK₂, hK₂₁⟩ := exists_compact_between isCompact_singleton
    isOpen_interior hpK₁
  let c := (d + b) / 2
  have hdc : d < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hcbslab : Set.Icc c b ⊆ D.carrier :=
    fun t ht => hslab ⟨had.le.trans (hdc.le.trans ht.1), ht.2⟩
  have hcbreg : Set.Ico c b ⊆ D.regular :=
    fun t ht => hreg ⟨had.trans (hdc.trans_le ht.1), ht.2⟩
  have hbound := metric_covariant_bounds_of_local_curvature_bounds S hS hcbslab hcbreg
    hV hVc (S.base.metric c) C₀
    (fun m t ht x hx => hcurv m t ⟨hdc.trans_le ht.1, ht.2⟩ x hx) hK₁ hK₁V
  choose C _hC0 hC using hbound
  obtain ⟨B, hB, hmet⟩ := metricFamily_uniform_comparison_on_compact_carrier
    (fun t => S.base.metric t) hS.smoothMetric isCompact_Icc hcbslab (S.base.metric c) hK₁
  have hB2 : 1 ≤ B ^ 2 := by nlinarith
  have heq (t : ℝ) (ht : t ∈ Set.Ico c b) :
      MetricUniformEquivalentOn (I := I) (interior K₁) (S.base.metric c)
        (S.base.metric t) (B ^ 2) := by
    refine ⟨hB2, ?_⟩
    intro x hx v
    have hh := hmet t ⟨ht.1, ht.2.le⟩ x (interior_subset hx) v
    exact ⟨(inv_mul_le_iff₀ (zero_lt_one.trans_le hB2)).mpr hh.1, hh.2⟩
  let A : ℕ → ℝ := fun q =>
    Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + q) + 2)) * max (C₀ q) 0
  have hA0 (q : ℕ) : 0 ≤ A q := mul_nonneg (Real.sqrt_nonneg _) (le_max_right _ _)
  have hric (q : ℕ) (t : ℝ) (ht : t ∈ Set.Ico c b) (x : M) (hx : x ∈ interior K₁) :
      Real.sqrt (normSq0S (I := I) (S.base.metric t) x (2 + q)
        (ricCovTower (I := I) (S.base.metric t) (S.base.metric t) q x)) ≤ A q := by
    calc
      _ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + q) + 2) *
          normSq0S (I := I) (S.base.metric t) x (4 + q)
            (nablaKRm04Field (I := I) S t q x)) :=
        Real.sqrt_le_sqrt (ricTower_normSq_le S t q x)
      _ = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + q) + 2)) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S q t x) := by
        rw [Real.sqrt_mul (by positivity)]
        rfl
      _ ≤ A q := mul_le_mul_of_nonneg_left
        ((hcurv q t ⟨hdc.trans_le ht.1, ht.2⟩ x (hK₁V (interior_subset hx))).trans
          (le_max_left _ _)) (Real.sqrt_nonneg _)
  have hlip (q : ℕ) : ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Set.Ico c b, ∀ t ∈ Set.Ico c b,
      ∀ x ∈ K₂, metricDerivNorm (I := I) q (S.base.metric s) (S.base.metric t)
        (S.base.metric c) x ≤ L * |s - t| := by
    let KShi := ∑ r ∈ Finset.range (q + 1), A r
    apply metric_time_lipschitz_of_local_bounds S hS hcbreg isOpen_interior hK₂ hK₂₁
      (S.base.metric c) hB2 heq q C
      (fun r _ t ht x hx => hC r t ht x (interior_subset hx))
      (KShi := KShi) (Finset.sum_nonneg fun r _ => hA0 r) ?_ q le_rfl
    intro ψ hψ r hr _ t ht x hx
    exact (hric r t ⟨ht.1, ht.2.trans_lt hψ.2⟩ x hx).trans
      (Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_range.mpr (by omega)))
  choose L hL hLip using hlip
  have hclosure : closure (interior K₂) ⊆ K₂ :=
    closure_minimal interior_subset hK₂.isClosed
  exact ⟨interior K₂, c, L, isOpen_interior, hpK₂ (Set.mem_singleton p),
    hK₂.of_isClosed_subset isClosed_closure hclosure, had.trans hdc, hcb, hL,
    fun q s hs t ht x hx => hLip q s hs t ht x (hclosure hx)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
