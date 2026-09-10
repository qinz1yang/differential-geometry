import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLocalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.Tail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TimeRegularity

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

local instance terminalCovariantC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
local instance terminalCovariantC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [SigmaCompactSpace M] in
theorem metric_covariant_bounds_of_local_curvature_bounds
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ico a b ⊆ D.regular)
    {U : Set M} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (gRef : SmoothRiemannianMetric I M) (C : ℕ → ℝ)
    (hcurv : ∀ m : ℕ, ∀ t ∈ Set.Ico a b, ∀ x ∈ U,
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤ C m)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ r : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Ico a b, ∀ x ∈ K,
      metricCovDerivNorm (I := I) r (S.base.metric t) gRef x ≤ B := by
  classical
  obtain ⟨L, hL, hmet⟩ := metricFamily_uniform_comparison_on_compact_carrier
    (fun t => S.base.metric t) hS.smoothMetric isCompact_Icc hslab gRef hUc
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have heq (t : ℝ) (ht : t ∈ Set.Ico a b) :
      MetricUniformEquivalentOn (I := I) U gRef (S.base.metric t) (L ^ 2) := by
    refine ⟨hL2, ?_⟩
    intro x hx v
    have hh := hmet t ⟨ht.1, ht.2.le⟩ x (subset_closure hx) v
    refine ⟨?_, hh.2⟩
    exact (inv_mul_le_iff₀ (zero_lt_one.trans_le hL2)).mpr hh.1
  let gSeq : ℕ → ℝ → SmoothRiemannianMetric I M := fun _ t => S.base.metric t
  have hequiv (ψ : ℝ) (hψ : ψ ∈ Set.Ico a b) :
      MetricUniformEquivalentOnWindow (I := I) U a ψ gRef gSeq (fun _ => L ^ 2) :=
    fun _ t ht => heq t ⟨ht.1, ht.2.trans_lt hψ.2⟩
  choose init hinit using fun q => metricCovDerivNorm_bddOn (I := I) hUc q
    (S.base.metric a) gRef
  have hev (ψ : ℝ) (hψ : ψ ∈ Set.Ico a b) (q : ℕ) :
      ∀ i : ℕ, ∀ x : M, ∀ s ∈ Set.Icc a ψ,
        ∀ v : Fin (q + 2) → TangentSpace I x,
          HasDerivAt (fun t => metricCovDeriv (I := I) (gSeq i t) gRef q x v)
            (((-2 : ℝ) • nablaRicReal (I := I) gSeq gRef q i s x) v) s := by
    exact hevComp_of_solutions (I := I) (β := a) (ψ := ψ) (N := q)
      (fun _ => D) (fun _ => S) (fun _ => hS) (fun _ _ => rfl)
      (fun _ t ht => hreg ⟨ht.1, ht.2.trans_lt hψ.2⟩)
      (fun _ p hp V x₀ => solutionTowerSwap_regularity (I := I) gRef S hS q
        (fun {_t} ht => D.regular_isOpen.mem_nhds ht) p hp V x₀)
  let A : ℕ → ℝ := fun q =>
    Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + q) + 2)) * max (C q) 0
  have hA0 (q : ℕ) : 0 ≤ A q := mul_nonneg (Real.sqrt_nonneg _) (le_max_right _ _)
  have hric (q : ℕ) (t : ℝ) (ht : t ∈ Set.Ico a b) (x : M) (hx : x ∈ U) :
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
        ((hcurv q t ht x hx).trans (le_max_left _ _)) (Real.sqrt_nonneg _)
  intro r
  by_cases hr : r = 0
  · subst r
    refine ⟨L ^ 2 * Real.sqrt (Module.finrank ℝ E : ℝ), by positivity, ?_⟩
    intro t ht x hx
    exact covOrder_zero_le (S.base.metric t) gRef (heq t ht) x (hKU hx)
  let KShi := ∑ q ∈ Finset.range (r + 1), A q
  have hKShi : 0 ≤ KShi := Finset.sum_nonneg fun q _ => hA0 q
  have hShi (ψ : ℝ) (hψ : ψ ∈ Set.Ico a b) :
      MovingShiBoundOn (I := I) U a ψ gSeq r KShi := by
    intro q hq _ t ht x hx
    exact (hric q t ⟨ht.1, ht.2.trans_lt hψ.2⟩ x hx).trans
      (Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_range.mpr (by omega)))
  obtain ⟨B, hB⟩ := covOrder_Ico_tail (I := I) hK hU hKU r (L ^ 2) hL2
    KShi hKShi (fun q => max (init q) 0) (fun q => le_max_right _ _)
    (b - a) (fun _ => L ^ 2) hequiv (fun _ _ => le_rfl) hShi
    (fun ψ hψ q _ _ i x _ => hev ψ hψ q i x)
    (fun q _ _ _ x hx => (hinit q x (subset_closure hx)).trans (le_max_left _ _))
    (fun t ht => by rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]; linarith [ht.2])
    r (by omega) le_rfl
  exact ⟨max B 0, le_max_right _ _, fun t ht x hx =>
    (hB 0 t ht x hx).trans (le_max_left _ _)⟩

theorem exists_local_metric_covariant_bounds_before_terminal
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (p : M) :
    ∃ (U : Set M) (c : ℝ) (C : ℕ → ℝ), IsOpen U ∧ p ∈ U ∧
      IsCompact (closure U) ∧ a < c ∧ c < b ∧ (∀ r, 0 ≤ C r) ∧
      ∀ r : ℕ, ∀ t ∈ Set.Ico c b, ∀ x ∈ closure U,
        metricCovDerivNorm (I := I) r (S.base.metric t) (S.base.metric c) x ≤ C r := by
  classical
  obtain ⟨V, d, C₀, hV, hpV, hVc, had, hdb, hcurv⟩ :=
    exists_local_curvature_derivative_bounds_before_terminal S hS hab hslab hreg p
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨K, hK, hpK, hKV⟩ := exists_compact_between isCompact_singleton hV
    (Set.singleton_subset_iff.mpr hpV)
  let c := (d + b) / 2
  have hdc : d < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hbound := metric_covariant_bounds_of_local_curvature_bounds S hS
    (a := c) (b := b) (fun t ht => hslab ⟨had.le.trans (hdc.le.trans ht.1), ht.2⟩)
    (fun t ht => hreg ⟨had.trans (hdc.trans_le ht.1), ht.2⟩)
    hV hVc (S.base.metric c) C₀
    (fun m t ht x hx => hcurv m t ⟨hdc.trans_le ht.1, ht.2⟩ x hx) hK hKV
  choose C hC0 hC using hbound
  have hclosure : closure (interior K) ⊆ K :=
    closure_minimal interior_subset hK.isClosed
  exact ⟨interior K, c, C, isOpen_interior, hpK (Set.mem_singleton p),
    hK.of_isClosed_subset isClosed_closure hclosure, had.trans hdc, hcb, hC0,
    fun r t ht x hx => hC r t ht x (hclosure hx)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
