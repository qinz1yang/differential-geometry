import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricContinuity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Spatial continuity and compact boundedness of the metric derivative norms

The two fixed-background derivative norms of the HCG compactness layer,

* `metricCovDerivNorm a h gRef z = |∇_{gRef}^a h|_{gRef}(z)` and
* `metricDerivNorm a gk gInf gRef z = |∇_{gRef}^a (gk − gInf)|_{gRef}(z)`,

are continuous in the base point `z` for FIXED smooth metrics, hence bounded on
every compact set.  The content is `Tensor0SBundle.normSq0S_cont` (spatial
continuity of the fibrewise tensor norm, `Tensor0SMetricContinuity.lean`)
applied to the smooth covariant-derivative tower `metricCovDeriv` (respectively
to the difference of two towers), composed with `Real.sqrt`.

This is the missing head/mid-range ingredient for the raw `hbdd` hypothesis of
`windowGInfAll` on a bump-extended metric sequence (P4 Brick 4): for the
finitely many indices below the tail threshold of a compact `K`, each
bump-extended metric is a single fixed smooth metric, and `metricCovDerivNorm_bddOn`
bounds its covariant norms on `K` with no transport or Leibniz analysis.

## Main results

* `metricCovDerivNorm_cont` / `metricDerivNorm_cont` — continuity in the base point.
* `metricCovDerivNorm_bddOn` — a bound on any compact set.
* `metricDerivNorm_bddOn` — a uniform bound over all orders `a ≤ p` on any compact set.
-/

noncomputable section

open Set Bundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- **Spatial continuity of the fixed-background covariant derivative norm.**
For fixed smooth metrics `h`, `gRef`, the function
`z ↦ |∇_{gRef}^a h|_{gRef}(z)` is continuous. -/
theorem metricCovDerivNorm_cont (a : Nat) (h gRef : SmoothRiemannianMetric I M) :
    Continuous (fun z : M => metricCovDerivNorm (I := I) a h gRef z) := by
  have hc := Tensor0SBundle.normSq0S_cont (I := I) (M := M) gRef
    (metricCovDeriv (I := I) h gRef a)
  change Continuous fun z : M =>
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (a + 2)
      (metricCovDeriv (I := I) h gRef a z))
  exact Real.continuous_sqrt.comp hc

/-- **Spatial continuity of the metric-difference derivative norm.**  For fixed
smooth metrics `gk`, `gInf`, `gRef`, the function
`z ↦ |∇_{gRef}^a (gk − gInf)|_{gRef}(z)` is continuous. -/
theorem metricDerivNorm_cont (a : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) :
    Continuous (fun z : M => metricDerivNorm (I := I) a gk gInf gRef z) := by
  have hc := Tensor0SBundle.normSq0S_cont (I := I) (M := M) gRef
    (metricCovDeriv (I := I) gk gRef a - metricCovDeriv (I := I) gInf gRef a)
  have heq : (fun z : M => Tensor0SBundle.normSq0S (I := I) gRef z (a + 2)
      ((metricCovDeriv (I := I) gk gRef a - metricCovDeriv (I := I) gInf gRef a) z)) =
      fun z : M => Tensor0SBundle.normSq0S (I := I) gRef z (a + 2)
        (metricDiffCovDerivAt (I := I) a gk gInf gRef z) := by
    funext z
    congr 1
  rw [heq] at hc
  change Continuous fun z : M =>
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z (a + 2)
      (metricDiffCovDerivAt (I := I) a gk gInf gRef z))
  exact Real.continuous_sqrt.comp hc

/-- **Compact boundedness of the fibrewise norm of a fixed smooth tensor
field**: on every compact `K` there is a nonnegative constant `C` with
`√(normSq0S gRef z s (A z)) ≤ C` for all `z ∈ K`.  This is the generic
ingredient bounding the covariant-derivative towers of a FIXED field (e.g. the
bump-cutoff `(0,0)`-field of a bump-extended metric sequence) on compacts. -/
theorem sqrtNormSq0S_bddOn {K : Set M} (hK : IsCompact K) (s : Nat)
    (gRef : SmoothRiemannianMetric I M)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    exists C : Real, 0 <= C /\ forall z, z ∈ K ->
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z s (A z)) <= C := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, le_refl 0, fun z hz => absurd hz (Set.notMem_empty z)⟩
  have hc : Continuous (fun z : M =>
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z s (A z))) :=
    Real.continuous_sqrt.comp (Tensor0SBundle.normSq0S_cont (I := I) gRef A)
  obtain ⟨z₀, _, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  refine ⟨max 0 (Real.sqrt (Tensor0SBundle.normSq0S (I := I) gRef z₀ s (A z₀))),
    le_max_left _ _, fun z hz => le_trans (hmax hz) (le_max_right _ _)⟩

/-- **Compact boundedness of the covariant derivative norm** for a fixed metric
pair: on every compact `K` there is a constant `C` with
`|∇_{gRef}^a h|_{gRef}(z) ≤ C` for all `z ∈ K`. -/
theorem metricCovDerivNorm_bddOn {K : Set M} (hK : IsCompact K)
    (a : Nat) (h gRef : SmoothRiemannianMetric I M) :
    exists C : Real, forall z, z ∈ K ->
      metricCovDerivNorm (I := I) a h gRef z <= C := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun z hz => absurd hz (Set.notMem_empty z)⟩
  obtain ⟨z₀, _, hmax⟩ := hK.exists_isMaxOn hne
    ((metricCovDerivNorm_cont (I := I) a h gRef).continuousOn)
  exact ⟨metricCovDerivNorm (I := I) a h gRef z₀, fun z hz => hmax hz⟩

/-- An eventual uniform covariant-derivative bound on a compact set extends across the finite
initial segment of a metric sequence. -/
theorem cov_bdd_of_eventual {K : Set M} (hK : IsCompact K)
    (a : ℕ) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M)
    (hevent : ∃ k₀ : ℕ, ∃ C : Real, ∀ k : ℕ, k₀ ≤ k → ∀ z ∈ K,
      metricCovDerivNorm (I := I) a (gSeq k) gRef z ≤ C) :
    ∃ C : Real, ∀ k : ℕ, ∀ z ∈ K,
      metricCovDerivNorm (I := I) a (gSeq k) gRef z ≤ C := by
  obtain ⟨k₀, Ctail, htail⟩ := hevent
  have hinit : ∀ n : ℕ, ∃ C : Real, ∀ k : ℕ, k < n → ∀ z ∈ K,
      metricCovDerivNorm (I := I) a (gSeq k) gRef z ≤ C := by
    intro n
    induction n with
    | zero => exact ⟨0, fun k hk => by omega⟩
    | succ n ih =>
      obtain ⟨Cn, hCn⟩ := ih
      obtain ⟨Ck, hCk⟩ := metricCovDerivNorm_bddOn (I := I) hK a (gSeq n) gRef
      refine ⟨max Cn Ck, fun k hk z hz => ?_⟩
      by_cases hkn : k < n
      · exact (hCn k hkn z hz).trans (le_max_left _ _)
      · have hkeq : k = n := by omega
        subst k
        exact (hCk z hz).trans (le_max_right _ _)
  obtain ⟨Cinit, hCinit⟩ := hinit k₀
  refine ⟨max Cinit Ctail, fun k z hz => ?_⟩
  by_cases hk : k < k₀
  · exact (hCinit k hk z hz).trans (le_max_left _ _)
  · exact (htail k (by omega) z hz).trans (le_max_right _ _)

/-- **Compact boundedness of the metric-difference derivative norm, uniformly in
the order `a ≤ p`**, for fixed metrics: the finitely many per-order sups on a
compact are dominated by one nonnegative constant. -/
theorem metricDerivNorm_bddOn {K : Set M} (hK : IsCompact K)
    (p : Nat) (gk gInf gRef : SmoothRiemannianMetric I M) :
    exists C : Real, 0 <= C /\ forall a : Nat, a <= p -> forall z, z ∈ K ->
      metricDerivNorm (I := I) a gk gInf gRef z <= C := by
  have h1 : forall a : Nat, exists C : Real, forall z, z ∈ K ->
      metricDerivNorm (I := I) a gk gInf gRef z <= C := by
    intro a
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun z hz => absurd hz (Set.notMem_empty z)⟩
    obtain ⟨z₀, _, hmax⟩ := hK.exists_isMaxOn hne
      ((metricDerivNorm_cont (I := I) a gk gInf gRef).continuousOn)
    exact ⟨metricDerivNorm (I := I) a gk gInf gRef z₀, fun z hz => hmax hz⟩
  choose Cf hCf using h1
  have hne0 : (Finset.range (p + 1)).Nonempty := ⟨0, Finset.mem_range.2 (Nat.succ_pos p)⟩
  refine ⟨max 0 ((Finset.range (p + 1)).sup' hne0 Cf), le_max_left 0 _,
    fun a ha z hz => ?_⟩
  refine le_trans (hCf a z hz) (le_trans ?_ (le_max_right 0 _))
  exact Finset.le_sup' Cf (Finset.mem_range.2 (Nat.lt_succ_of_le ha))

/-- Every pointwise derivative norm represented in the compact supremum is at most that
supremum. Compact boundedness supplies the `BddAbove` premise for `le_csSup`. -/
theorem derivNorm_le_sup {K : Set M} (hK : IsCompact K)
    {a p : ℕ} (hap : a ≤ p) (gk gInf gRef : SmoothRiemannianMetric I M)
    {x : M} (hx : x ∈ K) :
    metricDerivNorm (I := I) a gk gInf gRef x ≤
      metricDerivNormSupOn (I := I) K p gk gInf gRef := by
  obtain ⟨C, _, hC⟩ := metricDerivNorm_bddOn (I := I) hK p gk gInf gRef
  have hbdd : BddAbove {r : Real | ∃ q : ℕ, q ≤ p ∧ ∃ z : M, z ∈ K ∧
      metricDerivNorm (I := I) q gk gInf gRef z = r} := by
    refine ⟨C, ?_⟩
    rintro r ⟨q, hqp, z, hz, rfl⟩
    exact hC q hqp z hz
  exact le_csSup hbdd ⟨a, hap, x, hx, rfl⟩

end HCGCompactness
end DifferentialGeometry

end
