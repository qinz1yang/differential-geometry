import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialMetricJetBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedMetricLipschitz
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TimeRegularity

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [CompleteSpace E] [I.Boundaryless] in
private theorem reference_ricci_zero_bound {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (gRef : SmoothRiemannianMetric I M)
    (t Λ κ : ℝ) (hΛ : 1 ≤ Λ)
    (he : MetricUniformEquivalentOn univ gRef (S.base.metric t) Λ)
    (x : M)
    (hRic : Real.sqrt (normSq0S (S.base.metric t) x 2
      (ricCovTower (S.base.metric t) (S.base.metric t) 0 x)) ≤ κ) :
    Real.sqrt (normSq0S gRef x 2
      (nablaRicReal (fun _ s => S.base.metric s) gRef 0 0 t x)) ≤ Λ * κ := by
  have hh := sqrt_normSq0S_le_of_metric_equiv (g := S.base.metric t) (h := gRef) x 2 hΛ
    (fun v => (metricUniformEquivalentOn_symm he).2 x (mem_univ x) v)
    (nablaRicReal (fun _ s => S.base.metric s) gRef 0 0 t x)
  rw [Real.sqrt_sq (le_trans (by norm_num : (0 : ℝ) ≤ 1) hΛ)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hRic (le_trans (by norm_num) hΛ))

private theorem reference_metric_interior_evolution {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (gRef : SmoothRiemannianMetric I M) (a : ℕ) {s : ℝ} (hs : s ∈ D.regular)
    (x : M) (v : Fin (a + 2) → TangentSpace I x) :
    HasDerivAt (fun r => metricCovDeriv (S.base.metric r) gRef a x v)
      (((-2 : ℝ) • nablaRicReal (fun _ t => S.base.metric t) gRef a 0 s x) v) s := by
  have hwin : ∀ _i : ℕ, Icc s s ⊆ D.regular := by
    intro _ r hr
    have he : r = s := le_antisymm hr.2 hr.1
    exact he ▸ hs
  exact hevComp_of_solutions (I := I) (N := a) (gRef := gRef)
    (fun _ => D) (fun _ => S) (fun _ => hS) (fun _ _ => rfl) hwin
    (fun _ => solutionTowerSwap_regularity gRef S hS a (fun {t} ht => D.regular_isOpen.mem_nhds ht))
    0 x s ⟨le_rfl, le_rfl⟩ v

theorem exists_uniform_closed_initial_metric_time_bounds {D : RealTimeInterval}
    (T : ℝ) (hT : 0 ≤ T) (hreg : Ioo 0 T ⊆ D.regular)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (κ : ℕ → ℝ) (hκ : ∀ N, 0 ≤ κ N) :
    ∃ C L : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ S : SolutionOn (I := I) (M := M) D, IsSolutionOn S →
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
            (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
        (∀ t ∈ Icc 0 T,
          MetricUniformEquivalentOn univ (S.base.metric 0) (S.base.metric t) Λ) →
        (∀ N : ℕ, MovingShiBoundOn univ 0 T (fun _ t => S.base.metric t) N (κ N)) →
        (∀ N : ℕ, ∀ t ∈ Icc 0 T, ∀ x : M,
          metricCovDerivNorm N (S.base.metric t) (S.base.metric 0) x ≤ C N) ∧
        ∀ N : ℕ, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x : M,
          metricDerivNorm N (S.base.metric s) (S.base.metric t) (S.base.metric 0) x ≤ L N * |s - t| := by
  obtain ⟨C, hC, hCbound⟩ := exists_uniform_closed_initial_metric_bounds
    (I := I) (M := M) T hT hreg Λ hΛ κ hκ
  let cf := fun N => ricTowerCoeffs (Module.finrank ℝ E) N Λ C (κ N)
  let L := fun N => if N = 0 then 2 * Λ * κ 0 else 2 * ((cf N).slope * C N + (cf N).offset)
  have hL (N : ℕ) : 0 ≤ L N := by
    by_cases hN : N = 0
    · simp only [L, ite_eq_left hN]
      exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) hΛ)) (hκ 0)
    · have hc := ricCoeffs_nonneg (Module.finrank ℝ E) N Λ C (κ N) hΛ (hκ N)
      simp only [L, ite_eq_right hN]
      exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hc.1 (hC N)) hc.2)
  refine ⟨C, L, hC, hL, ?_⟩
  intro S hS hgram hequiv hShi
  have hnorm := hCbound S hS hgram hequiv hShi
  refine ⟨hnorm, ?_⟩
  intro N s hs t ht x
  let Ev := fun r (y : M) => (-2 : ℝ) •
    nablaRicReal (fun _ u => S.base.metric u) (S.base.metric 0) N 0 r y
  have hev : ∀ y ∈ (univ : Set M), ∀ r ∈ Ioo 0 T, ∀ v : Fin (N + 2) → TangentSpace I y,
      HasDerivAt (fun u => metricCovDeriv (S.base.metric u) (S.base.metric 0) N y v) (Ev r y v) r :=
    fun y _ r hr v => reference_metric_interior_evolution S hS (S.base.metric 0) N (hreg hr) y v
  have hEv : ∀ y ∈ (univ : Set M), ∀ r ∈ Ioo 0 T,
      Real.sqrt (normSq0S (S.base.metric 0) y (N + 2) (Ev r y)) ≤ L N := by
    intro y _ r hr
    have hrc : r ∈ Icc 0 T := Ioo_subset_Icc_self hr
    dsimp only [Ev]
    rw [sqrt_normSq0S_smul, show |(-2 : ℝ)| = 2 by norm_num]
    by_cases hN : N = 0
    · subst N
      simp only [L, ite_eq_left rfl]
      have hh := reference_ricci_zero_bound S (S.base.metric 0) r Λ (κ 0) hΛ (hequiv r hrc) y
        (hShi 0 0 le_rfl 0 r hrc y (mem_univ y))
      nlinarith
    · have hc := ricCoeffs_nonneg (Module.finrank ℝ E) N Λ C (κ N) hΛ (hκ N)
      have hh := ric_bound_field_on (I := I) (gSeq := fun _ u => S.base.metric u)
        (gRef := S.base.metric 0) isOpen_univ N (Nat.one_le_iff_ne_zero.mpr hN) Λ hΛ
        (fun _ => hequiv) C (fun a _ _ _ u hu z _ => hnorm a u hu z) (κ N) (hκ N) (hShi N)
        0 r hrc y (mem_univ y)
      have hh' := hh.trans (add_le_add
        (mul_le_mul_of_nonneg_left (hnorm N r hrc y) hc.1) le_rfl)
      simp only [L, ite_eq_right hN]
      exact mul_le_mul_of_nonneg_left hh' (by norm_num)
  exact metricDerivNorm_le_of_closed_evolution S.base.metric 0 T hgram (S.base.metric 0)
    N Ev univ (L N) (hL N) hev hEv s hs t ht x (mem_univ x)
end DifferentialGeometry.PDE.RicciFlow
