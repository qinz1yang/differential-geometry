import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.WithinTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.UniformTensorNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CompactPointedChartControl

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

theorem metric_time_jet_errors_uniform_on_compacts_of_closed_interval {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := I) (M := M) D) (hS : ∀ n, IsSolutionOn (S n))
    (S₀ : SolutionOn (I := I) (M := M) D) (hS₀ : IsSolutionOn S₀)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular)
    (R : SmoothRiemannianMetric I M)
    (hconv : ∀ K : Set M, IsCompact K → ∀ r : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc c b,
        metricDerivNormSupOn K r ((S n).base.metric t) (S₀.base.metric t) R < epsilon)
    (B : ℕ → ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (C : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hBzero : ∀ n s, B n 0 s = metricTensorField ((S n).base.metric s))
    (hCzero : ∀ s, C 0 s = metricTensorField (S₀.base.metric s))
    (hB : ∀ n q s, s ∈ Icc c b → ∀ x : M,
      HasDerivWithinAt (fun t => B n q t x) (B n (q + 1) s x) (Icc c b) s)
    (hC : ∀ q s, s ∈ Icc c b → ∀ x : M,
      HasDerivWithinAt (fun t => C q t x) (C (q + 1) s x) (Icc c b) s)
    {K : Set M} (hK : IsCompact K) (r q : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc c b, ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I) r (B n q t - C q t)
        (S₀.base.metric t) (S₀.base.metric t) x ≤ ε := by
  let F : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2 :=
    fun n t => B n q t - C q t
  apply uniform_on_compact_of_restricted_chart_bounds (I := I) (⊤ : TopologicalSpace.Opens M)
    hK (fun _ _ => mem_univ _)
    (fun n t x => tensor02CovDerivNormWith (I := I) r (F n t)
      (S₀.base.metric t) (S₀.base.metric t) x) (Icc c b)
  intro p Q hQ hQt
  have hU := isOpen_extChartAt_target (I := I) p
  have hUt := extChartAt_opens_target_subset (I := I) (⊤ : TopologicalSpace.Opens M) p
  have hBactual (n q : ℕ) (t : ℝ) (ht : t ∈ Icc c b) (x : M) :
      B n q t x = iteratedDerivWithin q (fun s => metricTensorField ((S n).base.metric s) x)
        (Icc c b) t := by
    apply (DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt
      (uniqueDiffOn_Icc hcb) _ (fun k s => B n k s x)
      (fun k s hs => hB n k s hs x) _ q ht).symm
    intro s _hs
    simp only [hBzero]
  have hCactual (q : ℕ) (t : ℝ) (ht : t ∈ Icc c b) (x : M) :
      C q t x = iteratedDerivWithin q (fun s => metricTensorField (S₀.base.metric s) x)
        (Icc c b) t := by
    apply (DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt
      (uniqueDiffOn_Icc hcb) _ (fun k s => C k s x)
      (fun k s hs => hC k s hs x) _ q ht).symm
    intro s _hs
    simp only [hCzero]
  have hcoord (slots : Fin 2 → Fin (Module.finrank ℝ E))
      (Q' : Set E) (hQ' : IsCompact Q') (hQ't : Q' ⊆ (extChartAt I p).target)
      (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc c b, ∀ y ∈ Q',
        ‖iteratedFDeriv ℝ m (fun z => F n t ((extChartAt I (p : M)).symm z)
          (fun j => chartBasisVecFiber (I := I) (p : M) (slots j)
            ((extChartAt I (p : M)).symm z))) y‖ ≤ ε := by
    obtain ⟨N, hN⟩ := uniform_ordinary_metric_jets_of_metric_convergence_on_closed_interval
      S hS S₀ hS₀ hac hcb hcarrier hregular isCompact_Icc Subset.rfl
      (p : M) hU hUt R hconv hQ' hQ't m q slots ε hε
    refine ⟨N, fun n hn t ht y hy => ?_⟩
    have hBc := tensor_field_chart_components_contDiffOn (B n q t) (p : M) hUt slots
    have hCc := tensor_field_chart_components_contDiffOn (C q t) (p : M) hUt slots
    have hsub := iteratedFDeriv_sub_apply (i := m)
      ((hBc.contDiffAt (hU.mem_nhds (hQ't hy))).of_le (by exact_mod_cast le_top))
      ((hCc.contDiffAt (hU.mem_nhds (hQ't hy))).of_le (by exact_mod_cast le_top))
    have hh := hN n hn t ht y hy
    simp_rw [← hBactual n q t ht, ← hCactual q t ht] at hh
    rw [← hsub] at hh
    exact hh
  exact uniform_tensor02_covariant_norm_on_compact_time_of_closed_interval S₀ hS₀
    hac hcb (by rw [hcarrier]) hregular isCompact_Icc Subset.rfl
    F (p : M) hU hUt hcoord hQ hQt r

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
