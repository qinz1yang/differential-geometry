import DifferentialGeometry.Geometry.Measure.ManifoldRademacher
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostChartLipComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.BranchUpper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Conjugate.MeasureZero

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem lCost_nondiff_null_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | ¬ MDifferentiableAt I (modelWithCornersSelf ℝ ℝ)
        (fun z : M ↦ lCost S T x z tau) y} = 0 := by
  apply DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null
    (I := I) g (fun z : M ↦ lCost S T x z tau)
  intro p
  exact lCost_chart_lip_of_rm (I := I) S hS K T hg x tau
    htau hreg hRm p

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
theorem lMinimizingVector_nonunique_image_null_on_of_locallyLipschitz
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M) (tau : ℝ)
    {U : Set M} (hU : IsOpen U)
    (hlip : ∀ p : M, LocallyLipschitzOn ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' U)
      ((fun y : M => lCost S T x y tau) ∘ (extChartAt I p).symm))
    (hbdd : ∀ Z : TangentSpace I x, (Z, tau) ∈ lMinDomain S T x → lExp S T x Z tau ∈ U →
      ∀ᶠ y in nhds (lExp S T x Z tau),
        BddBelow {r : ℝ | ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧
          γ (Real.sqrt tau) = y ∧ lRegularizedAction S T γ 0 (Real.sqrt tau) = r})
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | y ∈ U ∧ ∃ Z W : TangentSpace I x, Z ≠ W ∧ (Z, tau) ∈ lMinDomain S T x ∧
        (W, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau = y ∧ lExp S T x W tau = y} = 0 := by
  refine measure_mono_null ?_
    (measure_union_null
      (DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null_on g
        (fun y : M => lCost S T x y tau) hU hlip)
      (lConjugateImage_null S hS T x tau g))
  rintro y ⟨hyU, Z, W, hZW, hZ, hW, hZy, hWy⟩
  by_cases hZconj : IsLConjugate S T x Z tau
  · exact Or.inr ⟨Z, hZconj, hZy⟩
  by_cases hWconj : IsLConjugate S T x W tau
  · exact Or.inr ⟨W, hWconj, hWy⟩
  · have hn := lCost_nondiff_two_of_bdd S hS T x hZ hW hZconj hWconj hZW
      (hZy.trans hWy.symm) (hbdd Z hZ (hZy.symm ▸ hyU))
    exact Or.inl ⟨hyU, hZy ▸ hn⟩

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] in
theorem lMinimizingVector_nonunique_image_null_of_locallyLipschitz
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M) (tau : ℝ)
    (hlip : ∀ p : M, LocallyLipschitzOn (extChartAt I p).target
      ((fun y : M => lCost S T x y tau) ∘ (extChartAt I p).symm))
    (hbdd : ∀ Z : TangentSpace I x, (Z, tau) ∈ lMinDomain S T x →
      ∀ᶠ y in nhds (lExp S T x Z tau),
        BddBelow {r : ℝ | ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧
          γ (Real.sqrt tau) = y ∧ lRegularizedAction S T γ 0 (Real.sqrt tau) = r})
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {y : M | ∃ Z W : TangentSpace I x, Z ≠ W ∧ (Z, tau) ∈ lMinDomain S T x ∧
        (W, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau = y ∧ lExp S T x W tau = y} = 0 := by
  have hn := lMinimizingVector_nonunique_image_null_on_of_locallyLipschitz S hS T x tau
    (U := univ) isOpen_univ (by simpa only [preimage_univ, inter_univ] using hlip)
    (fun Z hZ _ => hbdd Z hZ) g
  simpa only [mem_univ, true_and] using hn

theorem lCutMulti_null_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      (lCutMulti S T x tau) = 0 := by
  apply measure_mono_null ?_
    (lMinimizingVector_nonunique_image_null_of_locallyLipschitz S hS T x tau
      (fun p => lCost_chart_lip_of_rm S hS K T hg x tau htau hreg hRm p) ?_ g)
  · rintro y ⟨Z, hZcut, W, hWne, hWmin, hend, rfl⟩
    exact ⟨Z, W, hWne.symm, ((mem_lCutDomain S T x tau Z).mp hZcut).1, hWmin, rfl, hend⟩
  · intro Z _
    exact Filter.Eventually.of_forall (fun y =>
      lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (Real.sqrt tau) le_rfl (Real.sqrt_nonneg tau)
        (by simpa only [Real.sq_sqrt htau.le] using hreg)
        (by simpa only [Real.sq_sqrt htau.le] using hRm) x y)

end DifferentialGeometry.PDE.RicciFlow

end
