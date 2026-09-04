import DifferentialGeometry.Analysis.Integration.Measure.Differentiation.Rademacher
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.ConjugateMeasureZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MultipleMinimizers
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.LocalCostBranch

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem lCutMulti_null
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      (lCutMulti S T x tau) = 0 := by
  classical
  rcases (lCutMulti S T x tau).eq_empty_or_nonempty with hempty | hmulti
  · rw [hempty, measure_empty]
  · rcases hmulti with ⟨y₀, hy₀⟩
    rcases hy₀ with ⟨Z₀, hZ₀cut, _⟩
    have hZ₀min : (Z₀, tau) ∈ lMinDomain S T x :=
      ((mem_lCutDomain S T x tau Z₀).1 hZ₀cut).1
    have htau : 0 < tau :=
      lMinDomain_pos S T x Z₀ tau hZ₀min
    have hZ₀dom : (Z₀, tau) ∈ lExpPosDom S T x :=
      ((mem_lMinDomain S T x Z₀ tau).1 hZ₀min).1
    have hslab : Icc (T - tau) T ⊆ D.regular := by
      intro r hr
      have hnonneg : 0 ≤ T - r := by
        linarith [hr.2]
      have hle : T - r ≤ tau := by
        linarith [hr.1]
      have hsqrt :
          Real.sqrt (T - r) ∈ Icc (0 : Real) (Real.sqrt tau) :=
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hle⟩
      have hreg :=
        lExpPosDom_reg S T x Z₀ hZ₀dom hsqrt
      have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
        rw [Real.sq_sqrt hnonneg]
        ring
      simpa only [heq] using hreg
    have hdiff₀ :
        riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | ¬ MDifferentiableAt I (modelWithCornersSelf Real Real)
            (fun z : M ↦ lCost S T x z tau) y} = 0 :=
      nondiff_null (I := I) (M := M) g
        (fun z : M ↦ lCost S T x z tau)
        (fun p ↦ lCost_chart_lip (I := I) S hS T x tau htau hslab p)
    refine measure_mono_null ?_
      (measure_union_null (lCutConj_null S hS T x tau g) hdiff₀)
    rintro y ⟨Z, hZcut, W, hWne, hWmin, hend, rfl⟩
    have hZmin : (Z, tau) ∈ lMinDomain S T x :=
      ((mem_lCutDomain S T x tau Z).1 hZcut).1
    have hWcut : (W : E) ∈ lCutDomain S T x tau :=
      lCut_other S hS T x hZcut hWne hWmin hend
    by_cases hZconj : IsLConj S T x Z tau
    · exact Or.inl ⟨Z, hZcut, hZconj, rfl⟩
    by_cases hWconj : IsLConj S T x W tau
    · exact Or.inl ⟨W, hWcut, hWconj, hend⟩
    · exact Or.inr <|
        lCost_nondiff_two (I := I) S hS T x
          hZmin hWmin hZconj hWconj hWne.symm hend.symm

theorem lCut_null
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (g : SmoothRiemannianMetric I M) :
    riemannianVolumeMeasure (I := I) (M := M) g
      (lCutImage S T x tau) = 0 := by
  rw [lCut_split S hS T x tau]
  exact measure_union_null
    (lCutConj_null S hS T x tau g)
    (lCutMulti_null S hS T x tau g)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
