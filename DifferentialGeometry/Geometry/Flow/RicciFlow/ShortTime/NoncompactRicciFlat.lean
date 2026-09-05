import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [BoundarylessManifold I M] [I.Boundaryless]
variable [T2Space M] [SigmaCompactSpace M]

def complete_bounded_curvature_solution_of_joint_ricci_flow
    {a b : Real} (hab : a < b)
    (g : Real → SmoothRiemannianMetric I M)
    (hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico a b ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hpde : ∀ t ∈ Set.Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g t) x v w)
        (Set.Ici a) t)
    (hcomplete : ∀ t ∈ Set.Ico a b,
      RiemannianMetricComplete (I := I) (g t))
    (hcurv : ∀ t ∈ Set.Ico a b, ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
      normSq0S (I := I) (g t) x 4 (metricRm04At (I := I) (g t) x) ≤ C) :
    CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
      (D := RealTimeInterval.closedOpen a b hab) := by
  have hsol : IsSolutionOn (I := I)
      ({ base := { metric := g } } :
        SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a b hab)) :=
    solutionOn_of_joint (I := I) (M := M) hab g hjoint hpde
  refine
    { solution := { base := { metric := g } }
      isSolution := hsol
      complete := ?_
      curvatureBound := ?_ }
  · intro t ht
    exact hcomplete t ht
  · intro t ht
    exact hcurv t ht

theorem ricci_flow_short_time_existence_of_ricci_flat
    (g₀ : SmoothRiemannianMetric I M)
    (hnoncompact : NoncompactSpace M)
    (hcomplete : RiemannianMetricComplete (I := I) g₀)
    (hRicci : ∀ (x : M) (v w : TangentSpace I x),
      ricciTensor (I := I) g₀ x v w = 0)
    (hcurv : ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
      normSq0S (I := I) g₀ x 4 (metricRm04At (I := I) g₀ x) ≤ C) :
    ∃ (T : Real) (hT : 0 < T),
      ∃ S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen 0 T hT),
        S.solution.base.metric 0 = g₀ := by
  let _ := hnoncompact.noncompact_univ
  let g : Real → SmoothRiemannianMetric I M := fun _ => g₀
  have hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          Integral.Measure.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico (0 : Real) 1 ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hcomp :=
      (Integral.Measure.chartGramMatrix_entry_contMDiffOn
        (I := I) g₀ x₀ i j).comp
      (contMDiffOn_snd (I := 𝓘(Real, Real)) (J := I)
        (n := (∞ : WithTop ℕ∞))
        (s := Set.Ico (0 : Real) 1 ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet))
      (fun p hp => hp.2)
    exact hcomp.congr (by intro p hp; rfl)
  have hpde : ∀ t ∈ Set.Ico (0 : Real) 1, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s : Real => (g s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (g t) x v w)
        (Set.Ici 0) t := by
    intro t ht x v w
    have hconst : HasDerivWithinAt (fun _ : Real => g₀.inner x v w) 0
        (Set.Ici 0) t :=
      hasDerivWithinAt_const t (Set.Ici 0) (g₀.inner x v w)
    have hzero : ((-2 : Real) * ricciTensor (I := I) (g t) x v w) = 0 := by
      simp [g, hRicci]
    simpa [g, hzero] using hconst
  refine ⟨1, by norm_num, ?_⟩
  refine ⟨?_, ?_⟩
  · exact complete_bounded_curvature_solution_of_joint_ricci_flow
      (I := I) (M := M) (by norm_num) g hjoint hpde
      (fun t ht => by simpa [g] using hcomplete)
      (fun t ht => by
        obtain ⟨C, hC, hbound⟩ := hcurv
        refine ⟨C, hC, ?_⟩
        intro x
        simpa [g] using hbound x)
  · rfl

end DifferentialGeometry.PDE.RicciFlow
