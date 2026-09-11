import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

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

def completeBoundedCurvatureSolutionOfJointRicciFlow
    {a b : Real} (hab : a < b)
    (g : Real → SmoothRiemannianMetric I M)
    (hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (I := I) (g p.1) x₀ p.2 i j)
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

omit [BoundarylessManifold I M] [I.Boundaryless] in
theorem CompleteBoundedCurvatureSolutionOn.exists_forward_restart
    {D : RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D))
    {t₀ T : Real} (hT : 0 < T)
    (hcarrier : ∀ s ∈ Set.Ico (0 : Real) T, s + t₀ ∈ D.carrier)
    (hregular : ∀ s ∈ Set.Ioo (0 : Real) T, s + t₀ ∈ D.regular) :
    ∃ S' : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen 0 T hT),
      S'.solution.base.metric 0 = S.solution.base.metric t₀ := by
  let D' := RealTimeInterval.closedOpen 0 T hT
  let Dshift := D.timeShift t₀
  have hcarrier' : D'.carrier ⊆ Dshift.carrier := by
    intro s hs
    change s + t₀ ∈ D.carrier
    change 0 ≤ s ∧ s < T at hs
    exact hcarrier s hs
  have hregular' : D'.regular ⊆ Dshift.regular := by
    intro s hs
    change s + t₀ ∈ D.regular
    change 0 < s ∧ s < T at hs
    exact hregular s hs
  let Sshift : SolutionOn (I := I) (M := M) Dshift := S.solution.timeShift t₀
  have hSshift : IsSolutionOn (I := I) Sshift :=
    isSolutionOn_timeShift S.isSolution t₀
  let S' : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D') :=
    { solution := Sshift.timeRestrict D'
      isSolution := isSolutionOn_timeRestrict hSshift hcarrier' hregular'
      complete := by
        intro s hs
        change DifferentialGeometry.RiemannianMetricComplete (I := I)
          (S.solution.base.metric (s + t₀))
        change 0 ≤ s ∧ s < T at hs
        exact S.complete (s + t₀) (hcarrier s hs)
      curvatureBound := by
        intro s hs
        change ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
          normSq0S (I := I) (S.solution.base.metric (s + t₀)) x 4
            (metricRm04At (I := I) (S.solution.base.metric (s + t₀)) x) ≤ C
        change 0 ≤ s ∧ s < T at hs
        exact S.curvatureBound (s + t₀) (hcarrier s hs) }
  refine ⟨S', ?_⟩
  dsimp [S', Sshift, SolutionOn.timeRestrict, SolutionOn.timeShift,
    SolutionFamily.timeShift]
  simp only [zero_add]

theorem ricci_flow_short_time_existence_of_ricci_flat
    (g₀ : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g₀)
    (hRicci : ∀ (x : M) (v w : TangentSpace I x),
      ricciTensor (I := I) g₀ x v w = 0)
    (hcurv : ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
      normSq0S (I := I) g₀ x 4 (metricRm04At (I := I) g₀ x) ≤ C) :
    ∃ (T : Real) (hT : 0 < T),
      ∃ S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen 0 T hT),
        S.solution.base.metric 0 = g₀ := by
  let g : Real → SmoothRiemannianMetric I M := fun _ => g₀
  have hjoint : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (I := I) (g p.1) x₀ p.2 i j)
        (Set.Ico (0 : Real) 1 ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hcomp :=
      (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn
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
  · exact completeBoundedCurvatureSolutionOfJointRicciFlow
      (I := I) (M := M) (by norm_num) g hjoint hpde
      (fun t ht => by simpa [g] using hcomplete)
      (fun t ht => by
        obtain ⟨C, hC, hbound⟩ := hcurv
        refine ⟨C, hC, ?_⟩
        intro x
        simpa [g] using hbound x)
  · rfl

end DifferentialGeometry.PDE.RicciFlow
