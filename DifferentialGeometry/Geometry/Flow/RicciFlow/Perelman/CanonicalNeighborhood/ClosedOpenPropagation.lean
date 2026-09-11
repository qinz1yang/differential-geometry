import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarLaplacianJet
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RmNormFromEigenvalues
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelCurvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

def ClosedOpenLocalPropagation (I : ModelWithCorners ℝ E H) (kappa c C : ℝ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
    {T : ℝ} {hT : (0 : ℝ) < T}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
    IsSolutionOn (I := I) S →
    ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
    ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 4 →
    ∀ Q : ℝ, ∀ hQ : 0 < Q, ∀ t0 : ℝ,
    ∀ ht0 : t0 ∈ (RealTimeInterval.closedOpen 0 T hT).carrier,
    ∀ Hd : ℝ, 2 * c ≤ Hd →
    Set.Icc (t0 - Hd / Q) t0 ⊆ (RealTimeInterval.closedOpen 0 T hT).regular →
    PhiAlmostNonnegative (I := I) (M := M) S (Set.Icc (t0 - Hd / Q) t0) Phi →
    (∀ (w : M) (t : ℝ), t ∈ Set.Icc (t0 - Hd / Q) t0 →
      2 * Q ≤ S.scalar t w → IsGoodPoint.{u, uE, uH} (I := I) eps kappa S w t) →
    ∀ (z : M) (sbar : ℝ), sbar ∈ Set.Icc (-(Hd / 2)) 0 →
    ∀ L : ℝ, L = 1 + |(parabolicSolution (I := I) S t0 Q hQ ht0).scalar sbar z| →
      Set.Icc (sbar - c / L) sbar ⊆
          (parabolicInterval (RealTimeInterval.closedOpen 0 T hT) t0 Q ht0).carrier ∧
        ∀ (y : M) (vbar : ℝ),
          (y, vbar) ∈ frozenBackwardCylinder (I := I)
            (parabolicSolution (I := I) S t0 Q hQ ht0) z sbar c c L →
            -6 * Q⁻¹ * Phi 0 ≤ (parabolicSolution (I := I) S t0 Q hQ ht0).scalar vbar y ∧
              (parabolicSolution (I := I) S t0 Q hQ ht0).scalar vbar y ≤ 4 * L ∧
              Real.sqrt (FlowMetricBall.rmNormSq (I := I)
                  (parabolicSolution (I := I) S t0 Q hQ ht0) vbar y) ≤
                C * (L + (Phi (4 * Q * L) + Phi 0) / Q)

theorem exists_goodPointBoundsOn_closedOpen_of_modelBound [I.Boundaryless]
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, uE, uH} I kappa) :
    ∃ CStar : ℝ, 0 ≤ CStar ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
        {T : ℝ} {hT : (0 : ℝ) < T}
        (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
        IsSolutionOn (I := I) S → ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 4 →
          GoodPointBoundsOn.{u, uE, uH} (I := I) S eps kappa CStar := by
  let : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; decide⟩
  obtain ⟨CStar, hCStar, hbound⟩ := goodPointBoundsOn_of_modelBound hmod
  refine ⟨CStar, hCStar, ?_⟩
  intro M _ _ _ _ _ _ T hT S hS eps heps hepsle
  let : IsManifold I 2 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  exact fun x t hgood => hbound M S hS x t eps heps hepsle hgood

theorem exists_closedOpenLocalPropagation_of_modelBound [I.Boundaryless]
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, uE, uH} I kappa) :
    ∃ CStar : ℝ, 0 ≤ CStar ∧ 0 < localPropagationRadius CStar ∧
      localPropagationRadius CStar ≤ 1 / 20 ∧
      ClosedOpenLocalPropagation.{u, uE, uH} I kappa
        (localPropagationRadius CStar) (4 * Real.sqrt 3) := by
  obtain ⟨CStar, hCStar, hbound⟩ :=
    exists_goodPointBoundsOn_closedOpen_of_modelBound hdim hmod
  refine ⟨CStar, hCStar, localPropagationRadius_pos hCStar,
    localPropagationRadius_le hCStar, ?_⟩
  intro M _ _ _ _ _ _ T hT S hS Phi hPhi eps heps hepsle
    Q hQ t0 ht0 Hd hHd hJ hanc hgood z sbar hsbar L hL
  have hbnd : GoodPointBoundsOn.{u, uE, uH} (I := I) S eps kappa CStar :=
    hbound M S hS eps heps hepsle
  have hbridge : RmNormBoundOn (I := I) S (2 * Real.sqrt 3) :=
    fun t x basis horth a ha =>
      sqrt_rmNormSq_le_of_abs_orderedSectionalCurvaturesAt_le S t x basis horth ha
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL]
    linarith [abs_nonneg ((parabolicSolution (I := I) S t0 Q hQ ht0).scalar sbar z)]
  constructor
  · intro r hr
    exact (RealTimeInterval.closedOpen 0 T hT).regular_subset
      (hJ (parabolicTime_mem_window (t0 := t0) (Q := Q) (Hd := Hd) (L := L)
        (c := localPropagationRadius CStar) hQ (localPropagationRadius_pos hCStar)
        hL1 hHd hsbar hr))
  · intro y vbar hmem
    have hfour : (2 : ℝ) * (2 * Real.sqrt 3) = 4 * Real.sqrt 3 := by ring
    simpa only [hfour] using
      local_propagation_paraSolution (I := I) hS hCStar
        (by positivity : 0 ≤ 2 * Real.sqrt 3) hQ ht0 hdim hPhi hanc hbridge
        hbnd hHd hJ hgood hsbar hL hmem

theorem exists_closedOpenLocalPropagation [I.Boundaryless]
    (hdim : Module.finrank ℝ E = 3) {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ CStar : ℝ, 0 ≤ CStar ∧ 0 < localPropagationRadius CStar ∧
      localPropagationRadius CStar ≤ 1 / 20 ∧
      ClosedOpenLocalPropagation.{u, uE, uH} I kappa
        (localPropagationRadius CStar) (4 * Real.sqrt 3) :=
  exists_closedOpenLocalPropagation_of_modelBound hdim
    (modelCurvatureBoundNearBase hdim hkappa)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

end
