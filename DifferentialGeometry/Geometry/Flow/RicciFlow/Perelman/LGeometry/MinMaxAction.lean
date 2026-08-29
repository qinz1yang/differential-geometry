import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.MinMaxCompact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RegAction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegKinetic_le
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (a b A C : Real) (hab : a ≤ b)
    (hpot : ∀ s ∈ Set.Icc a b,
      C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
    (hkin : IntervalIntegrable (lRegSpeedSq S T alpha) volume a b)
    (hLag : IntervalIntegrable (lRegLag S T alpha) volume a b)
    (hA : lRegAction S T alpha a b ≤ A) :
    (∫ s in a..b, lRegSpeedSq S T alpha s) ≤
      2 * (A - C * (b - a)) := by
  have hleft : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) * lRegSpeedSq S T alpha s + C)
      volume a b :=
    (hkin.const_mul (1 / 2 : Real)).add intervalIntegrable_const
  have hmono :
      (∫ s in a..b, (1 / 2 : Real) * lRegSpeedSq S T alpha s + C) ≤
        lRegAction S T alpha a b := by
    unfold lRegAction
    apply intervalIntegral.integral_mono_on hab hleft hLag
    intro s hs
    simpa only [lRegLag, lRegSpeedSq, add_comm] using
      add_le_add_left (hpot s hs)
        ((1 / 2 : Real) * lRegSpeedSq S T alpha s)
  rw [intervalIntegral.integral_add (hkin.const_mul (1 / 2 : Real))
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  have hmonoA := hmono.trans hA
  linarith

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegKinetic_bound
    [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    (T a b A : Real) (hab : a ≤ b)
    (ht : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ D.carrier) :
    ∃ C : Real, ∀ alpha : Real → M,
      IntervalIntegrable (lRegSpeedSq S T alpha) volume a b →
        IntervalIntegrable (lRegLag S T alpha) volume a b →
          lRegAction S T alpha a b ≤ A →
            (∫ s in a..b, lRegSpeedSq S T alpha s) ≤
              2 * (A - C * (b - a)) := by
  obtain ⟨C, hC⟩ := lScalar_lower (I := I) S hS T a b (by
    intro s hs
    exact ht s (by simpa only [Set.uIcc_of_le hab] using hs))
  refine ⟨C, ?_⟩
  intro alpha hkin hLag hA
  exact lRegKinetic_le (I := I) S T alpha a b A C hab
    (fun s hs ↦ hC s (by
      simpa only [Set.uIcc_of_le hab] using hs) (alpha s))
    hkin hLag hA

end DifferentialGeometry.PDE.RicciFlow.Perelman
