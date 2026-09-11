import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Concatenation

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M] {D : RealTimeInterval}

theorem isFiniteActionLCurve.mono
    {S : SolutionOn (I := I) (M := M) D} {T : ℝ}
    {Ω : Set (M × ℝ)} {a b c d : ℝ} {gamma : ℝ → M}
    (hgamma : isFiniteActionLCurve S T Ω a b gamma)
    (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b) :
    isFiniteActionLCurve S T Ω c d gamma := by
  have hab : a ≤ b := (hsub ⟨le_rfl, hcd⟩).1.trans (hsub ⟨le_rfl, hcd⟩).2
  have hsub' : uIcc c d ⊆ uIcc a b := by
    simpa only [uIcc_of_le hcd, uIcc_of_le hab] using hsub
  refine ⟨?_, ae_mono (Measure.restrict_mono hsub le_rfl) hgamma.2.1,
    hgamma.2.2.1.mono_set hsub', fun s hs => hgamma.2.2.2 s (hsub hs)⟩
  let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
  exact hgamma.1.mono hsub'

theorem isFiniteActionLCurve.piecewise_Iic
    {S : SolutionOn (I := I) (M := M) D} {T : ℝ}
    {Ω : Set (M × ℝ)} {a b c : ℝ} {gamma eta : ℝ → M}
    (hgamma : isFiniteActionLCurve S T Ω a b gamma)
    (heta : isFiniteActionLCurve S T Ω b c eta)
    (hab : a ≤ b) (hbc : b ≤ c) (hnode : gamma b = eta b) :
    isFiniteActionLCurve S T Ω a c (Set.piecewise (Set.Iic b) gamma eta) := by
  classical
  rcases hgamma with ⟨hgammaAC, hgammaDiff, hgammaInt, hgammaΩ⟩
  rcases heta with ⟨hetaAC, hetaDiff, hetaInt, hetaΩ⟩
  refine ⟨?_, ?_, intervalIntegrable_lDensity_piecewise_Iic S T a b c gamma eta
    hab hbc hgammaInt hetaInt, ?_⟩
  · let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
    exact AbsolutelyContinuousOnInterval.piecewise_Iic hab hbc hgammaAC hetaAC hnode
  · have hgammaDiff' :
        ∀ᵐ s ∂volume, s ∈ Icc a b → MDifferentiableAt 𝓘(ℝ, ℝ) I gamma s :=
      (ae_restrict_iff' measurableSet_Icc).mp hgammaDiff
    have hetaDiff' :
        ∀ᵐ s ∂volume, s ∈ Icc b c → MDifferentiableAt 𝓘(ℝ, ℝ) I eta s :=
      (ae_restrict_iff' measurableSet_Icc).mp hetaDiff
    filter_upwards
      [ae_restrict_mem measurableSet_Icc,
        ae_mono Measure.restrict_le_self hgammaDiff',
        ae_mono Measure.restrict_le_self hetaDiff',
        Measure.ae_ne (volume.restrict (Icc a c)) b]
        with s hs hsGamma hsEta hsb
    by_cases hleft : s ≤ b
    · have hslt : s < b := lt_of_le_of_ne hleft hsb
      apply (hsGamma ⟨hs.1, hleft⟩).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hslt] with r hr
      exact (Set.Iic b).piecewise_eq_of_mem gamma eta (Set.mem_Iic.mpr hr.le)
    · have hright : b < s := lt_of_not_ge hleft
      apply (hsEta ⟨hright.le, hs.2⟩).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hright] with r hr
      exact (Set.Iic b).piecewise_eq_of_notMem gamma eta
        (by simpa only [Set.mem_Iic] using not_le_of_gt hr)
  · intro s hs
    by_cases hleft : s ≤ b
    · rw [Set.piecewise_eq_of_mem (Set.Iic b) gamma eta hleft]
      exact hgammaΩ s ⟨hs.1, hleft⟩
    · rw [Set.piecewise_eq_of_notMem (Set.Iic b) gamma eta hleft]
      exact hetaΩ s ⟨le_of_not_ge hleft, hs.2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
