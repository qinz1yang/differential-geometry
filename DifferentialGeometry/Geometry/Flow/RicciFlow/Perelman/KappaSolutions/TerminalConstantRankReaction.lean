import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankRigidity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarPositivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalConstantRankFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalRankKernelPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProductEuclidean


set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

theorem not_forall_finrank_eq_of_finrank_ne_two :
    ¬ (∀ V W : Submodule ℝ (Fin 3 → ℝ),
      Module.finrank ℝ V ≠ 2 → Module.finrank ℝ W ≠ 2 →
        Module.finrank ℝ V = Module.finrank ℝ W) := by
  intro h
  have h0 : Module.finrank ℝ (⊥ : Submodule ℝ (Fin 3 → ℝ)) = 0 := by simp
  have h3 : Module.finrank ℝ (⊤ : Submodule ℝ (Fin 3 → ℝ)) = 3 := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hne0 : Module.finrank ℝ (⊥ : Submodule ℝ (Fin 3 → ℝ)) ≠ 2 := by
    rw [h0]
    norm_num
  have hne3 : Module.finrank ℝ (⊤ : Submodule ℝ (Fin 3 → ℝ)) ≠ 2 := by
    rw [h3]
    norm_num
  have hres := h _ _ hne0 hne3
  rw [h0, h3] at hres
  norm_num at hres

end DifferentialGeometry.Geometry.Curvature.DimensionThree

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree

universe uH

variable {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{0, 0, uH} (I := I) D)

local instance terminalConstantRankReactionTopology : TopologicalSpace F.M := F.topology
local instance terminalConstantRankReactionCharted : ChartedSpace H F.M := F.charted
local instance terminalConstantRankReactionSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalConstantRankReactionC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalConstantRankReactionT2 : T2Space F.M := F.t2
local instance terminalConstantRankReactionSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance terminalConstantRankReactionInhabited : Inhabited F.M := ⟨F.basepoint⟩

private abbrev terminalRmSub (x : F.M) :
    algebraicCurvatureTensorSubmodule (I := I) (M := F.M) x :=
  ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
    metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) (F.S.base.metric 0) x⟩

private theorem finrank_morseModel_three :
    Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
  simp [DifferentialGeometry.Topology.Morse.MorseModel]

omit [I.Boundaryless] in
theorem curvatureOperatorEndomorphismAt_inner_nonneg_of_kLim {kappa : ℝ}
    (hK : KLim (I := I) kappa F) :
    ∀ x : F.M, ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
      0 ≤ (twoFormMetricData (I := I) (F.S.base.metric 0) x).inner
        (curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
          (terminalRmSub F x) a) a := by
  intro x a
  exact curvatureOperatorEndomorphismAt_inner_nonneg_of_mem_nonnegativeCone
    (I := I) (M := F.M) finrank_morseModel_three (F.S.base.metric 0) x
    (terminalRmSub F x) (terminal_mem_nonnegativeCone F hK x) a

theorem curvatureOperatorImageAt_finrank_ne_two_of_constantRankParallelKernel
    (hker : TerminalConstantRankParallelKernel (I := I) F) :
    ∀ x : F.M, Module.finrank ℝ
      (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
        (terminalRmSub F x)) ≠ 2 := by
  obtain ⟨q, hq, hconst, _⟩ := hker
  have hq2 : q ≠ 2 := by rcases hq with h | h | h <;> omega
  intro x
  change Module.finrank ℝ
    (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
      ⟨metricRm04 (I := I) (F.S.base.metric 0) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I)
          (F.S.base.metric 0) x⟩) ≠ 2
  rw [hconst x]
  exact hq2

omit [I.Boundaryless] in
theorem curvatureOperatorReactionEndomorphism3_eq_zero_of_mem_ker_of_finrank_image_ne_two
    (hne : ∀ x : F.M, Module.finrank ℝ
      (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
        (terminalRmSub F x)) ≠ 2) :
    ∀ x : F.M, ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
      curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
          (terminalRmSub F x) a = 0 →
        curvatureOperatorReactionEndomorphism3
          (curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
            (terminalRmSub F x)).toLinearMap a = 0 := by
  intro x a ha
  have hdimx : Module.finrank ℝ (TangentSpace I x) = 3 :=
    (show Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) from rfl).trans
      finrank_morseModel_three
  have htwo : Module.finrank ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) = 3 := by
    rw [ContinuousAlternatingMap.finrank_continuousAlternatingMap, hdimx]
    norm_num
  have hrank : Module.finrank ℝ
      ((curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
        (terminalRmSub F x)).toLinearMap.range) ≠ 2 := by
    rw [← curvatureOperatorImageAt_eq_range]
    exact hne x
  exact curvatureOperatorReactionEndomorphism3_eq_zero_of_mem_ker_of_finrank_range_ne_two
    htwo _ hrank ha

theorem curvatureOperatorReactionEndomorphism3_eq_zero_of_mem_ker_of_constantRankParallelKernel
    (hker : TerminalConstantRankParallelKernel (I := I) F) :
    ∀ x : F.M, ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
      curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
          (terminalRmSub F x) a = 0 →
        curvatureOperatorReactionEndomorphism3
          (curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
            (terminalRmSub F x)).toLinearMap a = 0 :=
  curvatureOperatorReactionEndomorphism3_eq_zero_of_mem_ker_of_finrank_image_ne_two F
    (curvatureOperatorImageAt_finrank_ne_two_of_constantRankParallelKernel F hker)

theorem terminalConstantRank_derivedData_hypotheses_of_kLim {kappa : ℝ}
    (hK : KLim (I := I) kappa F)
    (hker : TerminalConstantRankParallelKernel (I := I) F) :
    (∀ x : F.M, ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
        0 ≤ (twoFormMetricData (I := I) (F.S.base.metric 0) x).inner
          (curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
            (terminalRmSub F x) a) a) ∧
      (∀ x : F.M, ∀ a : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
        curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
            (terminalRmSub F x) a = 0 →
          curvatureOperatorReactionEndomorphism3
            (curvatureOperatorEndomorphismAt (I := I) (F.S.base.metric 0) x
              (terminalRmSub F x)).toLinearMap a = 0) ∧
      (∀ x y : F.M, Module.finrank ℝ
          (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) x
            (terminalRmSub F x)) =
          Module.finrank ℝ
            (curvatureOperatorImageAt (I := I) (F.S.base.metric 0) y
              (terminalRmSub F y))) ∧
      DifferentialGeometry.Geometry.Connection.IsParallelContinuousAlternatingSubmoduleFamily
        (F.S.base.metric 0)
        (fun x => curvatureOperatorKernelAt (I := I) (F.S.base.metric 0) x
          (terminalRmSub F x)) := by
  have hann :=
    curvatureOperatorReactionEndomorphism3_eq_zero_of_mem_ker_of_constantRankParallelKernel F hker
  obtain ⟨q, _hq, hconst, hpar⟩ := hker
  exact ⟨curvatureOperatorEndomorphismAt_inner_nonneg_of_kLim F hK, hann,
    fun x y => by rw [hconst x, hconst y], hpar⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
