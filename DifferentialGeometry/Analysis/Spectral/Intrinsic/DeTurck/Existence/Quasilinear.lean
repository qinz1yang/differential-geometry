import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearity.Basic
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.MixedLipschitz
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g₀ g_bg : SmoothRiemannianMetric I M}

def deTurckLipConst (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ≥0 :=
  (deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose

theorem deTurckSobolevNHa2_lipschitzWith_lipConst (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    LipschitzWith (deTurckLipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super)
      (deTurckSobolevNonlinearity (I := I) (M := M) g₀ g_bg a) :=
  (deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose_spec

def deTurckTimeNemytskii (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {T : ℝ} :
    timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) T →
      timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ)) T :=
  nemytskii (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (a := (a : ℝ)) (T := T)
    (deTurckSobolevNHa2_lipschitzWith_lipConst (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg)
      a ha_super)

def deTurckLipConstSymm (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) : ℝ≥0 :=
  (deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose

theorem deTurckSobolevNHa2Symm_lipschitzWith_lipConst (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    LipschitzWith (deTurckLipConstSymm (I := I) (M := M) (g₀ := g₀) (g_bg := g_bg) a ha_super)
      (deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a) :=
  (deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super).choose_spec

theorem deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ C₁ C₂ : ℝ≥0, ∀ (u u' : TensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a u -
          deTurckSobolevNonlinearitySymm (I := I) (M := M) g₀ g_bg a u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖ :=
  deTurckSobolevNonlinearitySymm_mixed_lipschitz_pointwise (I := I) (M := M) g₀ g_bg a ha_super

end DifferentialGeometry.Analysis.Spectral

end
