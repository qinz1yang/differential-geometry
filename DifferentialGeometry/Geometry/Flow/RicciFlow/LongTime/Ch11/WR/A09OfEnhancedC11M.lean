import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.WR.EnhancedBridgeC11M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.MGLAdmission
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.A09Final_S153
import DifferentialGeometry.Geometry.Hyperbolic.Truncation.NonemptyHG03
import DifferentialGeometry.Geometry.Hyperbolic.HG06AdapterHGA

set_option autoImplicit false

/-!
# O-CH11-MERGE (M4)：A09 由 ch12 终端证出（REPOINT3 wrapper，后缀 `_C11M`）

`exists_late_cut_family_of_enhanced_C11M` = tracked A09 `exists_late_cut_family`
（`LT/LateCutGeometry.lean:149`）的陈述，只把 `hadm : hasAnalyticAdmissibility F δ` 换成 v2
`hasEnhancedAdmissibilityFull_C11F F δ`；证明 = ch12 终端 `A09_of_supplies_S153`：16 项 ch11 供给经
`WR/EnhancedBridgeC11M.lean`，三条外部输入：
* `hHG03` := `nonempty_hyperbolicTruncation_HG03`（ch8 HG 线，无条件，standard axioms）；
* `hHG06` := `hg06_S0_HGA.{u, u}`（ch8 HG-A 线；`ckErr_O19` 与 `ckErr_HGA` 定义体逐字同，`rfl` 桥）；
* `hMGL` := `External.exists_thick_ball_volume_lower_MGL`（admission，U4）。
-/

noncomputable section

open Set Filter TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open GC.LongTime
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- `ckErr` 桥：ch12 `ckErr_O19` 与 HG-A 的 `ckErr_HGA`（`N : Type u`）定义等式。 -/
theorem ckErr_O19_eq_HGA_C11M (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (k : ℕ) (p : H.Carrier) :
    Ch12.ckErr_O19 H g' c f k p = ckErr_HGA H g' c f k p := rfl

/-- `hHG06`（ch12 终端 binder 逐字）由 `hg06_S0_HGA.{u, u}` 给出。 -/
theorem hHG06_of_HGA_C11M :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
      ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ ∧
        ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (Tr : HyperbolicTruncation H)
          (Tr' : HyperbolicTruncation H'), Tr.count ≤ Tr'.count →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ k : ℕ, k ≤ n + 1 → ∀ p ∈ riemannianClosedBallOf H.metric o ξ⁻¹,
            Ch12.ckErr_O19 H H'.metric 1 f k p < ξ / 3) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
            (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
            ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
              riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η :=
  hg06_S0_HGA.{u, u}

/-- **A09（REPOINT3 wrapper）**：v2 enhanced admissibility + decay ⇒ late cut family。 -/
theorem exists_late_cut_family_of_enhanced_C11M {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : Ch11.hasEnhancedAdmissibilityFull_C11F F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation)
    (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier) :
    Nonempty (LateCutFamily F K slices) := by
  have hadm' : hasAnalyticAdmissibility F δ := hasAnalyticAdmissibility_of_full_C11F hadm
  obtain ⟨E⟩ := hadm
  exact Ch12.A09_of_supplies_S153 (F := F) (K := K) (hK := hK) (δ := δ) (hadm := hadm')
    (hdec := hdec) (slices := slices) (htimes := htimes) (hnonempty := hnonempty)
    (hHG03 := nonempty_hyperbolicTruncation_HG03.{u})
    (Hp := E.toAnalyticSurgeryProfile)
    (hP1 := p1_O2_of_C11M _ E.linked_windows) (Ctime := E.Ctime)
    (hP2 := p2_O2_of_C11M _ _ E.time_derivative) (hP3 := p3_O2_of_C11M _ E.collar_window)
    (hP4 := p4_O2_of_C11M _ E.epsilon_cone) (hP6 := p6_S23_of_C11M _ E.larger_ball_canonical)
    (hP5 := p5_O13_of_C11M _ E.late_linked_records)
    (hcompat := compat_S58_of_C11M _ E.compatible_cap_records)
    (hStrong := hStrong_of_C11M _ E.strongV1) (hprof := hprof_of_C11M _ E.model_constraints)
    (heps := heps_of_C11M _ E.epsilon_cone) (hRFCa := hRFCa_of_C11M _ E.frontier_collar_full)
    (hCapWin := hCapWin_of_C11M _)
    (hHG06 := hHG06_of_HGA_C11M.{u}) (hMGL := External.exists_thick_ball_volume_lower_MGL.{u})

/-- 型对齐：wrapper 的陈述 = tracked A09 的陈述，`hadm` 换成 v2 admissibility（以投影代入即复原）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : Ch11.hasEnhancedAdmissibilityFull_C11F F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (slices : ℕ → RegularSlice F.observation) (htimes : ∀ j : ℕ, (j : ℝ) < (slices j).time)
    (hnonempty : ∀ j : ℕ, Nonempty (slices j).stage.Carrier) :
    Nonempty (LateCutFamily F K slices) :=
  exists_late_cut_family_of_enhanced_C11M F K hK δ hadm hdec slices htimes hnonempty

end GC.LongTime.Ch11
