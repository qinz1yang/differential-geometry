import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCurvatureControl
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage

theorem exists_uniform_initial_curvature_bound (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ η K : ℝ, 0 < η ∧ ∀ (s : ℝ) (G : P.IncomingSlab 0 s), G.flow.base.metric 0 = g →
      ∀ t, 0 ≤ t → t < s → t ≤ η → ∀ x : P.Carrier,
        G.flow.scalar t x ≤ K ∧ G.riemannNorm t x ≤ K := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by omega⟩
  obtain ⟨K₂, _, hcurv₂⟩ := exists_rm04_bound g
  let K₀ := Real.sqrt K₂
  let B := Real.sqrt (2 * K₀ ^ 2 + 1)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  let c : ℝ := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2
  have hc : 0 ≤ c := sq_nonneg _
  refine ⟨compactCurvatureControlTime (Module.finrank ℝ ThreeSpace) K₀, c * B + B,
    compactCurvatureControlTime_pos _ _, ?_⟩
  intro s G hG t ht0 hts htη x
  have hslab : Icc (0 : ℝ) t ⊆ (RealTimeInterval.closedOpen 0 s G.lt).carrier :=
    fun u hu => ⟨hu.1, hu.2.trans_lt hts⟩
  have hreg : Ioo (0 : ℝ) t ⊆ (RealTimeInterval.closedOpen 0 s G.lt).regular :=
    fun u hu => ⟨hu.1, hu.2.trans hts⟩
  have hRm := curvature_bound_from_initial_compact t ht0 K₀ htη _ G.flow G.equation hslab hreg
    (fun x₀ i j => (chartGramMatrix_joint_contMDiffOn G.flow.base.metric (Ico 0 s)
      G.smoothUpTo.jointContMDiffOn x₀ i j).mono (prod_mono hslab subset_rfl))
    (fun y => by rw [hG]; exact Real.sqrt_le_sqrt (hcurv₂ y))
  have hN : Real.sqrt (normSq0S (G.flow.base.metric t) x 4
      (metricRm04 (G.flow.base.metric t) x)) ≤ B := hRm t ⟨ht0, le_rfl⟩ x
  have hN' : Real.sqrt (normSq0S (G.flow.base.metric t) x 4
      (metricRm04At (G.flow.base.metric t) x)) ≤ B := by
    rw [← metricRm04_apply]
    exact hN
  have hscal : |metricScalarAt (G.flow.base.metric t) x| ≤ c * B :=
    (scalar_abs_le_rm (G.flow.base.metric t) x).trans (mul_le_mul_of_nonneg_left hN' hc)
  have hS : G.flow.scalar t x ≤ c * B := (le_abs_self _).trans hscal
  have hR : G.riemannNorm t x ≤ B := hN
  have hcB : 0 ≤ c * B := mul_nonneg hc hB
  constructor
  · linarith
  · linarith

namespace IncomingSlab

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem canonicalOn_of_scalar_le {ε C1 C2 qcan τmin t₀ η : ℝ}
    (h : ∀ t, a < t → t₀ ≤ t → t < t₀ + η → t < s → ∀ y, G.flow.scalar t y ≤ qcan) :
    G.CanonicalOn ε C1 C2 qcan τmin t₀ η :=
  fun y t hat ht₀ htη hts hR _ => absurd hR (not_lt.mpr (h t hat ht₀ htη hts y))

theorem derivativeBoundOn_of_scalar_le {Ctime : ℝ≥0} {qcan t₀ η : ℝ}
    (h : ∀ t, a < t → t₀ ≤ t → t < t₀ + η → t < s → ∀ y, G.flow.scalar t y ≤ qcan) :
    G.DerivativeBoundOn Ctime qcan t₀ η :=
  fun y t hat ht₀ htη hts hR => absurd hR (not_lt.mpr (h t hat ht₀ htη hts y))

end IncomingSlab

theorem exists_uniform_initial_canonicalOn_derivativeBoundOn (P : OrientedThreeStage.{u})
    (g : P.Metric) :
    ∃ η K : ℝ, 0 < η ∧ ∀ qcan : ℝ, K ≤ qcan → ∀ (s : ℝ) (G : P.IncomingSlab 0 s),
      G.flow.base.metric 0 = g →
        (∀ ε C1 C2 τmin : ℝ, G.CanonicalOn ε C1 C2 qcan τmin 0 η) ∧
          ∀ Ctime : ℝ≥0, G.DerivativeBoundOn Ctime qcan 0 η := by
  obtain ⟨η, K, hη, hK⟩ := P.exists_uniform_initial_curvature_bound g
  have hle : ∀ qcan : ℝ, K ≤ qcan → ∀ (s : ℝ) (G : P.IncomingSlab 0 s),
      G.flow.base.metric 0 = g → ∀ t, (0 : ℝ) < t → (0 : ℝ) ≤ t → t < 0 + η → t < s →
        ∀ y, G.flow.scalar t y ≤ qcan :=
    fun qcan hq s G hG t _ ht₀ htη hts y =>
      (hK s G hG t ht₀ hts (by linarith) y).1.trans hq
  exact ⟨η, K, hη, fun qcan hq s G hG =>
    ⟨fun _ _ _ _ => G.canonicalOn_of_scalar_le (hle qcan hq s G hG),
      fun _ => G.derivativeBoundOn_of_scalar_le (hle qcan hq s G hG)⟩⟩

end OrientedThreeStage

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
