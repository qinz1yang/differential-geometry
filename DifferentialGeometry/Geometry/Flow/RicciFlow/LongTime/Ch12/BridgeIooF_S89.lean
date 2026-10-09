import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BridgeIoo_S89
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LiftBridge_S65
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ForwardWindowDef_S45

set_option autoImplicit false

/-!
# CH12-S89 / G3: the bridge in the S45 per-time shape (`fs`, `postStage`)

`hlift_Ioo_of_Ico_S89`: an `Ico` lift datum of `F.tower.history n` at the single time `t` (the
dyadic time = the left end of the `fs`-window `Icc t (2 t)`), together with the post-side scalar
`≤ 0` of `f(ball R)` at `t`, gives the `Ioo` datum (`a' < t`) with the same HEq clause.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime GC.LongTime.Ch12 GC.LongTime.CuspP1
open scoped Manifold ContDiff ENNReal
universe u

namespace GC.LongTime.Ch12

theorem metricScalarAt_heq_S89 {A B : OrientedThreeStage.{u}} (h : A = B) (gA : A.Metric)
    (gB : B.Metric) (hg : HEq gA gB) (x : A.Carrier) (y : B.Carrier) (hxy : HEq x y) :
    metricScalarAt gA x = metricScalarAt gB y := by
  subst h
  rw [eq_of_heq hg, eq_of_heq hxy]

theorem hlift_Ioo_of_Ico_S89 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] (S : Set X)
    (hSne : S.Nonempty) (W : Set ℝ) (w : ∀ r : ℝ, r ∈ W → X → (postStage F.observation r).Carrier)
    (s : ℝ) (hs : s ∈ W) (hs0 : 0 ≤ s)
    (hscale : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).toHistory.time i.succ = s →
      ∀ (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
        ((Hp.records n i).static b).neck.scale / 2 ≤
          metricScalarAt ((Hp.records n i).static b).witness.metric
            (((Hp.records n i).static b).witness.cap z))
    (hrc : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).toHistory.time i.succ = s →
      Hp.parameters.recenterConstant *
        Hp.parameters.delta ((F.tower.history n).toHistory.time i.succ) ≤ 1 / 2)
    (hneg : ∀ p ∈ S, metricScalarAt (postMetric F.observation s) (w s hs p) ≤ 0)
    (hIco : ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ s) (_ : ∀ r ∈ W, r ≤ s → a ≤ r) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (φ : X → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ S ∧
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
        (hrW : (r : ℝ) ∈ W), ∀ p ∈ S,
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
          (w r hrW p)) :
    ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (φ : X → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ S ∧
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
        (hrW : (r : ℝ) ∈ W), ∀ p ∈ S,
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
          (w r hrW p) := by
  obtain ⟨n, first, last, ordered, a, b, hat, hcov, htb, hb, stages, φ, hφ, hheq⟩ := hIco
  have hT0 : s ∈ Icc (0 : ℝ) (F.tower.history n).horizon := ⟨hs0, htb.le.trans hb⟩
  let T0 : Icc (0 : ℝ) (F.tower.history n).horizon := ⟨s, hT0⟩
  have hnegC : (F.tower.history n).toHistory.time first = s → ∀ p ∈ S,
      metricScalarAt ((F.tower.history n).toHistory.initialMetric first)
        ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered first le_rfl ordered (φ p)) ≤ 0 := by
    intro htime p hp
    have hT0st := stages T0 ⟨hat, htb⟩
    have hact : (F.tower.history n).toHistory.activeStage T0 = first := by
      refine le_antisymm ?_ hT0st.1
      by_contra hlt
      have h1 := (F.tower.history n).toHistory.time_strictMono (not_le.mp hlt)
      have h2 := (F.tower.history n).toHistory.activeStage_time_le T0
      rw [htime] at h1
      exact absurd h2 (not_le.mpr h1)
    have hsc := metricScalarAt_heq_S89 (postStage_eq_stage_active_CPD2 F.observation n T0)
      (postMetric F.observation s)
      ((F.tower.history n).toHistory.stageMetric ((F.tower.history n).toHistory.activeStage T0) s)
      (postMetric_heq_stageMetric_S65 F.observation n T0) _ _
      (hheq T0 ⟨hat, htb⟩ hs p hp).symm
    have hini := (F.tower.history n).toHistory.stageMetric_initial
      ((F.tower.history n).toHistory.activeStage T0)
    rw [hact, htime] at hini
    have := hneg p hp
    rw [hsc] at this
    subst hact
    rw [← hini]
    exact this
  obtain ⟨first', last', ordered', a', ha', htb', hb', stages', φ', hφ', hheq'⟩ :=
    hlift_Ioo_core_S89 (F.tower.history n).toHistory (Hp.records n) (hscale n) (hrc n) S hSne
    (α := fun r => (postStage F.observation (r : ℝ)).Carrier) W
    (fun r hrW q => w r hrW q) hs0
    hat (fun r hr => if h : r ≤ s then hcov r hr h else hat.trans (not_le.mp h).le) htb hb stages φ hφ hheq hnegC
  exact ⟨n, first', last', ordered', a', b, ha', htb', hb', stages', φ', hφ', hheq'⟩

end GC.LongTime.Ch12
