import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedWindowSeed_S43
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallShi_O13

/-!
# CH12-S43, group 2b: per-time seeds along the backward window ⇒ traced region about `y`

`traced_of_seeds_S43`: `enlarged_rm_bound_along_seed_trace_CX2` (G3a along a single trace) followed by
`slice_seed_tracedRegion_window_S43` (G3b with window-restricted cutoff hypotheses).  The seed family
(`hasSmallParabolicCurvature` + volume at each time `v ∈ [l, t]`, joined by a backward trace of `y`)
is the explicit input; producing it at micro test balls from the zero-order bound, P2 and
Hamilton–Ivey is the remaining part of ZT.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem traced_of_seeds_S43 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {a c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁) :
    ∃ T₀ ρ₀ K₀ : ℝ, 0 < T₀ ∧ 0 < ρ₀ ∧ 0 < K₀ ∧
      ∀ (s : RegularSlice F.observation) (l : Icc (0 : ℝ) s.history.horizon)
        (_ : l ≤ sliceTop_S8 s) (y : (s.history.stageAt (sliceTop_S8 s)).Carrier)
        (r τ Λ : ℝ), 0 < r → 0 < τ → 1 ≤ Λ → 2 * (9 * K₀) < Λ ^ 2 →
        Real.exp (9 * K₀ * τ) < 2 → l.val = s.time - τ * r ^ 2 →
      (∀ v : Icc (0 : ℝ) s.history.horizon, l ≤ v →
        T₀ ≤ (v : ℝ) ∧ r ≤ ρ₀ * Real.sqrt v) →
      (∀ (v : Icc (0 : ℝ) s.history.horizon) (_ : l ≤ v),
        ∃ yv : (s.history.stageAt v).Carrier,
          hasSmallParabolicCurvature s.history v yv (a * r) ∧
          ENNReal.ofReal (c₁ * (a * r) ^ 3) ≤
            ballVolume (s.history.stageMetric (s.history.activeStage v) v) yv (a * r) ∧
          ∃ A : BackwardPointTrace s.history (s.history.activeStage v)
              (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono
                (show v ≤ sliceTop_S8 s from v.property.2)) y,
            A.point (s.history.activeStage v) le_rfl
              (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) = yv) →
      (∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
        ∀ j, (Hp.records n i).delta j ≤ 1 / 8646) →
      (∀ n (i : Fin (F.tower.history n).eventCount),
        (F.tower.history n).time i.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
        ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) →
      s.history.isTracedRegion (sliceTop_S8 s) y (2 * r) (τ * r ^ 2) (K₀ / r ^ 2) := by
  obtain ⟨T₀, ρ₀, K₀, hT, hρ, hK, henl⟩ := enlarged_rm_bound_along_seed_trace_CX2 Hp ha hc₁
  refine ⟨T₀, ρ₀, K₀, hT, hρ, hK, ?_⟩
  intro s l hlt y r τ Λ hr hτ hΛ hKΛ hexp hl hsize hseed hδ hnom
  obtain ⟨A, hA⟩ := henl s l hlt y r hr hsize hseed
  exact slice_seed_tracedRegion_window_S43 Hp s hτ hr hK hΛ hKΛ hexp hl hlt
    (mem_riemannianBallOf_self_O13 _ y hr) A (fun v hav _ q hq => hA v hav q hq) hδ hnom

end GC.LongTime.Ch12
