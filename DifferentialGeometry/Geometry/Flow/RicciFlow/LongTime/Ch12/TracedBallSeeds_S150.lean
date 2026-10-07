import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedBallSeeds_S95
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedPath_CX2

/-!
# CH12-S150, group 1a: `traced_of_seeds_ball_S150` -- `traced_of_seeds_ball_S95` with a 60 r-ball bound handed to `hbar`

`[FROZEN] CH12-S150 G1/G2`, F-S150-1.  The tube of F-S146-1 has radius `60 r`, but `traced_of_seeds_ball_S95` only supplies
the bound `K₀/r²` on `20 r`-balls about the seed trace.  Both bounds come from `enlarged_rm_bound_of_slice_seed_CX2`:
`seed_along_trace_S150` is `enlarged_rm_bound_along_seed_trace_CX2` for an ARBITRARY trace `A` (not `∃ A`), and
`seed_along_trace60_S150` is the same at `(a/3, 3r)` (`a/3 * (3 r) = a r`, `20 * (3 r) = 60 r`), the scaling trick of
`L862Enlargement_CX12`.  `traced_of_seeds_ball_S150` has the S95 statement with one extra `hbar` premise `hbd60`.
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

/-- The 20 r-ball curvature bound along ANY seed trace `A` (`enlarged_rm_bound_along_seed_trace_CX2` with `∀ A`). -/
theorem seed_along_trace_S150 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {a c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁) :
    ∃ T₀ ρ₀ K₀ : ℝ, 0 < T₀ ∧ 0 < ρ₀ ∧ 0 < K₀ ∧
      ∀ (s : RegularSlice F.observation) (l : Icc (0 : ℝ) s.history.horizon)
        (hlt : l ≤ sliceTop_S8 s) (y : (s.history.stageAt (sliceTop_S8 s)).Carrier)
        (r : ℝ), 0 < r →
      (∀ v : Icc (0 : ℝ) s.history.horizon, l ≤ v →
        T₀ ≤ (v : ℝ) ∧ r ≤ ρ₀ * Real.sqrt v) →
      (∀ (v : Icc (0 : ℝ) s.history.horizon) (_ : l ≤ v),
        ∃ yv : (s.history.stageAt v).Carrier,
          hasSmallParabolicCurvature s.history v yv (a * r) ∧
          ENNReal.ofReal (c₁ * (a * r) ^ 3) ≤
            ballVolume (s.history.stageMetric (s.history.activeStage v) v) yv (a * r) ∧
          ∃ A : BackwardPointTrace s.history (s.history.activeStage v)
              (s.history.activeStage (sliceTop_S8 s))
              (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) y,
            A.point (s.history.activeStage v) le_rfl
              (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) = yv) →
      ∀ A : BackwardPointTrace s.history (s.history.activeStage l)
          (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hlt) y,
        ∀ (v : Icc (0 : ℝ) s.history.horizon) (hlv : l ≤ v),
          ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
            (A.point (s.history.activeStage v) (s.history.activeStage_mono hlv)
              (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2))) (20 * r),
            Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
              (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ K₀ / r ^ 2 := by
  obtain ⟨T₀, ρ₀, K₀, hT, hρ, hK, henlarge⟩ := enlarged_rm_bound_of_slice_seed_CX2 Hp ha hc₁
  refine ⟨T₀, ρ₀, K₀, hT, hρ, hK, ?_⟩
  intro s l hlt y r hr hsize hseed A v hlv q hq
  obtain ⟨yv, hseedv, hvolv, B, hB⟩ := hseed v hlv
  have hpoint := (seed_trace_point_unique_CX2 s.history (hat := hlt) hlv
    (show v ≤ sliceTop_S8 s from v.property.2) A B).trans hB
  have hq' : q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v) yv (20 * r) := by
    rwa [hpoint] at hq
  exact henlarge s v yv r hr (hsize v hlv).1 (hsize v hlv).2 hseedv hvolv q hq'

/-- The 60 r-ball curvature bound along any seed trace: `seed_along_trace_S150` at `(a/3, 3 r)`. -/
theorem seed_along_trace60_S150 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {a c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁) :
    ∃ T₀ ρ₀ K₀ : ℝ, 0 < T₀ ∧ 0 < ρ₀ ∧ 0 < K₀ ∧
      ∀ (s : RegularSlice F.observation) (l : Icc (0 : ℝ) s.history.horizon)
        (hlt : l ≤ sliceTop_S8 s) (y : (s.history.stageAt (sliceTop_S8 s)).Carrier)
        (r : ℝ), 0 < r →
      (∀ v : Icc (0 : ℝ) s.history.horizon, l ≤ v →
        T₀ ≤ (v : ℝ) ∧ r ≤ ρ₀ * Real.sqrt v) →
      (∀ (v : Icc (0 : ℝ) s.history.horizon) (_ : l ≤ v),
        ∃ yv : (s.history.stageAt v).Carrier,
          hasSmallParabolicCurvature s.history v yv (a * r) ∧
          ENNReal.ofReal (c₁ * (a * r) ^ 3) ≤
            ballVolume (s.history.stageMetric (s.history.activeStage v) v) yv (a * r) ∧
          ∃ A : BackwardPointTrace s.history (s.history.activeStage v)
              (s.history.activeStage (sliceTop_S8 s))
              (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) y,
            A.point (s.history.activeStage v) le_rfl
              (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) = yv) →
      ∀ A : BackwardPointTrace s.history (s.history.activeStage l)
          (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hlt) y,
        ∀ (v : Icc (0 : ℝ) s.history.horizon) (hlv : l ≤ v),
          ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
            (A.point (s.history.activeStage v) (s.history.activeStage_mono hlv)
              (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2))) (60 * r),
            Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
              (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ K₀ / r ^ 2 := by
  obtain ⟨T₀, ρ₀, K₀, hT, hρ, hK, h⟩ := seed_along_trace_S150 Hp (a := a / 3) (by positivity) hc₁
  refine ⟨T₀, ρ₀ / 3, K₀ / 9, hT, by positivity, by positivity, ?_⟩
  intro s l hlt y r hr hsize hseed A v hlv q hq
  have e : a / 3 * (3 * r) = a * r := by ring
  have hr3 : 0 < 3 * r := by positivity
  have hs3 : ∀ w : Icc (0 : ℝ) s.history.horizon, l ≤ w →
      T₀ ≤ (w : ℝ) ∧ 3 * r ≤ ρ₀ * Real.sqrt w := by
    intro w hw
    obtain ⟨h1, h2⟩ := hsize w hw
    refine ⟨h1, ?_⟩
    have : ρ₀ / 3 * Real.sqrt w = ρ₀ * Real.sqrt w / 3 := by ring
    rw [this] at h2
    linarith only [h2]
  have hseed3 : ∀ (w : Icc (0 : ℝ) s.history.horizon) (_ : l ≤ w),
        ∃ yv : (s.history.stageAt w).Carrier,
          hasSmallParabolicCurvature s.history w yv (a / 3 * (3 * r)) ∧
          ENNReal.ofReal (c₁ * (a / 3 * (3 * r)) ^ 3) ≤
            ballVolume (s.history.stageMetric (s.history.activeStage w) w) yv (a / 3 * (3 * r)) ∧
          ∃ A : BackwardPointTrace s.history (s.history.activeStage w)
              (s.history.activeStage (sliceTop_S8 s))
              (s.history.activeStage_mono (show w ≤ sliceTop_S8 s from w.property.2)) y,
            A.point (s.history.activeStage w) le_rfl
              (s.history.activeStage_mono (show w ≤ sliceTop_S8 s from w.property.2)) = yv := by
    intro w hw
    rw [e]
    exact hseed w hw
  have hq3 : q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
      (A.point (s.history.activeStage v) (s.history.activeStage_mono hlv)
        (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2))) (20 * (3 * r)) := by
    have e2 : 20 * (3 * r) = 60 * r := by ring
    rwa [e2]
  have hb := h s l hlt y (3 * r) hr3 hs3 hseed3 A v hlv q hq3
  refine hb.trans (le_of_eq ?_)
  field_simp
  ring

/-- `traced_of_seeds_ball_S95` with the extra `hbar` premise `hbd60`: the curvature bound `K₀/r²` on the `60 r`-balls about
the seed trace `A` (the tube of F-S146-1 / F-S150-1).  Constants: `T₀ := max`, `ρ₀ := min`, `K₀ := max` of the 20 r and 60 r ones. -/
theorem traced_of_seeds_ball_S150 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    {a c₁ : ℝ} (ha : 0 < a) (hc₁ : 0 < c₁) :
    ∃ T₀ ρ₀ K₀ : ℝ, 0 < T₀ ∧ 0 < ρ₀ ∧ 0 < K₀ ∧
      ∀ (s : RegularSlice F.observation) (l : Icc (0 : ℝ) s.history.horizon)
        (hlt : l ≤ sliceTop_S8 s) (y : (s.history.stageAt (sliceTop_S8 s)).Carrier)
        (r τ : ℝ), 0 < r → 0 < τ →
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
      (∀ A : BackwardPointTrace s.history (s.history.activeStage l)
          (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hlt) y,
        (∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : l ≤ v) (hvt : v ≤ sliceTop_S8 s),
          ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
            (A.point (s.history.activeStage v) (s.history.activeStage_mono hav)
              (s.history.activeStage_mono hvt)) (20 * r),
          Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
            (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ K₀ / r ^ 2) →
        (∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : l ≤ v) (hvt : v ≤ sliceTop_S8 s),
          ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
            (A.point (s.history.activeStage v) (s.history.activeStage_mono hav)
              (s.history.activeStage_mono hvt)) (60 * r),
          Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
            (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ K₀ / r ^ 2) →
        ∀ (i : Fin (sliceTowerHistory_CX2 s).eventCount)
          (hf : (sliceTowerHistory_CX2 s).activeStage
            (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) l) ≤ i.castSucc)
          (hl : i.succ ≤ (sliceTowerHistory_CX2 s).activeStage
            (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s))),
          (sliceTowerHistory_CX2 s).time i.succ ∈ Ioc (s.time - τ * r ^ 2) s.time →
          ∀ U : Set ((sliceTowerHistory_CX2 s).stage i.succ).Carrier,
          U ⊆ riemannianBallOf ((sliceTowerHistory_CX2 s).event i).outputMetric
            ((traceAtOfRestriction_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s)
              (hat := hlt) A).point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) →
          IsPreconnected U →
          (∀ y ∈ U, metricScalarAt ((sliceTowerHistory_CX2 s).event i).outputMetric y ≤
            (9 * K₀) / r ^ 2) →
          ∀ (x : ((sliceTowerHistory_CX2 s).event i).incoming.terminalRegularOpen)
            (y : ((sliceTowerHistory_CX2 s).stage i.succ).Carrier),
            y ∈ U → ((sliceTowerHistory_CX2 s).event i).RegularCrossing x.val y →
            U ⊆ interior (range ((sliceTowerHistory_CX2 s).event i).oldOutput)) →
      s.history.isTracedRegion (sliceTop_S8 s) y (2 * r) (τ * r ^ 2) (K₀ / r ^ 2) := by
  obtain ⟨T₁, ρ₁, K₁, hT₁, hρ₁, hK₁, h1⟩ := seed_along_trace_S150 Hp ha hc₁
  obtain ⟨T₂, ρ₂, K₂, hT₂, hρ₂, hK₂, h2⟩ := seed_along_trace60_S150 Hp ha hc₁
  refine ⟨max T₁ T₂, min ρ₁ ρ₂, max K₁ K₂, lt_max_of_lt_left hT₁, lt_min hρ₁ hρ₂,
    lt_max_of_lt_left hK₁, ?_⟩
  intro s l hlt y r τ hr hτ hexp hl hsize hseed hbar
  have hK : 0 < max K₁ K₂ := lt_max_of_lt_left hK₁
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hsize1 : ∀ v : Icc (0 : ℝ) s.history.horizon, l ≤ v → T₁ ≤ (v : ℝ) ∧ r ≤ ρ₁ * Real.sqrt v := by
    intro v hv
    obtain ⟨h1', h2'⟩ := hsize v hv
    refine ⟨(le_max_left _ _).trans h1', h2'.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
  have hsize2 : ∀ v : Icc (0 : ℝ) s.history.horizon, l ≤ v → T₂ ≤ (v : ℝ) ∧ r ≤ ρ₂ * Real.sqrt v := by
    intro v hv
    obtain ⟨h1', h2'⟩ := hsize v hv
    refine ⟨(le_max_right _ _).trans h1', h2'.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
  obtain ⟨_, _, _, A, _⟩ := hseed l le_rfl
  have hA20 : ∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : l ≤ v) (hvt : v ≤ sliceTop_S8 s),
      ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
        (A.point (s.history.activeStage v) (s.history.activeStage_mono hav)
          (s.history.activeStage_mono hvt)) (20 * r),
      Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
        (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ max K₁ K₂ / r ^ 2 :=
    fun v hav hvt q hq =>
      (h1 s l hlt y r hr hsize1 hseed A v hav q hq).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) hr2)
  have hA60 : ∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : l ≤ v) (hvt : v ≤ sliceTop_S8 s),
      ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
        (A.point (s.history.activeStage v) (s.history.activeStage_mono hav)
          (s.history.activeStage_mono hvt)) (60 * r),
      Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
        (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ max K₁ K₂ / r ^ 2 :=
    fun v hav hvt q hq =>
      (h2 s l hlt y r hr hsize2 hseed A v hav q hq).trans
        (div_le_div_of_nonneg_right (le_max_right _ _) hr2)
  exact slice_seed_tracedRegion_ball_S95 s hτ hr hK hexp hl hlt
    (mem_riemannianBallOf_self_O13 _ y hr) A hA20
    (fun i hf hl' ht U hU => hbar A hA20 hA60 i hf hl' ht U hU)

end GC.LongTime.Ch12
