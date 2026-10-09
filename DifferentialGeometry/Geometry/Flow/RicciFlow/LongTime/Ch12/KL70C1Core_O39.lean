import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StrongNeckV2_O31
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Pinch_O16
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciLowerBound
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

/-!
# CH12-O39, group 1: C1 core of KL70.2 (c) — full-window Hamilton–Ivey on the hStrong v2 flow

`[FROZEN] CH12-O39`.  The neck branch of hStrong v2 (`[FROZEN v2] CH12-O31 hStrong`) gives a local
flow `S` on an open `U ∋ x` over `[s.time − R(x)⁻¹, s.time]` together with the full-window binding
`S(v) = E(v)^* g_H(v)` (`E : RegularOpenBackwardTrace_O31`).  Through that binding the slice pinching
`hpinchS_O16` of the actual history transfers to `S` on the whole window (R4 point 2: the v1
terminal-only identification would give this at `v = s.time` only):

* `pinch_on_trace_O39`: `sec(S v) ≥ −Φ(R_{S v})` at every point of `U`, every `v` of the window;
* `eta_of_pinching_O39`: `η(R) := Φ(Λ R)/R → 0` (`Φ` admissible), and `R' ≤ Λ R ⇒ Φ R' ≤ η(R) R`;
* `C1_core_O39`: under a window scalar bound `R_{S v} ≤ Λ R(x)` on `U`,
  `sec(S v) ≥ −η(R(x)) R(x)` on the window — the sectional clause of the C1 sub-statement.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **Full-window Hamilton–Ivey on a bound backward flow.**  If `S(v) = E(v)^* g_H(v)` for every
`v ≥ a` of the slice history, then `S(v)` is `Φ`-pinched at every point of `U` for every such `v`
(`Φ` the admissible pinching function of `hpinchS_O16`). -/
theorem pinch_on_trace_O39 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
      ∀ (s : RegularSlice F.observation) (U : TopologicalSpace.Opens s.stage.Carrier)
        (a : Icc (0 : ℝ) s.history.horizon)
        (E : RegularOpenBackwardTrace_O31 s.history (s.history.activeStage a) U)
        {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := U) D),
        (∀ v : Icc (0 : ℝ) s.history.horizon, ∀ hav : a ≤ v,
          S.base.metric v =
            localPullMetric (s.history.stageMetric (s.history.activeStage v) v)
              (E.atStage (s.history.activeStage v) (s.history.activeStage_mono hav)
                (Fin.le_last _))
              (E.atStage_isLocalDiffeomorph _ _ _)) →
        ∀ v : Icc (0 : ℝ) s.history.horizon, a ≤ v → ∀ q : U,
          SectionalBoundedBelowAt (S.base.metric v) q
            (-(Phi (metricScalarAt (S.base.metric v) q))) := by
  obtain ⟨Phi, hPhi, hpin⟩ := hpinchS_O16 Hp
  refine ⟨Phi, hPhi, fun s U a E D S hbind v hav q => ?_⟩
  rw [hbind v hav]
  apply sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt
  rw [curvatureOperatorLowerBoundAt_localPullMetric_iff, metricScalarAt_localPull]
  exact hpin s v (by change (v : ℝ) ≤ s.time; exact v.2.2) _

/-- `η(R) := Φ(Λ R)/R → 0` for an admissible pinching function `Φ` and `Λ > 0`. -/
theorem eta_of_pinching_O39 {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    {Λ : ℝ} (hΛ : 0 < Λ) : Tendsto (fun R : ℝ => Phi (Λ * R) / R) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => Phi (Λ * R) / (Λ * R)) atTop (𝓝 0) :=
    hPhi.quotientTendsto.comp (tendsto_id.const_mul_atTop hΛ)
  have h2 : Tendsto (fun R : ℝ => Λ * (Phi (Λ * R) / (Λ * R))) atTop (𝓝 (Λ * 0)) :=
    h1.const_mul Λ
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  field_simp

/-- Pointwise step: `R' ≤ Λ R`, `0 < R` ⇒ `−Φ R' ≥ −(Φ(Λ R)/R) R`. -/
theorem neg_eta_le_O39 {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    {Λ R R' : ℝ} (hR : 0 < R) (hle : R' ≤ Λ * R) :
    -(Phi (Λ * R) / R * R) ≤ -Phi R' := by
  rw [div_mul_cancel₀ _ hR.ne']
  exact neg_le_neg (hPhi.mono hle)

/-- **C1 core (sectional clause).**  For the neck-branch data of hStrong v2 at `x` (window
`[s.time − R(x)⁻¹, s.time]`, `a = s.time − R(x)⁻¹`, full-window binding) and a window scalar bound
`R_{S v} ≤ Λ R(x)` on `U`: `sec(S v) ≥ −η R(x)` with `η = Φ(Λ R(x))/R(x)`
(`→ 0` as `R(x) → ∞`, `eta_of_pinching_O39`). -/
theorem C1_core_O39 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
      ∀ Λ : ℝ, 0 < Λ →
      ∀ (s : RegularSlice F.observation) (x : s.stage.Carrier),
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∀ (U : TopologicalSpace.Opens s.stage.Carrier) (_hxU : x ∈ U)
        (a : Icc (0 : ℝ) s.history.horizon)
        (E : RegularOpenBackwardTrace_O31 s.history (s.history.activeStage a) U)
        (S : SolutionOn (I := ThreeModel) (M := U)
          (RealTimeInterval.closed (s.time - (metricScalarAt s.metric x)⁻¹) s.time
            (sub_le_self _ (inv_nonneg.mpr
              (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
        (a : ℝ) = s.time - (metricScalarAt s.metric x)⁻¹ →
        (∀ v : Icc (0 : ℝ) s.history.horizon, ∀ hav : a ≤ v,
          S.base.metric v =
            localPullMetric (s.history.stageMetric (s.history.activeStage v) v)
              (E.atStage (s.history.activeStage v) (s.history.activeStage_mono hav)
                (Fin.le_last _))
              (E.atStage_isLocalDiffeomorph _ _ _)) →
        (∀ v ∈ Icc (s.time - (metricScalarAt s.metric x)⁻¹) s.time, ∀ q : U,
          metricScalarAt (S.base.metric v) q ≤ Λ * metricScalarAt s.metric x) →
        ∀ v ∈ Icc (s.time - (metricScalarAt s.metric x)⁻¹) s.time, ∀ q : U,
          SectionalBoundedBelowAt (S.base.metric v) q
            (-(Phi (Λ * metricScalarAt s.metric x) / metricScalarAt s.metric x *
              metricScalarAt s.metric x)) := by
  obtain ⟨Phi, hPhi, hpin⟩ := pinch_on_trace_O39 Hp
  refine ⟨Phi, hPhi, fun Λ _hΛ s x hR U _hxU a E S ha hbind hscal v hv q => ?_⟩
  have hRx : 0 < metricScalarAt s.metric x :=
    lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR
  have h0 : 0 ≤ v := by
    have := a.2.1
    rw [ha] at this
    exact this.trans hv.1
  have hvh : v ≤ s.history.horizon := hv.2.trans (sliceTop_S8 s).2.2
  let v' : Icc (0 : ℝ) s.history.horizon := ⟨v, h0, hvh⟩
  have hav : a ≤ v' := by
    change (a : ℝ) ≤ v
    rw [ha]
    exact hv.1
  exact (hpin s U a E S hbind v' hav q).mono (neg_eta_le_O39 hPhi hRx (hscal v hv q))

end GC.LongTime.Ch12
