import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TruncatedNeckScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness (metricScalarAt_restrictOpen)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

variable (H : ObservedHistory.{u})

def HasStrongNeckAt (eps : ℝ) (v : Icc (0 : ℝ) H.horizon) (p : (H.stageAt v).Carrier) : Prop :=
  ∃ (s : ℝ) (G : (H.stage (H.activeStage v)).IncomingSlab (H.time (H.activeStage v)) s),
    (v : ℝ) < s ∧
    (∀ τ ∈ Icc (H.time (H.activeStage v)) (v : ℝ),
      G.flow.base.metric τ = H.stageMetric (H.activeStage v) τ) ∧
    H.HistoryStrongNeck (H.activeStage v) G eps p v

theorem metricScalarAt_backwardSurvivor_eq_stageMetric {first k : Fin (H.eventCount + 1)}
    (hle : first ≤ k) {s t : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s)
    (hG : ∀ τ ∈ Icc (H.time k) t, G.flow.base.metric τ = H.stageMetric k τ)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorDomain first k hle))
    (hslab : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ k),
      ∀ τ ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow τ = H.backwardSurvivorSlabMetric first k hle j hf hl τ)
    (hterm : ∀ τ ∈ Ico (H.time k) s,
      gflow τ = (G.flow.base.metric τ).restrictOpen (H.backwardSurvivorDomain first k hle))
    (m : Fin (H.eventCount + 1)) (hfm : first ≤ m) (hmk : m ≤ k) {v : ℝ}
    (hv : v ∈ H.stageDomain m) (hvt : v ≤ t) (hvs : v < s)
    (z : H.backwardSurvivorDomain first k hle) :
    metricScalarAt (gflow v) z =
      metricScalarAt (H.stageMetric m v) (H.backwardSurvivorMap first k hle m hfm hmk z) := by
  have hleft : H.time m ≤ v := by
    cases m using Fin.lastCases with
    | last =>
      simp only [stageDomain, Fin.lastCases_last, mem_Icc] at hv
      exact hv.1
    | cast i =>
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at hv
      exact hv.1
  by_cases hm : m = k
  · subst hm
    rw [hterm v ⟨hleft, hvs⟩, metricScalarAt_restrictOpen, hG v ⟨hleft, hvt⟩,
      H.backwardSurvivorMap_last]
  · have hmlt : m < k := lt_of_le_of_ne hmk hm
    cases m using Fin.lastCases with
    | last => exact absurd (hmlt.trans_le (Fin.le_last k)) (lt_irrefl _)
    | cast i =>
      have hil : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp hmlt
      have hvi : v ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
        simpa only [stageDomain, Fin.lastCases_castSucc] using hv
      rw [hslab i hfm hil v ⟨hvi.1, hvi.2.le⟩, backwardSurvivorSlabMetric,
        metricScalarAt_localPull, (H.event i).terminal.extendedMetric_before hvi.2,
        metricScalarAt_restrictOpen, backwardSurvivorTerminalMap_val,
        stageMetric_castSucc_apply]

variable {H}

theorem exists_backwardPointTrace_scalar_bounds_of_hasStrongNeckAt {eps : ℝ}
    {t : Icc (0 : ℝ) H.horizon} {y : (H.stageAt t).Carrier} (h : H.HasStrongNeckAt eps t y) :
    0 < metricScalarAt (H.stageMetric (H.activeStage t) t) y ∧
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
      (a : ℝ) = t - (5 * metricScalarAt (H.stageMetric (H.activeStage t) t) y)⁻¹ ∧
      ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          |(metricScalarAt (H.stageMetric (H.activeStage t) t) y)⁻¹ *
              metricScalarAt (H.stageMetric (H.activeStage v) v)
                (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) -
            (1 - metricScalarAt (H.stageMetric (H.activeStage t) t) y * ((v : ℝ) - t))⁻¹| ≤
            2400 * eps := by
  obtain ⟨s, G, hts, hG, first, hle, hfs, gflow, hwin, hslab, hterm, _, z, hz, ⟨nk⟩⟩ := h
  subst hz
  let k := H.activeStage t
  let U := H.backwardSurvivorDomain first k hle
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have htk : H.time k ≤ t := H.activeStage_time_le t
  let S' : SolutionOn (I := ThreeModel) (M := U)
      (RealTimeInterval.closedOpen (H.time first) s hfs) := { base := { metric := gflow } }
  have hS'scalar (v : ℝ) : S'.scalar v z = metricScalarAt (gflow v) z := rfl
  have hGt : G.flow.scalar t z.val = metricScalarAt (H.stageMetric k t) z.val := by
    change metricScalarAt (G.flow.base.metric t) z.val = _
    rw [hG t ⟨htk, le_rfl⟩]
  have hQ' : S'.scalar t z = G.flow.scalar t z.val := by
    rw [hS'scalar, hterm t ⟨htk, hts⟩, metricScalarAt_restrictOpen]
    rfl
  set Q := metricScalarAt (H.stageMetric k t) z.val with hQdef
  have hQpos : 0 < Q := by
    rw [← hGt, ← hQ']
    exact nk.Q_pos
  have hwin' : H.time first ≤ (t : ℝ) - (5 * Q)⁻¹ := by
    have hh : (1 / 5 : ℝ) * (G.flow.scalar t z.val)⁻¹ = (5 * Q)⁻¹ := by
      rw [hGt, mul_inv, one_div]
    rw [← hh]
    exact hwin
  let a : Icc (0 : ℝ) H.horizon := ⟨t - (5 * Q)⁻¹,
    (H.time_nonneg first).trans hwin',
    (sub_le_self _ (inv_nonneg.mpr (by positivity))).trans t.2.2⟩
  have hat : a ≤ t := show (t : ℝ) - (5 * Q)⁻¹ ≤ t from sub_le_self _ (by positivity)
  have hfa : first ≤ H.activeStage a := H.le_activeStage a first hwin'
  refine ⟨hQpos, a, hat, rfl,
    (Classical.choice z.property).restrictFirst hfa (H.activeStage_mono hat), ?_⟩
  intro v hav hvt
  have hfm : first ≤ H.activeStage v := hfa.trans (H.activeStage_mono hav)
  have hpoint : ((Classical.choice z.property).restrictFirst hfa (H.activeStage_mono hat)).point
      (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt) =
      H.backwardSurvivorMap first k hle (H.activeStage v) hfm (H.activeStage_mono hvt) z := rfl
  have hid := H.metricScalarAt_backwardSurvivor_eq_stageMetric hle G
    (fun τ hτ => hG τ hτ) gflow hslab hterm (H.activeStage v) hfm (H.activeStage_mono hvt)
    (H.activeStage_mem v) hvt (lt_of_le_of_lt hvt hts) z
  rw [hpoint, ← hid, ← hS'scalar]
  have hvt' : (v : ℝ) ≤ t := hvt
  have hav' : (t : ℝ) - (5 * Q)⁻¹ ≤ v := hav
  have hr : Q * ((v : ℝ) - t) ∈ Icc (-(1 / 5 : ℝ)) 0 := by
    constructor
    · have hmul := mul_le_mul_of_nonneg_left (show -(5 * Q)⁻¹ ≤ (v : ℝ) - t by linarith)
        hQpos.le
      have hq : Q * -(5 * Q)⁻¹ = -(1 / 5) := by field_simp
      linarith
    · exact mul_nonpos_of_nonneg_of_nonpos hQpos.le (by linarith)
  have hmain := nk.abs_scalar_center_sub_le hr
  rw [hQ', hGt] at hmain
  have htime : (t : ℝ) + Q * ((v : ℝ) - t) / Q = v := by field_simp; ring
  rw [htime] at hmain
  exact hmain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
