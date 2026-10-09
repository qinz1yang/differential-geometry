import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WeakStrong_S85
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.GronwallLog_S45

set_option autoImplicit false

/-!
# CH12-S104 / G1a: logarithmic Grönwall on a stage piece, derivative only in the interior

`gronwall_variation_open_S104` is `metric_variation_S45` with the flow hypotheses on `Ioo a b` and only
`ContinuousOn` on `Icc a b` (a piece of the dyadic window between two events: the stage flow has no
value/derivative at the event end, only a left limit).
`stage_inner_hasDerivAt_S104` : `∂_ρ g_ρ(V,V) = -2 Ric_ρ(V,V)` at interior times of a stage.
`stage_variation_S104` : the two combine, with the defect hypothesis in the form `DefectAt_S85`.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u v

theorem gronwall_variation_open_S104 {gv rv : ℝ → ℝ} {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : ContinuousOn gv (Icc a b))
    (hflow : ∀ ρ ∈ Ioo a b, HasDerivAt gv (-2 * rv ρ) ρ)
    (hdef : ∀ ρ ∈ Ioo a b, |2 * ρ * rv ρ + gv ρ| ≤ η * gv ρ) :
    gv a / a ≤ (b / a) ^ η * (gv b / b) ∧ gv b / b ≤ (b / a) ^ η * (gv a / a) := by
  have hpos : ∀ ρ ∈ Icc a b, 0 < ρ := fun ρ hρ => ha.trans_le hρ.1
  have hφc : ContinuousOn (fun x => gv x / x) (Icc a b) :=
    hc.div continuousOn_id (fun x hx => (hpos x hx).ne')
  have hφ : ∀ s ∈ Ioo a b, HasDerivAt (fun x => gv x / x)
      ((-2 * rv s * s - gv s) / s ^ 2) s := by
    intro s hs
    have hs0 : s ≠ 0 := (hpos s ⟨hs.1.le, hs.2.le⟩).ne'
    have h := (hflow s hs).div (hasDerivAt_id' s) hs0
    convert h using 1
    ring
  have hbd : ∀ s ∈ Ioo a b, |(-2 * rv s * s - gv s) / s ^ 2| ≤ η / s * (gv s / s) := by
    intro s hs
    have hspos : 0 < s := hpos s ⟨hs.1.le, hs.2.le⟩
    have h1 := hdef s hs
    rw [abs_div, abs_of_pos (pow_pos hspos 2), div_le_iff₀ (pow_pos hspos 2)]
    have : |-2 * rv s * s - gv s| = |2 * s * rv s + gv s| := by
      rw [← abs_neg]; congr 1; ring
    rw [this]
    calc |2 * s * rv s + gv s| ≤ η * gv s := h1
      _ = η / s * (gv s / s) * s ^ 2 := by field_simp
  set φ : ℝ → ℝ := fun x => gv x / x with hφdef
  have hbpos : 0 < b := ha.trans_le hab
  have hp1 : 0 < b ^ η := Real.rpow_pos_of_pos hbpos _
  have hp2 : 0 < a ^ η := Real.rpow_pos_of_pos ha _
  have hrc : ∀ e : ℝ, ContinuousOn (fun x : ℝ => x ^ e) (Icc a b) := fun e x hx =>
    (Real.continuousAt_rpow_const x e (Or.inl (hpos x hx).ne')).continuousWithinAt
  constructor
  · -- lower comparison: ψ(x) = φ x * x^η is monotone
    have hψ : ∀ s ∈ Ioo a b, HasDerivAt (fun x => φ x * x ^ η)
        ((-2 * rv s * s - gv s) / s ^ 2 * s ^ η + φ s * (η * s ^ (η - 1))) s := fun s hs =>
      (hφ s hs).mul (Real.hasDerivAt_rpow_const (Or.inl (hpos s ⟨hs.1.le, hs.2.le⟩).ne'))
    have hmono : MonotoneOn (fun x => φ x * x ^ η) (Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      · exact hφc.mul (hrc η)
      · rw [interior_Icc]
        exact fun s hs => (hψ s hs).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have hspos : 0 < s := hpos s ⟨hs.1.le, hs.2.le⟩
        rw [(hψ s hs).deriv]
        have h1 : s ^ (η - 1) = s ^ η / s := by
          rw [Real.rpow_sub hspos, Real.rpow_one]
        have h2 := (abs_le.mp (hbd s hs)).1
        have h3 : 0 < s ^ η := Real.rpow_pos_of_pos hspos _
        rw [h1]
        have : (-2 * rv s * s - gv s) / s ^ 2 * s ^ η + φ s * (η * (s ^ η / s)) =
            ((-2 * rv s * s - gv s) / s ^ 2 + η / s * φ s) * s ^ η := by ring
        rw [this]
        exact mul_nonneg (by simp only [hφdef]; linarith) h3.le
    have key := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    simp only [hφdef] at key
    rw [Real.div_rpow hbpos.le ha.le, div_mul_eq_mul_div, le_div_iff₀ hp2]
    linarith [key]
  · -- upper comparison: ψ(x) = φ x * x^(-η) is antitone
    have hψ : ∀ s ∈ Ioo a b, HasDerivAt (fun x => φ x * x ^ (-η))
        ((-2 * rv s * s - gv s) / s ^ 2 * s ^ (-η) + φ s * (-η * s ^ (-η - 1))) s := fun s hs =>
      (hφ s hs).mul (Real.hasDerivAt_rpow_const (Or.inl (hpos s ⟨hs.1.le, hs.2.le⟩).ne'))
    have hanti : AntitoneOn (fun x => φ x * x ^ (-η)) (Icc a b) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      · exact hφc.mul (hrc (-η))
      · rw [interior_Icc]
        exact fun s hs => (hψ s hs).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        have hspos : 0 < s := hpos s ⟨hs.1.le, hs.2.le⟩
        rw [(hψ s hs).deriv]
        have h1 : s ^ (-η - 1) = s ^ (-η) / s := by
          rw [Real.rpow_sub hspos, Real.rpow_one]
        have h2 := (abs_le.mp (hbd s hs)).2
        have h3 : 0 < s ^ (-η) := Real.rpow_pos_of_pos hspos _
        rw [h1]
        have : (-2 * rv s * s - gv s) / s ^ 2 * s ^ (-η) + φ s * (-η * (s ^ (-η) / s)) =
            ((-2 * rv s * s - gv s) / s ^ 2 - η / s * φ s) * s ^ (-η) := by ring
        rw [this]
        exact mul_nonpos_of_nonpos_of_nonneg (by simp only [hφdef]; linarith) h3.le
    have key := hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    simp only [hφdef, Real.rpow_neg hbpos.le, Real.rpow_neg ha.le, ← div_eq_mul_inv] at key
    rw [div_le_div_iff₀ hp1 hp2] at key
    rw [Real.div_rpow hbpos.le ha.le, div_mul_eq_mul_div, le_div_iff₀ hp2]
    linarith [key]

/-- Interior time derivative of the stage metric: `∂_ρ g_ρ(V,V) = -2 Ric_ρ(V,V)`.  `hρ` : `ρ` lies in the
open interval where the stage `j` is the active one (between its start time and the next event/horizon). -/
theorem stage_inner_hasDerivAt_S104 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1))
    (z : (K.stage j).Carrier) (V : TangentSpace ThreeModel z) {ρ : ℝ}
    (hρ : ρ ∈ interior (K.stageDomain j)) :
    HasDerivAt (fun r => (K.stageMetric j r).inner z V V)
      (-2 * ricciTensor (K.stageMetric j ρ) z V V) ρ := by
  revert z V
  cases j using Fin.lastCases with
  | last =>
    intro z V
    have hdom : K.stageDomain (Fin.last K.eventCount) =
        Icc (K.time (Fin.last K.eventCount)) K.horizon := by
      ext τ
      exact ObservedHistory.mem_stageDomain_last K τ
    rw [hdom, interior_Icc] at hρ
    have hlt : K.time (Fin.last K.eventCount) < K.horizon := hρ.1.trans hρ.2
    have hm : ∀ τ, K.stageMetric (Fin.last K.eventCount) τ = (K.finalSlab hlt).flow.base.metric τ :=
      fun τ => ObservedHistory.stageMetric_last_of_lt (H := K) (h := hlt) τ
    simp only [hm]
    have h := DifferentialGeometry.PDE.RicciFlow.metricDerivAt (I := ThreeModel)
      (K.finalSlab hlt).flow (K.finalSlab hlt).equation ⟨ρ, hρ⟩ z V V
    refine h.congr_deriv ?_
    have e : (K.finalSlab hlt).flow.ricciAt ρ z (vec2 V V) =
        ricciTensor ((K.finalSlab hlt).flow.base.metric ρ) z V V :=
      metricRicciAt_apply_eq_ricciTensor _ z V V
    rw [e]
  | cast i =>
    intro z V
    have hdom : K.stageDomain i.castSucc = Ico (K.time i.castSucc) (K.time i.succ) := by
      rw [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
    rw [hdom, interior_Ico] at hρ
    simp only [ObservedHistory.stageMetric_castSucc_apply]
    have h := DifferentialGeometry.PDE.RicciFlow.metricDerivAt (I := ThreeModel)
      (K.event i).incoming.flow (K.event i).incoming.equation ⟨ρ, hρ⟩ z V V
    refine h.congr_deriv ?_
    have e : (K.event i).incoming.flow.ricciAt ρ z (vec2 V V) =
        ricciTensor ((K.event i).incoming.flow.base.metric ρ) z V V :=
      metricRicciAt_apply_eq_ricciTensor _ z V V
    rw [e]

end GC.LongTime.Ch12
