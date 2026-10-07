import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedFamily_S130

/-!
# CH12-O79 G2: `good_of_improved_R_O79` — the final material tail of R6 (`[FROZEN] CH12-O79 G2`)

Statement = binder type of `frozen_good_R_O79` (`build-logs/ch12/scratch/FrozenO79.lean`), on a
general `ObservedHistory`.  Inputs: a centre trace `X` on `[a, u]`; the improved-region bound
`|Rm| ≤ M r⁻²` on every `B_v(X v, r/4)` (the `M_ε` corollary of the regional KL82, review R6 §4.3);
the outgoing retention `B_out(X(i.succ), r/4) ⊆ interior (range oldOutput)` at the events of
`[a, u]` (from `Reg`'s whole-inner-ball retention, D-R6-4).
Route (review R6 §4.4): `traced_family_of_trace_S130` with `ρ := r/80` (`20ρ = r/4`,
`2ρ = r/40`), `K_S130 := M/6400` (`K_S130/ρ² = M/r²`), `τ_S130 := 6400 τ₂`
(`τ_S130 ρ² = τ₂ r²`, `9 K_S130 τ_S130 = 9 M τ₂ ≤ log 2/4 < log 2`), applied at every
`w ∈ [u - τ₁ r², u]` (`a + τ₂ r² ≤ w` from `(τ₁ + τ₂) r² ≤ u - a`); then radius/bound monotonicity
to `κ r ≤ r/40`, `M/r² ≤ K r⁻²`.  No `B(A)`, no drift, no O42 tail.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open scoped NNReal Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- **G2** (`[FROZEN] CH12-O79 G2`): improved region + outgoing retention ⇒ `Good`'s traced
regions, through S130 at scale `r/80`. -/
theorem good_of_improved_R_O79 (H : ObservedHistory.{u}) {a u : Icc (0 : ℝ) H.horizon}
    (hau : a ≤ u) {x : (H.stageAt u).Carrier}
    (X : BackwardPointTrace H (H.activeStage a) (H.activeStage u) (H.activeStage_mono hau) x)
    {r M τ₁ τ₂ κ K : ℝ} (hr : 0 < r) (hM : 0 < M) (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂)
    (hlog : 36 * M * τ₂ ≤ Real.log 2) (hwin : (a : ℝ) + (τ₁ + τ₂) * r ^ 2 ≤ u)
    (hκ : 0 < κ) (hκ40 : κ ≤ 1 / 40) (hMK : M ≤ K)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvu : v ≤ u),
      ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvu)) (r / 4),
        Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
          (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ M / r ^ 2)
    (hret : ∀ (i : Fin H.eventCount) (hf : H.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage u),
      riemannianBallOf (H.event i).outputMetric
          (X.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (r / 4) ⊆
        interior (range (H.event i).oldOutput)) :
    ∃ (a' : Icc (0 : ℝ) H.horizon) (ha' : a' ≤ u)
      (X' : BackwardPointTrace H (H.activeStage a') (H.activeStage u) (H.activeStage_mono ha') x),
      (a' : ℝ) = u - τ₁ * r ^ 2 ∧
      ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a' ≤ w) (hwu : w ≤ u),
        H.isTracedRegion w
          (X'.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwu))
          (κ * r) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹) := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hτ₁r : 0 < τ₁ * r ^ 2 := by positivity
  have hτ₂r : 0 < τ₂ * r ^ 2 := by positivity
  have ha0 : (0 : ℝ) ≤ a := a.2.1
  have hwin' : (a : ℝ) + τ₂ * r ^ 2 ≤ (u : ℝ) - τ₁ * r ^ 2 := by nlinarith
  let a' : Icc (0 : ℝ) H.horizon :=
    ⟨(u : ℝ) - τ₁ * r ^ 2, by linarith, (sub_le_self _ hτ₁r.le).trans u.2.2⟩
  have haa' : a ≤ a' := show (a : ℝ) ≤ (u : ℝ) - τ₁ * r ^ 2 by linarith
  have ha'u : a' ≤ u := show (u : ℝ) - τ₁ * r ^ 2 ≤ u from sub_le_self _ hτ₁r.le
  refine ⟨a', ha'u, X.restrictFirst (H.activeStage_mono haa') (H.activeStage_mono ha'u), rfl, ?_⟩
  intro w haw hwu
  have hρ : 0 < r / 80 := by positivity
  have hK' : 0 < M / 6400 := by positivity
  have hτ' : 0 < 6400 * τ₂ := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.exp (9 * (M / 6400) * (6400 * τ₂)) < 2 := by
    have e : 9 * (M / 6400) * (6400 * τ₂) = 9 * M * τ₂ := by ring
    rw [e]
    calc Real.exp (9 * M * τ₂) ≤ Real.exp (Real.log 2 / 4) := Real.exp_le_exp.mpr (by linarith)
      _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have e1 : (20 : ℝ) * (r / 80) = r / 4 := by ring
  have e2 : M / 6400 / (r / 80) ^ 2 = M / r ^ 2 := by field_simp; ring
  have e3 : 6400 * τ₂ * (r / 80) ^ 2 = τ₂ * r ^ 2 := by ring
  have hw : (a : ℝ) + 6400 * τ₂ * (r / 80) ^ 2 ≤ (w : ℝ) := by
    rw [e3]
    have : (u : ℝ) - τ₁ * r ^ 2 ≤ w := haw
    linarith
  have hS := traced_family_of_trace_S130 H hau hτ' hρ hK' hexp X
    (fun v hav hvt q hq => by
      rw [e2]
      exact hbound v hav hvt q (by rw [e1] at hq; exact hq))
    (fun i hf hl U hU _ _ _ _ _ _ => by
      rw [e1] at hU
      exact hU.trans (hret i hf hl))
    w hw hwu
  rw [e2] at hS
  have hκr : κ * r ≤ 2 * (r / 80) := by nlinarith
  have hMr : M / r ^ 2 ≤ K * (r ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hMK (by positivity)
  exact hS.mono (mul_pos hκ hr) hκr hτ₂r e3.symm.le (by positivity) hMr

end GC.LongTime.Ch12
