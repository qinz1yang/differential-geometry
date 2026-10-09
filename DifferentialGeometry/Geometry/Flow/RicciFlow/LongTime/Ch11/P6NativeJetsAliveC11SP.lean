import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeJetsC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedInnerJetsCXSP

set_option autoImplicit false

/-!
# NJ 的 alive 半边（O-CH11-NATIVE-NJ G1b，后缀 `_C11SP`）

`innerJets_or_born_of_dichotomy_C11SP`：G1 `native_boundedBall_of_SL1_C11SP` 的逐点二分（alive ∨ `Born`）
在一个 patch 球 `B(y, Rwide/√Q)` 上 ⇒ 要么 patch 内有 born 点，要么 `B_Q(y, Rr)`（`Rr < Rwide`）上全阶
jets `≤ J k`。`J` 只依赖 `Rr Rwide θ K0`，在 history / 时刻 / 点之前选（NJ 合同的一致性要求）。
alive patch 走 CXSP `exists_inner_jets_of_traced_region_CXSP`；born patch 是 NJ 余下的 repair（state §G1）。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- **G1b（PROVED）**：逐点 alive / born 二分 ⇒ born 点存在，或 patch 内球全阶 jets 一致有界。 -/
theorem innerJets_or_born_of_dichotomy_C11SP (Rr Rwide θ K0 : ℝ) (hRr : 0 ≤ Rr)
    (hRR : Rr < Rwide) (hθ : 0 < θ) (hK0 : 0 < K0) :
    ∃ J : ℕ → ℝ, (∀ k, 1 ≤ J k) ∧
      ∀ (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier)
        (Q : ℝ) (hQ : 0 < Q) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t),
        (a : ℝ) = (t : ℝ) - θ / Q →
      ∀ Born : (H.stageAt t).Carrier → Prop,
        (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
              (H.activeStage_mono hat) x, B.isRmBoundedBy (hat := hat) (K0 * Q)) ∨ Born x) →
        (∃ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          Born x) ∨
        ∀ k : ℕ, ∀ z ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) y Rr,
          curvDerivNorm k (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) z ≤ J k := by
  obtain ⟨J, hJ, hin⟩ := exists_inner_jets_of_traced_region_CXSP Rr Rwide θ K0 hRr hRR hθ hK0
  refine ⟨J, hJ, ?_⟩
  intro H t y Q hQ a hat ha Born hdich
  by_cases hb : ∃ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y
      (Rwide / Real.sqrt Q), Born x
  · exact Or.inl hb
  · refine Or.inr ?_
    have hRw : 0 < Rwide := lt_of_le_of_lt hRr hRR
    have htr : H.isTracedRegion t y (Rwide / Real.sqrt Q) (θ / Q) (K0 * Q) :=
      ⟨div_pos hRw (Real.sqrt_pos.mpr hQ), div_pos hθ hQ, a, hat, ha, fun x hx =>
        (hdich x hx).resolve_right fun hB => hb ⟨x, hx, hB⟩⟩
    exact hin H t y Q hQ htr

/-- consumer：G1 的逐点二分（`θ = β0/(m+1)`、`K0 = Km`、`Born` = G1 的 born 分支）直接喂 G1b。 -/
example (Rr Rwide θ K0 : ℝ) (hRr : 0 ≤ Rr) (hRR : Rr < Rwide) (hθ : 0 < θ) (hK0 : 0 < K0)
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier)
    (Q : ℝ) (hQ : 0 < Q) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t)
    (ha : (a : ℝ) = (t : ℝ) - θ / Q)
    (halive : ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y
      (Rwide / Real.sqrt Q), ∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
        (H.activeStage_mono hat) x, B.isRmBoundedBy (hat := hat) (K0 * Q)) :
    ∃ J : ℕ → ℝ, ∀ k : ℕ, ∀ z ∈ riemannianClosedBallOf
        (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) y Rr,
      curvDerivNorm k (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) z ≤ J k := by
  obtain ⟨J, _hJ, hmain⟩ := innerJets_or_born_of_dichotomy_C11SP.{u} Rr Rwide θ K0 hRr hRR hθ hK0
  refine ⟨J, ?_⟩
  rcases hmain H t y Q hQ a hat ha (fun _ => False) (fun x hx => Or.inl (halive x hx)) with
    ⟨_, _, hF⟩ | hjets
  · exact hF.elim
  · exact hjets

end GC.LongTime.Ch11
