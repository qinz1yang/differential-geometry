import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862SeedsKL82_O42

/-!
# CH12-O42 G1b: KL84.1(c) enlargement from the premises of `kl82_1_O36`

Tower-history form (as `enlarged_rm_tower_O37`), but the seed comes from
`seeds_from_kl82_O42`, so the curvature constant `B` depends on `w` and `A` only — not on the
a-priori trace bound `K` (lead ruling (1) of the O42 brief).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open GC.LongTime

namespace GC.LongTime.Ch12

universe u

/-- KL84.1(c) on the moving ball `B_v(X(v), 20 A r0)`, `v ∈ [top − c r0², top]`, from the
premises of `kl82_1_O36` at `(top, x0, r0)` with `τ = τ₀`; `B` is independent of `K`. -/
theorem enlarged_rm_kl82_O42
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) (A : ℝ) (hA : 0 < A) {w : ℝ} (hw : 0 < w) :
    ∃ τ₀ c T ρ B : ℝ, 0 < τ₀ ∧ τ₀ ≤ 1 ∧ 0 < c ∧ c ≤ τ₀ ∧ 0 < T ∧ 0 < ρ ∧ 0 < B ∧
      ∀ (s : RegularSlice F.observation) (top : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon),
        (top : ℝ) ≤ s.time →
        ∀ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hat : a ≤ top)
          (x0 : ((sliceTowerHistory_CX2 s).stageAt top).Carrier)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage top)
            ((sliceTowerHistory_CX2 s).activeStage_mono hat) x0)
          (r0 K : ℝ), 0 < r0 → (a : ℝ) = top - τ₀ * r0 ^ 2 →
        (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
              ((sliceTowerHistory_CX2 s).activeStage v) v)
              (X.point ((sliceTowerHistory_CX2 s).activeStage v)
                ((sliceTowerHistory_CX2 s).activeStage_mono hav)
                ((sliceTowerHistory_CX2 s).activeStage_mono hvt)) r0,
            ∃ A' : BackwardPointTrace (sliceTowerHistory_CX2 s)
                ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage v)
                ((sliceTowerHistory_CX2 s).activeStage_mono hav) q,
              A'.isRmBoundedBy (hat := hav) K) →
        (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
              ((sliceTowerHistory_CX2 s).activeStage v) v)
              (X.point ((sliceTowerHistory_CX2 s).activeStage v)
                ((sliceTowerHistory_CX2 s).activeStage_mono hav)
                ((sliceTowerHistory_CX2 s).activeStage_mono hvt)) r0,
            SectionalBoundedBelowAt ((sliceTowerHistory_CX2 s).stageMetric
              ((sliceTowerHistory_CX2 s).activeStage v) v) q (-(r0 ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r0 ^ 3) ≤
          ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage top) top) x0 r0 →
        ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvt : v ≤ top),
          (top : ℝ) - c * r0 ^ 2 ≤ v → T ≤ v → r0 ≤ ρ * Real.sqrt v →
          ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
              ((sliceTowerHistory_CX2 s).activeStage v) v)
            (X.point ((sliceTowerHistory_CX2 s).activeStage v)
              ((sliceTowerHistory_CX2 s).activeStage_mono hav)
              ((sliceTowerHistory_CX2 s).activeStage_mono hvt)) (20 * (A * r0)),
            Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric
                ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
              (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric
                ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ B / r0 ^ 2 := by
  obtain ⟨τ₀, α, c, c₁, hτ₀, hτ₀1, hα, hc, hcτ, hc₁, hseed⟩ := seeds_from_kl82_O42.{u} hw
  obtain ⟨T, ρ, B, hT, hρ, hB, henlarge⟩ :=
    enlarged_rm_bound_of_seed_O4 Hp (div_pos hα hA) hc₁
  obtain ⟨Phi, hPhi, hpinch⟩ := pinching_prefix_O37 Hp
  refine ⟨τ₀, c, T, ρ / A, B / A ^ 2, hτ₀, hτ₀1, hc, hcτ, hT, by positivity, by positivity, ?_⟩
  intro s top hts a hat x0 X r0 K hr0 ha hSF hsec hvol v hav hvt hv hTv hrv q hq
  obtain ⟨hsmall, hvolume⟩ := hseed (sliceTowerHistory_CX2 s) top x0 r0 K a hat X
    hPhi (fun v' hv' => hpinch s v' ((Subtype.coe_le_coe.mpr hv').trans hts)) hr0 ha hSF hsec
    hvol v hav hvt hv
  have hAr : A * r0 ≤ ρ * Real.sqrt v := by
    calc A * r0 ≤ A * (ρ / A * Real.sqrt v) := mul_le_mul_of_nonneg_left hrv hA.le
      _ = ρ * Real.sqrt v := by field_simp
  have he : α / A * (A * r0) = α * r0 := by field_simp
  have hsmall' : hasSmallParabolicCurvature (sliceTowerHistory_CX2 s) v
      (X.point ((sliceTowerHistory_CX2 s).activeStage v)
        ((sliceTowerHistory_CX2 s).activeStage_mono hav)
        ((sliceTowerHistory_CX2 s).activeStage_mono hvt)) (α / A * (A * r0)) := by
    rwa [he]
  have hvolume' : ENNReal.ofReal (c₁ * (α / A * (A * r0)) ^ 3) ≤
      ballVolume ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v)
        (X.point ((sliceTowerHistory_CX2 s).activeStage v)
          ((sliceTowerHistory_CX2 s).activeStage_mono hav)
          ((sliceTowerHistory_CX2 s).activeStage_mono hvt)) (α / A * (A * r0)) := by
    rwa [he]
  have h := henlarge (sliceTowerIndex_CX2 s) v _ (A * r0) (mul_pos hA hr0) hTv hAr hsmall'
    hvolume' q hq
  have hnorm : B / (A * r0) ^ 2 = B / A ^ 2 / r0 ^ 2 := by rw [mul_pow, div_mul_eq_div_div]
  exact h.trans_eq hnorm

end GC.LongTime.Ch12
