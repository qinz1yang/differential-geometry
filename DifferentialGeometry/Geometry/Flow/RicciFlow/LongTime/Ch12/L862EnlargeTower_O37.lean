import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Enlargement_CX12
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84PrefixTransfer_S74

/-!
# CH12-O37 G1: the KL84.1(c) enlargement in tower-history form (FINDING 3 of CH12-O34)

`enlarged_rm_of_traced_family_CX12` is stated on a regular slice at its top time. The restarted
balls of Sublemma 86.6 live in the slice's own tower history `N := sliceTowerHistory_CX2 s` at
an arbitrary earlier time `u ≤ s.time`. The local seed step `seeds_of_traced_family_CX12` is
already generic in the history, and the enlargement `enlarged_rm_bound_of_seed_O4` is already
stated on tower histories; the only slice-specific input is the Hamilton–Ivey pinching, which is
transported to the whole prefix `v ≤ s.time` of `N` here (`pinching_prefix_O37`, by
`restrict_stageAt` / `restrict_sliceMetric`, as `canonical_prefix_S74`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- Hamilton–Ivey pinching (one admissible pinching function for all slices) on the whole prefix
`v ≤ s.time` of the slice's own tower history. -/
theorem pinching_prefix_O37
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
      ∀ s : RegularSlice F.observation, ∀ v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon,
        (v : ℝ) ≤ s.time → ∀ x,
        curvatureOperatorLowerBoundAt
          ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) x
          (metricAlgebraicCurvatureTensorAt
            ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) x)
          (Phi (metricScalarAt
            ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
              x)) := by
  obtain ⟨Phi, hPhi, hpin⟩ := slice_pinching_input_CX12 Hp
  refine ⟨Phi, hPhi, fun s v hvs => ?_⟩
  obtain ⟨v1, h0, h1⟩ := v
  set N := sliceTowerHistory_CX2 s
  set cut := sliceTowerTime_CX2 s
  let v' : Icc (0 : ℝ) s.history.horizon := ⟨v1, h0, hvs⟩
  have hst : s.history.stage (s.history.activeStage v') =
      N.stage (N.activeStage (restrictTime_CX2 N cut v')) := N.restrict_stageAt cut v'
  have hm : HEq (s.history.stageMetric (s.history.activeStage v') v')
      (N.stageMetric (N.activeStage (restrictTime_CX2 N cut v')) (restrictTime_CX2 N cut v')) :=
    N.restrict_sliceMetric cut v'
  exact stageMetric_transport_O3 hst hm
    (fun Q m => ∀ x : Q.Carrier, curvatureOperatorLowerBoundAt m x
      (metricAlgebraicCurvatureTensorAt m x) (Phi (metricScalarAt m x)))
    (hpin s v' v'.2.2)

variable (hKL82 : ∀ w : ℝ, 0 < w → ∃ τ₀ K₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ 1 ∧ 0 < K₀ ∧
      ∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
        (r0 τ K : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
        (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
          (H.activeStage_mono hat) x0) {Phi : ℝ → ℝ},
        Perelman.AdmissiblePinchingFunction Phi →
        (∀ v : Icc (0 : ℝ) H.horizon, v ≤ top → ∀ x,
          curvatureOperatorLowerBoundAt (H.stageMetric (H.activeStage v) v) x
            (metricAlgebraicCurvatureTensorAt (H.stageMetric (H.activeStage v) v) x)
            (Phi (metricScalarAt (H.stageMetric (H.activeStage v) v) x))) →
        0 < r0 → 0 < τ → τ ≤ τ₀ → (a : ℝ) = top - τ * r0 ^ 2 →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
            ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage v)
                (H.activeStage_mono hav) q, A.isRmBoundedBy (hat := hav) K) →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) r0,
            SectionalBoundedBelowAt (H.stageMetric (H.activeStage v) v) q (-(r0 ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
          (top : ℝ) - 3 / 4 * τ * r0 ^ 2 ≤ v →
          ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
              (r0 / 4),
            metricScalarAt (H.stageMetric (H.activeStage v) v) q ≤ K₀ * τ⁻¹ * (r0 ^ 2)⁻¹) ∧
        ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
          ballVolume (H.stageMetric (H.activeStage a) a)
            (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4))

include hKL82

/-- `enlarged_rm_of_traced_family_CX12` in tower-history form: the traced family lives in the
slice's own tower history `N` at an arbitrary top time `u ≤ s.time` (no slice at time `u` is
needed). Same constants `c T ρ B` as the slice form (they depend only on `A w K τ₁ τ₂`, `hKL82`
and the profile). -/
theorem enlarged_rm_tower_O37
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) (A : ℝ) (hA : 0 < A) {w K τ₁ τ₂ : ℝ}
    (hw : 0 < w) (hK : 0 < K) (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) :
    ∃ c T ρ B : ℝ, 0 < c ∧ c ≤ τ₁ ∧ 0 < T ∧ 0 < ρ ∧ 0 < B ∧
      ∀ (s : RegularSlice F.observation) (u : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon),
        (u : ℝ) ≤ s.time →
        ∀ (a : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hau : a ≤ u)
          (x : ((sliceTowerHistory_CX2 s).stageAt u).Carrier)
          (X : BackwardPointTrace (sliceTowerHistory_CX2 s)
            ((sliceTowerHistory_CX2 s).activeStage a) ((sliceTowerHistory_CX2 s).activeStage u)
            ((sliceTowerHistory_CX2 s).activeStage_mono hau) x)
          (r : ℝ), 0 < r →
        (∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvu : v ≤ u),
          (sliceTowerHistory_CX2 s).isTracedRegion v
            (X.point ((sliceTowerHistory_CX2 s).activeStage v)
              ((sliceTowerHistory_CX2 s).activeStage_mono hav)
              ((sliceTowerHistory_CX2 s).activeStage_mono hvu))
            (r / 8) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹)) →
        (∀ d : ℝ, 0 < d → d ≤ r → ENNReal.ofReal (w * d ^ 3) ≤
          ballVolume ((sliceTowerHistory_CX2 s).stageMetric
            ((sliceTowerHistory_CX2 s).activeStage u) u) x d) →
        ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (hav : a ≤ v) (hvu : v ≤ u),
          (u : ℝ) - c * r ^ 2 ≤ v → T ≤ v → r ≤ ρ * Real.sqrt v →
          ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
              ((sliceTowerHistory_CX2 s).activeStage v) v)
            (X.point ((sliceTowerHistory_CX2 s).activeStage v)
              ((sliceTowerHistory_CX2 s).activeStage_mono hav)
              ((sliceTowerHistory_CX2 s).activeStage_mono hvu)) (20 * (A * r)),
            Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric
                ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
              (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric
                ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ B / r ^ 2 := by
  obtain ⟨α, c, c₁, hα, hαc, hc₁, hcτ, hseed⟩ :=
    seeds_of_traced_family_CX12 hKL82 hw hK hτ₁ hτ₂
  obtain ⟨T, ρ, B, hT, hρ, hB, henlarge⟩ :=
    enlarged_rm_bound_of_seed_O4 Hp (div_pos hα hA) hc₁
  have hc : 0 < c := (by positivity : 0 ≤ 2 * α ^ 2).trans_lt hαc
  obtain ⟨Phi, hPhi, hpinch⟩ := pinching_prefix_O37 Hp
  refine ⟨c, T, ρ / A, B / A ^ 2, hc, hcτ, hT, by positivity, by positivity, ?_⟩
  intro s u hus a hau x X r hr hTF hvol v hav hvu hv hTv hrv q hq
  obtain ⟨hsmall, hvolume⟩ := hseed (sliceTowerHistory_CX2 s) u x r a hau X
    hPhi (fun v' hv' => hpinch s v' ((Subtype.coe_le_coe.mpr hv').trans hus)) hr hTF hvol
    v hav hvu hv
  have hAr : A * r ≤ ρ * Real.sqrt v := by
    calc A * r ≤ A * (ρ / A * Real.sqrt v) := mul_le_mul_of_nonneg_left hrv hA.le
      _ = ρ * Real.sqrt v := by field_simp
  have he : α / A * (A * r) = α * r := by field_simp
  have hsmall' : hasSmallParabolicCurvature (sliceTowerHistory_CX2 s) v
      (X.point ((sliceTowerHistory_CX2 s).activeStage v)
        ((sliceTowerHistory_CX2 s).activeStage_mono hav)
        ((sliceTowerHistory_CX2 s).activeStage_mono hvu)) (α / A * (A * r)) := by
    rwa [he]
  have hvolume' : ENNReal.ofReal (c₁ * (α / A * (A * r)) ^ 3) ≤
      ballVolume ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v)
        (X.point ((sliceTowerHistory_CX2 s).activeStage v)
          ((sliceTowerHistory_CX2 s).activeStage_mono hav)
          ((sliceTowerHistory_CX2 s).activeStage_mono hvu)) (α / A * (A * r)) := by
    rwa [he]
  have h := henlarge (sliceTowerIndex_CX2 s) v _ (A * r) (mul_pos hA hr) hTv hAr hsmall'
    hvolume' q hq
  have hnorm : B / (A * r) ^ 2 = B / A ^ 2 / r ^ 2 := by rw [mul_pow, div_mul_eq_div_div]
  exact h.trans_eq hnorm

end GC.LongTime.Ch12
