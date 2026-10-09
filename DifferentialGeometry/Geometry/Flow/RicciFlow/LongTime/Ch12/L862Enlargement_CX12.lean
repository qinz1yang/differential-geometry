import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862LocalSeeds_CX12

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

/-- The local KL82 volume step and the profile's KL84.1(c) enlargement
combine into a uniform curvature bound on the moving 20r balls. The
traced family here is concrete input data at the selected smaller ball;
constructing that family is a separate step in the global contradiction. -/
theorem enlarged_rm_of_traced_family_CX12
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) (A : ℝ) (hA : 0 < A) {w K τ₁ τ₂ : ℝ}
    (hw : 0 < w) (hK : 0 < K) (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) :
    ∃ c T ρ B : ℝ, 0 < c ∧ c ≤ τ₁ ∧ 0 < T ∧ 0 < ρ ∧ 0 < B ∧
      ∀ (s : RegularSlice F.observation)
        (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
        (x : (s.history.stageAt (sliceTop_S8 s)).Carrier)
        (X : BackwardPointTrace s.history (s.history.activeStage a)
          (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x)
        (r : ℝ), 0 < r →
        (∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : a ≤ v) (hvt : v ≤ sliceTop_S8 s),
          s.history.isTracedRegion v
            (X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
              (s.history.activeStage_mono hvt)) (r / 8) (τ₂ * r ^ 2) (K * (r ^ 2)⁻¹)) →
        (∀ d : ℝ, 0 < d → d ≤ r → ENNReal.ofReal (w * d ^ 3) ≤
          ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x d) →
        ∀ (v : Icc (0 : ℝ) s.history.horizon) (hav : a ≤ v) (hvt : v ≤ sliceTop_S8 s),
          s.time - c * r ^ 2 ≤ v → T ≤ v → r ≤ ρ * Real.sqrt v →
          ∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage v) v)
            (X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
              (s.history.activeStage_mono hvt)) (20 * (A * r)),
            Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) q 4
              (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) q)) ≤ B / r ^ 2 := by
  obtain ⟨α, c, c₁, hα, hαc, hc₁, hcτ, hseed⟩ :=
    seeds_of_traced_family_CX12 hKL82 hw hK hτ₁ hτ₂
  obtain ⟨T, ρ, B, hT, hρ, hB, henlarge⟩ :=
    enlarged_rm_bound_of_slice_seed_CX2 Hp (div_pos hα hA) hc₁
  have hc : 0 < c := (by positivity : 0 ≤ 2 * α ^ 2).trans_lt hαc
  obtain ⟨Phi, hPhi, hpinch⟩ := slice_pinching_input_CX12 Hp
  refine ⟨c, T, ρ / A, B / A ^ 2, hc, hcτ, hT, by positivity, by positivity, ?_⟩
  intro s a hat x X r hr hTF hvol v hav hvt hv hTv hrv q hq
  obtain ⟨hsmall, hvolume⟩ := hseed s.history (sliceTop_S8 s) x r a hat X
    hPhi (hpinch s) hr hTF hvol v hav hvt hv
  have hAr : A * r ≤ ρ * Real.sqrt v := by
    calc A * r ≤ A * (ρ / A * Real.sqrt v) := mul_le_mul_of_nonneg_left hrv hA.le
      _ = ρ * Real.sqrt v := by field_simp
  have he : α / A * (A * r) = α * r := by field_simp
  have hsmall' : hasSmallParabolicCurvature s.history v
      (X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
        (s.history.activeStage_mono hvt)) (α / A * (A * r)) := by
    rwa [he]
  have hvolume' : ENNReal.ofReal (c₁ * (α / A * (A * r)) ^ 3) ≤
      ballVolume (s.history.stageMetric (s.history.activeStage v) v)
        (X.point (s.history.activeStage v) (s.history.activeStage_mono hav)
          (s.history.activeStage_mono hvt)) (α / A * (A * r)) := by
    rwa [he]
  have h := henlarge s v _ (A * r) (mul_pos hA hr) hTv hAr hsmall' hvolume' q hq
  have hnorm : B / (A * r) ^ 2 = B / A ^ 2 / r ^ 2 := by rw [mul_pow, div_mul_eq_div_div]
  exact h.trans_eq hnorm

end GC.LongTime.Ch12
