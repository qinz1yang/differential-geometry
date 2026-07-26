import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegInsertH1
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSPathIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetIntegral

/-!
# Low-regularity order-zero Ricci--DeTurck path coefficient

This file assembles the cancellation-preserving order-zero coefficient bounds
from the concrete low-regularity arms.  In dimension three, endpoint spectral
`H3` bounds control the pointwise-in-path intrinsic `H1` jet and hence, by the
parameter-integral jet theorem, the same jet of `rhsLow0PathIntegral`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- In dimension three, a common endpoint spectral `H3` bound controls the
pointwise-in-path intrinsic `H1` jet of the complete order-zero
Ricci--DeTurck coefficient.  The insertion arm is estimated only after its
background cancellation, so no fourth metric derivative is used. -/
theorem rhs0_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ₀)
        (R : ℝ), 0 ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ ≤ R →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (rhsLow0Coeff (I := I) (M := M) g₀ g_bg
                T T' hδ hδ' s)‖ ^ 2) ≤ (B R) ^ 2 := by
  classical
  obtain ⟨Cpath, hCpath, hpath⟩ := convex_h3_jet (I := I) (M := M) g₀
  obtain ⟨Bdlb, _hBdlb, hdlb⟩ :=
    dlbDiff_h1 (I := I) (M := M) hDim g₀ g_bg hδ₀_lt
  obtain ⟨Bins, _hBins, hins⟩ :=
    insert_h1 (I := I) (M := M) hDim g₀ g_bg hδ₀_lt
  obtain ⟨Bvb, _hBvb, hvb⟩ := vb_h1 (I := I) (M := M) hDim g₀ hδ₀_lt
  obtain ⟨Bam, _hBam, ham⟩ := amix_h1 (I := I) (M := M) hDim g₀ g_bg hδ₀_lt
  obtain ⟨Briem, _hBriem, hriem⟩ := riem_h1 (I := I) (M := M) hDim g₀ hδ₀_lt
  obtain ⟨Caux, BRic, BDla, _hCaux, _hBRic, _hBDla, haux⟩ :=
    rhs0_h1_of_aux (I := I) (M := M) hDim g₀ g_bg hδ₀_nonneg hδ₀_lt
  let L : ℝ → ℝ := fun R => Real.sqrt (5 *
    ((Bdlb (Cpath * R)) ^ 2 + (Bins (Cpath * R)) ^ 2 +
      (Bvb (Cpath * R) (Cpath * R)) ^ 2 +
      (Bam (Cpath * R) (Cpath * R)) ^ 2 + (Briem (Cpath * R)) ^ 2))
  let B : ℝ → ℝ := fun R => Real.sqrt (4 *
    (4 * (BRic (Caux * R)) ^ 2 + (BDla (Caux * R)) ^ 2 + (L R) ^ 2))
  refine ⟨B, fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro T T' hδ hδ' R hR hT hT' s hs
  let P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s
  let g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s
  have hA : 0 ≤ Cpath * R := mul_nonneg hCpath hR
  have hP3 : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (Cpath * R) ^ 2 := by
    simpa only [P] using hpath T T' R hR hT hT' s hs
  have hP2 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ (Cpath * R) ^ 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      (fun j _ _ => sq_nonneg _)).trans hP3
  have hPbound : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) δ₀ := by
    have h := convexPerturbation_gFibreOpBound
      (I := I) (M := M) g₀ T T' hδ hδ' hs.1 hs.2
    have hscalar : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    rw [hscalar] at h
    simpa only [P] using h
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    simpa only [g₁, P] using realizedFam_inner_of_mem
      (I := I) g₀ T T' hδ hδ'
        (Icc_subset_realizedSmallSet hδ₀_lt hδ₀_lt hs) y v w
  have hD := hdlb g₁ P htie le_rfl hδ₀_nonneg hPbound
    (Cpath * R) hA hP3
  have hI := hins g₁ P htie le_rfl hδ₀_nonneg hPbound
    (Cpath * R) hA hP2
  have hV := hvb g₁ P htie le_rfl hδ₀_nonneg hPbound
    (Cpath * R) (Cpath * R) hA hA hP2 hP3
  have hAm := ham g₁ P htie le_rfl hδ₀_nonneg hPbound
    (Cpath * R) (Cpath * R) hA hA hP2 hP3
  have hRm := hriem g₁ P htie le_rfl hδ₀_nonneg hPbound
    (Cpath * R) hA hP3
  have htail : (∑ i ∈ Finset.range 2,
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg +
          lieCorr0Field (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2) ≤
      (L R) ^ 2 := by
    simpa only [L] using tail_h1_parts (I := I) (M := M) g₀ g₁ g_bg
      (Bdlb (Cpath * R)) (Bins (Cpath * R))
      (Bvb (Cpath * R) (Cpath * R)) (Bam (Cpath * R) (Cpath * R))
      (Briem (Cpath * R)) hD hI hV hAm hRm
  have hout := haux T T' hδ hδ' R hR hT hT' s hs (L R) (by
    simpa only [g₁] using htail)
  simpa only [B] using hout

/-- The pointwise-in-path order-zero `H1` coefficient bound passes unchanged
to its interval-integrated coefficient field. -/
theorem rhs0_path_h1
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        (hδ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T') δ₀)
        (R : ℝ), 0 ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T‖ ≤ R →
        ‖ccTensorToHs (I := I) (M := M) g₀ 2 (3 : ℝ) T'‖ ≤ R →
        (∑ i ∈ Finset.range 2,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (rhsLow0PathIntegral (I := I) (M := M) g₀ g_bg T T'
              hδ₀_lt hδ hδ₀_lt hδ')‖ ^ 2) ≤ (B R) ^ 2 := by
  obtain ⟨B, hB, hcoeff⟩ :=
    rhs0_h1 (I := I) (M := M) hDim g₀ g_bg hδ₀_nonneg hδ₀_lt
  refine ⟨B, hB, ?_⟩
  intro T T' hδ hδ' R hR hT hT'
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ₀) (δ' := δ₀) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_realizedSmallSet hδ₀_lt hδ₀_lt
  have hpath := path_jetL2_le (I := I) (M := M) g₀ 2 2 1
    (fun s => rhsLow0Coeff (I := I) (M := M) g₀ g_bg T T' hδ hδ' s)
    (realizedSmallSet (δ := δ₀) (δ' := δ₀)) realizedSmallSet_isOpen hSI
    (rhsLow0_path_joint (I := I) (M := M) g₀ g_bg T T' hδ hδ')
    (hB R hR) (hcoeff T T' hδ hδ' R hR hT hT')
  simpa only [rhsLow0PathIntegral] using hpath

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
