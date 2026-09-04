import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Smoothness
import DifferentialGeometry.Analysis.Calculus.Inverse.ImplicitDerivativeBounds

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Analysis (norm_fderiv_implicit_le exists_hasFDerivAt_graph_block_comp
  norm_iteratedFDeriv_implicit_two_le)
open scoped Topology

section NormalCoordinateDerivativeBounds

open Set Bundle Manifold
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
structure CenterOfMassEquationInverseDerivativeBound
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E)) where
  Λ : ℝ
  L : E ≃L[ℝ] E
  hL : HasFDerivAt (fun z : E => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀
  hLinv : ‖(L.symm : E →L[ℝ] E)‖ ≤ Λ

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T3Space M] in
omit [ConnectedSpace M] in
theorem CenterOfMassEquationInverseDerivativeBound.toInv
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} {ι : Type} [Fintype ι] {z₀ : E} {params₀ : (ι → ℝ) × (ι → E)}
    (hbd : CenterOfMassEquationInverseDerivativeBound (I := I) g hEnorm p z₀ params₀) :
    ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (fun z : E => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p z params₀) (L : E →L[ℝ] E) z₀ :=
  ⟨hbd.L, hbd.hL⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def CenterOfMassEquationDerivativeBound
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (pOrd : ℕ) (B : ℕ → ℝ) : Prop :=
  ∀ j : ℕ, j ≤ pOrd →
    ‖iteratedFDeriv ℝ j
        (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2)
        (z₀, params₀)‖ ≤ B j

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
structure CenterOfMassEquationInverseDerivativeNeighborhoodBound
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {ι : Type} [Fintype ι]
    (c : ((ι → ℝ) × (ι → E)) → M) (params₀ : (ι → ℝ) × (ι → E)) where
  Λ : ℝ
  ev_isUnit : ∀ᶠ q in nhds params₀,
    IsUnit ((fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2)
      ((NormalCoordinates.normalChartAt (I := I) g p (c q) : E), q)).comp
      (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))))
  inv_le : ‖Ring.inverse
      ((fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2)
        ((NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E), params₀)).comp
      (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E))))‖ ≤ Λ

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T3Space M] in
omit [ConnectedSpace M] in
theorem normalChartCenterOfMassEquation_fderiv_norm_le
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hbd : CenterOfMassEquationInverseDerivativeBound (I := I) g hEnorm p z₀ params₀)
    (Dj : (E × ((ι → ℝ) × (ι → E))) →L[ℝ] E) (B1 : ℝ)
    (hG : HasFDerivAt (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2)
      Dj (z₀, params₀))
    (hB : ‖Dj‖ ≤ B1)
    (c : ((ι → ℝ) × (ι → E)) → M) (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E)
    (hcderiv : HasFDerivAt
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) Df params₀)
    (hc0 : (NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E) = z₀)
    (hc_solves : ∀ᶠ params in nhds params₀,
      normalChartCenterOfMassEquationStandard (I := I) g hEnorm p
        (NormalCoordinates.normalChartAt (I := I) g p (c params)) params = 0) :
    ‖iteratedFDeriv ℝ 1
        (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀‖
      ≤ hbd.Λ * B1 := by
  rw [norm_iteratedFDeriv_one, hcderiv.fderiv]
  exact norm_fderiv_implicit_le (fun z params => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p z params) z₀ params₀
    (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) Df Dj hbd.L hbd.Λ
      B1
    hc0 hcderiv hG hbd.hL hbd.hLinv hB hc_solves

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T3Space M] in
omit [ConnectedSpace M] in
theorem normalChartCenterOfMassEquation_second_derivative_norm_le
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {ι : Type} [Fintype ι] (z₀ : E) (params₀ : (ι → ℝ) × (ι → E))
    (hbd : CenterOfMassEquationInverseDerivativeBound (I := I) g hEnorm p z₀ params₀)
    (B : ℕ → ℝ)
    (Dj : (E × ((ι → ℝ) × (ι → E))) →L[ℝ] E)
    (hG : HasFDerivAt (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2)
      Dj (z₀, params₀))
    (hGbd : CenterOfMassEquationDerivativeBound (I := I) g hEnorm p z₀ params₀ 2 B)
    (c : ((ι → ℝ) × (ι → E)) → M) (Df : ((ι → ℝ) × (ι → E)) →L[ℝ] E)
    (hcderiv : HasFDerivAt
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) Df params₀)
    (hc0 : (NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E) = z₀)
    (hc_solves : ∀ᶠ params in nhds params₀,
      normalChartCenterOfMassEquationStandard (I := I) g hEnorm p
        (NormalCoordinates.normalChartAt (I := I) g p (c params)) params = 0)
    (hf2 : ContDiffAt ℝ 2
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀)
    (hG2 : ContDiffAt ℝ 2
      (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2) (z₀, params₀))
    (hnbhd : CenterOfMassEquationInverseDerivativeNeighborhoodBound (I := I) g hEnorm p c params₀)
    (Ctil : ℕ → ℝ)
    (hC0 : ‖z₀‖ ≤ Ctil 0)
    (hC1 : hbd.Λ * B 1 ≤ Ctil 1)
    (hC2 :
      hnbhd.Λ ^ 2 * (B 2 * (hbd.Λ * B 1 + 1)) * B 1
        + hnbhd.Λ * (B 2 * (hbd.Λ * B 1 + 1)) ≤ Ctil 2) :
    ∀ j : ℕ, j ≤ 2 →
      ‖iteratedFDeriv ℝ j
          (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀‖
        ≤ Ctil j := by
  intro j hj
  obtain _ | _ | _ | n := j
  · rw [norm_iteratedFDeriv_zero, hc0]; exact hC0
  · have hB : ‖Dj‖ ≤ B 1 := by
      have h := hGbd 1 hj
      rwa [norm_iteratedFDeriv_one, hG.fderiv] at h
    exact le_trans
      (normalChartCenterOfMassEquation_fderiv_norm_le (I := I) g hEnorm p z₀ params₀ hbd Dj (B 1) hG hB c Df hcderiv hc0 hc_solves)
      hC1
  · have hf_ev : ∀ᶠ q in nhds params₀,
        HasFDerivAt (fun q' => (NormalCoordinates.normalChartAt (I := I) g p (c q') : E))
          (fderiv ℝ (fun q' => (NormalCoordinates.normalChartAt (I := I) g p (c q') : E)) q) q := by
      filter_upwards [hf2.eventually (by simp)] with q hq
      exact (hq.differentiableAt (by norm_num)).hasFDerivAt
    have htend : Filter.Tendsto
        (fun q => ((NormalCoordinates.normalChartAt (I := I) g p (c q) : E), q))
        (nhds params₀) (nhds (z₀, params₀)) := by
      have hf_cont : Filter.Tendsto
          (fun q => (NormalCoordinates.normalChartAt (I := I) g p (c q) : E))
          (nhds params₀) (nhds z₀) := by
        rw [← hc0]; exact hf2.continuousAt
      exact hf_cont.prodMk_nhds Filter.tendsto_id
    have hG_ev : ∀ᶠ q in nhds params₀,
        HasFDerivAt (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2)
          (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2)
            ((NormalCoordinates.normalChartAt (I := I) g p (c q) : E), q))
          ((NormalCoordinates.normalChartAt (I := I) g p (c q) : E), q) := by
      filter_upwards [htend.eventually (hG2.eventually (by simp))] with q hq
      exact (hq.differentiableAt (by norm_num)).hasFDerivAt
    have hB1 : ‖Dj‖ ≤ B 1 := by
      have h := hGbd 1 (by omega)
      rwa [norm_iteratedFDeriv_one, hG.fderiv] at h
    have hDf_le : ‖Df‖ ≤ hbd.Λ * B 1 :=
      norm_fderiv_implicit_le (fun z params => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p z params) z₀ params₀
        (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) Df Dj
        hbd.L hbd.Λ (B 1) hc0 hcderiv hG hbd.hL hbd.hLinv hB1 hc_solves
    have hmax_le : max ‖Df‖ 1 ≤ hbd.Λ * B 1 + 1 :=
      max_le (hDf_le.trans (le_add_of_nonneg_right zero_le_one))
        (le_add_of_nonneg_left (le_trans (norm_nonneg Df) hDf_le))
    have hG1 : ContDiffAt ℝ 1
        (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2))
        (z₀, params₀) := hG2.fderiv_right (by norm_num)
    have hH0 : HasFDerivAt
        (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2))
        (fderiv ℝ (fderiv ℝ
          (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2))
          (z₀, params₀))
        (z₀, params₀) := (hG1.differentiableAt (by norm_num)).hasFDerivAt
    have hH : HasFDerivAt
        (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2))
        (fderiv ℝ (fderiv ℝ
          (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2))
          (z₀, params₀))
        ((NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E), params₀) := by
      rw [hc0]; exact hH0
    have hH'le : ‖fderiv ℝ (fderiv ℝ
        (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2))
        (z₀, params₀)‖ ≤ B 2 := by
      have h := hGbd 2 hj
      have heq2 : ‖fderiv ℝ (fderiv ℝ
          (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2))
          (z₀, params₀)‖
          = ‖iteratedFDeriv ℝ 2
              (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2)
              (z₀, params₀)‖ := by
        rw [← norm_iteratedFDeriv_one]
        exact norm_iteratedFDeriv_fderiv
      rw [heq2]; exact h
    obtain ⟨A', hAd, hA'le⟩ := exists_hasFDerivAt_graph_block_comp
      (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2))
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀ Df _
      hcderiv hH (ContinuousLinearMap.inl ℝ E ((ι → ℝ) × (ι → E)))
      (ContinuousLinearMap.norm_inl_le_one ℝ E ((ι → ℝ) × (ι → E)))
    obtain ⟨B', hBd, hB'le⟩ := exists_hasFDerivAt_graph_block_comp
      (fderiv ℝ (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2))
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀ Df _
      hcderiv hH (ContinuousLinearMap.inr ℝ E ((ι → ℝ) × (ι → E)))
      (ContinuousLinearMap.norm_inr_le_one ℝ E ((ι → ℝ) × (ι → E)))
    have hB2nonneg : (0 : ℝ) ≤ B 2 :=
      le_trans (ContinuousLinearMap.opNorm_nonneg _) hH'le
    have ha₂ : ‖A'‖ ≤ B 2 * (hbd.Λ * B 1 + 1) :=
      hA'le.trans (mul_le_mul hH'le hmax_le
        (le_trans zero_le_one (le_max_right _ _)) hB2nonneg)
    have hb₂ : ‖B'‖ ≤ B 2 * (hbd.Λ * B 1 + 1) :=
      hB'le.trans (mul_le_mul hH'le hmax_le
        (le_trans zero_le_one (le_max_right _ _)) hB2nonneg)
    have hfam0 : fderiv ℝ
        (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2)
        ((NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E), params₀) = Dj := by
      rw [hc0]; exact hG.fderiv
    have hb₁ : ‖(fderiv ℝ
        (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2)
        ((NormalCoordinates.normalChartAt (I := I) g p (c params₀) : E), params₀)).comp
        (ContinuousLinearMap.inr ℝ E ((ι → ℝ) × (ι → E)))‖ ≤ B 1 := by
      rw [hfam0]
      refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
      calc ‖Dj‖ * ‖ContinuousLinearMap.inr ℝ E ((ι → ℝ) × (ι → E))‖
          ≤ B 1 * 1 := mul_le_mul hB1
            (ContinuousLinearMap.norm_inr_le_one ℝ E ((ι → ℝ) × (ι → E))) (norm_nonneg _)
            (le_trans (norm_nonneg _) hB1)
        _ = B 1 := mul_one _
    have hmain := norm_iteratedFDeriv_implicit_two_le
      (fun z params => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p z params)
      (fun params => (NormalCoordinates.normalChartAt (I := I) g p (c params) : E)) params₀
      (fun q => fderiv ℝ
        (fun q' => (NormalCoordinates.normalChartAt (I := I) g p (c q') : E)) q)
      (fun q => fderiv ℝ
        (fun w : E × ((ι → ℝ) × (ι → E)) => normalChartCenterOfMassEquationStandard (I := I) g hEnorm p w.1 w.2)
        ((NormalCoordinates.normalChartAt (I := I) g p (c q) : E), q))
      A' B' hnbhd.Λ (B 2 * (hbd.Λ * B 1 + 1)) (B 1) (B 2 * (hbd.Λ * B 1 + 1))
      hf_ev hG_ev hc_solves hnbhd.ev_isUnit hAd hBd hnbhd.inv_le hb₁ ha₂ hb₂
    exact hmain.trans hC2
  · omega

end NormalCoordinateDerivativeBounds

end CheegerGromovCompactness
end DifferentialGeometry
