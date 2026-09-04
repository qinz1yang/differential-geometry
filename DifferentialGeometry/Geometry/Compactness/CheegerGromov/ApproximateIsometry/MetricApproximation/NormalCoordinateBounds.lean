import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.Basic
import DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.ComponentBounds
import DifferentialGeometry.Analysis.Estimates.BilinearMapPerturbation

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff BigOperators Topology
open DifferentialGeometry.Geometry.Riemannian

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space (TangentBundle I N)]

omit [Module.Finite ℝ E] in
theorem SmoothPullbackMetricTensor.tensor_sub_metricTensorField_apply_le_of_normalChartAt
    [Module.Finite ℝ E] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    {F : M → N} {p : M}
    (hpb : SmoothPullbackMetricTensor (I := I) F h)
    (hF : DifferentiableAt ℝ
      (fun z => NormalCoordinates.normalChartAt (I := I) h (F p)
        (F ((NormalCoordinates.normalChartAt (I := I) g p).symm z))) (0 : E))
    (heq : F =ᶠ[nhds p] fun q =>
      (NormalCoordinates.normalChartAt (I := I) h (F p)).symm
        (NormalCoordinates.normalChartAt (I := I) h (F p)
          (F ((NormalCoordinates.normalChartAt (I := I) g p).symm
            (NormalCoordinates.normalChartAt (I := I) g p q)))))
    {ε η : ℝ}
    (hA : ‖fderiv ℝ (fun z => NormalCoordinates.normalChartAt (I := I) h (F p)
        (F ((NormalCoordinates.normalChartAt (I := I) g p).symm z))) (0 : E)
      - ContinuousLinearMap.id ℝ E‖ ≤ ε)
    (hB : ∀ v' w' : E,
      |h.inner (F p) v' w' - g.inner p v' w'| ≤ η * (‖v'‖ * ‖w'‖))
    (v w : TangentSpace I p) :
    |(hpb.tensor p - Tensor0SBundle.metricTensorField (I := I) g p)
        (fun a : Fin 2 => if a = 0 then v else w)| ≤
      ((‖h.inner (F p)‖ * ε * (2 + ε)) + η) * (‖v‖ * ‖w‖) := by
  have hsub : (hpb.tensor p - Tensor0SBundle.metricTensorField (I := I) g p)
      (fun a : Fin 2 => if a = 0 then v else w) =
        hpb.tensor p (fun a : Fin 2 => if a = 0 then v else w) -
          Tensor0SBundle.metricTensorField (I := I) g p
            (fun a : Fin 2 => if a = 0 then v else w) := rfl
  have hpba := hpb.tensor_apply p (fun a : Fin 2 => if a = 0 then v else w)
  norm_num at hpba
  set A := fderiv ℝ (fun z => NormalCoordinates.normalChartAt (I := I) h (F p)
    (F ((NormalCoordinates.normalChartAt (I := I) g p).symm z))) (0 : E) with hAdef
  have hmv : mfderiv I I F p v = A v :=
    DFunLike.congr_fun
      (NormalCoordinates.mfderiv_eq_fderiv_normalChartAt (I := I) g h F p hF heq) v
  have hmw : mfderiv I I F p w = A w :=
    DFunLike.congr_fun
      (NormalCoordinates.mfderiv_eq_fderiv_normalChartAt (I := I) g h F p hF heq) w
  rw [hsub, hpba, hmv, hmw, Tensor0SBundle.metricTensorField_apply]
  norm_num
  have h1 := bilinPerturb (B := h.inner (F p)) (A := A) v w
  have h2 := hB v w
  have hAle : ‖A‖ ≤ 1 + ε := by
    calc
      ‖A‖ = ‖ContinuousLinearMap.id ℝ E + (A - ContinuousLinearMap.id ℝ E)‖ := by
        congr 1
        abel
      _ ≤ ‖ContinuousLinearMap.id ℝ E‖ + ‖A - ContinuousLinearMap.id ℝ E‖ :=
        norm_add_le _ _
      _ ≤ 1 + ε := add_le_add ContinuousLinearMap.norm_id_le hA
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hA
  have hcoef : ‖h.inner (F p)‖ * ‖A - ContinuousLinearMap.id ℝ E‖ * (1 + ‖A‖) ≤
      ‖h.inner (F p)‖ * ε * (2 + ε) := by
    have h2' : (1 : ℝ) + ‖A‖ ≤ 2 + ε := by linarith [hAle]
    gcongr
  calc
    |h.inner (F p) (A v) (A w) - g.inner p v w| =
        |(h.inner (F p) (A v) (A w) - h.inner (F p) v w) +
          (h.inner (F p) v w - g.inner p v w)| := by ring_nf
    _ ≤ |h.inner (F p) (A v) (A w) - h.inner (F p) v w| +
        |h.inner (F p) v w - g.inner p v w| := abs_add_le _ _
    _ ≤ ‖h.inner (F p)‖ * ‖A - ContinuousLinearMap.id ℝ E‖ * (1 + ‖A‖) *
          (‖v‖ * ‖w‖) + η * (‖v‖ * ‖w‖) := add_le_add h1 h2
    _ ≤ ‖h.inner (F p)‖ * ε * (2 + ε) * (‖v‖ * ‖w‖) +
        η * (‖v‖ * ‖w‖) := by gcongr
    _ = ((‖h.inner (F p)‖ * ε * (2 + ε)) + η) * (‖v‖ * ‖w‖) := by ring

omit [Module.Finite ℝ E] in
theorem SmoothPullbackMetricTensor.metricTensorErrorNorm_le_of_normalChartAt
    [Module.Finite ℝ E] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    {F : M → N} {p : M}
    (hpb : SmoothPullbackMetricTensor (I := I) F h)
    (hF : DifferentiableAt ℝ
      (fun z => NormalCoordinates.normalChartAt (I := I) h (F p)
        (F ((NormalCoordinates.normalChartAt (I := I) g p).symm z))) (0 : E))
    (heq : F =ᶠ[nhds p] fun q =>
      (NormalCoordinates.normalChartAt (I := I) h (F p)).symm
        (NormalCoordinates.normalChartAt (I := I) h (F p)
          (F ((NormalCoordinates.normalChartAt (I := I) g p).symm
            (NormalCoordinates.normalChartAt (I := I) g p q)))))
    {ε η c : ℝ} (hη : 0 ≤ η) (hc : 0 < c)
    (hlow : ∀ v : TangentSpace I p, c * ‖v‖ ^ 2 ≤ g.inner p v v)
    (hA : ‖fderiv ℝ (fun z => NormalCoordinates.normalChartAt (I := I) h (F p)
        (F ((NormalCoordinates.normalChartAt (I := I) g p).symm z))) (0 : E)
      - ContinuousLinearMap.id ℝ E‖ ≤ ε)
    (hB : ∀ v' w' : E,
      |h.inner (F p) v' w' - g.inner p v' w'| ≤ η * (‖v'‖ * ‖w'‖)) :
    metricTensorErrorNorm (I := I) hpb.tensor g p ≤
      (Module.finrank ℝ (TangentSpace I p) : ℝ) *
        (((‖h.inner (F p)‖ * ε * (2 + ε)) + η) *
          ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹)) := by
  obtain ⟨basis, hON, hbd⟩ :=
    Tensor0SBundle.exists_orthonormal_basis_norm_le_of_coercive
      (I := I) g p hc hlow
  have hinv := Tensor0SBundle.metricInverseInBasis_of_orthonormal
    (I := I) g basis hON
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hA
  have hs0 : (0 : ℝ) ≤ (Real.sqrt c)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hc0 : 0 ≤ (((‖h.inner (F p)‖ * ε * (2 + ε)) + η) *
      ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹)) := by positivity
  have hmain := Tensor0SBundle.sqrt_normSq0S_le_card_of_component_bound
    (I := I) g p 2 basis hinv
    (hpb.tensor p - Tensor0SBundle.metricTensorField (I := I) g p)
    (((‖h.inner (F p)‖ * ε * (2 + ε)) + η) *
      ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹)) hc0 (by
        intro slots
        rw [Tensor0SBundle.component0S_apply]
        have hslots :
            (fun a : Fin 2 => if a = 0 then basis (slots 0) else basis (slots 1)) =
              fun a : Fin 2 => basis (slots a) := by
          funext a
          fin_cases a <;> simp
        rw [← hslots]
        have happly := hpb.tensor_sub_metricTensorField_apply_le_of_normalChartAt
          g h hF heq hA hB (basis (slots 0)) (basis (slots 1))
        have hbb : ‖(basis (slots 0) : TangentSpace I p)‖ *
            ‖(basis (slots 1) : TangentSpace I p)‖ ≤
              (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ :=
          mul_le_mul (hbd (slots 0)) (hbd (slots 1)) (norm_nonneg _) hs0
        have hcoefnn : 0 ≤ (‖h.inner (F p)‖ * ε * (2 + ε)) + η := by positivity
        exact happly.trans (mul_le_mul_of_nonneg_left hbb hcoefnn))
  change Real.sqrt (Tensor0SBundle.normSq0S (I := I) g p 2
      (hpb.tensor p - Tensor0SBundle.metricTensorField (I := I) g p)) ≤ _
  simpa [Fintype.card_congr, Nat.cast_pow, Real.sqrt_sq_eq_abs] using hmain

end HCGCompactness
end DifferentialGeometry
