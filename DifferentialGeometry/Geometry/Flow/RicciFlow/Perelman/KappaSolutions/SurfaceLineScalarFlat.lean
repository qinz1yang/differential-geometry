import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceRicciAlgebra
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannSmooth
import DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.CoordinateFormula
import DifferentialGeometry.Geometry.Operator.Hessian.TraceFormula
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Bundle.FiberBundleHausdorff

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Topology
open scoped _root_.Topology ContDiff Manifold NNReal ENNReal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

local instance surfaceLineScalarFlatOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

section Affine

variable [NeZero (Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem ricci_gradient_eq_zero_of_unit_hessian_zero
    (g : SmoothRiemannianMetric I M) {b : M → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
    (hunit : ∀ q : M, g.inner q (gradientFun (I := I) g b q)
      (gradientFun (I := I) g b q) = 1)
    (hH : ∀ q : M, hessFun (I := I) g b q = 0) (p : M) :
    ricciTensor (I := I) g p (gradientFun (I := I) g b p)
      (gradientFun (I := I) g b p) = 0 := by
  have hcomponent (q : M) (i j : Fin (Module.finrank ℝ E)) :
      chartHessianTensor (I := I) g q b i j q = 0 := by
    rw [← hessFun_basis_apply, hH]
    rfl
  have hHnorm : chartHessFrobeniusSq (I := I) g b p = 0 := by
    simp only [chartHessFrobeniusSq_def, hcomponent, mul_zero, Finset.sum_const_zero]
  have hLap : ΔG (I := I) g ⟨b, hb⟩ = fun _ : M => (0 : ℝ) := by
    funext q
    rw [← chartInvGram_trace_hessianTensor_eq_laplacian_of_boundaryless (I := I) g hb q]
    simp only [hcomponent, mul_zero, Finset.sum_const_zero]
  have hnorm : normGradSqFun (I := I) g b =ᶠ[𝓝 p] fun _ : M => (1 : ℝ) :=
    Filter.Eventually.of_forall hunit
  have hnormSmooth := normGradSqFun_contMDiff (I := I) g hb
  have hLapnorm : ΔG (I := I) g ⟨normGradSqFun (I := I) g b, hnormSmooth⟩ p = 0 := by
    calc
      _ = ΔG (I := I) g ⟨fun _ : M => (1 : ℝ), contMDiff_const⟩ p :=
        Δ_g_congr_of_eventuallyEq (I := I) g hnormSmooth contMDiff_const hnorm
      _ = 0 := Δ_g_const (I := I) g 1 p
  have hbochner := bochner_pointwise_half_grad_normSq_of_boundaryless (I := I) g hb p
  change (1 / 2 : ℝ) *
      ΔG (I := I) g ⟨normGradSqFun (I := I) g b, hnormSmooth⟩ p =
    chartHessFrobeniusSq (I := I) g b p +
      ricciTensor (I := I) g p (gradientFun (I := I) g b p)
        (gradientFun (I := I) g b p) +
      g.inner p (gradientFun (I := I) g b p)
        (gradientFun (I := I) g (ΔG (I := I) g ⟨b, hb⟩) p) at hbochner
  rw [hLapnorm, hHnorm, hLap, gradientFun_const] at hbochner
  simpa only [mul_zero, zero_add, map_zero, add_zero] using hbochner.symm

end Affine

section CompatibleLine

variable [CompleteSpace E]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [PreconnectedSpace M]
  [RiemannianBundle (fun p : M => TangentSpace I p)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun p : M => TangentSpace I p)]

theorem surface_scalar_eq_zero_of_nonnegative_ricci_line
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hdim : Module.finrank ℝ E = 2)
    (hRic : ∀ p : M, ∀ v : TangentSpace I p, 0 ≤ ricciTensor (I := I) g p v v)
    {gamma : ℝ → M} (hgamma : Isometry gamma) (p : M) :
    metricScalarAt (I := I) g p = 0 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let b := busemann (fun t : ℝ≥0 => gamma t)
  have hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b := busemann_contMDiff g hEnorm hRic hgamma
  have hunit (q : M) : g.inner q (gradientFun (I := I) g b q)
      (gradientFun (I := I) g b q) = 1 :=
    (opposite_busemann_gradient_unit g hEnorm hRic hgamma q).1
  have hH (q : M) : hessFun (I := I) g b q = 0 :=
    busemann_hessian_eq_zero g hEnorm hRic hgamma q
  have hzero := ricci_gradient_eq_zero_of_unit_hessian_zero g hb hunit hH p
  rw [ricciTensor_apply_of_finrank_two g hdim, hunit, mul_one] at hzero
  linarith

end CompatibleLine

section IntrinsicLine

variable [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem surface_scalar_eq_zero_of_intrinsic_line
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (hdim : Module.finrank ℝ E = 2)
    (hRic : ∀ p : M, ∀ v : TangentSpace I p, 0 ≤ ricciTensor (I := I) g p v v)
    {gamma : ℝ → M}
    (hline : ∀ s t : ℝ, riemannianEDistOf (I := I) g (gamma s) (gamma t) =
      ENNReal.ofReal |s - t|) (p : M) : metricScalarAt (I := I) g p = 0 := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun q : M => TangentSpace I q) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun q : M => TangentSpace I q) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro q v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : CompleteSpace M := hg.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := fun q v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g q v
  let _ : MetricSpace M := riemMetricSpace (I := I) (M := M)
  let _ : ProperSpace M := properSpace_riemMetric (I := I) hg.complete g hEnorm
  have hgamma : Isometry gamma := by
    apply Isometry.of_dist_eq
    intro s t
    rw [riemMetric_dist_eq (I := I),
      ← riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm, hline,
      ENNReal.toReal_ofReal (abs_nonneg _), Real.dist_eq]
  exact surface_scalar_eq_zero_of_nonnegative_ricci_line g hEnorm hdim hRic hgamma p

theorem not_intrinsic_line_of_surface_scalar_pos
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (hdim : Module.finrank ℝ E = 2)
    (hRic : ∀ p : M, ∀ v : TangentSpace I p, 0 ≤ ricciTensor (I := I) g p v v)
    (p : M) (hpos : 0 < metricScalarAt (I := I) g p) :
    ¬ ∃ gamma : ℝ → M, ∀ s t : ℝ,
      riemannianEDistOf (I := I) g (gamma s) (gamma t) = ENNReal.ofReal |s - t| := by
  rintro ⟨gamma, hgamma⟩
  have hz := surface_scalar_eq_zero_of_intrinsic_line g hg hdim hRic hgamma p
  exact (ne_of_gt hpos) hz

end IntrinsicLine

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
