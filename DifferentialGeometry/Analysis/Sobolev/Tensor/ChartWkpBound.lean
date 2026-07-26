import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpSupport
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpTransport
import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartBoundStrictMemWkpHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.ChartTransitionTransportCLM

/-!
# Quantitative `W^{2,p}` transport of weak tensor chart components

The raw tensor transition law in `ChartWkpTransport.lean` contains a scalar
transition coefficient which is smooth only on a chart overlap.  The existing
spectral construction supplies its canonical globally smooth compactly
supported extension, obtained by multiplying by the two chart-kernel cutoffs.
This file pushes that coefficient to the source Euclidean chart and combines
the quantitative smooth-multiplier theorem with `crossChartJointK`.

The resulting estimate is deliberately fixed at order two, which is the order
needed by the maximal-regularity Ricci--DeTurck construction.  The exponent is
still arbitrary in the natural range `1 <= p < infinity`; in particular the
constant is independent of the transported weak component.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The globally smooth cutoff transition coefficient, written in source-chart
Euclidean coordinates and extended by zero off the source chart target. -/
def transCoeffE
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P Q : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  etaEuclid (I := I) (M := M) β
    (transportCoeffManifold (I := I) (M := M) g r s β α P Q)

/-- The Euclidean transition coefficient is globally smooth. -/
theorem transCoeffE_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P Q : TensorCompIdx (E := E) r s) :
    ContDiff ℝ (⊤ : ℕ∞) (transCoeffE (I := I) (M := M) g r s β α P Q) := by
  exact contDiff_etaEuclid (I := I) (M := M) β
    (transportCoeffManifold (I := I) (M := M) g r s β α P Q)
    (contMDiff_transportCoeffManifold (I := I) (M := M) g r s β α P Q)
    (hasCompactSupport_transportCoeffManifold
      (I := I) (M := M) g r s β α P Q)
    (tsupport_transportCoeffManifold_subset_sourceβ
      (I := I) (M := M) g r s β α P Q)

/-- The Euclidean transition coefficient has compact support. -/
theorem transCoeffE_cpt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P Q : TensorCompIdx (E := E) r s) :
    HasCompactSupport (transCoeffE (I := I) (M := M) g r s β α P Q) := by
  exact hasCompactSupport_etaEuclid (I := I) (M := M) β
    (transportCoeffManifold (I := I) (M := M) g r s β α P Q)
    (hasCompactSupport_transportCoeffManifold
      (I := I) (M := M) g r s β α P Q)
    (tsupport_transportCoeffManifold_subset_sourceβ
      (I := I) (M := M) g r s β α P Q)

/-- On the source chart, `transCoeffE` evaluates to the manifold transition
coefficient at the corresponding point. -/
theorem transCoeffE_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P Q : TensorCompIdx (E := E) r s) {x : M}
    (hx : x ∈ (chartAt H β).source) :
    transCoeffE (I := I) (M := M) g r s β α P Q
        (toEuclidean (E := E) (extChartAt I β x)) =
      transportCoeffManifold (I := I) (M := M) g r s β α P Q x := by
  rw [transCoeffE, etaEuclid_apply_of_mem (I := I) (M := M) β _
    (toEuclidean_extChartAt_mem_chartTargetEuclid
      (I := I) (M := M) β hx)]
  rw [symm_toEuclidean_symm_toEuclidean_extChartAt
    (I := I) (M := M) β hx]

/-- Multiplication by one cutoff transition coefficient is quantitatively
bounded on `W^{2,p}` of the source chart. -/
theorem coeffMulJoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (β α : M) (P Q : TensorCompIdx (E := E) r s) :
    ∃ K : ℝ, 0 < K ∧ ∀ {v : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) 2 p v
          (chartTargetEuclid (I := I) (M := M) β) →
      MemWkp (d := Module.finrank ℝ E) 2 p
          (fun y => transCoeffE (I := I) (M := M) g r s β α P Q y * v y)
          (chartTargetEuclid (I := I) (M := M) β) ∧
        wkpNorm (d := Module.finrank ℝ E) 2 p
            (fun y => transCoeffE (I := I) (M := M) g r s β α P Q y * v y)
            (chartTargetEuclid (I := I) (M := M) β) ≤
          ENNReal.ofReal K *
            wkpNorm (d := Module.finrank ℝ E) 2 p v
              (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  have h_smooth := transCoeffE_smooth (I := I) (M := M) g r s β α P Q
  have h_cpt := transCoeffE_cpt (I := I) (M := M) g r s β α P Q
  obtain ⟨C, hC_nonneg, hC_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) h_smooth h_cpt 2
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) 2 hp hp_top
      (chartTargetEuclid_isOpen (I := I) (M := M) β)
      h_smooth hC_nonneg (fun j hj y _ => hC_bound y j hj)
  refine ⟨K, hK_pos, fun {v} hv => ⟨?_, hK_bound hv⟩⟩
  exact MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) 2 hp
    (chartTargetEuclid_isOpen (I := I) (M := M) β)
    h_smooth (fun j hj y _ => hC_bound y j hj) hv

/-- The contribution of source component `Q` in chart `β` to target
component `P` in chart `α`. -/
def secTransTerm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P Q : TensorCompIdx (E := E) r s) (v : EuclN → ℝ) : EuclN → ℝ :=
  chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
    (chartPullback I β
      (fun y => transCoeffE (I := I) (M := M) g r s β α P Q y * v y))

/-- A compactly POU-supported source component contributes a quantitatively
controlled `W^{2,p}` function in every target chart. -/
theorem secTermJoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (β α : M) (P Q : TensorCompIdx (E := E) r s) :
    ∃ K : ℝ, 0 < K ∧ ∀ {v : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) 2 p v
          (chartTargetEuclid (I := I) (M := M) β) →
      tsupport v ⊆ chartImagePOUTsupport (I := I) (M := M) β →
      MemWkp (d := Module.finrank ℝ E) 2 p
          (secTransTerm (I := I) (M := M) g r s β α P Q v)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        wkpNorm (d := Module.finrank ℝ E) 2 p
            (secTransTerm (I := I) (M := M) g r s β α P Q v)
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K *
            wkpNorm (d := Module.finrank ℝ E) 2 p v
              (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  obtain ⟨K_mul, hK_mul_pos, hK_mul⟩ :=
    coeffMulJoint (I := I) (M := M) g r s hp hp_top β α P Q
  obtain ⟨K_cross, hK_cross_pos, hK_cross⟩ :=
    crossChartJointK (I := I) (M := M) g 2 hp hp_top α β
      (K_α := tsupport
        (((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)))
      (isClosed_tsupport _).isCompact
      (chartAtlasPOU_isSubordinate I M β)
  refine ⟨K_cross * K_mul, mul_pos hK_cross_pos hK_mul_pos, ?_⟩
  intro v hv hv_support
  have hmul := hK_mul hv
  have hprod_support :
      tsupport
          (fun y => transCoeffE (I := I) (M := M) g r s β α P Q y * v y) ⊆
        (fun x : M => toEuclidean (E := E) (extChartAt I β x)) ''
          tsupport (((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
    have hs := (tsupport_mul_subset_right
      (f := transCoeffE (I := I) (M := M) g r s β α P Q)
      (g := v)).trans hv_support
    simpa only [chartImagePOUTsupport, Set.image_image, Function.comp_apply] using hs
  have hcross := hK_cross hmul.1 hprod_support
  refine ⟨hcross.1, ?_⟩
  calc
    wkpNorm (d := Module.finrank ℝ E) 2 p
        (secTransTerm (I := I) (M := M) g r s β α P Q v)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal K_cross *
        wkpNorm (d := Module.finrank ℝ E) 2 p
          (fun y => transCoeffE (I := I) (M := M) g r s β α P Q y * v y)
          (chartTargetEuclid (I := I) (M := M) β) := hcross.2
    _ ≤ ENNReal.ofReal K_cross *
        (ENNReal.ofReal K_mul *
          wkpNorm (d := Module.finrank ℝ E) 2 p v
            (chartTargetEuclid (I := I) (M := M) β)) :=
      mul_le_mul_left' hmul.2 _
    _ = ENNReal.ofReal (K_cross * K_mul) *
        wkpNorm (d := Module.finrank ℝ E) 2 p v
          (chartTargetEuclid (I := I) (M := M) β) := by
      rw [ENNReal.ofReal_mul hK_cross_pos.le]
      simp only [mul_assoc]

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
