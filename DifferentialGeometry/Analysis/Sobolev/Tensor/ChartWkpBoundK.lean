import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpBound

/-!
# Quantitative tensor-chart transport in `W^{k,p}`

`ChartWkpBound.lean` packages the order-two estimate used by the original
maximal-regularity lane.  The contraction topology for the low-regularity
Ricci--DeTurck construction is instead `W^{3,p}`.  This file records the same
two estimates at arbitrary finite order, using the already general
smooth-multiplier and cross-chart theorems.

All constants below are attached only to the fixed background metric, chart
pair, tensor indices, order, and exponent.  In particular they do not depend
on an evolving metric or on a time horizon.
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

/-- Multiplication by one fixed cutoff transition coefficient is bounded on
`W^{k,p}` of the source chart. -/
theorem coeffMulJointK
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (β α : M) (P Q : TensorCompIdx (E := E) r s) :
    ∃ K : ℝ, 0 < K ∧ ∀ {v : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M) β) →
      MemWkp (d := Module.finrank ℝ E) k p
          (fun y => transCoeffE (I := I) (M := M) g r s β α P Q y * v y)
          (chartTargetEuclid (I := I) (M := M) β) ∧
        wkpNorm (d := Module.finrank ℝ E) k p
            (fun y => transCoeffE (I := I) (M := M) g r s β α P Q y * v y)
            (chartTargetEuclid (I := I) (M := M) β) ≤
          ENNReal.ofReal K *
            wkpNorm (d := Module.finrank ℝ E) k p v
              (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  have h_smooth := transCoeffE_smooth (I := I) (M := M) g r s β α P Q
  have h_cpt := transCoeffE_cpt (I := I) (M := M) g r s β α P Q
  obtain ⟨C, hC_nonneg, hC_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) h_smooth h_cpt k
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) k hp hp_top
      (chartTargetEuclid_isOpen (I := I) (M := M) β)
      h_smooth hC_nonneg (fun j hj y _ => hC_bound y j hj)
  refine ⟨K, hK_pos, fun {v} hv => ⟨?_, hK_bound hv⟩⟩
  exact MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) k hp
    (chartTargetEuclid_isOpen (I := I) (M := M) β)
    h_smooth (fun j hj y _ => hC_bound y j hj) hv

/-- A source component supported in the coordinate image of any fixed
compact subset of its source chart contributes a quantitatively controlled
`W^{k,p}` function in every target chart.  This is the local-support form
needed after applying a strict fine-chart cutoff; it does not require the
source to stay inside the canonical atlas POU support. -/
theorem secTermJointOn
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (β α : M) (P Q : TensorCompIdx (E := E) r s)
    {K₀ : Set M} (hK₀ : IsCompact K₀)
    (hK₀src : K₀ ⊆ (chartAt H β).source) :
    ∃ K : ℝ, 0 < K ∧ ∀ {v : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M) β) →
      tsupport v ⊆
          (fun x : M => toEuclidean (E := E) (extChartAt I β x)) '' K₀ →
      MemWkp (d := Module.finrank ℝ E) k p
          (secTransTerm (I := I) (M := M) g r s β α P Q v)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        wkpNorm (d := Module.finrank ℝ E) k p
            (secTransTerm (I := I) (M := M) g r s β α P Q v)
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K *
            wkpNorm (d := Module.finrank ℝ E) k p v
              (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  obtain ⟨K_mul, hK_mul_pos, hK_mul⟩ :=
    coeffMulJointK (I := I) (M := M) g r s k hp hp_top β α P Q
  obtain ⟨K_cross, hK_cross_pos, hK_cross⟩ :=
    crossChartJointK (I := I) (M := M) g k hp hp_top α β
      (K_α := K₀) hK₀ hK₀src
  refine ⟨K_cross * K_mul, mul_pos hK_cross_pos hK_mul_pos, ?_⟩
  intro v hv hv_support
  have hmul := hK_mul hv
  have hprod_support :
      tsupport
          (fun y => transCoeffE (I := I) (M := M) g r s β α P Q y * v y) ⊆
        (fun x : M => toEuclidean (E := E) (extChartAt I β x)) '' K₀ :=
    (tsupport_mul_subset_right
      (f := transCoeffE (I := I) (M := M) g r s β α P Q)
      (g := v)).trans hv_support
  have hcross := hK_cross hmul.1 hprod_support
  refine ⟨hcross.1, ?_⟩
  calc
    wkpNorm (d := Module.finrank ℝ E) k p
        (secTransTerm (I := I) (M := M) g r s β α P Q v)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal K_cross *
        wkpNorm (d := Module.finrank ℝ E) k p
          (fun y => transCoeffE (I := I) (M := M) g r s β α P Q y * v y)
          (chartTargetEuclid (I := I) (M := M) β) := hcross.2
    _ ≤ ENNReal.ofReal K_cross *
        (ENNReal.ofReal K_mul *
          wkpNorm (d := Module.finrank ℝ E) k p v
            (chartTargetEuclid (I := I) (M := M) β)) :=
      mul_le_mul_left' hmul.2 _
    _ = ENNReal.ofReal (K_cross * K_mul) *
        wkpNorm (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M) β) := by
      rw [ENNReal.ofReal_mul hK_cross_pos.le]
      simp only [mul_assoc]

/-- A compactly POU-supported source component contributes a quantitatively
controlled `W^{k,p}` function in every target chart. -/
theorem secTermJointK
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (β α : M) (P Q : TensorCompIdx (E := E) r s) :
    ∃ K : ℝ, 0 < K ∧ ∀ {v : EuclN → ℝ},
      MemWkp (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M) β) →
      tsupport v ⊆ chartImagePOUTsupport (I := I) (M := M) β →
      MemWkp (d := Module.finrank ℝ E) k p
          (secTransTerm (I := I) (M := M) g r s β α P Q v)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        wkpNorm (d := Module.finrank ℝ E) k p
            (secTransTerm (I := I) (M := M) g r s β α P Q v)
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K *
            wkpNorm (d := Module.finrank ℝ E) k p v
              (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  obtain ⟨K_mul, hK_mul_pos, hK_mul⟩ :=
    coeffMulJointK (I := I) (M := M) g r s k hp hp_top β α P Q
  obtain ⟨K_cross, hK_cross_pos, hK_cross⟩ :=
    crossChartJointK (I := I) (M := M) g k hp hp_top α β
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
    wkpNorm (d := Module.finrank ℝ E) k p
        (secTransTerm (I := I) (M := M) g r s β α P Q v)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal K_cross *
        wkpNorm (d := Module.finrank ℝ E) k p
          (fun y => transCoeffE (I := I) (M := M) g r s β α P Q y * v y)
          (chartTargetEuclid (I := I) (M := M) β) := hcross.2
    _ ≤ ENNReal.ofReal K_cross *
        (ENNReal.ofReal K_mul *
          wkpNorm (d := Module.finrank ℝ E) k p v
            (chartTargetEuclid (I := I) (M := M) β)) :=
      mul_le_mul_left' hmul.2 _
    _ = ENNReal.ofReal (K_cross * K_mul) *
        wkpNorm (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M) β) := by
      rw [ENNReal.ofReal_mul hK_cross_pos.le]
      simp only [mul_assoc]

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
