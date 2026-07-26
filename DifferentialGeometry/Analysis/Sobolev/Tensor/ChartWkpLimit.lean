import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkp
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartAe

/-!
# Chartwise limits for tensor `W^{k,p}` Cauchy sequences

This file performs the first completeness step for the genuine-section carrier
`WkpTensor`.  A Cauchy sequence in the total tensor chart norm is Cauchy in
every scalar chart component, so Euclidean Sobolev completeness supplies a
`MemWkp` limit for every chart and pair of component indices.

The component limits are not declared to be smooth and are not treated as an
independent array-valued replacement for a tensor section.  Instead,
`secModelLimit` reconstructs a model-fibre tensor using the public chart-frame
basis, `secModelPull` pulls such a measurable model field back to the genuine
dependent tensor fibre, and `tensorLimitSec` takes the finite atlas-POU sum.
The remaining analytic step is to prove the tensor chart-transition
`W^{k,p}` bound which places this genuine candidate in `MemWkpTensor` and
proves convergence in the total norm.
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

/-- A fixed scalar chart component is bounded by the total tensor chart norm. -/
theorem wkpNorm_secComp_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ) (p : ℝ≥0∞)
    (S : RSTensorSection I M r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wkpNorm (d := Module.finrank ℝ E) k p
        (secChartComp (I := I) (M := M) r s S α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      wkpTensorNorm (I := I) (M := M) g k p S := by
  unfold wkpTensorNorm
  have hJ :
      wkpNorm (d := Module.finrank ℝ E) k p
          (secChartComp (I := I) (M := M) r s S α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) k p
            (secChartComp (I := I) (M := M) r s S α Idx Jdx')
            (chartTargetEuclid (I := I) (M := M) α) := by
    exact Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ Jdx)
  have hI :
      (∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) k p
            (secChartComp (I := I) (M := M) r s S α Idx Jdx')
            (chartTargetEuclid (I := I) (M := M) α)) ≤
        ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) k p
              (secChartComp (I := I) (M := M) r s S α Idx' Jdx')
              (chartTargetEuclid (I := I) (M := M) α) := by
    exact Finset.single_le_sum
      (fun _ _ => Finset.sum_nonneg (fun _ _ => zero_le _))
      (Finset.mem_univ Idx)
  exact hJ.trans (hI.trans (ENNReal.le_tsum α))

/-- Total-norm Cauchy convergence implies scalar `wkpNorm` Cauchy convergence
in every fixed chart component. -/
theorem secComp_cauchy
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpNorm (d := Module.finrank ℝ E) k p
        (fun y =>
          secChartComp (I := I) (M := M) r s (u m).1 α Idx Jdx y -
            secChartComp (I := I) (M := M) r s (u n).1 α Idx Jdx y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h_cauchy ε hε
  refine ⟨N, ?_⟩
  intro m n hm hn
  have hcomp := wkpNorm_secComp_le (I := I) (M := M) g k p
    ((u m).1 - (u n).1) α Idx Jdx
  have hle := hcomp.trans (hN m n hm hn)
  rw [secChartComp_sub (I := I) (M := M)] at hle
  exact hle

/-- Euclidean completeness gives an actual scalar Sobolev limit for each
chart and tensor component. -/
theorem exists_secComp_lim
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
      MemWkp (d := Module.finrank ℝ E) k p v
          (chartTargetEuclid (I := I) (M := M) α) ∧
        Tendsto
          (fun n => wkpNorm (d := Module.finrank ℝ E) k p
            (fun y =>
              secChartComp (I := I) (M := M) r s (u n).1 α Idx Jdx y -
                v y)
            (chartTargetEuclid (I := I) (M := M) α))
          atTop (𝓝 0) := by
  exact MemWkp.exists_limit_of_wkpNorm_cauchy
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    k p hp hp_top (fun n => (u n).2 α Idx Jdx)
    (secComp_cauchy (I := I) (M := M) g r s k hp u h_cauchy α Idx Jdx)

/-- The chosen scalar Sobolev limit of one chart component. -/
noncomputable def secCompLimit
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  (exists_secComp_lim (I := I) (M := M) g r s k hp hp_top u
    h_cauchy α Idx Jdx).choose

/-- The chosen scalar component limit belongs to Euclidean `W^{k,p}`. -/
theorem secCompLimit_mem
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) k p
      (secCompLimit (I := I) (M := M) g r s k hp hp_top u
        h_cauchy α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (exists_secComp_lim (I := I) (M := M) g r s k hp hp_top u
    h_cauchy α Idx Jdx).choose_spec.1

/-- The original component sequence converges in `wkpNorm` to its chosen
scalar Sobolev limit. -/
theorem secCompLimit_tendsto
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Tendsto
      (fun n => wkpNorm (d := Module.finrank ℝ E) k p
        (fun y =>
          secChartComp (I := I) (M := M) r s (u n).1 α Idx Jdx y -
            secCompLimit (I := I) (M := M) g r s k hp hp_top u
              h_cauchy α Idx Jdx y)
        (chartTargetEuclid (I := I) (M := M) α))
      atTop (𝓝 0) :=
  (exists_secComp_lim (I := I) (M := M) g r s k hp hp_top u
    h_cauchy α Idx Jdx).choose_spec.2

/-- The closed-kernel representative of a chosen component limit.  It is
pointwise zero off `chartImagePOUTsupport α`; support inheritance later proves
that it is a.e. equal to `secCompLimit` on the chart target. -/
noncomputable def secCompRep
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  compactRep (chartImagePOUTsupport (I := I) (M := M) α)
    (secCompLimit (I := I) (M := M) g r s k hp hp_top u
      h_cauchy α Idx Jdx)

/-- The canonical model-fibre tensor reconstructed from all chosen scalar
component limits in one chart.  This field is only Sobolev regular. -/
noncomputable def secModelLimit
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M) (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    TensorRSModel r s ℝ E :=
  ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      secCompRep (I := I) (M := M) g r s k hp hp_top u
          h_cauchy α Idx Jdx y •
        tensorChartBasisElement (E := E) r s Idx Jdx

/-- Projecting the reconstructed model tensor recovers the chosen component
limit. -/
theorem secModelLimit_proj
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M) (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentProjection (E := E) r s Idx Jdx
        (secModelLimit (I := I) (M := M) g r s k hp hp_top u
          h_cauchy α y) =
      secCompRep (I := I) (M := M) g r s k hp hp_top u
        h_cauchy α Idx Jdx y := by
  classical
  rw [secModelLimit, map_sum, Finset.sum_eq_single Idx]
  · rw [map_sum, Finset.sum_eq_single Jdx]
    · rw [map_smul, smul_eq_mul,
        tensorChartComponentProjection_basisElement (E := E)
          r s Idx Idx Jdx Jdx]
      simp
    · intro Jdx' _ hJdx
      rw [map_smul, smul_eq_mul,
        tensorChartComponentProjection_basisElement (E := E)
          r s Idx Idx Jdx Jdx', if_pos rfl, if_neg hJdx,
        mul_zero, mul_zero]
    · simp
  · intro Idx' _ hIdx
    rw [map_sum]
    refine Finset.sum_eq_zero ?_
    intro Jdx' _
    rw [map_smul, smul_eq_mul,
      tensorChartComponentProjection_basisElement (E := E)
        r s Idx Idx' Jdx Jdx', if_neg (Ne.symm hIdx),
      zero_mul, mul_zero]
  · simp

/-- Pull a model-fibre field on the Euclidean target back to the genuine
tensor fibre of chart `α`, extending it by zero outside the chart source. -/
noncomputable def secModelPull (r s : ℕ) (α : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      TensorRSModel r s ℝ E) : RSTensorSection I M r s :=
  fun x =>
    if hx : x ∈ (chartAt H α).source then
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z) α).symmL ℝ x
          (v (toEuclidean (extChartAt I α x)))
    else 0

/-- The genuine dependent tensor-section candidate obtained by taking the
finite atlas-POU sum of the reconstructed chartwise model limits. -/
noncomputable def tensorLimitSec
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε) :
    RSTensorSection I M r s :=
  fun x =>
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      secModelPull (I := I) (M := M) r s α
        (secModelLimit (I := I) (M := M) g r s k hp hp_top u
          h_cauchy α) x

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
