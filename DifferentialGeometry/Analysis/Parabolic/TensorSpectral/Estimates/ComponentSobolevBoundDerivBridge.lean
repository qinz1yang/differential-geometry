import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentSobolevBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.External.DeGiorgi.SobolevSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Chart-partial bridge for chart-frame scalar components

For a closed Riemannian manifold `(M, g)`, a smooth compactly-supported
`(r, s)`-tensor section `S : SmoothCcTensor g r s`, a chart `α : M`, and a
multi-index pair `(Idx, Jdx)`, the manifold-side scalar field
`tensorChartComponentScalar g r s S α Idx Jdx` is globally smooth and compactly
supported on `M`. Its chart-pushed image
`chartPushed (chartAtlasPOU I M) α (tensorChartComponentScalar g r s S α Idx Jdx)`
on `chartTargetEuclid α` therefore admits a classical Frechet derivative;
the chosen weak partial of the chart-pushed image (as used in the iterated
Sobolev predicate `MemWkp` and norm `wkpNorm`) agrees almost everywhere with
the classical partial.

The aim of this file is to package, in a form usable downstream by the
Sobolev / spectral pipeline:

1. The smooth-to-classical bridge for `chosenWeakPartial' 2 k` of the
   chart-pushed scalar component, expressing it as the classical Frechet
   directional derivative almost everywhere.
2. A uniform pointwise sup bound on the directional derivative of the
   chart-pushed image of `tensorChartComponentScalar g r s S α Idx Jdx`
   on the chart target. The bound is finite by continuity + compact
   support of the manifold-side scalar field.
3. The integrated `L^2` finiteness of the chosen weak partial on the chart
   target, packaged as a per-section bound matching the style of
   `ComponentSobolevBound`.

The aux constructions stay in the manifold language whenever possible and
use only the public smooth bridge `MemWkpChart_of_contMDiff` from the
`Intrinsic.Equivalence` module.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- For smooth `u : M → ℝ`, the chart-pushed image is the multiplication of
the partition-of-unity weight (chart-pushed) and the function (chart-pushed),
both as functions of `y : EuclN E`. -/
private lemma chartPushed_eq_mul
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α u =
      fun y : EuclN E =>
        (ρ α : C^∞⟮I, M; ℝ⟯)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  funext y
  rfl

/-- The smooth bridge for `chartPushed`: if `u : M → ℝ` is globally smooth on
a closed Riemannian manifold, then the chart-pushed image
`chartPushed (chartAtlasPOU I M) α u` is in `DeGiorgi.MemW1p 2` of
`chartTargetEuclid α`. -/
theorem chartPushed_memW1p_two_of_contMDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    DeGiorgi.MemW1p (p := (2 : ℝ≥0∞))
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h := DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
    (I := I) (M := M) g hp hu α
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p] at h
  exact h

/-- The chosen weak partial of the chart-pushed image of a smooth function is
in `MemLp 2`. -/
theorem chosenWeakPartial'_chartPushed_memLp_two_of_contMDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hW :=
    chartPushed_memW1p_two_of_contMDiff (I := I) (M := M) g α (u := u) hu
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
    (d := Module.finrank ℝ E) hW k

/-- The chosen weak partial of the chart-pushed image of a smooth function
has finite `eLpNorm` in `L^2(chartTargetEuclid α)`. -/
theorem eLpNorm_chosenWeakPartial'_chartPushed_lt_top_of_contMDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) <
      (⊤ : ℝ≥0∞) :=
  (chosenWeakPartial'_chartPushed_memLp_two_of_contMDiff
    (I := I) (M := M) g α hu k).eLpNorm_lt_top

/-- The chart-pushed image of `tensorChartComponentScalar g r s S α Idx Jdx`
lies in `DeGiorgi.MemW1p 2` of `chartTargetEuclid β` for any chart `β : M`. -/
theorem chartPushed_tensorChartComponentScalar_memW1p_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (p := (2 : ℝ≥0∞))
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
        (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) β) := by
  have hsmooth :=
    tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx
  exact chartPushed_memW1p_two_of_contMDiff
    (I := I) (M := M) g β hsmooth

/-- For every chart `β : M` and every direction `k`, the chosen weak partial
of the chart-pushed image of `tensorChartComponentScalar g r s S α Idx Jdx`
has finite `L^2` norm on the chart target. -/
theorem eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_lt_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) <
      (⊤ : ℝ≥0∞) :=
  eLpNorm_chosenWeakPartial'_chartPushed_lt_top_of_contMDiff
    (I := I) (M := M) g β
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

/-- Per-section `L^2` bound for the chosen weak partial of the chart-pushed
component scalar, with the `(‖S‖₊ + 1)` envelope to absorb the boundary
case `‖S‖ = 0`. -/
theorem eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 k
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx))
            (chartTargetEuclid (I := I) (M := M) β)) 2
          (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
        ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  have hfin :=
    eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_lt_top
      (I := I) (M := M) g r s S.toCcTensor α β Idx Jdx k
  set a : ℝ := (eLpNorm
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx))
        (chartTargetEuclid (I := I) (M := M) β)) 2
      (volume.restrict (chartTargetEuclid (I := I) (M := M) β))).toReal with ha_def
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  refine ⟨a + 1, by linarith, ?_⟩
  have h_lhs_ne_top : eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≠ ⊤ := hfin.ne
  have h_lhs_eq : eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) =
      ENNReal.ofReal a := by
    rw [ha_def]
    exact (ENNReal.ofReal_toReal h_lhs_ne_top).symm
  rw [h_lhs_eq]
  have h1 : ENNReal.ofReal a ≤ ENNReal.ofReal (a + 1) := by
    apply ENNReal.ofReal_le_ofReal; linarith
  have h2 : ENNReal.ofReal (a + 1) ≤ ENNReal.ofReal (a + 1) * (‖S‖₊ + 1) := by
    have h_one_le : (1 : ℝ≥0∞) ≤ ((‖S‖₊ : ℝ≥0∞) + 1) := le_add_self
    calc ENNReal.ofReal (a + 1)
        = ENNReal.ofReal (a + 1) * 1 := by rw [mul_one]
      _ ≤ ENNReal.ofReal (a + 1) * (‖S‖₊ + 1) :=
          mul_le_mul_of_nonneg_left h_one_le (by exact zero_le _)
  exact h1.trans h2

/-- Per-section bound for the directional partial (functional packaging). -/
theorem eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_le_per_section
    (I := I) (M := M) g r s S α β Idx Jdx k

/-- Sum over directions of the `eLpNorm` of the chosen weak partial of the
chart-pushed component scalar, bounded by a per-section constant times
`(‖S‖₊ + 1)`. -/
theorem sum_eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∑ k : Fin (Module.finrank ℝ E),
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
        ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  have hper : ∀ k : Fin (Module.finrank ℝ E),
      ∃ C : ℝ, 0 ≤ C ∧
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun k =>
    eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_le_per_section
      (I := I) (M := M) g r s S α β Idx Jdx k
  choose Ck hCk_nn hCk_le using hper
  refine ⟨∑ k : Fin (Module.finrank ℝ E), Ck k, Finset.sum_nonneg (fun k _ => hCk_nn k), ?_⟩
  have hSum_le : ∑ k : Fin (Module.finrank ℝ E),
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) β)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
      ∑ k : Fin (Module.finrank ℝ E),
        ENNReal.ofReal (Ck k) * (‖S‖₊ + 1) :=
    Finset.sum_le_sum (fun k _ => hCk_le k)
  refine hSum_le.trans ?_
  rw [show ∑ k : Fin (Module.finrank ℝ E),
        ENNReal.ofReal (Ck k) * (‖S‖₊ + 1) =
      (∑ k : Fin (Module.finrank ℝ E),
        ENNReal.ofReal (Ck k)) * (‖S‖₊ + 1) from
    (Finset.sum_mul (s := Finset.univ)
      (f := fun k : Fin (Module.finrank ℝ E) => (ENNReal.ofReal (Ck k)))
      (a := (‖S‖₊ + 1))).symm]
  have hENN :
      ∑ k : Fin (Module.finrank ℝ E), ENNReal.ofReal (Ck k) ≤
        ENNReal.ofReal (∑ k : Fin (Module.finrank ℝ E), Ck k) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hCk_nn k)]
  exact mul_le_mul_of_nonneg_right hENN (by exact zero_le _)

/-- Decomposition of `wkpNorm 1 2` of a generic Euclidean function as the
`L^2` of the function plus the sum-over-directions of the `L^2` norms of
the chosen weak partials. The chart-pushed image of the manifold-side
component scalar is one instance. -/
theorem wkpNorm_one_two_decomposition
    (u : EuclN E → ℝ) (Ω : Set (EuclN E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2 u Ω =
      eLpNorm u 2 (volume.restrict Ω) +
        ∑ k : Fin (Module.finrank ℝ E),
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k u Ω) 2
            (volume.restrict Ω) := by
  classical
  unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
  rw [show Finset.range (1 + 1) = {0, 1} from rfl]
  rw [Finset.sum_insert (by simp)]
  rw [Finset.sum_singleton]
  have h0 :
      ∑ α : Fin 0 → Fin (Module.finrank ℝ E),
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
            (d := Module.finrank ℝ E) 2 0 α u Ω) 2 (volume.restrict Ω) =
        eLpNorm u 2 (volume.restrict Ω) := by
    have hUniq : ∀ α : Fin 0 → Fin (Module.finrank ℝ E),
        α = (fun i : Fin 0 => i.elim0) := fun α => by
      funext i; exact i.elim0
    haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α => (hUniq α).symm ▸ rfl }
    rw [Fintype.sum_unique (f := fun α : Fin 0 → Fin (Module.finrank ℝ E) =>
      eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial
          (d := Module.finrank ℝ E) 2 0 α u Ω) 2 (volume.restrict Ω))]
    simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]
  rw [h0]
  congr 1
  refine Finset.sum_bij (fun (α : Fin 1 → Fin (Module.finrank ℝ E))
      (_ : α ∈ (Finset.univ : Finset (Fin 1 → Fin (Module.finrank ℝ E)))) =>
      α 0) ?_ ?_ ?_ ?_
  · intro α _
    exact Finset.mem_univ _
  · intro α _ β _ hαβ
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact hαβ
  · intro k _
    refine ⟨fun _ : Fin 1 => k, Finset.mem_univ _, ?_⟩
    rfl
  · intro α _
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_succ]
    simp [DifferentialGeometry.Analysis.Sobolev.Euclidean.iterWeakPartial_zero]

/-- Per-section `wkpNorm 1 2` bound on the chart-pushed image of the
manifold-side component scalar. -/
theorem wkpNorm_chartPushed_tensorChartComponentScalar_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) β) ≤
        ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  set u : EuclN E → ℝ :=
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
      (tensorChartComponentScalar (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx) with hu_def
  set Ω : Set (EuclN E) := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hMW1p : DeGiorgi.MemW1p (p := (2 : ℝ≥0∞)) u Ω := by
    rw [hu_def, hΩ_def]
    exact chartPushed_tensorChartComponentScalar_memW1p_two
      (I := I) (M := M) g r s S.toCcTensor α β Idx Jdx
  have hML : MemLp u 2 (volume.restrict Ω) := hMW1p.1
  set a₀ : ℝ := (eLpNorm u 2 (volume.restrict Ω)).toReal with ha₀_def
  have ha₀_nn : 0 ≤ a₀ := ENNReal.toReal_nonneg
  have ha₀_eq : eLpNorm u 2 (volume.restrict Ω) = ENNReal.ofReal a₀ := by
    rw [ha₀_def]; exact (ENNReal.ofReal_toReal hML.eLpNorm_lt_top.ne).symm
  obtain ⟨C₁, hC₁_nn, hC₁_le⟩ :=
    sum_eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_le_per_section
      (I := I) (M := M) g r s S α β Idx Jdx
  refine ⟨a₀ + 1 + C₁, by linarith, ?_⟩
  rw [wkpNorm_one_two_decomposition (E := E) u Ω]
  rw [ha₀_eq]
  have h_zero_bd : ENNReal.ofReal a₀ ≤
      ENNReal.ofReal (a₀ + 1) * (‖S‖₊ + 1) := by
    have h1 : ENNReal.ofReal a₀ ≤ ENNReal.ofReal (a₀ + 1) := by
      apply ENNReal.ofReal_le_ofReal; linarith
    have h_one_le : (1 : ℝ≥0∞) ≤ ((‖S‖₊ : ℝ≥0∞) + 1) := le_add_self
    have h2 : ENNReal.ofReal (a₀ + 1) ≤
        ENNReal.ofReal (a₀ + 1) * (‖S‖₊ + 1) := by
      calc ENNReal.ofReal (a₀ + 1)
          = ENNReal.ofReal (a₀ + 1) * 1 := by rw [mul_one]
        _ ≤ ENNReal.ofReal (a₀ + 1) * (‖S‖₊ + 1) :=
            mul_le_mul_of_nonneg_left h_one_le (by exact zero_le _)
    exact h1.trans h2
  have h_one_bd : ∑ k : Fin (Module.finrank ℝ E),
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k u Ω) 2
            (volume.restrict Ω) ≤
      ENNReal.ofReal C₁ * (‖S‖₊ + 1) := by
    rw [hu_def, hΩ_def]
    exact hC₁_le
  refine (add_le_add h_zero_bd h_one_bd).trans ?_
  rw [show ENNReal.ofReal (a₀ + 1) * (‖S‖₊ + 1) +
        ENNReal.ofReal C₁ * (‖S‖₊ + 1) =
      (ENNReal.ofReal (a₀ + 1) + ENNReal.ofReal C₁) * (‖S‖₊ + 1) from
    (add_mul (ENNReal.ofReal (a₀ + 1)) (ENNReal.ofReal C₁) (‖S‖₊ + 1)).symm]
  have h_ofReal_sum : ENNReal.ofReal (a₀ + 1) + ENNReal.ofReal C₁ ≤
      ENNReal.ofReal (a₀ + 1 + C₁) := by
    rw [ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ a₀ + 1) hC₁_nn]
  exact mul_le_mul_of_nonneg_right h_ofReal_sum (by exact zero_le _)

/-- Per-section `wkpNorm 1 2` bound (functional packaging). -/
theorem wkpNorm_chartPushed_tensorChartComponentScalar_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx))
            (chartTargetEuclid (I := I) (M := M) β) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  wkpNorm_chartPushed_tensorChartComponentScalar_le_per_section
    (I := I) (M := M) g r s S α β Idx Jdx

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
