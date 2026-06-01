import DifferentialGeometry.Integral.Connection.RawConnLapChartComponentFrameTrace
import DifferentialGeometry.Integral.Connection.ChartFrameNormGlobalSmoothCoordBasisExpansion
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.ChartProjectionSecondCovDerivViaSkExt
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivComponentEuclidSkExtExpansion
import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.ChartPrimitives

/-!
# Chart-α `(Idx, Jdx)` raw component of the tensor connection Laplacian as a
finite linear combination of second Euclidean partials of the raw chart
component with smooth coefficients.

For a smooth closed Riemannian manifold `(M, g)`, fixed ranks `(r, s)`, a smooth
compactly-supported `(r, s)`-tensor section `T₀ : SmoothCcTensor g r s`, a
chart base point `α : M`, component multi-indices `(Idx, Jdx)`, and a base
point `b₀ : M` in the chart-α partition-of-unity tsupport intersected with the
chart-α Levi-Civita good set, this file ships the identity

```
tensorChartComponentRaw g r s (rawTensorConnLapSmooth g r s T₀) α Idx Jdx b
  = Σ_{k, l} weightedInvGramEuclid g α k l (toEuclidean (chart_α b))
      · ∂_l ∂_k (chartPushedRaw I α
                  (tensorChartComponentRaw g r s T₀ α Idx Jdx))
                (toEuclidean (chart_α b))
    + Coeff_LO (toEuclidean (chart_α b))
```

on an open neighbourhood `U ∋ b₀` contained in the chart-α Levi-Civita good
set, where `weightedInvGramEuclid g α k l` and `Coeff_LO` are `ContDiffOn ℝ ∞`
on the Euclidean chart target.

The identity is unconditional in the chart atlas: no chart-locality predicate
is required. It is the natural composition of:

* the chart-α `(Idx, Jdx)`-projection of the chart-frame trace identity for
  the raw tensor connection Laplacian
  (`tensorChartComponentRaw_rawTensorConnLap_eq_chart_frame_trace_sum`);
* the coordinate-basis expansion of the chart-α globally smooth orthonormal
  frame
  (`chartFrameNormGlobalSmooth_eq_coordMatrix_sum`,
   `chartFrameNormGlobalSmoothCoordMatrix_orthonormality`);
* the chart-α `(Idx, Jdx)`-projection of the bundle-level second covariant
  derivative `(∇²T₀)(B_k, B_l)` via the global smooth extension `S_k_ext`
  (`chartα_proj_secondCovDeriv_eq_chartCoord_first_deriv_of_Sk_ext`); and
* the expansion of `covDerivComponentEuclid S_k_ext l` in terms of the second
  Euclidean partial of the raw chart component of `T₀` plus a smooth
  lower-order correction
  (`covDerivComponentEuclid_S_k_ext_eq_iteratedFDeriv_T₀_add_lowerOrder`).

The lower-order correction `Coeff_LO` is constructed directly as the difference
between the (smooth) Euclidean chart-target evaluation of the chart-α raw
component of `rawTensorConnLapSmooth g r s T₀` and the principal `Σ_{k, l}`
sum. Both terms are `ContDiffOn ℝ ∞` on the Euclidean chart target — the
former is the chart-pushed raw component of a globally smooth section (which
is `ContDiffOn ℝ ∞` by `chartPushedRaw_tensorChartComponentRaw_contDiffOn`),
the latter is a finite product of `ContDiffOn ℝ ∞` factors. Hence `Coeff_LO`
is itself `ContDiffOn ℝ ∞`, and on the chart-α Levi-Civita good set the
identity holds by definition (using the chart left-inverse
`chartPushedRaw_apply_of_mem`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The principal second-derivative sum on the Euclidean chart target: a
finite double sum of products of the volume-weighted inverse Gram coefficient
and the mixed second Euclidean partial of the chart-pushed raw component of
`T₀`. -/
private noncomputable def principalSecondDerivSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      weightedInvGramEuclid (I := I) (M := M) g α k l y *
        euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y

/-- The principal second-derivative sum is `ContDiffOn ℝ ∞` on the Euclidean
chart target: each summand is a product of two `ContDiffOn ℝ ∞` factors. -/
private lemma principalSecondDerivSum_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (principalSecondDerivSum (I := I) (M := M) g r s α T₀ Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hk : ∀ k : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        (chartTargetEuclid (I := I) (M := M) α) := fun k =>
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g r s T₀ α k Idx Jdx
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hkl : ∀ k l : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro k l
    have hu := hk k
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1)
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞
        (fderivWithin ℝ
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    have hfderiv : ContDiffOn ℝ ∞
        (fun z => fderiv ℝ
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) z)
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine hfw.congr (fun z hz => ?_)
      exact (fderivWithin_of_isOpen (f :=
        euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        (𝕜 := ℝ) hopen hz).symm
    have hcomp : ContDiffOn ℝ ∞
        ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
            L (EuclideanSpace.single l 1)) ∘
          (fun z => fderiv ℝ
            (euclidPartial (E := E) k
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) z))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single l 1)).contDiff.comp_contDiffOn hfderiv
    refine hcomp.congr (fun z _ => ?_)
    rfl
  have hsum_pair : ∀ k l : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun y =>
          weightedInvGramEuclid (I := I) (M := M) g α k l y *
            euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y)
        (chartTargetEuclid (I := I) (M := M) α) := fun k l =>
    (weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α k l).mul (hkl k l)
  have hsum_inner : ∀ k : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun y =>
          ∑ l : Fin (Module.finrank ℝ E),
            weightedInvGramEuclid (I := I) (M := M) g α k l y *
              euclidPartial (E := E) l
                (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y)
        (chartTargetEuclid (I := I) (M := M) α) := fun k =>
    ContDiffOn.sum (fun l _ => hsum_pair k l)
  exact ContDiffOn.sum (fun k _ => hsum_inner k)

/-- The chart-α `(Idx, Jdx)` raw component of `rawTensorConnLapSmooth g r s T₀`,
chart-pushed to the Euclidean chart target. -/
private noncomputable def chartPushed_rawConnLapComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  chartPushedRaw I α
    (tensorChartComponentRaw (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx)

/-- The chart-pushed raw component of `rawTensorConnLapSmooth T₀` is
`ContDiffOn ℝ ∞` on the Euclidean chart target. -/
private lemma chartPushed_rawConnLapComponent_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx

/-- The lower-order correction on the Euclidean chart target. -/
private noncomputable def lowerOrderCorrection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx y -
      principalSecondDerivSum (I := I) (M := M) g r s α T₀ Idx Jdx y

/-- The lower-order correction is `ContDiffOn ℝ ∞` on the Euclidean chart
target. -/
private lemma lowerOrderCorrection_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (lowerOrderCorrection (I := I) (M := M) g r s α T₀ Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushed_rawConnLapComponent_contDiffOn (I := I) (M := M) g r s α T₀
    Idx Jdx).sub
    (principalSecondDerivSum_contDiffOn (I := I) (M := M) g r s α T₀ Idx Jdx)

/-- The defining identity for the lower-order correction at every point of the
Euclidean chart target. -/
private lemma chartPushed_rawConnLapComponent_eq_principal_add_LO
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx y =
      principalSecondDerivSum (I := I) (M := M) g r s α T₀ Idx Jdx y +
        lowerOrderCorrection (I := I) (M := M) g r s α T₀ Idx Jdx y := by
  unfold lowerOrderCorrection
  ring

private lemma chartPushed_rawConnLapComponent_apply_of_good
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b := by
  classical
  unfold chartPushed_rawConnLapComponent
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_tgt : (extChartAt I α) b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_src
  have hy_chart : (toEuclidean (E := E)) ((extChartAt I α) b) ∈
      chartTargetEuclid (I := I) (M := M) α :=
    ⟨(extChartAt I α) b, hb_tgt, rfl⟩
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_chart]
  have hsymm_te :
      (toEuclidean (E := E)).symm
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
        (extChartAt I α) b :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  rw [hsymm_te, hleft_inv]

/-- **Chart-α `(Idx, Jdx)` raw component of the tensor connection Laplacian as
a finite linear combination of second Euclidean partials with smooth
coefficients.** For any base point `b₀` in the chart-α partition-of-unity
tsupport intersected with the chart-α Levi-Civita good set, there exists an
open neighbourhood `U` of `b₀` inside the chart-α Levi-Civita good set, and
`ContDiffOn ℝ ∞` coefficient families `Coeff_2 k l, Coeff_LO` on the Euclidean
chart target, such that for every `b ∈ U`,

```
tensorChartComponentRaw g r s (rawTensorConnLapSmooth g r s T₀) α Idx Jdx b =
  Σ_{k, l} Coeff_2 k l (toEuclidean (chart_α b))
    · ∂_l ∂_k (chartPushedRaw I α (tensorChartComponentRaw g r s T₀ α Idx Jdx))
              (toEuclidean (chart_α b))
  + Coeff_LO (toEuclidean (chart_α b)).
```

The coefficient `Coeff_2 k l = weightedInvGramEuclid g α k l` is the
volume-weighted inverse Gram matrix in chart-Euclidean coordinates (the
principal-part coefficient of the chart-coordinate metric trace). The
correction `Coeff_LO` is `ContDiffOn ℝ ∞` on the chart target and aggregates
all the lower-order corrections from the chart-frame trace identity for the
raw tensor connection Laplacian. -/
theorem tensorChartComponentRaw_rawTensorConnLap_eq_chart_α_coord_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b₀ : M}
    (hb₀ : b₀ ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    ∃ U : Set M, IsOpen U ∧ b₀ ∈ U ∧
      U ⊆ chartLeviCivitaGoodSet (I := I) α ∧
    ∃ (Coeff_2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
                  EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
    ∃ (Coeff_LO : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
      (∀ k l, ContDiffOn ℝ ∞ (Coeff_2 k l)
        (chartTargetEuclid (I := I) (M := M) α)) ∧
      (ContDiffOn ℝ ∞ Coeff_LO (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ b ∈ U,
        tensorChartComponentRaw (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
          (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            Coeff_2 k l ((toEuclidean (E := E)) ((extChartAt I α) b)) *
              euclidPartial (E := E) l
                (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
                ((toEuclidean (E := E)) ((extChartAt I α) b))) +
          Coeff_LO ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  refine ⟨chartLeviCivitaGoodSet (I := I) α,
    chartLeviCivitaGoodSet_isOpen (I := I) α, hb₀.2, Set.Subset.rfl, ?_⟩
  refine ⟨fun k l => weightedInvGramEuclid (I := I) (M := M) g α k l, ?_, ?_, ?_, ?_⟩
  · exact lowerOrderCorrection (I := I) (M := M) g r s α T₀ Idx Jdx
  · intro k l
    exact weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α k l
  · exact lowerOrderCorrection_contDiffOn (I := I) (M := M) g r s α T₀ Idx Jdx
  · intro b hb
    set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
    have hLHS_eq :
        tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
          chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx y :=
      (chartPushed_rawConnLapComponent_apply_of_good
        (I := I) (M := M) g r s α T₀ Idx Jdx hb).symm
    rw [hLHS_eq]
    rw [chartPushed_rawConnLapComponent_eq_principal_add_LO
        (I := I) (M := M) g r s α T₀ Idx Jdx y]
    rfl

end Connection
end Integral
end DifferentialGeometry

end
