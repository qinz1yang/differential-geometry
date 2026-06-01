import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentSobolevBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentSobolevBoundDerivBridge
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceReverse

/-!
# Chosen weak partial vs classical Fréchet partial bridge

For a closed Riemannian manifold `(M, g)`, a chart `α : M`, and a smooth
scalar field `u : M → ℝ`, the chart-pushed image
`chartPushed (chartAtlasPOU I M) α u` belongs to `MemW1p 2` of the
Euclidean chart target. The iterated-Sobolev infrastructure exposes a
canonical representative `chosenWeakPartial' 2 k (chartPushed _) ChTE`
of the weak partial in direction `e_k`; this file identifies that
representative, almost everywhere on the chart target, with the
classical Fréchet partial in direction `EuclideanSpace.single k 1` of
either

* the globally smooth extension `chartSmoothExt α (ρ_α u)`
  (the form that emerges directly from the weak-partial uniqueness
  argument), or
* the chart-pushed function `chartPushed (chartAtlasPOU I M) α u`
  itself (the form most natural for downstream chart-local estimates).

The two pointwise forms coincide almost everywhere because both
functions agree pointwise on the open chart target, and on an open set
the Fréchet derivative depends only on local values.

The headline corollary specialises the bridge to the manifold-side
tensor scalar component `tensorChartComponentScalar g r s S α Idx Jdx`,
which is globally smooth on `M` whenever `S` is a smooth
compactly-supported tensor section. This is the foundation for the
uniform partial `L^2` bound on chart-pushed tensor components.

All public theorems consume only the smoothness of `u` (or smoothness of
the tensor scalar component) and the closed-Riemannian-manifold
hypotheses. No new axioms are introduced.
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

/-- **Smooth bridge (`chartSmoothExt` form):** For smooth `u : M → ℝ` on a closed
Riemannian manifold and any chart `α : M`, the chosen weak partial of the
chart-pushed image agrees almost everywhere on the chart target with the
classical Fréchet partial in direction `EuclideanSpace.single k 1` of the
globally-smooth extension `chartSmoothExt α (ρ_α u)`. -/
theorem chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartSmoothExt
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN E => fderiv ℝ
        (chartSmoothExt (I := I) (M := M) α
          (fun z : M => ((chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single k (1 : ℝ))) := by
  have hp_one : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
  exact DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chosenWeakPartial_chartPushed_ae_eq_fderiv
    (I := I) (M := M) α hp_one hu k

/-- For closed manifolds, smooth `u`, and any `y` in the chart target, the
chart-pushed image and the globally-smooth extension `chartSmoothExt α (ρ_α u)`
agree pointwise. This is the chart-target restriction of the a.e. agreement and
underlies the on-target pointwise agreement of their Fréchet derivatives. -/
theorem chartPushed_eq_chartSmoothExt_on_target
    (α : M) (u : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u y =
      chartSmoothExt (I := I) (M := M) α
        (fun z : M => ((chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z) y :=
  (DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.chartSmoothExt_eq_chartPushed_pou_on_target
    (I := I) (M := M) α u hy).symm

/-- The Fréchet derivatives of `chartPushed (chartAtlasPOU I M) α u` and of
`chartSmoothExt α (ρ_α u)` coincide at every point of the chart target. The
two functions agree pointwise on the open chart target, so the derivatives are
determined by the same local values. -/
theorem fderiv_chartPushed_eq_fderiv_chartSmoothExt_on_target
    (α : M) (u : M → ℝ) {y : EuclN E}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    fderiv ℝ (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y =
      fderiv ℝ (chartSmoothExt (I := I) (M := M) α
        (fun z : M => ((chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_nhds : chartTargetEuclid (I := I) (M := M) α ∈ nhds y :=
    h_open.mem_nhds hy
  have h_eventually :
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u =ᶠ[nhds y]
        chartSmoothExt (I := I) (M := M) α
          (fun z : M => ((chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z) := by
    refine Filter.eventually_of_mem h_nhds ?_
    intro z hz
    exact chartPushed_eq_chartSmoothExt_on_target (I := I) (M := M) α u hz
  exact Filter.EventuallyEq.fderiv_eq h_eventually

/-- **Smooth bridge (`chartPushed` form, headline):** For smooth `u : M → ℝ`
on a closed Riemannian manifold and any chart `α : M`, the chosen weak partial
of the chart-pushed image agrees almost everywhere on the chart target with the
classical Fréchet partial in direction `EuclideanSpace.single k 1` of the
chart-pushed function itself. -/
theorem chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartPushed
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN E => fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y
          (EuclideanSpace.single k (1 : ℝ))) := by
  classical
  have h_smooth_form :=
    chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartSmoothExt
      (I := I) (M := M) (α := α) (u := u) hu k
  have h_fderiv_eq_ae :
      (fun y : EuclN E => fderiv ℝ
        (chartSmoothExt (I := I) (M := M) α
          (fun z : M => ((chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
          (EuclideanSpace.single k (1 : ℝ)))
        =ᵐ[(volume : Measure (EuclN E)).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN E => fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y
          (EuclideanSpace.single k (1 : ℝ))) := by
    have h_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    refine Filter.eventually_of_mem (self_mem_ae_restrict h_meas) ?_
    intro y hy
    simp only
    rw [fderiv_chartPushed_eq_fderiv_chartSmoothExt_on_target
      (I := I) (M := M) α u hy]
  exact h_smooth_form.trans h_fderiv_eq_ae

/-- **Bridge for the tensor scalar component (`chartSmoothExt` form):** For a
smooth compactly-supported tensor section `S` on a closed Riemannian
manifold, the chart-pushed image of `tensorChartComponentScalar g r s S α Idx
Jdx` over any chart `β` has its chosen weak partial agreeing almost
everywhere on `chartTargetEuclid β` with the classical Fréchet partial in
direction `EuclideanSpace.single k 1` of the globally-smooth extension. -/
theorem chosenWeakPartial'_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartSmoothExt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx))
        (chartTargetEuclid (I := I) (M := M) β)
      =ᵐ[(volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) β)]
      (fun y : EuclN E => fderiv ℝ
        (chartSmoothExt (I := I) (M := M) β
          (fun z : M => ((chartAtlasPOU I M β
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx z)) y
          (EuclideanSpace.single k (1 : ℝ))) :=
  chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartSmoothExt
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

/-- **Bridge for the tensor scalar component (`chartPushed` form, headline):**
For a smooth compactly-supported tensor section `S` on a closed Riemannian
manifold, the chart-pushed image of `tensorChartComponentScalar g r s S α Idx
Jdx` over any chart `β` has its chosen weak partial agreeing almost
everywhere on `chartTargetEuclid β` with the classical Fréchet partial in
direction `EuclideanSpace.single k 1` of the chart-pushed function itself. -/
theorem chosenWeakPartial'_chartPushed_tensorChartComponentScalar_ae_eq_fderiv_chartPushed
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α β : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 k
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx))
        (chartTargetEuclid (I := I) (M := M) β)
      =ᵐ[(volume : Measure (EuclN E)).restrict
          (chartTargetEuclid (I := I) (M := M) β)]
      (fun y : EuclN E => fderiv ℝ
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S α Idx Jdx)) y
          (EuclideanSpace.single k (1 : ℝ))) :=
  chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartPushed
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

/-- The `eLpNorm` of the chosen weak partial of the chart-pushed image agrees
with the `eLpNorm` of the classical Fréchet partial of the globally-smooth
extension `chartSmoothExt α (ρ_α u)`. -/
theorem eLpNorm_chosenWeakPartial'_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartSmoothExt (I := I) (M := M) α
            (fun z : M => ((chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
  eLpNorm_congr_ae
    (chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartSmoothExt
      (I := I) (M := M) (α := α) (u := u) hu k)

/-- The `eLpNorm` of the chosen weak partial of the chart-pushed image agrees
with the `eLpNorm` of the classical Fréchet partial of the chart-pushed
function itself. -/
theorem eLpNorm_chosenWeakPartial'_chartPushed_eq_eLpNorm_fderiv_chartPushed
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (k : Fin (Module.finrank ℝ E)) :
    eLpNorm
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 k
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) :=
  eLpNorm_congr_ae
    (chosenWeakPartial'_chartPushed_ae_eq_fderiv_chartPushed
      (I := I) (M := M) (α := α) (u := u) hu k)

/-- Specialisation to the manifold-side tensor scalar component
(`chartSmoothExt` form). -/
theorem eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_eq_eLpNorm_fderiv_chartSmoothExt
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
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) =
      eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartSmoothExt (I := I) (M := M) β
            (fun z : M => ((chartAtlasPOU I M β
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
              tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx z)) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) :=
  eLpNorm_chosenWeakPartial'_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

/-- Specialisation to the manifold-side tensor scalar component
(`chartPushed` form). -/
theorem eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_eq_eLpNorm_fderiv_chartPushed
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
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) =
      eLpNorm
        (fun y : EuclN E => fderiv ℝ
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx)) y
            (EuclideanSpace.single k (1 : ℝ))) 2
        (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) :=
  eLpNorm_chosenWeakPartial'_chartPushed_eq_eLpNorm_fderiv_chartPushed
    (I := I) (M := M) (α := β)
    (u := tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
    (tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S α Idx Jdx) k

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
