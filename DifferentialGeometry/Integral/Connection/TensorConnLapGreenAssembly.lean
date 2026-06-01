import DifferentialGeometry.Integral.Connection.TensorConnLapSecondOrderIBP
import DifferentialGeometry.Integral.Connection.TensorCovGradL2InnerDirichletBridge
import DifferentialGeometry.Integral.Connection.RawTensorConnLapChartFrameTrace
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Integral.Connection.TensorRSMetricCompatible
import DifferentialGeometry.Integral.DivergenceTheorem.POUReduction
import DifferentialGeometry.Analysis.Sobolev.Manifold.Rellich

/-!
# Partition-of-unity assembly of the `(0, 2)` connection-Laplacian Green identity

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file develops the partition-of-unity assembly
infrastructure that combines the per-direction second-order integration-by-parts
identity with the chart-frame trace identity to produce the integrated Green
identity for the rough (connection) Laplacian on `(0, 2)`-tensor fields.

The headline target is

```
tensorL2Inner g 0 3 (covGrad g 0 2 T).toFun (covGrad g 0 2 v).toFun
  = − tensorL2Inner g 0 2 (rawTensorConnLapSmooth g 0 2 T).toFun v.toFun.
```

The assembly proceeds by inserting `1 = ∑_α ρ_α` (the chart-atlas partition of
unity) into the integrated Dirichlet pairing, reducing the integrand on each
chart-`α` partition-of-unity tsupport to a diagonal frame sum over the globally
smooth orthonormal chart-`α` frame `chartFrameNormGlobalSmooth g α i`, applying
the per-direction second-order integration-by-parts identity, summing over the
frame index `i` to collapse the second covariant derivative to the rough
Laplacian, and finally summing over `α`.

The genuinely new ingredient supplied here is the **partition-of-unity gradient
cancellation** `chartAtlasPOU_tangentSectionAction_finset_sum_eq_zero`: the sum
over the chart-atlas partition-of-unity Finset of the directional derivatives
`X(ρ_α)` of the partition weights vanishes pointwise, because the partition
weights sum to the constant `1`. This is the algebraic identity through which the
per-chart Leibniz weight terms `B(ρ_α) · ⟨∇_B T, v⟩`, produced by the
partition-of-unity-weighted integration by parts, cancel after summation over
`α`.

## Main results

* `chartAtlasPOU_tangentSectionAction_finset_sum_eq_zero` — the partition-of-unity
  gradient cancellation: `∑_α X(ρ_α) x = 0`.

* `integral_weighted_secondOrder_combined_eq_neg_weightDeriv` — the
  partition-of-unity-weighted second-order combined integration-by-parts
  identity for a fixed smooth tangent vector field `B` and a smooth scalar weight
  `ρ`: the integral of `ρ · (⟨∇_B(∇_B T), v⟩ + ⟨∇_B T, ∇_B v⟩ + ⟨∇_B T, v⟩·divᵍ B)`
  equals minus the integral of the Leibniz weight term `⟨∇_B T, v⟩ · B(ρ)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open Tensor0SNabla TensorRSNabla TensorMetricLowering

section PouGradientCancellation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

/-- **Generic partition-of-unity gradient cancellation.** For a smooth tangent
vector field `X`, a smooth partition of unity `ρ` on `M` indexed by `M`, and a
Finset `S` over which the partition weights sum to the constant `1` at every
point, the sum over `S` of the directional derivatives `X(ρ_α)` vanishes at every
point.

Stated over a *variable* partition `ρ` and a *variable* Finset `S` so that no
opaque `def` (such as `chartAtlasPOU` / `chartAtlasPOU_finset`, built from choice
terms) is unfolded during elaboration. The proof commutes the directional
derivative through the finite sum (`tangentSectionAction_finset_sum`), identifies
the summed weights with the constant `1` on a neighbourhood (here, everywhere),
and uses that the directional derivative of a locally-constant function vanishes
(`EventuallyEq.mfderiv_eq` + `mfderiv_const`). -/
theorem pou_tangentSectionAction_finset_sum_eq_zero
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (S : Finset M)
    (hsum_one : ∀ y : M, ∑ α ∈ S, (ρ α : M → ℝ) y = 1) (x : M) :
    ∑ α ∈ S, tangentSectionAction (I := I) X ((ρ α : M → ℝ)) x = 0 := by
  classical
  have hMDiff_each : ∀ α ∈ S,
      MDifferentiableAt I 𝓘(ℝ) ((ρ α : M → ℝ)) x :=
    fun α _ => (ρ α).contMDiff.mdifferentiable (by simp) x
  rw [← tangentSectionAction_finset_sum (I := I) X S
    (fun α => ((ρ α : M → ℝ))) x hMDiff_each]
  have h_eq_one : (fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y) =ᶠ[𝓝 x]
      (fun _ : M => (1 : ℝ)) :=
    Filter.Eventually.of_forall hsum_one
  unfold tangentSectionAction
  have h_fun_eq : (∑ α ∈ S, (fun β => (ρ β : M → ℝ)) α) =
      fun y : M => ∑ α ∈ S, (ρ α : M → ℝ) y := by
    funext y; rw [Finset.sum_apply]
  rw [h_fun_eq, Filter.EventuallyEq.mfderiv_eq h_eq_one, mfderiv_const]
  rfl

/-- **Partition-of-unity gradient cancellation.** For a smooth tangent vector
field `X` on a closed manifold, the sum over the chart-atlas partition-of-unity
Finset of the directional derivatives `X(ρ_α)` of the partition weights vanishes
at every point:

```
∑_{α ∈ chartAtlasPOU_finset} tangentSectionAction X (ρ_α) x = 0.
```

The proof instantiates the generic `pou_tangentSectionAction_finset_sum_eq_zero`
with the chart-atlas partition of unity and the constant-`1` property
`chartAtlasPOU_finset_sum_eq_one`.

This is the algebraic device through which the per-chart Leibniz weight terms
`B(ρ_α) · ⟨∇_B T, v⟩`, produced by the partition-of-unity-weighted integration by
parts, cancel after summation over `α`. -/
theorem chartAtlasPOU_tangentSectionAction_finset_sum_eq_zero
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        tangentSectionAction (I := I) X
          ((chartAtlasPOU I M α : M → ℝ)) x = 0 := by
  classical
  have hsum_one := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M)
  set ρ : SmoothPartitionOfUnity M I M Set.univ := chartAtlasPOU I M with hρ_def
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  exact pou_tangentSectionAction_finset_sum_eq_zero (I := I) X ρ S hsum_one x

end PouGradientCancellation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The directional derivative of a scalar `f` along the smooth weighted vector
field `ρ · B` equals `ρ` times the directional derivative along `B`. This is the
scalar-linearity of `mfderiv` in the direction (the derivative is a continuous
linear map, hence commutes with the scalar `ρ x` applied to the direction). -/
lemma tangentSectionAction_smoothSmul
    (ρ : M → ℝ) (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : M → ℝ) (x : M) :
    tangentSectionAction (I := I) (smoothSmul (I := I) ρ hρ B) f x =
      ρ x * tangentSectionAction (I := I) B f x := by
  rw [tangentSectionAction_def, tangentSectionAction_def]
  rw [smoothSmul_apply]
  rw [(mfderiv I 𝓘(ℝ) f x).map_smul (ρ x) (B x)]
  rw [smul_eq_mul]

/-- **Partition-of-unity-weighted second-order combined integration by parts.**
For smooth `(0, 2)`-tensor sections `T`, `v`, a smooth tangent vector field `B`,
and a smooth scalar weight `ρ` on a closed Riemannian manifold,

```
∫_M ρ · (⟨(∇_B (∇_B T))ᵇ, vᵇ⟩ + ⟨(∇_B T)ᵇ, (∇_B v)ᵇ⟩ + ⟨∇_B T, v⟩ · divᵍ B) dvol_g
  = − ∫_M ⟨∇_B T, v⟩ · B(ρ) dvol_g,
```

where `(·)ᵇ` denotes metric index-lowering and `B(ρ)` is the directional derivative
of the weight `ρ` along `B`. The left-hand integrand is the `ρ`-weighted form of the
unweighted second-order Leibniz expression of
`integral_secondOrder_combined_eq_zero`; the right-hand side is the Leibniz weight
correction term.

No integrability hypothesis is exposed: it is discharged internally by the scalar
integration-by-parts identity and the smoothness of the inner-product scalar. -/
theorem integral_weighted_secondOrder_combined_eq_neg_weightDeriv
    (g : SmoothRiemannianMetric I M)
    (T v : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (ρ : M → ℝ) (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) :
    ∫ x, ρ x * (tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T B) B x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 2 v x))
          + tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 2
                (covDerivAlongVFSection (I := I) (M := M) g T B) x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v B x))
          + tensorInnerScalar (I := I) (M := M) g 0 2
              (covDerivAlongVFSection (I := I) (M := M) g T B) v x
            * divergence_g (I := I) g B x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, tensorInnerScalar (I := I) (M := M) g 0 2
              (covDerivAlongVFSection (I := I) (M := M) g T B) v x
            * tangentSectionAction (I := I) B ρ x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set W : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
    covDerivAlongVFSection (I := I) (M := M) g T B with hW_def
  set f : M → ℝ := tensorInnerScalar (I := I) (M := M) g 0 2 W v with hf_def
  have hf_smooth : ContMDiff I 𝓘(ℝ) ∞ f :=
    tensorInnerScalar_contMDiff (I := I) (M := M) g 0 2 W v
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothSmul (I := I) ρ hρ B with hY_def
  have hY_cs : HasCompactSupport (Y : ∀ x, TangentSpace I x) :=
    HasCompactSupport.of_compactSpace _
  have hIBP := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hf_smooth Y hY_cs
  have hLHS_pt : ∀ x : M,
      tangentSectionAction (I := I) Y f x =
        ρ x * (tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 W B x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2 v x))
            + tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2 W x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v B x))) := by
    intro x
    rw [hY_def, tangentSectionAction_smoothSmul (I := I) ρ hρ B f x]
    congr 1
    rw [hf_def]
    have hLeibniz := tangentSectionAction_tensorInnerScalar
      (I := I) (M := M) g 0 2 W v B x
    rw [hLeibniz]
    rw [show loweredCovDerivAt (I := I) (M := M) g 0 2 W x (B x) =
          loweredCovDerivAlongVF (I := I) (M := M) g 0 2 W B x from rfl]
    rw [show loweredCovDerivAt (I := I) (M := M) g 0 2 v x (B x) =
          loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v B x from rfl]
  have hRHS_pt : ∀ x : M,
      f x * divergence_g (I := I) g Y x =
        ρ x * (f x * divergence_g (I := I) g B x) +
          f x * tangentSectionAction (I := I) B ρ x := by
    intro x
    rw [hY_def, divergence_g_smoothSmul (I := I) g ρ hρ B x]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hRHS_pt)] at hIBP
  have hf_cont : Continuous f := hf_smooth.continuous
  have hρ_cont : Continuous ρ := hρ.continuous
  have hdivB_cont : Continuous (divergence_g (I := I) g B) :=
    (divergence_g_contMDiff (I := I) g B).continuous
  have hBρ_cont : Continuous (tangentSectionAction (I := I) B ρ) :=
    (tangentSectionAction_contMDiff (I := I) B hρ).continuous
  have h_int_a : Integrable
      (fun x : M => ρ x * (f x * divergence_g (I := I) g B x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g (hρ_cont.mul (hf_cont.mul hdivB_cont))
      (HasCompactSupport.of_compactSpace _)
  have h_int_b : Integrable
      (fun x : M => f x * tangentSectionAction (I := I) B ρ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g (hf_cont.mul hBρ_cont)
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add h_int_a h_int_b, neg_add] at hIBP
  have hgoal_pt : ∀ x : M,
      ρ x * (tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g x
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 W B x))
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2 v x))
            + tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g x
              (Tensor0SSpace.toModel
                (liftedTensorSection (I := I) (M := M) g 0 2 W x))
              (Tensor0SSpace.toModel
                (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v B x))
            + f x * divergence_g (I := I) g B x) =
        tangentSectionAction (I := I) Y f x +
          ρ x * (f x * divergence_g (I := I) g B x) := by
    intro x
    rw [hLHS_pt x]
    ring
  rw [show (fun x : M => ρ x * (tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g x
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 W B x))
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 2 v x))
          + tensorInnerPointwise_0s (I := I) (M := M) (0 + 2) g x
            (Tensor0SSpace.toModel
              (liftedTensorSection (I := I) (M := M) g 0 2 W x))
            (Tensor0SSpace.toModel
              (loweredCovDerivAlongVF (I := I) (M := M) g 0 2 v B x))
          + tensorInnerScalar (I := I) (M := M) g 0 2 W v x
            * divergence_g (I := I) g B x)) =
      (fun x : M => tangentSectionAction (I := I) Y f x +
          ρ x * (f x * divergence_g (I := I) g B x)) from
    funext (fun x => hgoal_pt x)]
  have h_int_act : Integrable (tangentSectionAction (I := I) Y f)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g (tangentSectionAction_contMDiff (I := I) Y hf_smooth).continuous
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add h_int_act h_int_a]
  rw [hIBP]
  ring

end Connection
end Integral
end DifferentialGeometry

end
