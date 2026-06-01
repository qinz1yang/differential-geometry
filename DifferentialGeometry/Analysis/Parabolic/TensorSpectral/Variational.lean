import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The variational tensor Laplacian on a closed Riemannian manifold

For a closed smooth Riemannian manifold `(M, g)` we construct the resolvent
operator `(1 - Δ_∇)⁻¹ : TensorL2 r s g → TensorH1Compl g r s` of the
variational tensor Laplacian.

The construction uses the H¹ Hilbert completion `TensorH1Compl g r s` and
the Lax-Milgram theorem.  The bilinear form
`B(u, v) := ⟨u, v⟩_{TensorH1Compl}`
is the inner product on `TensorH1Compl g r s` itself, hence trivially
continuous, symmetric, and coercive (with coercivity constant `1`).

For each `f ∈ TensorL2 r s g`, the linear functional
`L_f(v) := ⟨TensorH1ComplToTensorL2 v, f⟩_{L²}`
is continuous on `TensorH1Compl g r s`.  By Lax-Milgram, there is a unique
`u ∈ TensorH1Compl g r s` satisfying `B(u, v) = L_f(v)` for every `v`, i.e.
the variational equation `(1 - Δ_∇) u = f` in the H¹-dual sense.

`tensorResolvent g r s f := u`, and the assignment is continuous and
ℝ-linear in `f`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum in
`(-∞, 0]`. The resolvent is `(1 - Δ_∇)⁻¹` (spectrum in `[1, ∞)`, always
invertible).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The bilinear form `B(u, v) := ⟨u, v⟩_{TensorH1Compl}` packaged as a
continuous bilinear map
`TensorH1Compl g r s →L[ℝ] TensorH1Compl g r s →L[ℝ] ℝ`. This is the inner
product of `TensorH1Compl g r s` itself. -/
noncomputable def tensorH1ComplBilin (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s →L[ℝ] TensorH1Compl g r s →L[ℝ] ℝ :=
  innerSL ℝ

@[simp] lemma tensorH1ComplBilin_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u v : TensorH1Compl g r s) :
    tensorH1ComplBilin (I := I) (M := M) g r s u v = ⟪u, v⟫_ℝ := rfl

/-- Coercivity of the bilinear form `B = ⟨·, ·⟩` on `TensorH1Compl g r s`:
`B(u, u) = ‖u‖²`. -/
lemma tensorH1ComplBilin_isCoercive (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCoercive (tensorH1ComplBilin (I := I) (M := M) g r s) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u
  rw [one_mul]
  rw [show tensorH1ComplBilin (I := I) (M := M) g r s u u = ⟪u, u⟫_ℝ from rfl]
  rw [real_inner_self_eq_norm_sq]
  ring_nf
  exact le_refl _

/-- The map `f ↦ L_f : TensorL2 r s g →L[ℝ] (TensorH1Compl g r s →L[ℝ] ℝ)` is
continuous and linear, where
`L_f(v) := ⟨TensorH1ComplToTensorL2 v, f⟩_{L²}`.

Constructed as the composition
`f ↦ ⟨·, f⟩_{L²} ↦ (⟨·, f⟩_{L²}) ∘ TensorH1ComplToTensorL2`. -/
noncomputable def tensorLpFunctionalCLM (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] (TensorH1Compl g r s →L[ℝ] ℝ) :=
  let applyL :
      (TensorL2 r s g →L[ℝ] ℝ) →L[ℝ]
        (TensorH1Compl g r s →L[ℝ] TensorL2 r s g) →L[ℝ]
        (TensorH1Compl g r s →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (TensorH1Compl g r s) (TensorL2 r s g) ℝ
  ((applyL.flip) (TensorH1ComplToTensorL2 (I := I) (M := M) g r s)).comp
    (innerSL ℝ : TensorL2 r s g →L[ℝ] TensorL2 r s g →L[ℝ] ℝ)

@[simp] lemma tensorLpFunctionalCLM_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) (v : TensorH1Compl g r s) :
    tensorLpFunctionalCLM (I := I) (M := M) g r s f v =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ := by
  change (innerSL ℝ f) (TensorH1ComplToTensorL2 (I := I) (M := M) g r s v) =
    ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ
  rw [innerSL_apply_apply]
  exact real_inner_comm (TensorH1ComplToTensorL2 (I := I) (M := M) g r s v) f

/-- The Lax-Milgram operator associated with the bilinear form `B = inner` on
`TensorH1Compl g r s`. By the Riesz isomorphism on the Hilbert space
`TensorH1Compl g r s`, this is in fact the identity, but we go through
Lax-Milgram for the standard abstract framework. -/
noncomputable def tensorH1ComplLaxMilgramEquiv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorH1Compl g r s ≃L[ℝ] TensorH1Compl g r s :=
  IsCoercive.continuousLinearEquivOfBilin
    (tensorH1ComplBilin_isCoercive (I := I) (M := M) g r s)

/-- Defining property of `tensorH1ComplLaxMilgramEquiv`: it solves
`⟪tensorH1ComplLaxMilgramEquiv u, w⟫ = ⟪u, w⟫`, i.e. it is the identity. -/
@[simp] lemma tensorH1ComplLaxMilgramEquiv_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u w : TensorH1Compl g r s) :
    ⟪tensorH1ComplLaxMilgramEquiv (I := I) (M := M) g r s u, w⟫_ℝ = ⟪u, w⟫_ℝ :=
  IsCoercive.continuousLinearEquivOfBilin_apply _ u w

/-- The Riesz representative of an element of the dual of `TensorH1Compl g r s`,
recovered via `InnerProductSpace.toDual`. We work through `LinearMap`-level
constructions to avoid the conjugate-linear `ₛₗᵢ⋆` typing of the dual map. -/
noncomputable def tensorH1ComplRieszRepr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    (TensorH1Compl g r s →L[ℝ] ℝ) →L[ℝ] TensorH1Compl g r s :=
  LinearMap.mkContinuous
    { toFun := fun φ => (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ
      map_add' := fun φ ψ => by
        exact (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm.map_add φ ψ
      map_smul' := fun c φ => by
        change (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm (c • φ) =
          c • (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ
        rw [LinearIsometryEquiv.map_smulₛₗ
          (InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm c φ]
        rfl }
    1 (fun φ => by
      change ‖(InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ‖ ≤ 1 * ‖φ‖
      rw [one_mul]
      exact le_of_eq
        ((InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm.norm_map φ))

/-- Defining property of the Riesz representative on `TensorH1Compl g r s`. -/
lemma tensorH1ComplRieszRepr_inner (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (φ : TensorH1Compl g r s →L[ℝ] ℝ) (w : TensorH1Compl g r s) :
    ⟪tensorH1ComplRieszRepr (I := I) (M := M) g r s φ, w⟫_ℝ = φ w := by
  change ⟪(InnerProductSpace.toDual ℝ (TensorH1Compl g r s)).symm φ, w⟫_ℝ = φ w
  exact InnerProductSpace.toDual_symm_apply
    (𝕜 := ℝ) (E := TensorH1Compl g r s) (x := w) (y := φ)

/-- The resolvent operator
`(1 - Δ_∇)⁻¹ : TensorL2 r s g →L[ℝ] TensorH1Compl g r s`.

For each `f ∈ TensorL2 r s g`, `tensorResolvent g r s f` is the unique
element `u ∈ TensorH1Compl g r s` satisfying the variational equation
`⟨u, v⟩_{TensorH1Compl} = ⟨TensorH1ComplToTensorL2 v, f⟩_{L²}` for every
`v ∈ TensorH1Compl g r s`.

This is the Lax-Milgram solution to the equation `(1 - Δ_∇) u = f` in the
H¹-dual sense, with the geometer Laplacian sign convention. -/
noncomputable def tensorResolvent (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] TensorH1Compl g r s :=
  (tensorH1ComplRieszRepr (I := I) (M := M) g r s).comp
    (tensorLpFunctionalCLM (I := I) (M := M) g r s)

/-- Defining property of the resolvent: for every `f ∈ TensorL2 r s g` and
every test `v ∈ TensorH1Compl g r s`,
`⟨tensorResolvent g r s f, v⟩_{TensorH1Compl}
  = ⟨TensorH1ComplToTensorL2 v, f⟩_{L²}`. -/
theorem tensorResolvent_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) (v : TensorH1Compl g r s) :
    ⟪tensorResolvent (I := I) (M := M) g r s f, v⟫_ℝ =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ := by
  unfold tensorResolvent
  rw [ContinuousLinearMap.comp_apply, tensorH1ComplRieszRepr_inner,
    tensorLpFunctionalCLM_apply]

/-- Equivalent formulation: the resolvent satisfies the variational identity
in the H¹-bilinear-form formulation. -/
theorem tensorResolvent_bilin_eq_lpFunctional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) (v : TensorH1Compl g r s) :
    tensorH1ComplBilin (I := I) (M := M) g r s
        (tensorResolvent (I := I) (M := M) g r s f) v =
      ⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s v, f⟫_ℝ := by
  rw [tensorH1ComplBilin_apply]
  exact tensorResolvent_inner_eq_lpFunctional (I := I) (M := M) g r s f v

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] TensorH1Compl g r s :=
  tensorResolvent (I := I) (M := M) g r s

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
