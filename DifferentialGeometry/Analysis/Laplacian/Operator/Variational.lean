import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.L2Inclusion
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The variational Laplacian on a closed Riemannian manifold

For a closed smooth Riemannian manifold `(M, g)` we construct the resolvent
operator `(1 - Δ_g)⁻¹ : Lp ℝ 2 μ_g → H1Compl g` of the variational Laplacian.

The construction uses the H¹ Hilbert completion `H1Compl g` and the
Lax-Milgram theorem.  The bilinear form
`B(u, v) := ⟨u, v⟩_{H1Compl}`
is the inner product on `H1Compl g` itself, hence trivially continuous,
symmetric, and coercive (with coercivity constant `1`).

For each `f ∈ Lp ℝ 2 μ_g`, the linear functional
`L_f(v) := ⟨H1ComplToLp v, f⟩_{L²}`
is continuous on `H1Compl g`.  By Lax-Milgram, there is a unique `u ∈ H1Compl g`
satisfying `B(u, v) = L_f(v)` for every `v`, i.e. the variational equation
`(1 - Δ_g) u = f` in the H¹-dual sense.

`resolvent g f := u`, and the assignment is continuous and ℝ-linear in `f`.

## Sign convention

We follow the geometer convention `Δ_g = div_g ∘ grad_g`, with spectrum in
`(-∞, 0]`. The resolvent is `(1 - Δ_g)⁻¹` (spectrum in `[1, ∞)`, always
invertible).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The bilinear form `B(u, v) := ⟨u, v⟩_{H1Compl}` packaged as a continuous
bilinear map `H1Compl g →L[ℝ] H1Compl g →L[ℝ] ℝ`. This is the inner product
of `H1Compl g` itself. -/
noncomputable def H1ComplBilin (g : SmoothRiemannianMetric I M) :
    H1Compl g →L[ℝ] H1Compl g →L[ℝ] ℝ :=
  innerSL ℝ

@[simp] lemma H1ComplBilin_apply (g : SmoothRiemannianMetric I M)
    (u v : H1Compl g) :
    H1ComplBilin (I := I) (M := M) g u v = ⟪u, v⟫_ℝ := rfl

/-- Coercivity of the bilinear form `B = ⟨·, ·⟩` on `H1Compl g`: `B(u, u) = ‖u‖²`. -/
lemma H1ComplBilin_isCoercive (g : SmoothRiemannianMetric I M) :
    IsCoercive (H1ComplBilin (I := I) (M := M) g) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u
  rw [one_mul]
  rw [show H1ComplBilin (I := I) (M := M) g u u = ⟪u, u⟫_ℝ from rfl]
  rw [real_inner_self_eq_norm_sq]
  ring_nf
  exact le_refl _

/-- The map `f ↦ L_f : Lp ℝ 2 μ_g →L[ℝ] (H1Compl g →L[ℝ] ℝ)` is continuous and
linear, where `L_f(v) := ⟨H1ComplToLp v, f⟩_{Lp ℝ 2}`.

Constructed as the composition
`f ↦ ⟨·, f⟩_{Lp} ↦ (⟨·, f⟩_{Lp}) ∘ H1ComplToLp`. -/
noncomputable def lpFunctionalCLM (g : SmoothRiemannianMetric I M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      (H1Compl g →L[ℝ] ℝ) :=
  let applyL : (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ) →L[ℝ]
      (H1Compl g →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) →L[ℝ]
        (H1Compl g →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (H1Compl g)
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) ℝ
  ((applyL.flip) (H1ComplToLp (I := I) (M := M) g)).comp
    (innerSL ℝ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ)

@[simp] lemma lpFunctionalCLM_apply (g : SmoothRiemannianMetric I M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (v : H1Compl g) :
    lpFunctionalCLM (I := I) (M := M) g f v =
      ⟪H1ComplToLp (I := I) (M := M) g v, f⟫_ℝ := by
  change (innerSL ℝ f) (H1ComplToLp (I := I) (M := M) g v) =
    ⟪H1ComplToLp (I := I) (M := M) g v, f⟫_ℝ
  rw [innerSL_apply_apply]
  exact real_inner_comm (H1ComplToLp (I := I) (M := M) g v) f

/-- The Lax-Milgram operator associated with the bilinear form `B = inner` on
`H1Compl g`. By the Riesz isomorphism on the Hilbert space `H1Compl g`, this
is in fact the identity, but we go through Lax-Milgram for the standard
abstract framework. -/
noncomputable def H1ComplLaxMilgramEquiv (g : SmoothRiemannianMetric I M) :
    H1Compl g ≃L[ℝ] H1Compl g :=
  IsCoercive.continuousLinearEquivOfBilin
    (H1ComplBilin_isCoercive (I := I) (M := M) g)

/-- Defining property of `H1ComplLaxMilgramEquiv`: it solves
`⟪H1ComplLaxMilgramEquiv u, w⟫ = ⟪u, w⟫`, i.e. it is the identity. -/
@[simp] lemma H1ComplLaxMilgramEquiv_apply
    (g : SmoothRiemannianMetric I M) (u w : H1Compl g) :
    ⟪H1ComplLaxMilgramEquiv (I := I) (M := M) g u, w⟫_ℝ = ⟪u, w⟫_ℝ :=
  IsCoercive.continuousLinearEquivOfBilin_apply _ u w

/-- The Riesz representative of an element of the dual of `H1Compl g`,
recovered via `InnerProductSpace.toDual`. We work through `LinearMap`-level
constructions to avoid the conjugate-linear `ₛₗᵢ⋆` typing of the dual map. -/
noncomputable def H1ComplRieszRepr (g : SmoothRiemannianMetric I M) :
    (H1Compl g →L[ℝ] ℝ) →L[ℝ] H1Compl g :=
  LinearMap.mkContinuous
    { toFun := fun φ => (InnerProductSpace.toDual ℝ (H1Compl g)).symm φ
      map_add' := fun φ ψ => by
        exact (InnerProductSpace.toDual ℝ (H1Compl g)).symm.map_add φ ψ
      map_smul' := fun c φ => by
        change (InnerProductSpace.toDual ℝ (H1Compl g)).symm (c • φ) =
          c • (InnerProductSpace.toDual ℝ (H1Compl g)).symm φ
        rw [LinearIsometryEquiv.map_smulₛₗ
          (InnerProductSpace.toDual ℝ (H1Compl g)).symm c φ]
        rfl }
    1 (fun φ => by
      change ‖(InnerProductSpace.toDual ℝ (H1Compl g)).symm φ‖ ≤ 1 * ‖φ‖
      rw [one_mul]
      exact le_of_eq ((InnerProductSpace.toDual ℝ (H1Compl g)).symm.norm_map φ))

/-- Defining property of the Riesz representative on `H1Compl g`. -/
lemma H1ComplRieszRepr_inner (g : SmoothRiemannianMetric I M)
    (φ : H1Compl g →L[ℝ] ℝ) (w : H1Compl g) :
    ⟪H1ComplRieszRepr (I := I) (M := M) g φ, w⟫_ℝ = φ w := by
  change ⟪(InnerProductSpace.toDual ℝ (H1Compl g)).symm φ, w⟫_ℝ = φ w
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := H1Compl g) (x := w) (y := φ)

/-- The resolvent operator `(1 - Δ_g)⁻¹ : Lp ℝ 2 μ_g →L[ℝ] H1Compl g`.

For each `f ∈ Lp ℝ 2 μ_g`, `resolvent g f` is the unique element `u ∈ H1Compl g`
satisfying the variational equation
`⟨u, v⟩_{H1Compl} = ⟨H1ComplToLp v, f⟩_{L²}` for every `v ∈ H1Compl g`.

This is the Lax-Milgram solution to the equation `(1 - Δ_g) u = f` in the
H¹-dual sense, with the geometer Laplacian sign convention. -/
noncomputable def resolvent (g : SmoothRiemannianMetric I M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] H1Compl g :=
  (H1ComplRieszRepr (I := I) (M := M) g).comp
    (lpFunctionalCLM (I := I) (M := M) g)

/-- Defining property of the resolvent: for every `f ∈ Lp ℝ 2 μ_g` and every
test `v ∈ H1Compl g`,
`⟨resolvent g f, v⟩_{H1Compl} = ⟨H1ComplToLp v, f⟩_{L²}`. -/
theorem resolvent_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric I M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (v : H1Compl g) :
    ⟪resolvent (I := I) (M := M) g f, v⟫_ℝ =
      ⟪H1ComplToLp (I := I) (M := M) g v, f⟫_ℝ := by
  unfold resolvent
  rw [ContinuousLinearMap.comp_apply, H1ComplRieszRepr_inner,
    lpFunctionalCLM_apply]

/-- Equivalent formulation: the resolvent satisfies the variational identity
in the H¹-bilinear-form formulation. -/
theorem resolvent_bilin_eq_lpFunctional
    (g : SmoothRiemannianMetric I M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (v : H1Compl g) :
    H1ComplBilin (I := I) (M := M) g
        (resolvent (I := I) (M := M) g f) v =
      ⟪H1ComplToLp (I := I) (M := M) g v, f⟫_ℝ := by
  rw [H1ComplBilin_apply]
  exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g f v

example (g : SmoothRiemannianMetric I M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] H1Compl g :=
  resolvent (I := I) (M := M) g

end Laplacian
end Analysis
end DifferentialGeometry

end
