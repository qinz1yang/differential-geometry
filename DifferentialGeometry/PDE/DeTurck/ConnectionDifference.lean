import DifferentialGeometry.Integral.Connection.LeviCivita

/-!
# The connection-difference tensor of two Riemannian metrics

Given two smooth Riemannian metrics `g` and `g'` on a smooth manifold `M` modelled on a
finite-dimensional inner product space `E`, their Levi-Civita covariant derivatives
`∇ = LeviCivita g` and `∇' = LeviCivita g'` differ by a genuine tensor field.  While
neither `∇` nor `∇'` is tensorial in the section being differentiated (each obeys a
Leibniz rule), the non-tensorial second-derivative contributions are identical for the
two connections and cancel in the difference.  The result
$$
  A(X, Y) := \nabla_Y X - \nabla'_Y X
$$
is therefore a `(1,2)`-tensor: a smooth section of `Hom(TM, Hom(TM, TM))`.

Mathlib packages exactly this construction as `CovariantDerivative.difference`, built on
the tensoriality criterion `TensorialAt`.  This file specialises it to the pair of
Levi-Civita connections.

## Main definitions

* `connDiff g g'` — the connection-difference tensor, as the pointwise family of
  continuous bilinear maps `TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x`.

## Main results

* `connDiff_apply` — the evaluation formula: on a section `σ` of the tangent bundle that
  is differentiable at `x`, `connDiff g g' x (σ x) v = (LeviCivita g) σ x v - (LeviCivita g') σ x v`.
* `connDiff_self` — the difference tensor of a metric with itself vanishes identically.
* `connDiff_contMDiff` — applied to two globally smooth tangent vector fields, the
  connection-difference tensor yields a globally smooth tangent vector field.
* `connDiff_contMDiffOn` — applied to a globally smooth tangent vector field in the
  differentiated slot and a vector field smooth on an open set in the direction slot,
  the connection-difference tensor yields a vector field smooth on that open set.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The **connection-difference tensor** of two smooth Riemannian metrics `g` and `g'`.

It is the difference of their Levi-Civita covariant derivatives, packaged by
`CovariantDerivative.difference` as a one-form valued in the endomorphism bundle of the
tangent bundle: at each point `x : M` it is a continuous bilinear map
`TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x`, with `connDiff g g' x w v`
representing `(∇_v - ∇'_v)` applied to a vector field with value `w` at `x`. -/
def connDiff (g g' : SmoothRiemannianMetric I M) :
    Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  CovariantDerivative.difference (LeviCivita (I := I) g) (LeviCivita (I := I) g')

/-- **Evaluation formula for the connection-difference tensor.**  On a tangent-bundle
section `σ` differentiable at `x`, the connection-difference tensor evaluated at the
value `σ x` reproduces the difference of the two Levi-Civita covariant derivatives of `σ`:
$$
  A(X, v) = \nabla_v X - \nabla'_v X.
$$
This is the specialisation of `IsCovariantDerivativeOn.difference_apply` to the
Levi-Civita pair. -/
@[simp]
theorem connDiff_apply (g g' : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x} {x : M} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    connDiff (I := I) g g' x (σ x) v =
      (LeviCivita (I := I) g).toFun σ x v - (LeviCivita (I := I) g').toFun σ x v := by
  have h := IsCovariantDerivativeOn.difference_apply
    (LeviCivita (I := I) g).isCovariantDerivativeOnUniv
    (LeviCivita (I := I) g').isCovariantDerivativeOnUniv
    (x := x) (mem_univ x) (σ := σ) hσ
  simp only [connDiff, CovariantDerivative.difference]
  rw [h]
  rfl

/-- The connection-difference tensor of a metric with itself vanishes identically:
the two Levi-Civita covariant derivatives coincide, so their difference is zero. -/
@[simp]
theorem connDiff_self (g : SmoothRiemannianMetric I M) :
    connDiff (I := I) g g = 0 := by
  classical
  funext x
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  have hσ : MDiffAt (T% fun y => σ y) x := σ.mdifferentiableAt
  have hval : connDiff (I := I) g g x (σ x) v =
      (LeviCivita (I := I) g).toFun (fun y => σ y) x v -
        (LeviCivita (I := I) g).toFun (fun y => σ y) x v :=
    connDiff_apply (I := I) g g hσ v
  rw [sub_self] at hval
  simpa [hσx] using hval

/-- The Levi-Civita covariant derivative of a globally smooth tangent vector field is a
globally smooth section of the endomorphism bundle `Hom(TM, TM)`.

This is the bundled-`CovariantDerivative` smoothness statement `LeviCivita_section_contMDiffOn_univ`
applied to the section `σ`, restated as an unconditional `ContMDiff` statement (the
hypothesis is at the same `C^∞` regularity because `∞ + 1 = ∞`). -/
private theorem leviCivita_section_contMDiff (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun σ x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  have hσ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact (hσ.of_le h_le).contMDiffOn
  have h := LeviCivita_section_contMDiffOn_univ (I := I) g hσ'
  rw [← contMDiffOn_univ]
  exact h

/-- **Smoothness of the connection-difference tensor on globally smooth vector fields.**

For two globally smooth tangent vector fields `σ` and `τ`, the vector field
`x ↦ connDiff g g' x (σ x) (τ x)` is globally smooth.

By the evaluation formula `connDiff_apply`, the field equals the difference of the two
Levi-Civita covariant derivatives of `σ`, each evaluated in the direction `τ`.  Each
covariant derivative of `σ` is a smooth section of `Hom(TM, TM)`; applying it to the
smooth vector field `τ` yields a smooth vector field, and the difference of two smooth
vector fields is smooth. -/
theorem connDiff_contMDiff (g g' : SmoothRiemannianMetric I M)
    {σ τ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% τ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) := by
  have hcovg := leviCivita_section_contMDiff (I := I) g hσ
  have hcovg' := leviCivita_section_contMDiff (I := I) g' hσ
  have hg : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g).toFun σ x (τ x)))) :=
    ContMDiff.clm_bundle_apply (b := id) hcovg hτ
  have hg' : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g').toFun σ x (τ x)))) :=
    ContMDiff.clm_bundle_apply (b := id) hcovg' hτ
  have hdiff := hg.sub_section hg'
  refine hdiff.congr (fun x => ?_)
  have hσ_at : MDiffAt (T% σ) x := (hσ x).mdifferentiableAt (by simp)
  have hval := connDiff_apply (I := I) g g' hσ_at (τ x)
  change (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ : TotalSpace E (TangentSpace I)) =
      ⟨x, ((fun y => (LeviCivita (I := I) g).toFun σ y (τ y)) -
        (fun y => (LeviCivita (I := I) g').toFun σ y (τ y))) x⟩
  rw [Pi.sub_apply, hval]

/-- **Smoothness of the connection-difference tensor with a locally smooth direction.**

For a globally smooth tangent vector field `σ` in the differentiated slot and a tangent
vector field `τ` smooth on an open set `U` in the direction slot, the vector field
`x ↦ connDiff g g' x (σ x) (τ x)` is smooth on `U`.

The differentiated slot still requires a globally smooth section, because the Levi-Civita
covariant derivative's `C^∞` instance is global; the direction slot, fed pointwise as a
vector, only needs smoothness on `U`. -/
theorem connDiff_contMDiffOn (g g' : SmoothRiemannianMetric I M)
    {U : Set M} {σ τ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ))
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% τ) U) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ :
          TotalSpace E (TangentSpace I))) U := by
  have hcovg := (leviCivita_section_contMDiff (I := I) g hσ).contMDiffOn (s := U)
  have hcovg' := (leviCivita_section_contMDiff (I := I) g' hσ).contMDiffOn (s := U)
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g).toFun σ x (τ x)))) U :=
    ContMDiffOn.clm_bundle_apply (b := id) hcovg hτ
  have hg' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M =>
        (TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
          ((LeviCivita (I := I) g').toFun σ x (τ x)))) U :=
    ContMDiffOn.clm_bundle_apply (b := id) hcovg' hτ
  have hdiff := hg.sub_section hg'
  refine hdiff.congr (fun x _hx => ?_)
  have hσ_at : MDiffAt (T% σ) x := (hσ x).mdifferentiableAt (by simp)
  have hval := connDiff_apply (I := I) g g' hσ_at (τ x)
  change (⟨x, connDiff (I := I) g g' x (σ x) (τ x)⟩ : TotalSpace E (TangentSpace I)) =
      ⟨x, ((fun y => (LeviCivita (I := I) g).toFun σ y (τ y)) -
        (fun y => (LeviCivita (I := I) g').toFun σ y (τ y))) x⟩
  rw [Pi.sub_apply, hval]

end DeTurck
end PDE
end DifferentialGeometry
