import DifferentialGeometry.Geometry.Metric.Construction.TensorBumpExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TimePolynomialField


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance bumpTimeC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem exists_tensor_bump_time_tower (U : TopologicalSpace.Opens M) (r : ℕ)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := U) (n := ∞) r)
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ) ∞ χ) (hsupp : tsupport χ ⊆ (U : Set M))
    (J : Set ℝ) (hA : ∀ q t, t ∈ J → ∀ x : U,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) J t) :
    ∃ B : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) r,
      (∀ q t, ∀ x : M, ∀ hx : x ∈ U, ∀ v : Fin r → TangentSpace I x,
        B q t x v = χ x * A q t ⟨x, hx⟩ v) ∧
      (∀ q t, ∀ x : M, x ∉ U → B q t x = 0) ∧
      ∀ q t, t ∈ J → ∀ x : M, HasDerivWithinAt (fun s => B q s x) (B (q + 1) t x) J t := by
  classical
  choose B hB using fun q t => exists_tensor_bump_extension U r (A q t) χ hχ hsupp
  refine ⟨B, fun q t => (hB q t).1, fun q t => (hB q t).2, ?_⟩
  intro q t ht x
  let basis := Module.finBasis ℝ (TangentSpace I x)
  apply tensor0S_hasDerivWithinAt_of_components basis
  intro slots
  let v : Fin r → TangentSpace I x := fun k => basis (slots k)
  change HasDerivWithinAt (fun s => B q s x v) (B (q + 1) t x v) J t
  by_cases hx : x ∈ U
  · have hd := (tensor0SEvalCLM (I := I) (M := U) (x := ⟨x, hx⟩) v).hasFDerivAt.comp_hasDerivWithinAt
      t (hA q t ht ⟨x, hx⟩)
    have hv : HasDerivWithinAt (fun s => A q s ⟨x, hx⟩ v) (A (q + 1) t ⟨x, hx⟩ v) J t := hd
    have hχv := hv.const_mul (χ x)
    have hχv' := hχv.congr_deriv ((hB (q + 1) t).1 x hx v).symm
    exact hχv'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => (hB q s).1 x hx v) ((hB q t).1 x hx v)
  · have hvalue (j : ℕ) (s : ℝ) : B j s x v = 0 := by
      rw [(hB j s).2 x hx]
      rfl
    have hd := (hasDerivWithinAt_const t J (0 : ℝ)).congr_deriv (hvalue (q + 1) t).symm
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (hvalue q)) (hvalue q t)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
