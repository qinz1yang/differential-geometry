/-
Authors: Jack McCarthy
-/
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Predual basis

Given a basis `b` of the continuous dual `E →L[𝕜] 𝕜`, this file constructs a
"predual" basis `B` of `E` satisfying `b i (B j) = δ_{ij}`.
-/

noncomputable section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {d : ℕ}

/-- Continuous dual basis of `E →L[𝕜] 𝕜` induced by a basis `B` of `E`. Obtained by
transporting the algebraic dual basis `B.dualBasis` across the finite-dimensional
linear equivalence `E →ₗ[𝕜] 𝕜 ≃ₗ[𝕜] E →L[𝕜] 𝕜`. -/
noncomputable def Module.Basis.cDualBasis [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (B : Module.Basis (Fin d) 𝕜 E) :
    Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜) :=
  B.dualBasis.map LinearMap.toContinuousLinearMap

/-- Duality pairing of `B.cDualBasis` with `B`: `B.cDualBasis i (B j) = δᵢⱼ`. -/
theorem Module.Basis.cDualBasis_apply_self [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (B : Module.Basis (Fin d) 𝕜 E) (i j : Fin d) :
    B.cDualBasis i (B j) = if i = j then (1 : 𝕜) else 0 := by
  change B.dualBasis i (B j) = _
  rw [Module.Basis.dualBasis_apply_self]
  split_ifs with h1 h2 <;> simp_all [eq_comm]

/-- Existence of a predual basis. Given a basis `b` of the continuous dual
`E →L[𝕜] 𝕜`, there exists a basis `B` of `E` such that `b i (B j) = δ_{ij}`. -/
theorem exists_predual_basis [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (b : Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜)) :
    ∃ B : Module.Basis (Fin d) 𝕜 E,
      ∀ i j, b i (B j) = if i = j then 1 else 0 := by

  let b_alg : Module.Basis (Fin d) 𝕜 (E →ₗ[𝕜] 𝕜) :=
    b.map (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := E)).symm

  let B : Module.Basis (Fin d) 𝕜 E :=
    b_alg.dualBasis.map (Module.evalEquiv 𝕜 E).symm
  refine ⟨B, fun i j => ?_⟩

  have agree : ∀ x, b i x = (b_alg i) x := by
    intro x; simp [b_alg, Module.Basis.map_apply]
  rw [agree]
  change (b_alg i) (B j) = _
  simp [B, Module.Basis.map_apply, Finsupp.single_apply]

/-- The continuous-linear analogue of `Basis.sum_dual_apply_smul_coord`: any
continuous linear functional on `E` decomposes in the dual basis as
`α = ∑ k, α (b k) • LinearMap.toContinuousLinearMap (b.coord k)`. -/
theorem cdual_sum_repr {d : ℕ} [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (b : Module.Basis (Fin d) 𝕜 E) (α : E →L[𝕜] 𝕜) :
    (∑ k, (α (b k)) • LinearMap.toContinuousLinearMap (b.coord k)) = α := by

  apply ContinuousLinearMap.coe_injective

  rw [show ((∑ k, (α (b k)) • LinearMap.toContinuousLinearMap (b.coord k)
        : E →L[𝕜] 𝕜) : E →ₗ[𝕜] 𝕜) =
      ∑ k, (α (b k)) • (b.coord k) by
    rw [ContinuousLinearMap.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.coe_smul, LinearMap.coe_toContinuousLinearMap]]
  exact b.sum_dual_apply_smul_coord (α : E →ₗ[𝕜] 𝕜)
