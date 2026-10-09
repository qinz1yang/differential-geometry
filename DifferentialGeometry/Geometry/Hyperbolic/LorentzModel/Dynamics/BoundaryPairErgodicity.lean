/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.IdealEndpoints

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.BoundaryPairErgodicity

open Hyperbolic HyperbolicAction HyperbolicBoundary BoundaryTopology
open GeodesicFlow BoundaryMeasure BoundaryGeodesic

variable {m : ℕ}

abbrev BoundaryPair (m : ℕ) := BoundaryH (m + 1) × BoundaryH (m + 1)

local instance : MulAction (IsometryGroup m) (HUpper (m + 1)) := poMulAction (by omega)
local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) := poBoundaryMulAction (by omega)
local instance : ContinuousSMul (IsometryGroup m) (BoundaryH (m + 1)) :=
  ⟨continuous_po_boundary (by omega)⟩

def descendedSet (Γ : Subgroup (IsometryGroup m)) (U : Set (BoundaryPair m))
    (hInv : ∀ (γ : Γ) (p : BoundaryPair m), (γ : IsometryGroup m) • p ∈ U ↔ p ∈ U) :
    Set (GeodesicQuotient Γ) :=
  {q | Quotient.lift (fun v : Tangent m => endpoints v ∈ U)
    (fun v w hvw => by
      obtain ⟨γ, hγ⟩ := hvw
      change (γ : IsometryGroup m) • w = v at hγ
      rw [← hγ, endpoints_smul]
      exact propext (hInv γ (endpoints w))) q}

theorem measurableSet_descendedSet (Γ : Subgroup (IsometryGroup m))
    {U : Set (BoundaryPair m)} (hU : MeasurableSet U)
    (hInv : ∀ (γ : Γ) (p : BoundaryPair m), (γ : IsometryGroup m) • p ∈ U ↔ p ∈ U) :
    MeasurableSet (descendedSet Γ U hInv) := by
  apply measurableSet_quotient.mpr
  change MeasurableSet (endpoints ⁻¹' U)
  exact continuous_endpoints.measurable hU

theorem descendedSet_flow (Γ : Subgroup (IsometryGroup m))
    (U : Set (BoundaryPair m))
    (hInv : ∀ (γ : Γ) (p : BoundaryPair m), (γ : IsometryGroup m) • p ∈ U ↔ p ∈ U)
    (t : ℝ) :
    quotientFlow Γ t ⁻¹' descendedSet Γ U hInv = descendedSet Γ U hInv := by
  ext q
  induction q using Quotient.inductionOn with
  | h v =>
    change endpoints (flow t v) ∈ U ↔ endpoints v ∈ U
    rw [endpoints_flow]

theorem haar_preimage_descendedSet (Γ : Subgroup (IsometryGroup m))
    (U : Set (BoundaryPair m))
    (hInv : ∀ (γ : Γ) (p : BoundaryPair m), (γ : IsometryGroup m) • p ∈ U ↔ p ∈ U) :
    (fun g : IsometryGroup m => GeodesicFlow.projection Γ (g • (standardTangent : Tangent m))) ⁻¹'
      descendedSet Γ U hInv = endpointPair ⁻¹' U := by
  ext g
  change endpoints (g • (standardTangent : Tangent m)) ∈ U ↔ endpointPair g ∈ U
  rw [endpoints_smul_standard]

variable [Nonempty (Fin m)]
variable [IsMulRightInvariant (volume : Measure (IsometryGroup m))]

theorem null_or_conull_of_invariant
    (Γ : Subgroup (IsometryGroup m)) (ν : Measure (GeodesicQuotient Γ))
    (hN : ∀ V : Set (GeodesicQuotient Γ), MeasurableSet V →
      (ν V = 0 ↔ volume ((fun g : IsometryGroup m =>
        GeodesicFlow.projection Γ (g • (standardTangent : Tangent m))) ⁻¹' V) = 0))
    (hE : ∀ V : Set (GeodesicQuotient Γ), MeasurableSet V →
      (∀ t : ℝ, quotientFlow Γ t ⁻¹' V =ᵐ[ν] V) → ν V = 0 ∨ ν Vᶜ = 0)
    {U : Set (BoundaryPair m)} (hU : MeasurableSet U)
    (hInv : ∀ (γ : Γ) (p : BoundaryPair m), (γ : IsometryGroup m) • p ∈ U ↔ p ∈ U) :
    ((boundaryMeasure m).prod (boundaryMeasure m)) U = 0 ∨
      ((boundaryMeasure m).prod (boundaryMeasure m)) Uᶜ = 0 := by
  let V := descendedSet Γ U hInv
  have hV : MeasurableSet V := measurableSet_descendedSet Γ hU hInv
  have hzero : ν V = 0 ↔ ((boundaryMeasure m).prod (boundaryMeasure m)) U = 0 := by
    rw [hN V hV, haar_preimage_descendedSet]
    exact haar_endpointPair_null_iff hU
  have hcompl : ν Vᶜ = 0 ↔ ((boundaryMeasure m).prod (boundaryMeasure m)) Uᶜ = 0 := by
    rw [hN Vᶜ hV.compl, preimage_compl, haar_preimage_descendedSet, ← preimage_compl]
    exact haar_endpointPair_null_iff hU.compl
  rcases hE V hV (fun t => Filter.EventuallyEq.of_eq (descendedSet_flow Γ U hInv t)) with h | h
  · exact Or.inl (hzero.mp h)
  · exact Or.inr (hcompl.mp h)

theorem null_or_conull_of_ae_invariant
    (Γ : Subgroup (IsometryGroup m)) [Countable Γ] (ν : Measure (GeodesicQuotient Γ))
    (hN : ∀ V : Set (GeodesicQuotient Γ), MeasurableSet V →
      (ν V = 0 ↔ volume ((fun g : IsometryGroup m =>
        GeodesicFlow.projection Γ (g • (standardTangent : Tangent m))) ⁻¹' V) = 0))
    (hE : ∀ V : Set (GeodesicQuotient Γ), MeasurableSet V →
      (∀ t : ℝ, quotientFlow Γ t ⁻¹' V =ᵐ[ν] V) → ν V = 0 ∨ ν Vᶜ = 0)
    {U : Set (BoundaryPair m)} (hU : MeasurableSet U)
    (hInv : ∀ γ : Γ, (fun p : BoundaryPair m => (γ : IsometryGroup m) • p) ⁻¹' U
      =ᵐ[(boundaryMeasure m).prod (boundaryMeasure m)] U) :
    ((boundaryMeasure m).prod (boundaryMeasure m)) U = 0 ∨
      ((boundaryMeasure m).prod (boundaryMeasure m)) Uᶜ = 0 := by
  let S : Set (BoundaryPair m) :=
    ⋂ γ : Γ, (fun p : BoundaryPair m => (γ : IsometryGroup m) • p) ⁻¹' U
  have hS : MeasurableSet S :=
    MeasurableSet.iInter fun γ => (continuous_const_smul (γ : IsometryGroup m)).measurable hU
  have hSU : S =ᵐ[(boundaryMeasure m).prod (boundaryMeasure m)] U := by
    filter_upwards [ae_all_iff.mpr hInv] with p hp
    apply propext
    change p ∈ S ↔ p ∈ U
    simp only [S, mem_iInter, mem_preimage]
    constructor
    · intro h
      simpa only [Subgroup.coe_one, one_smul] using h 1
    · intro h γ
      exact (hp γ).mpr h
  have hSinv (δ : Γ) (p : BoundaryPair m) :
      (δ : IsometryGroup m) • p ∈ S ↔ p ∈ S := by
    simp only [S, mem_iInter, mem_preimage]
    constructor
    · intro h γ
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_smul] using h (γ * δ⁻¹)
    · intro h γ
      simpa only [Subgroup.coe_mul, mul_smul] using h (γ * δ)
  rcases null_or_conull_of_invariant Γ ν hN hE hS hSinv with h | h
  · exact Or.inl ((measure_congr hSU).symm.trans h)
  · exact Or.inr ((measure_congr hSU.compl).symm.trans h)

end DifferentialGeometry.BoundaryPairErgodicity
