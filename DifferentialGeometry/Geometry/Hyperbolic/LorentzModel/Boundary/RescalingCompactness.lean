/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.EuclideanCharts
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.TripleCompactness
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Dynamics.GeodesicFlow

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.BoundaryBlowupCompactness

open HyperbolicBoundary BoundaryTopology Horospherical EuclideanBoundary
open GeodesicFlow MobiusBoundary BoundaryTripleCompactness

variable {m : ℕ}

local instance : MulAction (IsometryGroup m) (BoundaryH (m + 1)) :=
  poBoundaryMulAction (by omega)
local instance : ContinuousSMul (IsometryGroup m) (BoundaryH (m + 1)) :=
  ⟨continuous_po_boundary (by omega)⟩

theorem exists_mobius_of_normalized_limit (hm : 1 ≤ m)
    (ψ : BoundaryH (m + 1) ≃ₜ BoundaryH (m + 1))
    (r : IsometryGroup m) {s b : ℕ → IsometryGroup m} {s₀ : IsometryGroup m}
    (hs : Tendsto s atTop (𝓝 s₀))
    (hlim : ∀ x : Horizontal m, Tendsto (fun j => b j • ψ (s j • embed x))
      atTop (𝓝 (r • embed x))) :
    ∃ a : IsometryGroup m, ∀ ξ : BoundaryH (m + 1), ψ ξ = a • ξ := by
  classical
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨x₁, hx₁⟩ := exists_ne (0 : Horizontal m)
  obtain ⟨x₂, hx₂⟩ := Infinite.exists_notMem_finset ({0, x₁} : Finset (Horizontal m))
  have hx₂0 : x₂ ≠ 0 := fun h => hx₂ (by simp [h])
  have hx₂1 : x₂ ≠ x₁ := fun h => hx₂ (by simp [h])
  let t₀ : Triple (m + 1) :=
    ⟨(embed (0 : Horizontal m), embed x₁, embed x₂),
      fun h => hx₁ (embed_injective h).symm,
      fun h => hx₂0 (embed_injective h).symm,
      fun h => hx₂1 (embed_injective h).symm⟩
  let L (a : IsometryGroup m) : BoundaryH (m + 1) → BoundaryH (m + 1) :=
    fun v => ψ (a • v)
  have hL (a : IsometryGroup m) : Function.Injective (L a) :=
    ψ.injective.comp (MulAction.injective a)
  let t : ℕ → Triple (m + 1) := fun j => BoundaryTripleCompactness.map (L (s j)) (hL (s j)) t₀
  let p : Triple (m + 1) := BoundaryTripleCompactness.map (L s₀) (hL s₀) t₀
  let q : Triple (m + 1) := act (by omega) r t₀
  have hLt (v : BoundaryH (m + 1)) :
      Tendsto (fun j => ψ (s j • v)) atTop (𝓝 (ψ (s₀ • v))) :=
    (ψ.continuous.tendsto (s₀ • v)).comp (hs.smul tendsto_const_nhds)
  have ht : Tendsto t atTop (𝓝 p) := by
    apply tendsto_subtype_rng.mpr
    exact (hLt (embed 0)).prodMk_nhds ((hLt (embed x₁)).prodMk_nhds (hLt (embed x₂)))
  have hb : Tendsto (fun j => act (by omega) (b j) (t j)) atTop (𝓝 q) := by
    apply tendsto_subtype_rng.mpr
    exact (hlim 0).prodMk_nhds ((hlim x₁).prodMk_nhds (hlim x₂))
  obtain ⟨b₀, k, hk, hbk⟩ := exists_subsequence_of_triples (by omega) ht hb
  have he (x : Horizontal m) : b₀ • ψ (s₀ • embed x) = r • embed x := by
    have h₁ := hbk.smul ((hLt (embed x)).comp hk.tendsto_atTop)
    have h₂ := (hlim x).comp hk.tendsto_atTop
    exact tendsto_nhds_unique h₁ h₂
  have hall : ∀ ξ : BoundaryH (m + 1), b₀ • ψ (s₀ • ξ) = r • ξ :=
    eq_on_boundary_of_eq_on_horo
      ((continuous_const_smul b₀).comp (ψ.continuous.comp (continuous_const_smul s₀)))
      (continuous_const_smul r) hm
      (fun x => he ((EuclideanSpace.equiv (Fin m) ℝ).symm x))
  refine ⟨b₀⁻¹ * r * s₀⁻¹, fun ξ => ?_⟩
  have h := congrArg (fun v : BoundaryH (m + 1) => b₀⁻¹ • v) (hall (s₀⁻¹ • ξ))
  simpa only [smul_inv_smul, inv_smul_smul, mul_smul] using h

end DifferentialGeometry.BoundaryBlowupCompactness
