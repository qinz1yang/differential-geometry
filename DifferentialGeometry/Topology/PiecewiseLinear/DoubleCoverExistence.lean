/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CoveringTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.DoubleCoverComplex
import DifferentialGeometry.Topology.PiecewiseLinear.HomologyCocycle
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation

noncomputable section

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SimplicialBoolCocycle

variable {K : Geometry.SimplicialComplex ℝ E}

open Classical in
theorem finite_fiber [Finite K.faces] (ε : SimplicialBoolCocycle K) (x : K.space) :
    (ε.toBoolCocycle.toFiberBundleCore.proj ⁻¹' {x}).Finite := by
  rw [← Set.finite_coe_iff]
  apply Nat.finite_of_card_ne_zero
  rw [ε.card_fiber]
  decide

open Classical in
theorem exists_lift_simplicialComplex [FiniteDimensional ℝ E] [Finite K.faces]
    (ε : SimplicialBoolCocycle K) :
    ∃ (N : ℕ)
      (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (e : K'.space ≃ₜ ε.toBoolCocycle.toFiberBundleCore.TotalSpace),
      K'.faces.Finite ∧
      (∀ q, ∀ hq : q ∈ K'.faces,
        ∃ t ∈ K.faces,
        ∃ A : EuclideanSpace ℝ (Fin N) →ᵃ[ℝ] E,
          (∀ x (hx : x ∈ convexHull ℝ (q : Set _)),
            ((ε.toBoolCocycle.toFiberBundleCore.proj
              (e ⟨x, K'.convexHull_subset_space hq hx⟩) : K.space) : E) = A x) ∧
          A '' convexHull ℝ (q : Set _) = convexHull ℝ (t : Set E)) ∧
      ∀ n, IsCombinatorialManifoldWithBoundary n K →
        IsCombinatorialManifoldWithBoundary n K' :=
  PiecewiseLinear.exists_lift_simplicialComplex K ε.isCoveringMap ε.finite_fiber

open Classical in
theorem exists_connected_double_cover_complex [FiniteDimensional ℝ E]
    [Finite K.faces] [ConnectedSpace K.space]
    (ε : SimplicialBoolCocycle K) (hε : ¬ ε.IsCoboundary)
    {n : ℕ} (hK : IsCombinatorialManifoldWithBoundary n K) :
    ∃ (N : ℕ)
      (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (_ : K'.space ≃ₜ ε.toBoolCocycle.toFiberBundleCore.TotalSpace),
      K'.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary n K' ∧
      IsCoveringMap ε.toBoolCocycle.toFiberBundleCore.proj ∧
      (∀ x, Nat.card (ε.toBoolCocycle.toFiberBundleCore.proj ⁻¹' {x}) = 2) ∧
      ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace := by
  obtain ⟨N, K', e, hfinite, -, hmanifold⟩ := ε.exists_lift_simplicialComplex
  exact ⟨N, K', e, hfinite, hmanifold n hK, ε.isCoveringMap,
    ε.card_fiber, ε.connectedSpace_iff.mpr hε⟩

end SimplicialBoolCocycle

open Classical in
theorem exists_connected_double_cover_complex_of_isOrientable_of_boundary_component_not_sphere
    {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    (K : Geometry.SimplicialComplex ℝ E₀) [Finite K.faces] [ConnectedSpace K.space]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hor : IsOrientable 3 K)
    (c : ConnectedComponents (boundaryComplex 3 K).space)
    (hnot : ¬ IsPLSphere 2
      (connectedComponentComplex (boundaryComplex 3 K) c).space) :
    ∃ (ε : SimplicialBoolCocycle K)
      (N : ℕ)
      (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (_ : K'.space ≃ₜ ε.toBoolCocycle.toFiberBundleCore.TotalSpace),
      ¬ ε.IsCoboundary ∧
      K'.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 K' ∧
      IsCoveringMap ε.toBoolCocycle.toFiberBundleCore.proj ∧
      (∀ x, Nat.card (ε.toBoolCocycle.toFiberBundleCore.proj ⁻¹' {x}) = 2) ∧
      ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace := by
  have hconnected : IsConnected K.space :=
    isConnected_iff_connectedSpace.mpr inferInstance
  have hbetti := bettiNumber_one_pos_of_boundary_component_not_sphere
    (ZMod 2) K hK hor hconnected c hnot
  obtain ⟨ε, hε⟩ :=
    SimplicialBoolCocycle.exists_not_isCoboundary_of_bettiNumber_one_pos K hbetti
  obtain ⟨N, K', e, hfinite, hmanifold, hcover, hfiber, hconnected'⟩ :=
    ε.exists_connected_double_cover_complex hε hK
  exact ⟨ε, N, K', e, hε, hfinite, hmanifold, hcover, hfiber, hconnected'⟩

open Classical in
theorem exists_connected_double_cover_complex_of_not_isOrientable
    [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [ConnectedSpace K.space]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hI4 : ¬ IsOrientable 3 K →
      ∃ ε : SimplicialBoolCocycle (barycentricSubdivision K), ¬ ε.IsCoboundary)
    (hnot : ¬ IsOrientable 3 K) :
    ∃ (ε : SimplicialBoolCocycle (barycentricSubdivision K))
      (N : ℕ)
      (K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (_ : K'.space ≃ₜ ε.toBoolCocycle.toFiberBundleCore.TotalSpace),
      ¬ ε.IsCoboundary ∧
      K'.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 K' ∧
      IsCoveringMap ε.toBoolCocycle.toFiberBundleCore.proj ∧
      (∀ x, Nat.card (ε.toBoolCocycle.toFiberBundleCore.proj ⁻¹' {x}) = 2) ∧
      ConnectedSpace ε.toBoolCocycle.toFiberBundleCore.TotalSpace := by
  let _ : ConnectedSpace (barycentricSubdivision K).space := by
    rw [(barycentricSubdivision_isSubdivision K).space_eq]
    infer_instance
  obtain ⟨ε, hε⟩ := hI4 hnot
  obtain ⟨N, K', e, hfinite, hmanifold, hcover, hfiber, hconnected⟩ :=
    ε.exists_connected_double_cover_complex hε hK.barycentricSubdivision
  exact ⟨ε, N, K', e, hε, hfinite, hmanifold, hcover, hfiber, hconnected⟩

end DifferentialGeometry.Topology.PiecewiseLinear
