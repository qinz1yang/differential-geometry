/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeNormalizationLocality

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open Classical in
theorem IsCanonicalSurface.exists_bridge_normalization_sequence [DecidableEq E3]
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3))
    (h303 : Moise303) (h286 : Moise286) (h314 : Moise314)
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (hX : IsCanonicalSurface X (fun i => φ '' S i) T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v))
    (hmodel : ∀ i, HasEssentialBoundaryPLEmbeddings (X i) (T'' (2 * i + 1)))
    (hwitness : HasCanonicalBridgeWitnesses X T'') (rows : ℕ → Finset ℤ) :
    ∃ Y : ℕ → ℤ → Geometry.SimplicialComplex ℝ E3, Y 0 = X ∧
      ∀ n, IsCanonicalBridgeNormalization (Y n) (Y (n + 1)) (fun i => φ '' S i) S'' T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) (rows n) ∅ := by
  let valid (Z : ℤ → Geometry.SimplicialComplex ℝ E3) : Prop :=
    IsCanonicalSurface Z (fun i => φ '' S i) T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) ∧
      (∀ i, HasEssentialBoundaryPLEmbeddings (Z i) (T'' (2 * i + 1))) ∧
      HasCanonicalBridgeWitnesses Z T''
  have hnext (n : ℕ) (Z : {Z // valid Z}) :
      ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
        IsCanonicalBridgeNormalization Z.1 Y (fun i => φ '' S i) S'' T''
          (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) (rows n) ∅ :=
    Z.2.1.exists_window_bridge_normalization ht hu hv huv he htw havoid h303 h286 h314
      Z.2.2.1 Z.2.2.2 (rows n) (fun _ _ => empty_disjoint _) (fun _ _ => empty_disjoint _)
  let next (n : ℕ) (Z : {Z // valid Z}) : {Z // valid Z} :=
    ⟨(hnext n Z).choose, (hnext n Z).choose_spec.target.surface,
      (hnext n Z).choose_spec.target.embeddings, (hnext n Z).choose_spec.bridgeWitnesses⟩
  let seq : ℕ → {Z // valid Z} := fun n => Nat.rec ⟨X, hX, hmodel, hwitness⟩ next n
  refine ⟨fun n => (seq n).1, rfl, fun n => ?_⟩
  exact (hnext n (seq n)).choose_spec

end DifferentialGeometry.Topology.PiecewiseLinear
