import DifferentialGeometry.Topology.VanKampen.Pi1FiniteConnectedSum
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem simplyConnectedSpace_finiteConnectedSum_of_factors
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ (F : ConnectedClosedOrientedManifold.{u} 3) (p : F.Carrier),
      F ∈ L → Subsingleton (FundamentalGroup F.Carrier p))
    (y : (finiteConnectedSum L).Carrier) :
    SimplyConnectedSpace (finiteConnectedSum L).Carrier :=
  (VanKampen.simplyConnectedSpace_iff_fundamentalGroup_subsingleton
      (finiteConnectedSum L).Carrier y).mpr
    (subsingleton_of_finiteConnectedSum_factors L h
      (fun i => Classical.choice (inferInstance : Nonempty (L.get i).Carrier)) y)

theorem simplyConnectedSpace_finiteConnectedSum_of_simplyConnected
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (h : ∀ (F : ConnectedClosedOrientedManifold.{u} 3),
      F ∈ L → SimplyConnectedSpace F.Carrier)
    (y : (finiteConnectedSum L).Carrier) :
    SimplyConnectedSpace (finiteConnectedSum L).Carrier :=
  simplyConnectedSpace_finiteConnectedSum_of_factors L
    (fun F p hF =>
      (VanKampen.simplyConnectedSpace_iff_fundamentalGroup_subsingleton F.Carrier p).mp
        (h F hF)) y

theorem simplyConnectedSpace_of_mem_finiteConnectedSum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (F : ConnectedClosedOrientedManifold.{u} 3) (hF : F ∈ L)
    [SimplyConnectedSpace (finiteConnectedSum L).Carrier] :
    SimplyConnectedSpace F.Carrier := by
  let x : (i : Fin L.length) → (L.get i).Carrier := fun _ => Classical.choice inferInstance
  let y : (finiteConnectedSum L).Carrier := Classical.choice inferInstance
  let q : F.Carrier := Classical.choice inferInstance
  exact (VanKampen.simplyConnectedSpace_iff_fundamentalGroup_subsingleton F.Carrier q).mpr
    (subsingleton_fundamentalGroup_factor_of_subsingleton_finiteConnectedSum
      L F hF x y inferInstance q)

theorem simplyConnectedSpace_finiteConnectedSum_iff
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    SimplyConnectedSpace (finiteConnectedSum L).Carrier ↔
      ∀ F ∈ L, SimplyConnectedSpace F.Carrier := by
  constructor
  · intro h
    let := h
    exact fun F hF => simplyConnectedSpace_of_mem_finiteConnectedSum L F hF
  · intro h
    exact simplyConnectedSpace_finiteConnectedSum_of_simplyConnected L h
      (Classical.choice inferInstance)

theorem simplyConnectedSpace_finiteConnectedSum_append_replicate_iff
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (Z : ConnectedClosedOrientedManifold.{u} 3) (k : ℕ)
    (hZ : ¬ SimplyConnectedSpace Z.Carrier) :
    SimplyConnectedSpace (finiteConnectedSum (L ++ List.replicate k Z)).Carrier ↔
      k = 0 ∧ ∀ F ∈ L, SimplyConnectedSpace F.Carrier := by
  constructor
  · intro h
    have hfactor := (simplyConnectedSpace_finiteConnectedSum_iff
      (L ++ List.replicate k Z)).mp h
    refine ⟨?_, fun F hF => hfactor F (List.mem_append_left _ hF)⟩
    by_contra hk
    exact hZ (hfactor Z (List.mem_append_right _ (List.mem_replicate.mpr ⟨hk, rfl⟩)))
  · rintro ⟨rfl, h⟩
    rw [List.replicate_zero, List.append_nil]
    exact (simplyConnectedSpace_finiteConnectedSum_iff L).mpr h

theorem nonempty_homeomorph_finiteConnectedSum_of_simplyConnected
    {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (Z : ConnectedClosedOrientedManifold.{u} 3) (k : ℕ)
    (hZ : ¬ SimplyConnectedSpace Z.Carrier)
    (H : X ≃ₜ (finiteConnectedSum (L ++ List.replicate k Z)).Carrier) :
    Nonempty (X ≃ₜ (finiteConnectedSum L).Carrier) := by
  have hsc := H.toHomotopyEquiv.simplyConnectedSpace_iff.mp
    (inferInstance : SimplyConnectedSpace X)
  have hk := ((simplyConnectedSpace_finiteConnectedSum_append_replicate_iff L Z k hZ).mp hsc).1
  subst k
  rw [List.replicate_zero, List.append_nil] at H
  exact ⟨H⟩


end DifferentialGeometry.Topology
