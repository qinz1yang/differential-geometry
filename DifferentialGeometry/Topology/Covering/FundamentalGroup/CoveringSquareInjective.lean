/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Homotopy.Lifting
import DifferentialGeometry.Topology.FundamentalGroup.ConnectedComponent

set_option autoImplicit false

open scoped unitInterval

namespace DifferentialGeometry.Topology

theorem fundamentalGroup_map_injective_of_covering_square
    {L T E H : Type*} [TopologicalSpace L] [TopologicalSpace T]
    [TopologicalSpace E] [TopologicalSpace H]
    (q : C(L, T)) (p : C(E, H)) (i : C(T, H)) (j : C(L, E))
    (hq : IsCoveringMap q) (hp : IsCoveringMap p)
    (comm : ∀ z, p (j z) = i (q z)) (hj : Function.Injective j)
    (s : L) [SimplyConnectedSpace (connectedComponent s)] :
    Function.Injective (FundamentalGroup.map i (q s)) := by
  refine (injective_iff_map_eq_one (FundamentalGroup.map i (q s))).mpr ?_
  intro a
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective a
  intro ha
  obtain ⟨Γ, hΓq, hΓ0⟩ := hq.exists_path_lifts γ s γ.source
  have hΓt (t : I) : q (Γ t) = γ t := congrFun hΓq t
  have hnull : (γ.map (map_continuous i)).Homotopic (Path.refl (i (q s))) :=
    Path.Homotopic.Quotient.eq.mp ha
  have hstart : (γ.map (map_continuous i)).toContinuousMap 0 = p (j s) :=
    (DFunLike.congr_arg i γ.source).trans (comm s).symm
  have hx : i (q s) = p (j s) := (comm s).symm
  have hend :
      hp.liftPath (γ.map (map_continuous i)).toContinuousMap (j s) hstart 1 = j s :=
    (hp.liftPath_apply_one_eq_of_homotopicRel hnull (j s) hstart hx).trans
      (DFunLike.congr_fun (hp.liftPath_const hx) 1)
  have hlift : j.comp Γ =
      hp.liftPath (γ.map (map_continuous i)).toContinuousMap (j s) hstart := by
    refine (hp.eq_liftPath_iff' hstart).mpr ⟨?_, ?_⟩
    · funext t
      exact (comm (Γ t)).trans (DFunLike.congr_arg i (hΓt t))
    · exact DFunLike.congr_arg j hΓ0
  have hjΓ : j (Γ 1) = j s := (DFunLike.congr_fun hlift 1).trans hend
  have hΓ1 : Γ 1 = s := hj hjΓ
  let δ : Path s s := ⟨Γ, hΓ0, hΓ1⟩
  have hδq : δ.map (map_continuous q) = γ := by
    ext t
    exact hΓt t
  have hsub : Subsingleton (FundamentalGroup L s) :=
    subsingleton_fundamentalGroup_of_simplyConnected_connectedComponent s
  have hδ : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ) = 1 :=
    @Subsingleton.elim _ hsub _ _
  have hmap : FundamentalGroup.map q s
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) :=
    congrArg Path.Homotopic.Quotient.mk hδq
  exact hmap.symm.trans ((congrArg (FundamentalGroup.map q s) hδ).trans
    (map_one (FundamentalGroup.map q s)))

theorem fundamentalGroup_subtype_map_injective_of_covering_preimage
    {E H : Type*} [TopologicalSpace E] [TopologicalSpace H]
    (p : C(E, H)) (hp : IsCoveringMap p) (T : Set H)
    (s : p ⁻¹' T) [SimplyConnectedSpace (connectedComponent s)] :
    Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(T, H)) ⟨p s, s.property⟩) :=
  fundamentalGroup_map_injective_of_covering_square
    (⟨T.restrictPreimage p, (map_continuous p).restrictPreimage⟩ : C(p ⁻¹' T, T)) p
    ⟨Subtype.val, continuous_subtype_val⟩ ⟨Subtype.val, continuous_subtype_val⟩
    (hp.restrictPreimage T) hp (fun _ => rfl) Subtype.val_injective s

end DifferentialGeometry.Topology
