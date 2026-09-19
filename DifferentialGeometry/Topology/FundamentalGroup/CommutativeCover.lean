/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnected
import DifferentialGeometry.Topology.VanKampen.FreeProduct

/-! Simply connected sides of covers with commutative fundamental group. -/

namespace DifferentialGeometry.Topology

open Set VanKampen

theorem simplyConnectedSpace_or_of_open_cover_of_isMulCommutative
    {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    [PathConnectedSpace U] [PathConnectedSpace V] [SimplyConnectedSpace (↑(U ∩ V))]
    (x : X) (hx : x ∈ U ∩ V) (hcomm : IsMulCommutative (FundamentalGroup X x)) :
    SimplyConnectedSpace U ∨ SimplyConnectedSpace V := by
  classical
  by_contra hn
  obtain ⟨hUn, hVn⟩ := not_or.mp hn
  obtain ⟨a, ha⟩ := exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace
    hUn (leftBasepoint U x hx.1)
  obtain ⟨b, hb⟩ := exists_fundamentalGroup_ne_one_of_not_simplyConnectedSpace
    hVn (rightBasepoint V x hx.2)
  let G := fundamentalGroupFactor U V x hx
  let wa : Monoid.CoprodI.Word G := Monoid.CoprodI.Word.cons (i := false) a
    .empty (by simp [Monoid.CoprodI.Word.fstIdx, Monoid.CoprodI.Word.empty]) ha
  let wb : Monoid.CoprodI.Word G := Monoid.CoprodI.Word.cons (i := true) b
    .empty (by simp [Monoid.CoprodI.Word.fstIdx, Monoid.CoprodI.Word.empty]) hb
  let wab : Monoid.CoprodI.Word G := Monoid.CoprodI.Word.cons (i := false) a wb
    (by change some true ≠ some false; decide) ha
  let wba : Monoid.CoprodI.Word G := Monoid.CoprodI.Word.cons (i := true) b wa
    (by change some false ≠ some true; decide) hb
  let e := fundamentalGroupEquivFreeProduct U V hU hV hcover x hx
  have hprod : wab.prod = wba.prod := by
    apply e.injective
    simp only [wab, wba, wa, wb, Monoid.CoprodI.Word.prod_cons, map_mul]
    exact isMulCommutative_iff.mp hcomm _ _
  have hw : wab = wba := (Monoid.CoprodI.Word.equiv (M := G)).symm.injective hprod
  have hi := congrArg Monoid.CoprodI.Word.fstIdx hw
  simp only [wab, wba, Monoid.CoprodI.Word.fstIdx_cons, Option.some.injEq,
    Bool.false_eq_true] at hi

end DifferentialGeometry.Topology
