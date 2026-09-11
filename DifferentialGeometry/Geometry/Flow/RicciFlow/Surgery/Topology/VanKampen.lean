/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Authors: Sebastian Kumar
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Subpath
import Mathlib.Topology.UnitInterval

noncomputable section

open Set Function Filter Topology
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem SimplyConnectedCover.trans_mem {X : Type*} [TopologicalSpace X] {s : Set X} {x y z : X}
    (p : Path x y) (q : Path y z) (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    ∀ t, p.trans q t ∈ s := by
  apply Set.range_subset_iff.mp
  rw [Path.trans_range]
  exact Set.union_subset (Set.range_subset_iff.mpr hp) (Set.range_subset_iff.mpr hq)

structure FundamentalGroupVanKampen.TwoOpenCover (X : Type*) [TopologicalSpace X] where
  U : TopologicalSpace.Opens X
  V : TopologicalSpace.Opens X
  cover : (U : Set X) ∪ V = Set.univ
  pathConnectedU : IsPathConnected (U : Set X)
  pathConnectedV : IsPathConnected (V : Set X)
  pathConnectedIntersection : IsPathConnected ((U : Set X) ∩ V)
  base : X
  baseU : base ∈ U
  baseV : base ∈ V

abbrev FundamentalGroupVanKampen.TwoOpenCover.chart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : Bool → TopologicalSpace.Opens X
  | false => D.U
  | true => D.V

theorem FundamentalGroupVanKampen.TwoOpenCover.base_mem_chart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) : D.base ∈ D.chart i := by
  cases i
  · exact D.baseU
  · exact D.baseV

theorem FundamentalGroupVanKampen.TwoOpenCover.chart_open {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) : IsOpen (D.chart i : Set X) :=
  (D.chart i).isOpen

theorem FundamentalGroupVanKampen.TwoOpenCover.chart_cover {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : ⋃ i, (D.chart i : Set X) = Set.univ := by
  apply subset_antisymm (Set.subset_univ _)
  intro x _
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨Bool.false, hx⟩
  · exact Set.mem_iUnion.mpr ⟨Bool.true, hx⟩

theorem FundamentalGroupVanKampen.TwoOpenCover.mem_U_or_V {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : X) : x ∈ D.U ∨ x ∈ D.V := by
  have hx : x ∈ (D.U : Set X) ∪ D.V := by rw [D.cover]; trivial
  exact hx

def FundamentalGroupVanKampen.TwoOpenCover.rawPathTo {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : X) : Path D.base x := by
  classical
  exact
    if h : x ∈ (D.U : Set X) ∩ D.V then
      (D.pathConnectedIntersection.joinedIn D.base ⟨D.baseU, D.baseV⟩ x h).somePath
    else
      if hU : x ∈ D.U then (D.pathConnectedU.joinedIn D.base D.baseU x hU).somePath
      else
        (D.pathConnectedV.joinedIn D.base D.baseV x ((D.mem_U_or_V x).resolve_left hU)).somePath

theorem FundamentalGroupVanKampen.TwoOpenCover.rawPathTo_mem {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : X) (hx : x ∈ D.chart i)
    (t : (unitInterval)) : D.rawPathTo x t ∈ D.chart i := by
  classical
  cases i with
  | false =>
    change D.rawPathTo x t ∈ D.U
    change x ∈ D.U at hx
    unfold rawPathTo
    by_cases h : x ∈ (D.U : Set X) ∩ D.V
    · rw [dif_pos h]
      exact
        ((D.pathConnectedIntersection.joinedIn D.base ⟨D.baseU, D.baseV⟩ x h).somePath_mem t).1
    · rw [dif_neg h, dif_pos hx]
      exact JoinedIn.somePath_mem _ t
  | true =>
    change D.rawPathTo x t ∈ D.V
    change x ∈ D.V at hx
    unfold rawPathTo
    by_cases h : x ∈ (D.U : Set X) ∩ D.V
    · rw [dif_pos h]
      exact
        ((D.pathConnectedIntersection.joinedIn D.base ⟨D.baseU, D.baseV⟩ x h).somePath_mem t).2
    · have hnU : x ∉ D.U := fun hU => h ⟨hU, hx⟩
      rw [dif_neg h, dif_neg hnU]
      exact JoinedIn.somePath_mem _ t

def FundamentalGroupVanKampen.TwoOpenCover.pathTo {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : X) : Path D.base x := by
  classical exact if h : x = D.base then (Path.refl D.base).cast rfl h else D.rawPathTo x

@[simp]
theorem FundamentalGroupVanKampen.TwoOpenCover.pathTo_base {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.pathTo D.base = Path.refl D.base := by
  classical simp [pathTo]

theorem FundamentalGroupVanKampen.TwoOpenCover.pathTo_mem {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : X) (hx : x ∈ D.chart i)
    (t : (unitInterval)) : D.pathTo x t ∈ D.chart i := by
  classical
  unfold pathTo
  split_ifs
  · exact D.base_mem_chart i
  · exact D.rawPathTo_mem i x hx t

abbrev FundamentalGroupVanKampen.TwoOpenCover.baseUPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.U :=
  ⟨D.base, D.baseU⟩

abbrev FundamentalGroupVanKampen.TwoOpenCover.baseVPoint {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.V :=
  ⟨D.base, D.baseV⟩

abbrev FundamentalGroupVanKampen.TwoOpenCover.baseChart {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) : D.chart i :=
  ⟨D.base, D.base_mem_chart i⟩

abbrev FundamentalGroupVanKampen.TwoOpenCover.UGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :=
  FundamentalGroup D.U D.baseUPoint

abbrev FundamentalGroupVanKampen.TwoOpenCover.VGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :=
  FundamentalGroup D.V D.baseVPoint

def FundamentalGroupVanKampen.TwoOpenCover.inclusionU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : C(D.U, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def FundamentalGroupVanKampen.TwoOpenCover.inclusionV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : C(D.V, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def FundamentalGroupVanKampen.TwoOpenCover.inclusionHomU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.UGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionU D.baseUPoint

def FundamentalGroupVanKampen.TwoOpenCover.inclusionHomV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.VGroup →* FundamentalGroup X D.base :=
  FundamentalGroup.map D.inclusionV D.baseVPoint

def FundamentalGroupVanKampen.pathIn {X : Type*} [TopologicalSpace X] {S : Set X} {x y : X}
    (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) : Path (⟨x, hx⟩ : S) ⟨y, hy⟩
    where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp]
theorem FundamentalGroupVanKampen.pathIn_apply {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) (t : (unitInterval)) :
    (pathIn p hx hy hp t : X) = p t :=
  rfl

@[simp]
theorem FundamentalGroupVanKampen.pathIn_map {X : Type*} [TopologicalSpace X] {S : Set X}
    {x y : X} (p : Path x y) (hx : x ∈ S) (hy : y ∈ S) (hp : ∀ t, p t ∈ S) :
    (pathIn p hx hy hp).map continuous_subtype_val = p := by
  ext t
  rfl

theorem TriangleRegularBaseFundamentalGroup.pathClass_property_cast {X : Type*}
    [TopologicalSpace X] (P : ∀ {x y : X}, Path.Homotopic.Quotient x y → Prop) {x y x' y' : X}
    (q : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y) (hq : P q) : P (q.cast hx hy) :=
  by
  cases hx
  cases hy
  simpa using hq

theorem TriangleRegularBaseFundamentalGroup.pathClass_induction_of_open_cover {X : Type*}
    [TopologicalSpace X] {ι : Type*} (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (P : ∀ {x y : X}, Path.Homotopic.Quotient x y → Prop)
    (h_refl : ∀ x, P (Path.Homotopic.Quotient.refl x))
    (h_trans :
      ∀ {x y z : X} {p : Path.Homotopic.Quotient x y} {q : Path.Homotopic.Quotient y z},
        P p → P q → P (p.trans q))
    (h_local :
      ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i → P (Path.Homotopic.Quotient.mk p)) :
    ∀ {x y : X} (q : Path.Homotopic.Quotient x y), P q := by
  intro x y q
  obtain ⟨p⟩ := q
  have hpre : Set.univ ⊆ ⋃ i, p ⁻¹' U i := by
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (fun i => (hopen i).preimage p.continuous)
      hpre
  have hwalk : ∀ k : ℕ, P (Path.Homotopic.Quotient.mk (p.subpath 0 (t k))) := by
    intro k
    induction k with
    | zero =>
      rw [ht0, Path.subpath_self, Path.Homotopic.Quotient.mk_refl]
      exact h_refl (p 0)
    | succ k ih =>
      obtain ⟨i, hi⟩ := hsub k
      have hmem : Set.range (p.subpath (t k) (t (k + 1))) ⊆ U i := by
        rw [p.range_subpath_of_le _ _ (hmono (Nat.le_succ k))]
        exact Set.image_subset_iff.mpr hi
      have hconcat :
        Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (p.subpath 0 (t k)))
            (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1)))) =
          Path.Homotopic.Quotient.mk (p.subpath 0 (t (k + 1))) := by
        rw [← Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.eq]
        exact ⟨Path.Homotopy.subpathTransSubpath p 0 (t k) (t (k + 1))⟩
      rw [← hconcat]
      exact h_trans ih (h_local i _ hmem)
  have hfull := hwalk n
  rw [hn n le_rfl] at hfull
  have hp :
    (Path.Homotopic.Quotient.mk (p.subpath 0 1)).cast p.source.symm p.target.symm =
      Path.Homotopic.Quotient.mk p := by
    rw [← Path.Homotopic.Quotient.mk_cast, Path.subpath_zero_one]
    rfl
  have htransport := pathClass_property_cast P _ p.source.symm p.target.symm hfull
  rwa [hp] at htransport

theorem TriangleRegularBaseFundamentalGroup.quotient_symm_trans_cancel {X : Type*}
    [TopologicalSpace X] {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : p.symm.trans (p.trans q) = q := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

def TriangleRegularBaseFundamentalGroup.basedLoop {X : Type*} [TopologicalSpace X] {o : X}
    (F : ∀ x, Path.Homotopic.Quotient o x) {x y : X} (p : Path.Homotopic.Quotient x y) :
    FundamentalGroup X o :=
  ((F x).trans p).trans (F y).symm

@[simp]
theorem TriangleRegularBaseFundamentalGroup.basedLoop_refl {X : Type*} [TopologicalSpace X]
    {o : X} (F : ∀ x, Path.Homotopic.Quotient o x) (x : X) :
    basedLoop F (Path.Homotopic.Quotient.refl x) = 1 := by
  simp only [basedLoop, Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.trans_symm,
    FundamentalGroup.one_def]

theorem TriangleRegularBaseFundamentalGroup.basedLoop_trans {X : Type*} [TopologicalSpace X]
    {o x y z : X} (F : ∀ x, Path.Homotopic.Quotient o x) (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : basedLoop F (p.trans q) = basedLoop F q * basedLoop F p :=
  by
  simp only [basedLoop, FundamentalGroup.mul_def, Path.Homotopic.Quotient.trans_assoc,
    quotient_symm_trans_cancel]

theorem FundamentalGroupVanKampen.TwoOpenCover.hom_ext {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (f g : FundamentalGroup X D.base →* G) (hU : f.comp D.inclusionHomU = g.comp D.inclusionHomU)
    (hV : f.comp D.inclusionHomV = g.comp D.inclusionHomV) : f = g := by
  let F (x : X) : Path.Homotopic.Quotient D.base x := Path.Homotopic.Quotient.mk (D.pathTo x)
  have hlocal :
    ∀ (i : Bool) {x y : X} (p : Path x y),
      (∀ t, p t ∈ D.chart i) →
        f (TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p)) =
          g (TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p)) := by
    intro i x y p hp
    have hx : x ∈ D.chart i := by simpa using hp 0
    have hy : y ∈ D.chart i := by simpa using hp 1
    let l : Path D.base D.base := ((D.pathTo x).trans p).trans (D.pathTo y).symm
    have hl : ∀ t, l t ∈ D.chart i :=
      SimplyConnectedCover.trans_mem _ _
        (SimplyConnectedCover.trans_mem _ _ (D.pathTo_mem i x hx) hp)
        (fun t => D.pathTo_mem i y hy (unitInterval.symm t))
    let l' : Path (D.baseChart i) (D.baseChart i) :=
      FundamentalGroupVanKampen.pathIn l (D.base_mem_chart i) (D.base_mem_chart i) hl
    have hmap :
      (Path.Homotopic.Quotient.mk l').map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(D.chart i, X)) =
        TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p) := by
      change
        Path.Homotopic.Quotient.mk (l'.map continuous_subtype_val) =
          TriangleRegularBaseFundamentalGroup.basedLoop F (Path.Homotopic.Quotient.mk p)
      rw [show l'.map continuous_subtype_val = l from
          FundamentalGroupVanKampen.pathIn_map _ _ _ _]
      rfl
    cases i with
    | false =>
      have h := DFunLike.congr_fun hU (Path.Homotopic.Quotient.mk l')
      exact (congrArg f hmap).symm.trans (h.trans (congrArg g hmap))
    | true =>
      have h := DFunLike.congr_fun hV (Path.Homotopic.Quotient.mk l')
      exact (congrArg f hmap).symm.trans (h.trans (congrArg g hmap))
  have hall :
    ∀ {x y : X} (q : Path.Homotopic.Quotient x y),
      f (TriangleRegularBaseFundamentalGroup.basedLoop F q) =
        g (TriangleRegularBaseFundamentalGroup.basedLoop F q) := by
    apply
      TriangleRegularBaseFundamentalGroup.pathClass_induction_of_open_cover
        (fun i => (D.chart i : Set X)) D.chart_open D.chart_cover
        (fun q =>
          f (TriangleRegularBaseFundamentalGroup.basedLoop F q) =
            g (TriangleRegularBaseFundamentalGroup.basedLoop F q))
    · intro x
      simp only [TriangleRegularBaseFundamentalGroup.basedLoop_refl, map_one]
    · intro x y z p q hp hq
      rw [TriangleRegularBaseFundamentalGroup.basedLoop_trans, map_mul, map_mul, hp, hq]
    · intro i x y p hp
      exact hlocal i p (Set.range_subset_iff.mp hp)
  have hbase : F D.base = Path.Homotopic.Quotient.refl D.base := by
    simp only [F, D.pathTo_base, Path.Homotopic.Quotient.mk_refl]
  have hsymm : (Path.Homotopic.Quotient.refl D.base).symm = Path.Homotopic.Quotient.refl D.base :=
    by
    change (1 : FundamentalGroup X D.base)⁻¹ = 1
    exact inv_one
  apply MonoidHom.ext
  intro q
  simpa only [TriangleRegularBaseFundamentalGroup.basedLoop, hbase,
    Path.Homotopic.Quotient.refl_trans, hsymm, Path.Homotopic.Quotient.trans_refl] using hall q

theorem fundamentalGroup_eq_one_of_path {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    (hx : ∀ g : FundamentalGroup X x, g = 1) (g : FundamentalGroup X y) : g = 1 := by
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  obtain ⟨h, rfl⟩ := e.surjective g
  rw [hx h, map_one]

theorem simplyConnectedSpace_iff_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) : SimplyConnectedSpace X ↔ ∀ g : FundamentalGroup X x, g = 1 :=
  by
  constructor
  · intro h
    let : SimplyConnectedSpace X := h
    exact fun _ => Subsingleton.elim _ _
  · intro hx
    apply simply_connected_iff_loops_nullhomotopic.mpr
    refine ⟨inferInstance, ?_⟩
    intro y γ
    exact
      Path.Homotopic.Quotient.eq.mp
        (fundamentalGroup_eq_one_of_path (PathConnectedSpace.somePath x y) hx
          (Path.Homotopic.Quotient.mk γ))

theorem simplyConnectedSpace_of_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) (hx : ∀ g : FundamentalGroup X x, g = 1) :
    SimplyConnectedSpace X :=
  (simplyConnectedSpace_iff_fundamentalGroup_eq_one x).mpr hx

theorem SphereHomology.twoOpenCover_pathConnectedSpace {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : PathConnectedSpace X := by
  apply pathConnectedSpace_iff_univ.mpr
  rw [← D.cover]
  exact D.pathConnectedU.union D.pathConnectedV ⟨D.base, D.baseU, D.baseV⟩

theorem SphereHomology.twoOpenCover_fundamentalGroup_eq_one {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) [SimplyConnectedSpace D.U]
    [SimplyConnectedSpace D.V] (g : FundamentalGroup X D.base) : g = 1 := by
  have h :
    MonoidHom.id (FundamentalGroup X D.base) =
      (1 : FundamentalGroup X D.base →* FundamentalGroup X D.base) := by
    apply D.hom_ext
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomU a = 1
      rw [ha, map_one]
    · ext a
      have ha : a = 1 := Subsingleton.elim _ _
      change D.inclusionHomV a = 1
      rw [ha, map_one]
  exact DFunLike.congr_fun h g

theorem SphereHomology.twoOpenCover_simplyConnectedSpace {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) [SimplyConnectedSpace D.U]
    [SimplyConnectedSpace D.V] : SimplyConnectedSpace X := by
  let := twoOpenCover_pathConnectedSpace D
  exact
    simplyConnectedSpace_of_fundamentalGroup_eq_one D.base
      (twoOpenCover_fundamentalGroup_eq_one D)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
