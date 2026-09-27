/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartLocalApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPastingManifold
import DifferentialGeometry.Topology.PiecewiseLinear.Moise308Nested
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOn
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Endpoint
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Logic.Relation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

section Annulus

variable {M : Type*} [TopologicalSpace M]

def IsAnnulusOn (A A₀ A₁ : Set M) : Prop :=
  ∃ φ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Icc (0 : ℝ) 1) ≃ₜ A,
    A₀ = Subtype.val '' (φ '' {p | (p.2 : ℝ) = 0}) ∧
    A₁ = Subtype.val '' (φ '' {p | (p.2 : ℝ) = 1})

theorem isAnnulusOn_univ_prod :
    IsAnnulusOn
        (univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Icc (0 : ℝ) 1))
        {p | (p.2 : ℝ) = 0} {p | (p.2 : ℝ) = 1} ∧
      Disjoint
        {p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Icc (0 : ℝ) 1 |
          (p.2 : ℝ) = 0}
        {p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Icc (0 : ℝ) 1 |
          (p.2 : ℝ) = 1} := by
  have key : ∀ S : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Icc (0 : ℝ) 1),
      Subtype.val '' ((Homeomorph.Set.univ
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Set.Icc (0 : ℝ) 1)).symm '' S) = S := by
    intro S
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact hz
    · exact fun x hx => ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨⟨(Homeomorph.Set.univ _).symm, (key _).symm, (key _).symm⟩,
    Set.disjoint_left.mpr fun p hp hp' => ?_⟩
  exact absurd (hp.symm.trans hp') zero_ne_one

theorem IsAnnulusOn.first_subset {A A₀ A₁ : Set M} (h : IsAnnulusOn A A₀ A₁) : A₀ ⊆ A := by
  obtain ⟨φ, h₀, -⟩ := h
  rw [h₀]
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem IsAnnulusOn.second_subset {A A₀ A₁ : Set M} (h : IsAnnulusOn A A₀ A₁) : A₁ ⊆ A := by
  obtain ⟨φ, -, h₁⟩ := h
  rw [h₁]
  rintro _ ⟨z, -, rfl⟩
  exact z.2

end Annulus

inductive Section34Label (Vx Tt Ed Fc Pa Ar Eg Mk : Type v) : Type v
  | vertexBall (v : Vx)
  | tetraBall (t : Tt)
  | splitDisk (e : Ed)
  | faceDisk (s : Fc)
  | patch (x : Pa)
  | faceArc (a : Ar)
  | edgeArc (i : Eg)
  | markedPoint (p : Mk)

def section34Dim {Vx Tt Ed Fc Pa Ar Eg Mk : Type v} :
    Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → ℕ
  | .vertexBall _ => 3
  | .tetraBall _ => 3
  | .splitDisk _ => 2
  | .faceDisk _ => 2
  | .patch _ => 2
  | .faceArc _ => 1
  | .edgeArc _ => 1
  | .markedPoint _ => 0

def section34Cell {M : Type*} {Vx Tt Ed Fc Pa Ar Eg Mk : Type v}
    (cV : Vx → Set M) (cT : Tt → Set M) (cE : Ed → Set M) (cF : Fc → Set M)
    (cP : Pa → Set M) (cA : Ar → Set M) (cG : Eg → Set M) (cM : Mk → Set M) :
    Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M
  | .vertexBall v => cV v
  | .tetraBall t => cT t
  | .splitDisk e => cE e
  | .faceDisk s => cF s
  | .patch x => cP x
  | .faceArc a => cA a
  | .edgeArc i => cG i
  | .markedPoint p => cM p

def section34Face {Λ : Type*} {M : Type*} (c : Λ → Set M) (l : Λ) : Set Λ :=
  {m | c m ⊆ c l}

theorem section34Dim_eq_three {Vx Tt Ed Fc Pa Ar Eg Mk : Type v}
    {l : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk} (hl : section34Dim l = 3) :
    (∃ v, l = .vertexBall v) ∨ ∃ t, l = .tetraBall t := by
  cases l with
  | vertexBall v => exact Or.inl ⟨v, rfl⟩
  | tetraBall t => exact Or.inr ⟨t, rfl⟩
  | splitDisk e => simp [section34Dim] at hl
  | faceDisk s => simp [section34Dim] at hl
  | patch x => simp [section34Dim] at hl
  | faceArc a => simp [section34Dim] at hl
  | edgeArc i => simp [section34Dim] at hl
  | markedPoint p => simp [section34Dim] at hl

def CarriesFundamentalGroupOnto {Y : Type*} [TopologicalSpace Y] (J T : Set Y) : Prop :=
  J ⊆ T ∧ ∀ (hJT : J ⊆ T) (b : J),
    Function.Surjective
      (FundamentalGroup.map (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)) b)

section Generator

theorem fundamentalGroup_map_continuousMap_comp {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    FundamentalGroup.map (g.comp f) x =
      (FundamentalGroup.map g (f x)).comp (FundamentalGroup.map f x) := by
  apply MonoidHom.ext
  intro p
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
    change Path.Homotopic.Quotient.mk (p.map (g.comp f).continuous) =
      Path.Homotopic.Quotient.mk ((p.map f.continuous).map g.continuous)
    congr 1

theorem carriesFundamentalGroupOnto_of_homeomorph {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {J T : Set Y} {J' T' : Set Z} (hJT : J ⊆ T) (hJT' : J' ⊆ T')
    (Φ : T ≃ₜ T') (hΦ : ∀ y : T, (y : Y) ∈ J ↔ (Φ y : Z) ∈ J')
    (hcarry : CarriesFundamentalGroupOnto J' T') :
    CarriesFundamentalGroupOnto J T := by
  have hto : ∀ y : J, ((Φ (inclusion hJT y) : T') : Z) ∈ J' :=
    fun y => (hΦ (inclusion hJT y)).1 y.2
  have hfrom : ∀ z : J', ((Φ.symm (inclusion hJT' z) : T) : Y) ∈ J := by
    intro z
    refine (hΦ (Φ.symm (inclusion hJT' z))).2 ?_
    rw [Φ.apply_symm_apply]
    exact z.2
  let ΦJ : J ≃ₜ J' :=
    { toFun := fun y => ⟨_, hto y⟩
      invFun := fun z => ⟨_, hfrom z⟩
      left_inv := fun y => Subtype.ext (by
        change ((Φ.symm (Φ (inclusion hJT y)) : T) : Y) = (y : Y)
        rw [Φ.symm_apply_apply])
      right_inv := fun z => Subtype.ext (by
        change ((Φ (Φ.symm (inclusion hJT' z)) : T') : Z) = (z : Z)
        rw [Φ.apply_symm_apply])
      continuous_toFun :=
        (continuous_subtype_val.comp (Φ.continuous.comp (continuous_inclusion hJT))).subtype_mk _
      continuous_invFun :=
        (continuous_subtype_val.comp
          (Φ.symm.continuous.comp (continuous_inclusion hJT'))).subtype_mk _ }
  refine ⟨hJT, fun hsub b => ?_⟩
  set i : C(J, T) := ⟨inclusion hsub, continuous_inclusion hsub⟩ with hidef
  set i' : C(J', T') := ⟨inclusion hJT', continuous_inclusion hJT'⟩ with hi'def
  set Φc : C(T, T') := ⟨Φ, Φ.continuous⟩ with hΦcdef
  set ΦJc : C(J, J') := ⟨ΦJ, ΦJ.continuous⟩ with hΦJcdef
  have hsquare : i'.comp ΦJc = Φc.comp i := by
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    rfl
  have hΦbij : Function.Bijective (FundamentalGroup.map Φc (i b)) :=
    DifferentialGeometry.Topology.bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse
      Φ.symm.toHomotopyEquiv Φc (fun x => Φ.symm_apply_apply x) (i b)
  have hΦJsurj : Function.Surjective (FundamentalGroup.map ΦJc b) :=
    (DifferentialGeometry.Topology.bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse
      ΦJ.symm.toHomotopyEquiv ΦJc (fun x => ΦJ.symm_apply_apply x) b).2
  have hsurj' : Function.Surjective (FundamentalGroup.map i' (ΦJc b)) := hcarry.2 hJT' (ΦJc b)
  have key : Function.Surjective (FundamentalGroup.map (Φc.comp i) b) := by
    rw [← hsquare, fundamentalGroup_map_continuousMap_comp]
    intro z
    obtain ⟨y, hy⟩ := hsurj' z
    obtain ⟨s, hs⟩ := hΦJsurj y
    exact ⟨s, by rw [MonoidHom.comp_apply, hs, hy]⟩
  rw [fundamentalGroup_map_continuousMap_comp] at key
  intro t
  obtain ⟨s, hs⟩ := key (FundamentalGroup.map Φc (i b) t)
  exact ⟨s, hΦbij.1 hs⟩

theorem carriesFundamentalGroupOnto_of_nestedSolidTorus {Y : Type*} [TopologicalSpace Y]
    {J T : Set Y} {S₁ S₂ Te Je : Set (EuclideanSpace ℝ (Fin 3))} (hJT : J ⊆ T)
    (Φ : T ≃ₜ Te) (hΦ : ∀ y : T, (y : Y) ∈ J ↔ (Φ y : EuclideanSpace ℝ (Fin 3)) ∈ Je)
    (hS₁ : IsTopologicalSolidTorus S₁) (hS₂ : IsTopologicalSolidTorus S₂)
    (hTe : IsCombinatorialSolidTorus Te) (h₁T : S₁ ⊆ interior Te) (hT₂ : Te ⊆ interior S₂)
    (hshell : IsToroidalShell (closure (S₂ \ S₁)) (frontier S₁) (frontier S₂))
    (hspine : IsSpine S₁ Je) (hJe : Je ⊆ Te) :
    CarriesFundamentalGroupOnto J T := by
  refine carriesFundamentalGroupOnto_of_homeomorph hJT hJe Φ hΦ ⟨hJe, fun hsub b => ?_⟩
  exact (moise308Nested S₁ Te S₂ Je hS₁ hS₂ hTe h₁T hT₂ hshell hspine hsub b).2

end Generator

section Exporters

theorem biUnion_ulift_down {Λ : Type v} {M : Type*} (f : Λ → Set M) (S : Set (ULift.{u} Λ))
    (T : Set Λ) (hST : ∀ m : ULift.{u} Λ, m ∈ S ↔ m.down ∈ T) :
    ⋃ m ∈ S, f m.down = ⋃ m ∈ T, f m := by
  ext x
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, hm, hx⟩
    exact ⟨m.down, (hST m).1 hm, hx⟩
  · rintro ⟨m, hm, hx⟩
    exact ⟨⟨m⟩, (hST ⟨m⟩).2 hm, hx⟩

theorem iUnion_ulift_down {Λ : Type v} {M : Type*} (f : Λ → Set M) :
    ⋃ m : ULift.{u} Λ, f m.down = ⋃ m, f m := by
  ext x
  simp only [mem_iUnion]
  exact ⟨fun ⟨m, hx⟩ => ⟨m.down, hx⟩, fun ⟨m, hx⟩ => ⟨⟨m⟩, hx⟩⟩

theorem finite_ulift_down {Λ : Type v} (T : Set Λ) (hT : T.Finite) :
    {m : ULift.{u} Λ | m.down ∈ T}.Finite :=
  (hT.image ULift.up).subset fun m hm => ⟨m.down, hm, rfl⟩

theorem finite_face_of_locallyFinite {Λ : Type*} {M : Type*} [TopologicalSpace M]
    (U : Set M) (sc : Λ → Set M) (m : Λ) (hne : ∀ l, (sc l).Nonempty)
    (hcpt : IsCompact (sc m)) (hsub : ∀ l, sc l ⊆ U)
    (hLF : ∀ x ∈ U, ∃ W ∈ 𝓝 x, {l | (sc l ∩ W).Nonempty}.Finite) :
    (section34Face sc m).Finite := by
  classical
  have key : ∀ x : M, ∃ W : Set M, x ∈ sc m →
      W ∈ 𝓝 x ∧ {l | (sc l ∩ W).Nonempty}.Finite := by
    intro x
    by_cases hx : x ∈ sc m
    · obtain ⟨W, hW, hfin⟩ := hLF x (hsub m hx)
      exact ⟨W, fun _ => ⟨hW, hfin⟩⟩
    · exact ⟨univ, fun hx' => absurd hx' hx⟩
  choose W hW using key
  obtain ⟨t, hts, ht⟩ := hcpt.elim_nhds_subcover W fun x hx => (hW x hx).1
  have hfin : (⋃ x ∈ (t : Set M), {l | (sc l ∩ W x).Nonempty}).Finite :=
    t.finite_toSet.biUnion fun x hx => (hW x (hts x (Finset.mem_coe.mp hx))).2
  refine hfin.subset fun l hl => ?_
  obtain ⟨y, hy⟩ := hne l
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (ht (hl hy))
  exact mem_iUnion₂.mpr ⟨x, Finset.mem_coe.mpr hx, ⟨y, hy, hyx⟩⟩

theorem carrier_subset_and_dist_lt_of_parent {Λ : Type*} {M N : Type*} [PseudoMetricSpace N]
    (sc : Λ → Set M) (tc car : Λ → Set N) (par : Λ → Λ) (h : M → N) (η : M → ℝ)
    (hsrc : ∀ l, sc l ⊆ sc (par l)) (htgt : ∀ l, tc l ⊆ tc (par l))
    (hcar : ∀ l, h '' sc (par l) ∪ tc (par l) ⊆ car (par l))
    (hsm : ∀ l, ∀ x ∈ sc (par l), ∀ y ∈ car (par l), ∀ z ∈ car (par l), dist y z < η x) :
    (∀ l, h '' sc l ∪ tc l ⊆ car (par l)) ∧
      ∀ l, ∀ x ∈ sc l, ∀ y ∈ car (par l), ∀ z ∈ car (par l), dist y z < η x := by
  constructor
  · rintro l w (⟨x, hx, rfl⟩ | hw)
    · exact hcar l (Or.inl ⟨x, hsrc l hx, rfl⟩)
    · exact hcar l (Or.inr (htgt l hw))
  · exact fun l x hx y hy z hz => hsm l x (hsrc l hx) y hy z hz

theorem exists_nhds_finite_of_subset_carriers {ι κ : Type*} {Y : Type*} [TopologicalSpace Y]
    (Y₀ : Set Y) (S : ι → Set Y) (Hc : κ → Set Y) (cr : ι → κ)
    (hSH : ∀ i, S i ⊆ Hc (cr i)) (hHY : ∀ i, Hc (cr i) ⊆ Y₀)
    (hfib : ∀ k, {i | cr i = k}.Finite)
    (hLF : ∀ y ∈ Y₀, ∃ V ∈ 𝓝[Y₀] y, {k | ∃ i, cr i = k ∧ (Hc k ∩ V).Nonempty}.Finite) :
    ∀ y ∈ ⋃ i, S i, ∃ V ∈ 𝓝 y, {i | (S i ∩ V).Nonempty}.Finite := by
  intro y hy
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp hy
  obtain ⟨V, hV, hfin⟩ := hLF y (hHY i₀ (hSH i₀ hi₀))
  obtain ⟨O, hOopen, hyO, hOV⟩ := mem_nhdsWithin.mp hV
  refine ⟨O, hOopen.mem_nhds hyO, ((hfin.biUnion fun k _ => hfib k).subset ?_)⟩
  rintro i ⟨x, hx, hxO⟩
  have hxH : x ∈ Hc (cr i) := hSH i hx
  have hxV : x ∈ V := hOV ⟨hxO, hHY i hxH⟩
  exact mem_iUnion₂.mpr ⟨cr i, ⟨i, rfl, ⟨x, hxH, hxV⟩⟩, rfl⟩

theorem locallyFinite_subtype_of_subset_carriers {ι κ : Type*} {Y : Type*} [TopologicalSpace Y]
    (Y₀ : Set Y) (S : ι → Set Y) (Hc : κ → Set Y) (cr : ι → κ)
    (hSH : ∀ i, S i ⊆ Hc (cr i)) (hfib : ∀ k, {i | cr i = k}.Finite)
    (hLF : ∀ y ∈ Y₀, ∃ V ∈ 𝓝[Y₀] y, {k | ∃ i, cr i = k ∧ (Hc k ∩ V).Nonempty}.Finite) :
    LocallyFinite fun i => {y : Y₀ | (y : Y) ∈ S i} := by
  intro y
  obtain ⟨V, hV, hfin⟩ := hLF (y : Y) y.2
  refine ⟨Subtype.val ⁻¹' V, ?_, (hfin.biUnion fun k _ => hfib k).subset ?_⟩
  · rw [nhds_subtype_eq_comap_nhdsWithin Y₀ y]
    exact Filter.preimage_mem_comap hV
  · rintro i ⟨z, hz, hzV⟩
    exact mem_iUnion₂.mpr ⟨cr i, ⟨i, rfl, ⟨(z : Y), hSH i hz, hzV⟩⟩, rfl⟩

theorem locallyFinite_subtype_of_subset_of_finite_fibers {ι κ : Type*} {Y : Type*}
    [TopologicalSpace Y] {Y₀ : Set Y} (S : ι → Set Y) (T : κ → Set Y) (cr : ι → κ)
    (hST : ∀ i, S i ⊆ T (cr i)) (hfib : ∀ k, {i | cr i = k}.Finite)
    (hT : LocallyFinite fun k => {y : Y₀ | (y : Y) ∈ T k}) :
    LocallyFinite fun i => {y : Y₀ | (y : Y) ∈ S i} := by
  intro y
  obtain ⟨V, hV, hfin⟩ := hT y
  refine ⟨V, hV, (hfin.biUnion fun k _ => hfib k).subset ?_⟩
  rintro i ⟨z, hz, hzV⟩
  exact mem_iUnion₂.mpr ⟨cr i, ⟨z, hST i hz, hzV⟩, rfl⟩

theorem eqOn_of_eqOn_off_support {M N : Type*} {F F' : M → N} {C A : Set M} {Z : Set N}
    (hoff : EqOn F' F {x ∈ C | F x ∉ Z}) (hAC : A ⊆ C) (hdisj : Disjoint (F '' A) Z) :
    EqOn F' F A :=
  fun x hx => hoff ⟨hAC hx, fun hz => Set.disjoint_left.mp hdisj ⟨x, hx, rfl⟩ hz⟩

theorem exists_isPLHomeomorphInto_dualCellPaste {ι : Type*} {M₁ M₂ : Type u}
    [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [TopologicalSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] (base : M₁ → M₂) (C : ι → Set M₁)
    (G : ι → M₁ → M₂) (hC : ∀ i, IsClosed (C i)) (hD : ∀ i, IsClosed (G i '' C i))
    (hG : ∀ i, IsPLHomeomorphInto 3 (G i) (C i))
    (hcompat : ∀ i j, EqOn (G i) (G j) (C i ∩ C j))
    (hmeet : ∀ i j, G i '' (C i ∩ C j) = G i '' C i ∩ G j '' C j)
    (hsrc : ∀ x ∈ ⋃ i, C i, ∃ V ∈ 𝓝 x, {i | (C i ∩ V).Nonempty}.Finite)
    (htgt : ∀ y ∈ ⋃ i, G i '' C i, ∃ V ∈ 𝓝 y, {i | (G i '' C i ∩ V).Nonempty}.Finite) :
    ∃ F : M₁ → M₂, IsPLHomeomorphInto 3 F (⋃ i, C i) ∧ (∀ i, EqOn F (G i) (C i)) ∧
      F '' (⋃ i, C i) = ⋃ i, G i '' C i := by
  obtain ⟨F, hF, -, hFG, hFim⟩ :=
    exists_isPLHomeomorphInto_union_of_locallyFinite_pieces (A := (∅ : Set M₁))
      (B := (∅ : Set M₂)) (S := C) (T := fun i => G i '' C i) (F₀ := base) (f := G)
      isClosed_empty isClosed_empty hC hD (isPLHomeomorphInto_empty base) (image_empty base)
      hG (fun _ => rfl) (fun _ x hx => absurd hx.1 (notMem_empty x))
      (fun i => by rw [empty_inter, image_empty, empty_inter]) hcompat hmeet
      (fun x hx => hsrc x (by rwa [empty_union] at hx))
      (fun y hy => htgt y (by rwa [empty_union] at hy))
  rw [empty_union] at hF
  rw [empty_union, empty_union] at hFim
  exact ⟨F, hF, hFG, hFim⟩

end Exporters

section CellInterior

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [T2Space M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem mem_interior_image_of_notMem_image_boundary {S B : Set M₁} (hS : IsPLCellOn 3 S B)
    {G : M₁ → M₂} (hG : IsPLHomeomorphInto 3 G S) {p : M₂} (hpS : p ∈ G '' S)
    (hpB : p ∉ G '' B) : p ∈ interior (G '' S) := by
  obtain ⟨x, hx, rfl⟩ := hpS
  have hkey : G '' (S \ B) = interior (G '' S) :=
    (IsPLCellOn.image_boundary_interior hS hG).2
  rw [← hkey]
  exact ⟨x, ⟨hx, fun hb => hpB ⟨x, hb, rfl⟩⟩, rfl⟩

end CellInterior

section Triangulation

variable {Ea : Type*} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] {X : Type*} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}

def simplexBody (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (t : Finset Ea) : Set X :=
  𝒦.map '' convexHull ℝ (t : Set Ea)

def simplexRim (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (t : Finset Ea) : Set X :=
  ⋃ s ∈ {s : Finset Ea | s ⊂ t}, simplexBody 𝒦 s

def graphSkeletonSpace (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) : Set X :=
  ⋃ t ∈ {t : Finset Ea | t ∈ 𝒦.complex.faces ∧ t.card ≤ 2}, simplexBody 𝒦 t

def Section34CarrierSupport (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (t : Finset Ea) : Set X :=
  ⋃ w ∈ (t : Set Ea), ⋃ s ∈ {s : Finset Ea | s ∈ 𝒦.complex.faces ∧ w ∈ s}, simplexBody 𝒦 s

def Section34Incident (s t : Finset Ea) : Prop := (s : Set Ea) ⊆ convexHull ℝ (t : Set Ea)

abbrev Section34SimplexIndex (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (k : ℕ) :=
  {t : Finset Ea // t ∈ 𝒦.complex.faces ∧ t.card = k}

abbrev Section34GraphIndex (𝒦 : LocallyFinitePLPieceIn Ea 3 X U) (Γ : Set X) (k : ℕ) :=
  {t : Finset Ea // t ∈ 𝒦.complex.faces ∧ t.card = k ∧ simplexBody 𝒦 t ⊆ Γ}

abbrev Section34VertexIndex (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 X U) :=
  Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 1

abbrev Section34EdgeIndex (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 X U) :=
  Section34GraphIndex 𝒦' (graphSkeletonSpace 𝒦) 2

abbrev Section34PatchIndex (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 X U) :=
  {p : Section34SimplexIndex 𝒦 4 × Section34VertexIndex 𝒦 𝒦' //
    Section34Incident p.2.1 p.1.1}

abbrev Section34ArcIndex (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 X U) :=
  {p : Section34SimplexIndex 𝒦 3 × Section34VertexIndex 𝒦 𝒦' //
    Section34Incident p.2.1 p.1.1}

abbrev Section34EdgeArcIndex (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 X U) :=
  {p : Section34SimplexIndex 𝒦 4 × Section34EdgeIndex 𝒦 𝒦' //
    Section34Incident p.2.1 p.1.1}

abbrev Section34MarkIndex (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 X U) :=
  {p : Section34SimplexIndex 𝒦 3 × Section34EdgeIndex 𝒦 𝒦' //
    Section34Incident p.2.1 p.1.1}

abbrev Section34CutLabelOf (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 X U) :=
  Section34Label (Section34VertexIndex 𝒦 𝒦') (Section34SimplexIndex 𝒦 4)
    (Section34EdgeIndex 𝒦 𝒦') (Section34SimplexIndex 𝒦 3) (Section34PatchIndex 𝒦 𝒦')
    (Section34ArcIndex 𝒦 𝒦') (Section34EdgeArcIndex 𝒦 𝒦') (Section34MarkIndex 𝒦 𝒦')

def Section34CutStep {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 X U} :
    Section34CutLabelOf 𝒦 𝒦' → Section34CutLabelOf 𝒦 𝒦' → Prop
  | .splitDisk e, .vertexBall w => w.1 ⊆ e.1
  | .patch x, .vertexBall w => x.1.2 = w
  | .faceDisk s, .tetraBall t => Section34Incident s.1 t.1
  | .patch x, .tetraBall t => x.1.1 = t
  | .edgeArc i, .splitDisk e => i.1.2 = e
  | .faceArc a, .faceDisk s => a.1.1 = s
  | .faceArc a, .patch x => a.1.2 = x.1.2 ∧ Section34Incident a.1.1.1 x.1.1.1
  | .edgeArc i, .patch x => i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1
  | .markedPoint p, .faceArc a => p.1.1 = a.1.1 ∧ a.1.2.1 ⊆ p.1.2.1
  | .markedPoint p, .edgeArc i => p.1.2 = i.1.2 ∧ Section34Incident p.1.1.1 i.1.1.1
  | _, _ => False

def Section34CutLe {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 X U} :
    Section34CutLabelOf 𝒦 𝒦' → Section34CutLabelOf 𝒦 𝒦' → Prop :=
  Relation.ReflTransGen Section34CutStep

end Triangulation

section Frames

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

def section34LabelSimplex {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea) :
    Section34CutLabelOf 𝒦 𝒦' → Finset Ea
  | .vertexBall w => cr w
  | .tetraBall t => t.1
  | .splitDisk e => e.1
  | .faceDisk s => s.1
  | .patch x => x.1.1.1
  | .faceArc a => a.1.1.1
  | .edgeArc i => i.1.1.1
  | .markedPoint p => p.1.1.1

def Section34CarrierControl (U : Set M₁) (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) (h : M₁ → M₂)
    (η : M₁ → ℝ) (H : Finset Ea → Set M₂) : Prop :=
  (∀ t ∈ 𝒦.complex.faces, h '' Section34CarrierSupport 𝒦 t ⊆ interior (H t)) ∧
  (∀ t ∈ 𝒦.complex.faces, H t ⊆ h '' U) ∧
  (∀ y ∈ h '' U, ∃ V ∈ 𝓝[h '' U] y,
    {t | t ∈ 𝒦.complex.faces ∧ (H t ∩ V).Nonempty}.Finite) ∧
  (∀ t ∈ 𝒦.complex.faces, ∀ x ∈ Section34CarrierSupport 𝒦 t, ∀ y ∈ H t, ∀ z ∈ H t,
    dist y z < η x) ∧
  (∀ t ∈ 𝒦.complex.faces, IsPLCellOn 3 (H t) (frontier (H t))) ∧
  ∀ t ∈ 𝒦.complex.faces, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, H t ⊆ c.source

omit [FiniteDimensional ℝ Ea] in
theorem exists_chart_iUnion_carrier_subset_source {U : Set M₁}
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {h : M₁ → M₂} {η : M₁ → ℝ}
    {H : Finset Ea → Set M₂} (hH : Section34CarrierControl U 𝒦 h η H)
    (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (hQtri : ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      Section34Incident w.1 s.1 → Q w ⊆ H s.1) (s : Section34SimplexIndex 𝒦 3) :
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂,
      (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 s.1), Q w) ⊆ c.source := by
  obtain ⟨-, -, -, -, -, hchart⟩ := hH
  obtain ⟨c, hc, hcs⟩ := hchart s.1 s.2.1
  exact ⟨c, hc, iUnion₂_subset fun w hw => (hQtri w s hw).trans hcs⟩

def Section34CutFrame (U : Set M₁) (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁) : Prop :=
  IsCombinatorialManifold 3 𝒦.complex ∧
  IsSubdivision 𝒦'.complex 𝒦.complex ∧
  𝒦'.map = 𝒦.map ∧
  (∀ l, IsPLCellOn (section34Dim l) (src l) (srcBd l)) ∧
  (∀ l, srcBd l = ⋃ m ∈ section34Face src l \ {l}, src m) ∧
  (∀ l m, src l ∩ src m = ⋃ k ∈ section34Face src l ∩ section34Face src m, src k) ∧
  (∀ l m, src m ⊆ src l → m = l ∨ section34Dim m < section34Dim l) ∧
  (∀ x ∈ U, ∃ V ∈ 𝓝 x, {l | (src l ∩ V).Nonempty}.Finite) ∧
  (⋃ l, src l) = U ∧
  (∀ a : Section34ArcIndex 𝒦 𝒦',
    src (.faceArc a) = src (.vertexBall a.1.2) ∩ src (.faceDisk a.1.1)) ∧
  (∀ p : Section34MarkIndex 𝒦 𝒦',
    src (.markedPoint p) = src (.splitDisk p.1.2) ∩ src (.faceDisk p.1.1)) ∧
  (∀ x : Section34PatchIndex 𝒦 𝒦',
    src (.patch x) = src (.tetraBall x.1.1) ∩ src (.vertexBall x.1.2)) ∧
  (∀ i : Section34EdgeArcIndex 𝒦 𝒦',
    src (.edgeArc i) = src (.tetraBall i.1.1) ∩ src (.splitDisk i.1.2)) ∧
  (∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
    ¬ Section34Incident w.1 s.1 → src (.faceDisk s) ∩ src (.vertexBall w) = ∅) ∧
  (∀ (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦'),
    ¬ Section34Incident e.1 s.1 → src (.faceDisk s) ∩ src (.splitDisk e) = ∅) ∧
  (∀ (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦'),
    ¬ Section34Incident w.1 t.1 → src (.tetraBall t) ∩ src (.vertexBall w) = ∅) ∧
  (∀ (t : Section34SimplexIndex 𝒦 4) (e : Section34EdgeIndex 𝒦 𝒦'),
    ¬ Section34Incident e.1 t.1 → src (.tetraBall t) ∩ src (.splitDisk e) = ∅) ∧
  (∀ l, ∃ m, section34Dim m = 3 ∧ src l ⊆ src m) ∧
  (∀ s : Section34SimplexIndex 𝒦 3, src (.faceDisk s) ⊆ simplexBody 𝒦 s.1) ∧
  (∀ t : Section34SimplexIndex 𝒦 4, src (.tetraBall t) ⊆ Section34CarrierSupport 𝒦 t.1) ∧
  (∀ w : Section34VertexIndex 𝒦 𝒦', simplexBody 𝒦' w.1 ⊆ src (.vertexBall w)) ∧
  (∀ (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦'),
    (src (.vertexBall w) ∩ src (.splitDisk e)).Nonempty → w.1 ⊆ e.1) ∧
  (∀ e : Section34EdgeIndex 𝒦 𝒦', ∃ w w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' ∧
    (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (w'.1 : Set Ea) ∧
      src (.splitDisk e) = src (.vertexBall w) ∩ src (.vertexBall w')) ∧
  (∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
    Section34Incident s.1 t.1 → src (.faceDisk s) ⊆ src (.tetraBall t)) ∧
  ∀ s : Section34SimplexIndex 𝒦 3, ∃ t : Section34SimplexIndex 𝒦 4,
    Section34Incident s.1 t.1

omit [FiniteDimensional ℝ Ea] in
theorem finite_splitDisk_of_section34CutFrame {U : Set M₁}
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (D : Section34EdgeIndex 𝒦 𝒦' → Section34VertexIndex 𝒦 𝒦')
    (hD : ∀ e, src (Section34Label.splitDisk e) ⊆ src (Section34Label.vertexBall (D e)))
    (w : Section34VertexIndex 𝒦 𝒦') : {e | D e = w}.Finite := by
  obtain ⟨-, -, -, hcell, -, -, -, hLF, hcover, -⟩ := id hframe
  have hsub : ∀ l, src l ⊆ U := fun l => (subset_iUnion src l).trans hcover.subset
  have hface := finite_face_of_locallyFinite U src (Section34Label.vertexBall w)
    (fun l => (hcell l).nonempty) (hcell _).isCompact hsub hLF
  refine Set.Finite.of_finite_image (f := fun e =>
    (Section34Label.splitDisk e : Section34CutLabelOf 𝒦 𝒦')) (hface.subset ?_) ?_
  · rintro _ ⟨e, he, rfl⟩
    have hsube := hD e
    rw [show D e = w from he] at hsube
    exact hsube
  · intro a _ b _ hab
    simpa using hab

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem locallyFinite_support_of_section34CutFrame {U : Set M₁}
    {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {h : M₁ → M₂}
    {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
    (Sp : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hends : ∀ e, src (Section34Label.splitDisk e) =
      src (Section34Label.vertexBall (ends e).1) ∩ src (Section34Label.vertexBall (ends e).2))
    (hSpQ : ∀ e, Sp e ⊆ Q (ends e).1)
    (hQlfU : LocallyFinite fun w => {y : h '' U | (y : M₂) ∈ Q w}) :
    LocallyFinite fun e => {y : h '' U | (y : M₂) ∈ Sp e} :=
  locallyFinite_subtype_of_subset_of_finite_fibers Sp Q (fun e => (ends e).1) hSpQ
    (finite_splitDisk_of_section34CutFrame hframe (fun e => (ends e).1)
      (fun e => by rw [hends e]; exact inter_subset_left)) hQlfU

def section34CutNeighborhood {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (src : Section34CutLabelOf 𝒦 𝒦' → Set M₁) : Set M₁ :=
  ⋃ w : Section34VertexIndex 𝒦 𝒦', src (.vertexBall w)

def section34FaceTorus {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (V : Section34VertexIndex 𝒦 𝒦' → Set M₂) (s : Section34SimplexIndex 𝒦 3) : Set M₂ :=
  ⋃ (a : Section34ArcIndex 𝒦 𝒦') (_ : a.1.1 = s), V a.1.2

def Section34GraphFrame (U W : Set M₁) (h : M₁ → M₂) (ψ : M₁ → ℝ) (H : Finset Ea → Set M₂)
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (src : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
    (cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea) (f₁ : M₁ → M₂) : Prop :=
  IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
    (graphSkeletonSpace 𝒦) U ∧
  section34CutNeighborhood src ⊆ W ∧
  IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src) ∧
  f₁ '' section34CutNeighborhood src ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) ∧
  (∀ x ∈ section34CutNeighborhood src, dist (f₁ x) (h x) < ψ x) ∧
  (∀ w : Section34VertexIndex 𝒦 𝒦',
    h '' simplexBody 𝒦' w.1 ⊆ interior (f₁ '' src (.vertexBall w))) ∧
  (∀ (e : Section34EdgeIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
    (f₁ '' src (.splitDisk e) ∩ h '' simplexBody 𝒦 s.1).Nonempty →
      Section34Incident e.1 s.1) ∧
  (∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
    (f₁ '' src (.vertexBall w) ∩ h '' simplexBody 𝒦 s.1).Nonempty →
      Section34Incident w.1 s.1) ∧
  (∀ s : Section34SimplexIndex 𝒦 3, h '' simplexRim 𝒦 s.1 ⊆
    interior (section34FaceTorus (fun w => f₁ '' src (.vertexBall w)) s)) ∧
  (∀ s : Section34SimplexIndex 𝒦 3, CarriesFundamentalGroupOnto (h '' simplexRim 𝒦 s.1)
    (section34FaceTorus (fun w => f₁ '' src (.vertexBall w)) s)) ∧
  (∀ w : Section34VertexIndex 𝒦 𝒦', cr w ∈ 𝒦.complex.faces) ∧
  (∀ w : Section34VertexIndex 𝒦 𝒦',
    src (.vertexBall w) ⊆ Section34CarrierSupport 𝒦 (cr w)) ∧
  (∀ σ : Finset Ea, {w | cr w = σ}.Finite) ∧
  ∀ w : Section34VertexIndex 𝒦 𝒦',
    h '' src (.vertexBall w) ∪ f₁ '' src (.vertexBall w) ⊆ H (cr w)

def section34TetraObstacle {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fbl : Section34SimplexIndex 𝒦 3 → Set M₂) (t : Section34SimplexIndex 𝒦 4) : Set M₂ :=
  (⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.1 = t), tgtV x.1.2) ∪
    ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), fbl s

def Section34Exterior {U : Set M₁} (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U) (h : M₁ → M₂)
    (H : Finset Ea → Set M₂) (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fbl : Section34SimplexIndex 𝒦 3 → Set M₂) : Prop :=
  (∀ t : Section34SimplexIndex 𝒦 4,
    section34TetraObstacle tgtV fbl t ⊆ interior (H t.1)) ∧
  (∀ w : Section34VertexIndex 𝒦 𝒦', h '' simplexBody 𝒦' w.1 ⊆ interior (tgtV w)) ∧
  ∀ (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦'),
    ¬ Section34Incident w.1 t.1 → ∀ y ∈ h '' simplexBody 𝒦' w.1, y ∈ H t.1 →
      y ∉ section34TetraObstacle tgtV fbl t ∧
        (connectedComponentIn (H t.1 \ section34TetraObstacle tgtV fbl t) y ∩
          frontier (H t.1)).Nonempty

def Section34Trace {U : Set M₁} (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) : Prop :=
  ∃ (r : Section34SimplexIndex 𝒦 3 → ℕ)
    (J : Section34SimplexIndex 𝒦 3 → ℕ → Set M₂),
    (∀ s, 0 < r s) ∧
    (∀ s, ∀ i < r s, IsPolyhedralSphere (n := 3) 1 (J s i)) ∧
    (∀ s, ∀ i < r s, ∀ j < r s, i ≠ j → Disjoint (J s i) (J s j)) ∧
    (∀ s, fblBd s ∩ frontier (⋃ w : Section34VertexIndex 𝒦 𝒦', tgtV w) =
      ⋃ i < r s, J s i) ∧
    (∀ s, fblBd s ∩ frontier (section34FaceTorus tgtV s) = ⋃ i < r s, J s i) ∧
    ∀ s, ∀ i < r s, ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
      ∃ p, J s i ∩ tgtEBd e = {p}

def Section34NormalPlus (U : Set M₁) (h : M₁ → M₂) (η : M₁ → ℝ)
    (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁) (H : Finset Ea → Set M₂)
    (cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea) (f₁ : M₁ → M₂)
    (tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂) : Prop :=
  Section34CutFrame U 𝒦 𝒦' src srcBd ∧
  Section34CarrierControl U 𝒦 h η H ∧
  Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁ ∧
  Section34Exterior 𝒦 𝒦' h H tgtV fbl ∧
  Section34Trace 𝒦 𝒦' tgtV tgtEBd fblBd ∧
  (∀ w, tgtV w = f₁ '' src (.vertexBall w)) ∧
  (∀ e, tgtE e = f₁ '' src (.splitDisk e)) ∧
  (∀ w, IsPLCellOn 3 (tgtV w) (tgtVBd w)) ∧
  (∀ e, IsPLCellOn 2 (tgtE e) (tgtEBd e)) ∧
  (∀ (e : Section34EdgeIndex 𝒦 𝒦') (w : Section34VertexIndex 𝒦 𝒦'),
    src (.splitDisk e) ⊆ src (.vertexBall w) → tgtE e ⊆ tgtVBd w) ∧
  (∀ w w', w ≠ w' → tgtV w ∩ tgtV w' ⊆ ⋃ e, tgtE e) ∧
  (∀ t : Section34SimplexIndex 𝒦 4, h '' src (.tetraBall t) ⊆ H t.1) ∧
  (∀ s, IsPLCellOn 3 (fbl s) (fblBd s)) ∧
  (∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
    ¬ Section34Incident w.1 s.1 → fbl s ∩ tgtV w = ∅) ∧
  (∀ s s', s ≠ s' → fbl s ∩ fbl s' ⊆ interior (⋃ w, tgtV w)) ∧
  (∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦') (Dj Jd : Set M₂),
    IsPLCellOn 2 Dj Jd → Dj ⊆ tgtVBd w → Jd ⊆ fblBd s → Dj ∩ fblBd s = Jd →
    (∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint Dj (tgtE e)) →
    (∀ s' : Section34SimplexIndex 𝒦 3, s' ≠ s → Disjoint (Dj \ Jd) (fbl s')) → False) ∧
  ∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (e : Section34EdgeIndex 𝒦 𝒦') (B B' Bb Dj Jd : Set M₂),
    IsPLCellOn 1 B Bb → B ⊆ fblBd s → B ⊆ tgtVBd w → Bb ⊆ tgtEBd e →
    B ∩ (⋃ e' : Section34EdgeIndex 𝒦 𝒦', tgtE e') = Bb →
    IsPLCellOn 1 B' Bb → B' ⊆ tgtEBd e → B ∩ B' = Bb →
    IsPLCellOn 2 Dj Jd → Dj ⊆ tgtVBd w ∩ frontier (⋃ w, tgtV w) → Jd = B ∪ B' →
    (∀ s' : Section34SimplexIndex 𝒦 3, Disjoint (Dj \ Jd) (fblBd s')) → False

def Section34FaceDiskFamily {U : Set M₁} (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (fblBd : Section34SimplexIndex 𝒦 3 → Set M₂)
    (tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂)
    (tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂)
    (tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂) : Prop :=
  (∀ s, IsPLCellOn 2 (tgtD s) (tgtDBd s)) ∧
  (∀ s, tgtD s ⊆ fblBd s) ∧
  (∀ s, tgtD s ∩ (⋃ w : Section34VertexIndex 𝒦 𝒦', tgtV w) = tgtDBd s) ∧
  (∀ s, tgtDBd s ⊆ frontier (⋃ w : Section34VertexIndex 𝒦 𝒦', tgtV w)) ∧
  (∀ s s', s ≠ s' → Disjoint (tgtD s) (tgtD s')) ∧
  (∀ a, IsPLCellOn 1 (tgtA a) (tgtABd a)) ∧
  (∀ a : Section34ArcIndex 𝒦 𝒦', tgtDBd a.1.1 ∩ tgtV a.1.2 = tgtA a) ∧
  (∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
    ¬ Section34Incident w.1 s.1 → tgtD s ∩ tgtV w = ∅) ∧
  (∀ p, IsPLCellOn 0 (tgtP p) ∅) ∧
  (∀ p : Section34MarkIndex 𝒦 𝒦', tgtDBd p.1.1 ∩ tgtEBd p.1.2 = tgtP p) ∧
  (∀ (s : Section34SimplexIndex 𝒦 3) (e : Section34EdgeIndex 𝒦 𝒦'),
    ¬ Section34Incident e.1 s.1 → tgtDBd s ∩ tgtEBd e = ∅) ∧
  ∀ a : Section34ArcIndex 𝒦 𝒦', tgtABd a = tgtA a ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtE e

def Section34ResidualPlus {U : Set M₁} (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (H : Finset Ea → Set M₂) (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (tgtD : Section34SimplexIndex 𝒦 3 → Set M₂)
    (tgtA : Section34ArcIndex 𝒦 𝒦' → Set M₂)
    (tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂)
    (tgtR tgtRBd : Section34SimplexIndex 𝒦 4 → Set M₂)
    (tgtX tgtXBd : Section34PatchIndex 𝒦 𝒦' → Set M₂)
    (tgtI tgtIBd : Section34EdgeArcIndex 𝒦 𝒦' → Set M₂) : Prop :=
  (∀ t, IsPLCellOn 3 (tgtR t) (tgtRBd t)) ∧
  (∀ x, IsPLCellOn 2 (tgtX x) (tgtXBd x)) ∧
  (∀ i, IsPLCellOn 1 (tgtI i) (tgtIBd i)) ∧
  (∀ x : Section34PatchIndex 𝒦 𝒦', tgtR x.1.1 ∩ tgtV x.1.2 = tgtX x) ∧
  (∀ (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦'),
    ¬ Section34Incident w.1 t.1 → tgtR t ∩ tgtV w = ∅) ∧
  (∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
    Section34Incident s.1 t.1 → tgtR t ∩ tgtD s = tgtD s) ∧
  (∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
    ¬ Section34Incident s.1 t.1 → tgtR t ∩ tgtD s = ∅) ∧
  (∀ t t', t ≠ t' → tgtR t ∩ tgtR t' ⊆ ⋃ s, tgtD s) ∧
  (∀ i : Section34EdgeArcIndex 𝒦 𝒦', tgtR i.1.1 ∩ tgtE i.1.2 = tgtI i) ∧
  (∀ (t : Section34SimplexIndex 𝒦 4) (e : Section34EdgeIndex 𝒦 𝒦'),
    ¬ Section34Incident e.1 t.1 → tgtR t ∩ tgtE e = ∅) ∧
  (∀ i : Section34EdgeArcIndex 𝒦 𝒦', tgtI i ⊆ tgtEBd i.1.2) ∧
  (∀ t : Section34SimplexIndex 𝒦 4, tgtRBd t =
    (⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s) ∪
      ⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.1 = t), tgtX x) ∧
  (∀ i : Section34EdgeArcIndex 𝒦 𝒦', tgtIBd i =
    ⋃ (p : Section34MarkIndex 𝒦 𝒦')
      (_ : p.1.2 = i.1.2 ∧ Section34Incident p.1.1.1 i.1.1.1), tgtP p) ∧
  (∀ x : Section34PatchIndex 𝒦 𝒦', tgtXBd x =
    (⋃ (a : Section34ArcIndex 𝒦 𝒦')
      (_ : a.1.2 = x.1.2 ∧ Section34Incident a.1.1.1 x.1.1.1), tgtA a) ∪
    ⋃ (i : Section34EdgeArcIndex 𝒦 𝒦')
      (_ : i.1.1 = x.1.1 ∧ x.1.2.1 ⊆ i.1.2.1), tgtI i) ∧
  (∀ (i : Section34EdgeArcIndex 𝒦 𝒦') (p : Section34MarkIndex 𝒦 𝒦'),
    p.1.2 = i.1.2 → tgtP p ⊆ tgtI i → tgtP p ⊆ tgtIBd i) ∧
  (∀ t : Section34SimplexIndex 𝒦 4, tgtR t ⊆ H t.1) ∧
  (∀ w : Section34VertexIndex 𝒦 𝒦', frontier (tgtV w) ⊆
    (⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : w.1 ⊆ e.1), tgtE e) ∪
      ⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.2 = w), tgtX x) ∧
  ∀ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e ⊆
    ⋃ (i : Section34EdgeArcIndex 𝒦 𝒦') (_ : i.1.2 = e), tgtI i

def Section34OuterTorus {U : Set M₁} (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U) (h : M₁ → M₂)
    (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3)))
    (Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ s : Section34SimplexIndex 𝒦 3, ct s ∈ (plGroupoid 3).maximalAtlas M₂ ∧
    (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 s.1), Q w) ⊆
      (ct s).source) ∧
  (∀ s : Section34SimplexIndex 𝒦 3, h '' simplexRim 𝒦 s.1 ⊆
    ⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 s.1), Q w) ∧
  (∀ s : Section34SimplexIndex 𝒦 3, IsTopologicalSolidTorus (Sd s) ∧
    IsSpine (Sd s) (ct s '' (h '' simplexRim 𝒦 s.1))) ∧
  (∀ s : Section34SimplexIndex 𝒦 3,
    ct s '' (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 s.1), Q w) ⊆
      interior (Sd s)) ∧
  ∀ (s : Section34SimplexIndex 𝒦 3) (D B : Set M₂), IsPLCellOn 2 D B →
    B = h '' simplexRim 𝒦 s.1 →
    ¬ D ⊆ ⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 s.1), Q w

def section34CellThickening {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
    (h : M₁ → M₂) (Cp : Section34VertexIndex 𝒦 𝒦' → Set M₁)
    (ε : Section34VertexIndex 𝒦 𝒦' → ℝ) (w : Section34VertexIndex 𝒦 𝒦') : Set M₂ :=
  ⋃ x ∈ Cp w, Metric.ball (h x) (ε w)

def Section34VertexPreparation (U : Set M₁) (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (h : M₁ → M₂) (src : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
    (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁)
    (Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁)
    (ε : Section34VertexIndex 𝒦 𝒦' → ℝ) : Prop :=
  (∀ w, 0 < ε w) ∧
  (∀ w, IsPLCellOn 3 (Cc w) (CcBd w)) ∧
  (∀ w, src (.vertexBall w) ⊆ Cc w ∧ Cp w ⊆ Cc w ∧ Cc w ⊆ U) ∧
  (∀ w, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, h '' Cc w ⊆ c.source) ∧
  (∀ w, IsPLCellOn 3 (Cp w) (CpBd w)) ∧
  (∀ w, simplexBody 𝒦' w.1 ⊆ interior (Cp w)) ∧
  (∀ w, h '' Cc w ⊆ interior (Q w)) ∧
  (∀ x ∈ ⋃ w, Cc w, ∃ V ∈ 𝓝 x, {w | (Cc w ∩ V).Nonempty}.Finite) ∧
  (∀ e, (ends e).1 ≠ (ends e).2 ∧
    (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea) ∧
    src (.splitDisk e) = src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2)) ∧
  (∀ e, IsPolyhedralSphere (n := 3) 1 (CpBd (ends e).1 ∩ CpBd (ends e).2) ∧
    CpBd (ends e).1 ∩ CpBd (ends e).2 ⊆ src (.splitDisk e)) ∧
  (∀ e, IsLocallyFiniteRegularNeighborhoodOf (n := 3) (Sn e)
      (CpBd (ends e).1 ∩ CpBd (ends e).2) U ∧
    IsLocallyFiniteRegularNeighborhoodOf (n := 3) (Tn e)
      (CpBd (ends e).1 ∩ CpBd (ends e).2) U) ∧
  (∀ e, Tn e ⊆ interior (Sn e) ∧ IsTopologicalSolidTorus (Sn e) ∧
    IsTopologicalSolidTorus (Tn e) ∧ Disjoint (Sn e) (graphSkeletonSpace 𝒦)) ∧
  (∀ e, ∀ w, w = (ends e).1 ∨ w = (ends e).2 → Sn e ⊆ Cc w) ∧
  (∀ e d, e ≠ d → Disjoint (Sn e) (Sn d)) ∧
  (∀ e, Aa e = CpBd (ends e).1 ∩ Tn e ∧ IsAnnulusOn (Aa e) (Ab₀ e) (Ab₁ e)) ∧
  (∀ e, Bb e ⊆ CpBd (ends e).2 ∧ IsAnnulusOn (Bb e) (Bb₀ e) (Bb₁ e)) ∧
  (∀ e, Tn e ∩ CpBd (ends e).2 ⊆ Bb e \ (Bb₀ e ∪ Bb₁ e)) ∧
  (∀ e, Bb e ⊆ interior (Sn e) ∧ Bb₀ e ∪ Bb₁ e ⊆ Sn e \ Tn e) ∧
  (∀ e, IsAnnulusOn (Bc e) (Bc₀ e) (Bc₁ e) ∧ Bc e ⊆ Bb e ∩ interior (Tn e)) ∧
  (∀ e, CpBd (ends e).1 ∩ CpBd (ends e).2 ⊆ Bc e \ (Bc₀ e ∪ Bc₁ e)) ∧
  (∀ e, Ab₀ e ⊆ interior (Cp (ends e).2) ∧ Ab₁ e ∩ Cp (ends e).2 = ∅) ∧
  (∀ e, (∃ y₀ ∈ Bb e ∩ Cp (ends e).1, ∀ z ∈ Bb e ∩ Cp (ends e).1, z ∉ Tn e →
      z ∈ connectedComponentIn (Bb e ∩ Cp (ends e).1) y₀) ∧
    ∃ y₀ ∈ Bb e \ Cp (ends e).1, ∀ z ∈ Bb e \ Cp (ends e).1, z ∉ Tn e →
      z ∈ connectedComponentIn (Bb e \ Cp (ends e).1) y₀) ∧
  (∀ e, CarriesFundamentalGroupOnto (Ab₀ e) (Tn e) ∧
    CarriesFundamentalGroupOnto (Ab₁ e) (Tn e) ∧
    CarriesFundamentalGroupOnto (Ab₀ e) (Sn e)) ∧
  (∀ w, ∀ x ∈ Cc w, Metric.ball (h x) (ε w) ⊆ interior (Q w)) ∧
  (∀ e, ∀ x ∈ Sn e, Metric.ball (h x) (ε (ends e).1 + ε (ends e).2) ⊆
    interior (Q (ends e).1) ∩ interior (Q (ends e).2)) ∧
  (∀ w, ∀ x ∈ CcBd w, ∀ y ∈ h '' simplexBody 𝒦' w.1, ε w < dist (h x) y) ∧
  (∀ w, ∀ x ∈ CpBd w, ∀ y ∈ h '' simplexBody 𝒦' w.1, ε w < dist (h x) y) ∧
  (∀ e, ∀ x ∈ Bb₀ e ∪ Bb₁ e, ∀ y ∈ Tn e,
    ε (ends e).1 + ε (ends e).2 < dist (h x) (h y)) ∧
  (∀ e, ∀ x ∈ CpBd (ends e).1 \ (Aa e \ (Ab₀ e ∪ Ab₁ e)), ∀ y ∈ CpBd (ends e).2,
    ε (ends e).1 + ε (ends e).2 < dist (h x) (h y)) ∧
  (∀ e, ∀ x ∈ CpBd (ends e).1, ∀ y ∈ CpBd (ends e).2 \ (Bb e \ (Bb₀ e ∪ Bb₁ e)),
    ε (ends e).1 + ε (ends e).2 < dist (h x) (h y)) ∧
  (∀ e, ∀ x ∈ Ab₁ e, ∀ y ∈ Cp (ends e).2,
    ε (ends e).1 + ε (ends e).2 < dist (h x) (h y)) ∧
  (∀ e, ∀ x ∈ Bb e, ∀ y ∈ Cc (ends e).1 \ interior (Sn e),
    ε (ends e).1 + ε (ends e).2 < dist (h x) (h y)) ∧
  (∀ e, ∀ x ∈ Bc₀ e ∪ Bc₁ e, ∀ y ∈ Sn e \ interior (Tn e),
    ε (ends e).1 + ε (ends e).2 < dist (h x) (h y)) ∧
  (∀ e, ∀ w, w = (ends e).1 ∨ w = (ends e).2 →
    ∀ x ∈ Sn e, ∀ y ∈ graphSkeletonSpace 𝒦, ε w < dist (h x) (h y)) ∧
  (∀ e w, ∀ x ∈ Sn e, ∀ y ∈ simplexBody 𝒦' w.1,
    ε (ends e).1 + ε w < dist (h x) (h y)) ∧
  (∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 → ∀ x ∈ Sn e, ∀ y ∈ CpBd w,
    ε (ends e).1 + ε w < dist (h x) (h y)) ∧
  (∀ w w', Disjoint (Cp w) (Cp w') → ∀ x ∈ Cp w, ∀ y ∈ Cp w',
    ε w + ε w' < dist (h x) (h y)) ∧
  (∀ e d, e ≠ d → ∀ x ∈ Sn e, ∀ y ∈ Sn d,
    ε (ends e).1 + ε (ends d).1 < dist (h x) (h y)) ∧
  (∀ w, IsCompact (Kcore w) ∧ simplexBody 𝒦' w.1 ⊆ Kcore w ∧ Kcore w ⊆ Cp w \ CpBd w) ∧
  graphSkeletonSpace 𝒦 ⊆ (⋃ w, Kcore w) ∧
  (∀ w, ∀ F : M₁ → M₂, IsPLHomeomorphInto 3 F (Cp w) →
    (∀ z ∈ Cp w, dist (h z) (F z) < ε w) → h '' Kcore w ⊆ interior (F '' Cp w)) ∧
  (∀ e w, ∀ x ∈ Sn e, ∀ y ∈ Kcore w, ε (ends e).1 + ε w < dist (h x) (h y)) ∧
  (∀ w w', w ≠ w' → ∀ x ∈ Cp w', ∀ y ∈ simplexBody 𝒦' w.1, ε w' < dist (h x) (h y)) ∧
  (∀ w w', w ≠ w' → (¬ ∃ e : Section34EdgeIndex 𝒦 𝒦',
      (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1)) →
    Disjoint (Cp w) (Cp w')) ∧
  ∀ e d, e ≠ d →
    Disjoint (section34CellThickening h Cp ε (ends e).1 ∩
        section34CellThickening h Cp ε (ends e).2)
      (section34CellThickening h Cp ε (ends d).1 ∩
        section34CellThickening h Cp ε (ends d).2)

def Section34PiercingConditions (U : Set M₁) (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (h : M₁ → M₂) (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (Cp CpBd Cc : Section34VertexIndex 𝒦 𝒦' → Set M₁)
    (Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁)
    (Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂) (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ)
    (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂)
    (G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) : Prop :=
  (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) ∧
  (∀ w, G w '' Cc w ⊆ Q w) ∧
  (∀ e, G (ends e).2 '' Sn e ⊆ Q (ends e).1 ∧ G (ends e).1 '' Sn e ⊆ Q (ends e).2) ∧
  (∀ e, Sp e = G (ends e).1 '' Sn e ∧ Tp e = G (ends e).1 '' Tn e) ∧
  LocallyFinite (fun e => {y : h '' U | (y : M₂) ∈ Sp e}) ∧
  (∀ e d, e ≠ d → Disjoint (Sp e) (Sp d)) ∧
  (∀ e, G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
    G (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
      G (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e)) ∩ interior (Tp e)) ∧
  (∀ e, G (ends e).1 '' Ab₀ e ⊆ interior (G (ends e).2 '' Cp (ends e).2) ∧
    Disjoint (G (ends e).1 '' Ab₁ e) (G (ends e).2 '' Cp (ends e).2)) ∧
  (∀ e, G (ends e).2 '' Bb e ⊆ interior (Sp e) ∧
    Disjoint (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) (Tp e)) ∧
  (∀ e, Disjoint (Sp e) (h '' graphSkeletonSpace 𝒦)) ∧
  (∀ w, IsPLHomeomorphInto 3 (G w) (Cp w)) ∧
  (∀ w e, Disjoint (G w '' simplexBody 𝒦' w.1) (Sp e)) ∧
  (∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 → Disjoint (Sp e) (G w '' CpBd w)) ∧
  (∀ w w', Disjoint (Cp w) (Cp w') → Disjoint (G w '' Cp w) (G w' '' Cp w')) ∧
  (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
    ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y₀) ∧
  (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
    ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1, z ∉ Tp e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y₀) ∧
  (∀ e, 0 < cnt e ∧
    G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e = ⋃ i < cnt e, Pg e i) ∧
  (∀ e, ∀ i < cnt e, IsPolyhedralSphere (n := 3) 1 (Pg e i) ∧
    Pg e i ⊆ G (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
      G (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e))) ∧
  (∀ e, ∀ i < cnt e, ∀ j < cnt e, i ≠ j → Disjoint (Pg e i) (Pg e j)) ∧
  (∀ e, ∀ y ∈ G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e,
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
      HasPLCrossingAt (c '' (G (ends e).1 '' Aa e ∩ c.source))
        (c '' (G (ends e).2 '' Bb e ∩ c.source)) (c y)) ∧
  (∀ e d, e ≠ d →
    Disjoint (G (ends e).1 '' Cp (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2)
      (G (ends d).1 '' Cp (ends d).1 ∩ G (ends d).2 '' Cp (ends d).2)) ∧
  ∀ w w', w ≠ w' → Disjoint (h '' simplexBody 𝒦' w.1) (G w' '' Cp w')

section Margins

variable {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {h : M₁ → M₂}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
  {Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem section34FaceTorus_subset_outerTorus (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (D : Section34VertexIndex 𝒦 𝒦' → Set M₂) (hD : ∀ w, D w ⊆ Q w)
    (s : Section34SimplexIndex 𝒦 3) :
    section34FaceTorus D s ⊆ (ct s).source ∧
      ct s '' section34FaceTorus D s ⊆ interior (Sd s) := by
  obtain ⟨hsrc, -, -, hbuf, -⟩ := htor
  have hsub : section34FaceTorus D s ⊆
      ⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 s.1), Q w := by
    simp only [section34FaceTorus]
    refine iUnion₂_subset fun a ha => ?_
    subst ha
    exact fun y hy => mem_iUnion₂.mpr ⟨a.1.2, a.2, hD _ hy⟩
  exact ⟨hsub.trans (hsrc s).2, (image_mono hsub).trans (hbuf s)⟩

omit [FiniteDimensional ℝ Ea] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] in
theorem mem_nhdsSet_iUnion_image_of_section34Core
    (hcov : graphSkeletonSpace 𝒦 ⊆ ⋃ w, Kcore w)
    (hcore : ∀ w, h '' Kcore w ⊆ interior (G w '' Cp w)) :
    (⋃ w, G w '' Cp w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) := by
  rw [mem_nhdsSet_iff_forall]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨w, hw⟩ := mem_iUnion.mp (hcov hx)
  exact mem_interior_iff_mem_nhds.mp
    (interior_mono (subset_iUnion (fun v => G v '' Cp v) w) (hcore w ⟨x, hw, rfl⟩))

omit [FiniteDimensional ℝ Ea] in
theorem section34MarkerConditions
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hGp : ∀ w, IsPLHomeomorphInto 3 (G w) (Cp w))
    (hGdist : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w) :
    (∀ w, h '' Kcore w ⊆ interior (G w '' Cp w)) ∧
      (∀ w e, Disjoint (h '' Kcore w) (G (ends e).1 '' Sn e)) ∧
      ∀ w w', w ≠ w' → Disjoint (h '' simplexBody 𝒦' w.1) (G w' '' Cp w') := by
  obtain ⟨hεpos, -, hsubs, -, -, -, -, -, -, -, -, -, hsncc, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstab, hkmar, hvmar, -⟩ := hprep
  have hCpCc : ∀ w, Cp w ⊆ Cc w := fun w => (hsubs w).2.1
  refine ⟨fun w => hstab w (G w) (hGp w) fun z hz => ?_, fun w e => ?_, fun w w' hne => ?_⟩
  · rw [dist_comm]
    exact hGdist w z (hCpCc w hz)
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨x, hx, hxy⟩
    have hxc : x ∈ Cc (ends e).1 := hsncc e _ (Or.inl rfl) hx
    have d1 : dist (h x) (G (ends e).1 x) < ε (ends e).1 := by
      rw [dist_comm]; exact hGdist (ends e).1 x hxc
    have d2 : dist (G (ends e).1 x) (h y) = 0 := by rw [hxy]; exact dist_self _
    have dt := dist_triangle (h x) (G (ends e).1 x) (h y)
    linarith [hkmar e w x hx y hy, hεpos w]
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨x, hx, hxy⟩
    have d1 : dist (h x) (G w' x) < ε w' := by
      rw [dist_comm]; exact hGdist w' x (hCpCc w' hx)
    have d2 : dist (G w' x) (h y) = 0 := by rw [hxy]; exact dist_self _
    have dt := dist_triangle (h x) (G w' x) (h y)
    linarith [hvmar w w' hne x hx y hy]

omit [FiniteDimensional ℝ Ea] in
theorem section34OverlapConditions
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hGdist : ∀ w, ∀ z ∈ Cp w, dist (h z) (G w z) < ε w) :
    ∀ e d, e ≠ d →
      Disjoint (G (ends e).1 '' Cp (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2)
        (G (ends d).1 '' Cp (ends d).1 ∩ G (ends d).2 '' Cp (ends d).2) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hover⟩ := hprep
  have himg : ∀ w, G w '' Cp w ⊆ section34CellThickening h Cp ε w := by
    rintro w _ ⟨z, hz, rfl⟩
    exact mem_biUnion hz (Metric.mem_ball'.mpr (hGdist w z hz))
  exact fun e d hne => (hover e d hne).mono (inter_subset_inter (himg _) (himg _))
    (inter_subset_inter (himg _) (himg _))

omit [FiniteDimensional ℝ Ea] in
theorem section34MarginConditions
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hGdist : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w) :
    (∀ w, G w '' Cc w ⊆ Q w) ∧
      (∀ e, G (ends e).2 '' Sn e ⊆ Q (ends e).1 ∧ G (ends e).1 '' Sn e ⊆ Q (ends e).2) ∧
      (∀ e, Disjoint (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) (G (ends e).1 '' Tn e)) ∧
      (∀ e, Disjoint (G (ends e).1 '' Sn e) (h '' graphSkeletonSpace 𝒦)) ∧
      (∀ e d, e ≠ d → Disjoint (G (ends e).1 '' Sn e) (G (ends d).1 '' Sn d)) ∧
      (∀ e, G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
        G (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
          G (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e))) ∧
      (∀ e, Disjoint (G (ends e).1 '' Ab₁ e) (G (ends e).2 '' Cp (ends e).2)) ∧
      (∀ w e, Disjoint (G w '' simplexBody 𝒦' w.1) (G (ends e).1 '' Sn e)) ∧
      (∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 →
        Disjoint (G (ends e).1 '' Sn e) (G w '' CpBd w)) ∧
      ∀ w w', Disjoint (Cp w) (Cp w') → Disjoint (G w '' Cp w) (G w' '' Cp w') := by
  obtain ⟨hεpos, -, hsubs, -, hcpcell, hbody, -, -, -, -, -, htn, hsncc, -, haa, -, -, hbbd,
    -, -, -, -, -, hball, hsnball, -, -, hbt, h29, h30, h31, -, -, hgraph, h35, h36, h37,
    htube, -⟩ := hprep
  have hcp : ∀ w, IsPLCellOn 3 (Cp w) (CpBd w) := hcpcell
  have hann : ∀ e, IsAnnulusOn (Aa e) (Ab₀ e) (Ab₁ e) := fun e => (haa e).2
  have hCpCc : ∀ w, Cp w ⊆ Cc w := fun w => (hsubs w).2.1
  have hCpBdCc : ∀ w, CpBd w ⊆ Cc w := fun w =>
    ((hcp w).boundary_subset).trans (hCpCc w)
  have hbodyCc : ∀ w, simplexBody 𝒦' w.1 ⊆ Cc w := fun w =>
    ((hbody w).trans interior_subset).trans (hCpCc w)
  have hAb₁Cc : ∀ e, Ab₁ e ⊆ Cc (ends e).1 := by
    intro e x hx
    refine hCpBdCc _ ?_
    have hAasub : Aa e ⊆ CpBd (ends e).1 := by
      rw [(haa e).1]
      exact inter_subset_left
    exact hAasub ((hann e).second_subset hx)
  have h1 : ∀ w, G w '' Cc w ⊆ Q w := by
    rintro w _ ⟨x, hx, rfl⟩
    exact interior_subset (hball w x hx (Metric.mem_ball.mpr (hGdist w x hx)))
  refine ⟨h1, fun e => ?_, fun e => ?_, fun e => ?_, fun e d hne => ?_, fun e => ?_,
    fun e => ?_, fun w e => ?_, fun e w hw1 hw2 => ?_, fun w w' hdisj => ?_⟩
  · have hmem : ∀ w, (w = (ends e).1 ∨ w = (ends e).2) → ∀ x ∈ Sn e,
        G w x ∈ Metric.ball (h x) (ε (ends e).1 + ε (ends e).2) := by
      intro w hw x hx
      have hlt := hGdist w x (hsncc e w hw hx)
      have hp1 := hεpos (ends e).1
      have hp2 := hεpos (ends e).2
      refine Metric.mem_ball.mpr ?_
      rcases hw with rfl | rfl <;> linarith
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact interior_subset (hsnball e x hx (hmem _ (Or.inr rfl) x hx)).1
    · rintro _ ⟨x, hx, rfl⟩
      exact interior_subset (hsnball e x hx (hmem _ (Or.inl rfl) x hx)).2
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hxc : x ∈ Cc (ends e).2 := hsncc e _ (Or.inr rfl) ((hbbd e).2 hx).1
    have hyc : y ∈ Cc (ends e).1 := hsncc e _ (Or.inl rfl) (interior_subset ((htn e).1 hy))
    have d1 : dist (h x) (G (ends e).2 x) < ε (ends e).2 := by
      rw [dist_comm]; exact hGdist (ends e).2 x hxc
    have d2 : dist (G (ends e).2 x) (h y) < ε (ends e).1 := by
      rw [← hxy]; exact hGdist (ends e).1 y hyc
    have dt := dist_triangle (h x) (G (ends e).2 x) (h y)
    linarith [hbt e x hx y hy]
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hxc : x ∈ Cc (ends e).1 := hsncc e _ (Or.inl rfl) hx
    have d1 : dist (h x) (h y) < ε (ends e).1 := by
      rw [hxy, dist_comm]; exact hGdist (ends e).1 x hxc
    linarith [hgraph e (ends e).1 (Or.inl rfl) x hx y hy]
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hxc : x ∈ Cc (ends e).1 := hsncc e _ (Or.inl rfl) hx
    have hyc : y ∈ Cc (ends d).1 := hsncc d _ (Or.inl rfl) hy
    have d1 : dist (h x) (G (ends e).1 x) < ε (ends e).1 := by
      rw [dist_comm]; exact hGdist (ends e).1 x hxc
    have d2 : dist (G (ends e).1 x) (h y) < ε (ends d).1 := by
      rw [← hxy]; exact hGdist (ends d).1 y hyc
    have dt := dist_triangle (h x) (G (ends e).1 x) (h y)
    linarith [htube e d hne x hx y hy]
  · rintro z ⟨⟨x, hx, rfl⟩, y, hy, hxy⟩
    have hxc : x ∈ Cc (ends e).1 := hCpBdCc _ hx
    have hyc : y ∈ Cc (ends e).2 := hCpBdCc _ hy
    have d1 : dist (h x) (G (ends e).1 x) < ε (ends e).1 := by
      rw [dist_comm]; exact hGdist (ends e).1 x hxc
    have d2 : dist (G (ends e).1 x) (h y) < ε (ends e).2 := by
      rw [← hxy]; exact hGdist (ends e).2 y hyc
    have dt := dist_triangle (h x) (G (ends e).1 x) (h y)
    have hd : dist (h x) (h y) < ε (ends e).1 + ε (ends e).2 := by linarith
    have hxA : x ∈ Aa e \ (Ab₀ e ∪ Ab₁ e) := by
      by_contra hcon
      linarith [h29 e x ⟨hx, hcon⟩ y hy]
    have hyB : y ∈ Bb e \ (Bb₀ e ∪ Bb₁ e) := by
      by_contra hcon
      linarith [h30 e x hx y ⟨hy, hcon⟩]
    exact ⟨⟨x, hxA, rfl⟩, y, hyB, hxy⟩
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hxc : x ∈ Cc (ends e).1 := hAb₁Cc e hx
    have hyc : y ∈ Cc (ends e).2 := hCpCc _ hy
    have d1 : dist (h x) (G (ends e).1 x) < ε (ends e).1 := by
      rw [dist_comm]; exact hGdist (ends e).1 x hxc
    have d2 : dist (G (ends e).1 x) (h y) < ε (ends e).2 := by
      rw [← hxy]; exact hGdist (ends e).2 y hyc
    have dt := dist_triangle (h x) (G (ends e).1 x) (h y)
    linarith [h31 e x hx y hy]
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨x, hx, hxy⟩
    have hyc : y ∈ Cc w := hbodyCc w hy
    have hxc : x ∈ Cc (ends e).1 := hsncc e _ (Or.inl rfl) hx
    have d1 : dist (h x) (G (ends e).1 x) < ε (ends e).1 := by
      rw [dist_comm]; exact hGdist (ends e).1 x hxc
    have d2 : dist (G (ends e).1 x) (h y) < ε w := by
      rw [hxy]; exact hGdist w y hyc
    have dt := dist_triangle (h x) (G (ends e).1 x) (h y)
    linarith [h35 e w x hx y hy]
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hxc : x ∈ Cc (ends e).1 := hsncc e _ (Or.inl rfl) hx
    have hyc : y ∈ Cc w := hCpBdCc w hy
    have d1 : dist (h x) (G (ends e).1 x) < ε (ends e).1 := by
      rw [dist_comm]; exact hGdist (ends e).1 x hxc
    have d2 : dist (G (ends e).1 x) (h y) < ε w := by
      rw [← hxy]; exact hGdist w y hyc
    have dt := dist_triangle (h x) (G (ends e).1 x) (h y)
    linarith [h36 e w hw1 hw2 x hx y hy]
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hxc : x ∈ Cc w := hCpCc w hx
    have hyc : y ∈ Cc w' := hCpCc w' hy
    have d1 : dist (h x) (G w x) < ε w := by
      rw [dist_comm]; exact hGdist w x hxc
    have d2 : dist (G w x) (h y) < ε w' := by
      rw [← hxy]; exact hGdist w' y hyc
    have dt := dist_triangle (h x) (G w x) (h y)
    linarith [h37 w w' hdisj x hx y hy]

end Margins

end Frames

end DifferentialGeometry.Topology.PiecewiseLinear
