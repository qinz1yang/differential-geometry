/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartLocalApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPastingManifold
import DifferentialGeometry.Topology.PiecewiseLinear.Moise308Nested
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Endpoint
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Logic.Relation

/-!
# The Section 34 cut frame

The labelled vocabulary shared by the two halves of Section 34 of Moise: the eight kinds of cell
of a cut diagram, the typed incidence index sets, the cut, graph, carrier, exterior and trace
frames, the face order of the source cut, the preparation and piercing packages of pages
248--250, and the elementary exporters that depend on no unproved input.

The *realisation ambient* is a parameter `Ea`, never the chart model.  A triangulation
`LocallyFinitePLPieceIn Ea 3 M₁ U` realises **all** of `U` inside `Ea` by its `bijOn` field, so
fixing `Ea = EuclideanSpace ℝ (Fin 3)` would force `U` to embed in `ℝ³` and exclude `U = S³`.
Only `ChartedSpace`, `plGroupoid`, `IsPLCellOn`, `IsPolyhedralSphere` carry the manifold
dimension three.

`IsPLCellOn d S B` says that `S` is a piecewise linear `d`-cell with *intrinsic* boundary `B`,
that is `S = u '' P` and `B = u '' (r '' stdSimplexBoundary d)`.  Ambient frontiers occur in
`Section34Trace`, in `Section34Exterior`, and in the carrier clause
`IsPLCellOn 3 (H t) (frontier (H t))` of `Section34CarrierControl`: a carrier is used to name an
exterior, so it must be a closed piecewise linear ball and not a set with a hole, for which the
component test of `Section34Exterior` is false.

| dim | source | target | label |
| --- | --- | --- | --- |
| 3 | `C_v` | `V_v` | `vertexBall` |
| 3 | `Q_t` | `R_t` | `tetraBall` |
| 2 | `D_e` | `E_e` | `splitDisk` |
| 2 | `d_σ` | `Δ_σ` | `faceDisk` |
| 2 | `X_{tv}` | `X''_{tv}` | `patch` |
| 1 | `a_{vσ}` | `a''_{vσ}` | `faceArc` |
| 1 | `I_{te}` | `I''_{te}` | `edgeArc` |
| 0 | `p_{σe}` | `p''_{σe}` | `markedPoint` |

Incidence is not a free parameter: the index types are the incident pairs themselves.  Dual
balls and splitting disks are indexed by the vertices and the edges of the subdivision `𝒦'`
whose bodies lie in the one skeleton `graphSkeletonSpace 𝒦`; face disks and residual balls are
indexed by the triangles and the tetrahedra of `𝒦` itself, because their rims must lie in the
one skeleton of `𝒦`.  `Section34CutFrame` now carries `IsCombinatorialManifold 3 𝒦.complex`,
`IsSubdivision 𝒦'.complex 𝒦.complex` and `𝒦'.map = 𝒦.map`, without which the cut has no
combinatorial relation to `𝒦` at all and no face of `𝒦` need meet the graph in more than two
edges.

Two face relations occur.  `section34Face src l = {m | src m ⊆ src l}` is the nesting ideal used
by the terminal assembly; `Section34CutLe` is the reflexive transitive closure of the explicit
codimension-one incidences `Section34CutStep` read off the boundary formulas
`∂C_v = ⋃_{e ∋ v} D_e ∪ ⋃_{t ∋ v} X_{tv}`, `∂Q_t = ⋃_{σ < t} d_σ ∪ ⋃_{v ∈ t} X_{tv}`,
`∂D_e = ⋃_{t > e} I_{te}`, `∂d_σ = ⋃_{v ∈ σ} a_{vσ}`, `∂X_{tv}`, `∂I_{te}`,
`∂a_{vσ} = ⋃ p_{σe}`.  That the two agree on the source cut is an obligation on the producer of
the cut, not a consequence of the cut frame: nothing in the cut frame forbids a face disk from
lying inside a dual ball.

`Section34NormalPlus` is the configuration after step P5.  `Section34VertexPreparation` and
`Section34PiercingConditions` are the two packages of Moise 35.1: the enlarged cells `C''_v`
with their tolerances `ε_v` fixed *before* any map, and conditions (2)--(8) of pages 249--250
with the annuli `A_e`, `B_e`, the regular neighbourhoods `S_e`, `T_e` of the piercing circles
and the two boundary circles of each annulus.

`carriesFundamentalGroupOnto_of_nestedSolidTorus` is proved, not assumed: it transports the
unconditional `moise308Nested` from `ℝ³` to a subset of a metrised piecewise linear
`3`-manifold along a homeomorphism of pairs, which is why a nested-torus certificate and not a
mere neighbourhood clause is what a producer has to output.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

section Cell

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

def IsPLCellOn (d : ℕ) (S B : Set M) : Prop :=
  ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin (d + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
    (u : EuclideanSpace ℝ (Fin 3) → M),
    IsPLHomeomorphOn r (stdSimplex ℝ (Fin (d + 1))) P ∧ IsPLHomeomorphInto 3 u P ∧
      S = u '' P ∧ B = u '' (r '' stdSimplexBoundary d)

theorem IsPLCellOn.isCompact {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B) : IsCompact S := by
  obtain ⟨P, r, u, hr, hu, hcell, -⟩ := hS
  rw [hcell]
  exact ((IsPLBall.isPolyhedron ⟨r, hr⟩).isCompact).image_of_continuousOn hu.continuousOn

theorem IsPLCellOn.nonempty {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B) : S.Nonempty := by
  obtain ⟨P, r, u, hr, -, hcell, -⟩ := hS
  rw [hcell]
  exact (IsPLBall.nonempty ⟨r, hr⟩).image u

end Cell

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
  ∀ t ∈ 𝒦.complex.faces, IsPLCellOn 3 (H t) (frontier (H t))

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
  ∀ (t : Section34SimplexIndex 𝒦 4) (s : Section34SimplexIndex 𝒦 3),
    Section34Incident s.1 t.1 → src (.faceDisk s) ⊆ src (.tetraBall t)

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
    (e : Section34EdgeIndex 𝒦 𝒦') (B Bb Dj Jd : Set M₂),
    IsPLCellOn 1 B Bb → B ⊆ fblBd s → B ⊆ tgtVBd w → Bb ⊆ tgtEBd e →
    B ∩ (⋃ e' : Section34EdgeIndex 𝒦 𝒦', tgtE e') = Bb → IsPLCellOn 2 Dj Jd →
    Dj ⊆ tgtVBd w → Jd ⊆ B ∪ tgtEBd e →
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
  ∀ t : Section34SimplexIndex 𝒦 4, tgtR t ⊆ H t.1

def Section34VertexPreparation (U : Set M₁) (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (h : M₁ → M₂) (src : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
    (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (Cc CcBd : Section34VertexIndex 𝒦 𝒦' → Set M₁)
    (ε : Section34VertexIndex 𝒦 𝒦' → ℝ) : Prop :=
  (∀ w, IsPLCellOn 3 (Cc w) (CcBd w)) ∧
  (∀ w, src (.vertexBall w) ⊆ interior (Cc w)) ∧
  (∀ w, Cc w ⊆ U) ∧
  (∀ w, h '' Cc w ⊆ interior (Q w)) ∧
  (∀ w, 0 < ε w) ∧
  (∀ w, ∀ x ∈ Cc w, Metric.ball (h x) (ε w) ⊆ interior (Q w)) ∧
  (∀ w, ∀ x ∈ CcBd w, ∀ y ∈ h '' simplexBody 𝒦' w.1, ε w < dist (h x) y) ∧
  ∀ x ∈ ⋃ w, Cc w, ∃ V ∈ 𝓝 x, {w | (Cc w ∩ V).Nonempty}.Finite

def Section34PiercingConditions (U : Set M₁) (𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U)
    (h : M₁ → M₂) (src : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
    (Q : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (Cc CcBd : Section34VertexIndex 𝒦 𝒦' → Set M₁)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (Sn Tn Aa Bb Ab₀ Ab₁ Bb₀ Bb₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁)
    (G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) : Prop :=
  (∀ e, (ends e).1 ≠ (ends e).2 ∧
    (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea)) ∧
  (∀ w, src (.vertexBall w) ⊆ Cc w) ∧
  (∀ e, Tn e ⊆ interior (Sn e) ∧ Sn e ⊆ U ∧ Disjoint (Sn e) (graphSkeletonSpace 𝒦)) ∧
  (∀ e, Aa e = CcBd (ends e).1 ∩ Tn e) ∧
  (∀ e, Bb e ⊆ CcBd (ends e).2 ∧ Tn e ∩ CcBd (ends e).2 ⊆ Bb e \ (Bb₀ e ∪ Bb₁ e)) ∧
  (∀ e, Bb e ⊆ interior (Sn e) ∧ Bb₀ e ∪ Bb₁ e ⊆ Sn e \ Tn e) ∧
  (∀ e, IsPolyhedralSphere (n := 3) 1 (Ab₀ e) ∧ IsPolyhedralSphere (n := 3) 1 (Ab₁ e) ∧
    IsPolyhedralSphere (n := 3) 1 (Bb₀ e) ∧ IsPolyhedralSphere (n := 3) 1 (Bb₁ e)) ∧
  (∀ e, Disjoint (Ab₀ e) (Ab₁ e) ∧ Disjoint (Bb₀ e) (Bb₁ e) ∧
    Ab₀ e ∪ Ab₁ e ⊆ Aa e ∧ Bb₀ e ∪ Bb₁ e ⊆ Bb e) ∧
  (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) ∧
  (∀ w, G w '' Cc w ⊆ Q w) ∧
  (∀ e, G (ends e).2 '' Sn e ⊆ Q (ends e).1 ∧ G (ends e).1 '' Sn e ⊆ Q (ends e).2) ∧
  (∀ e, G (ends e).1 '' CcBd (ends e).1 ∩ G (ends e).2 '' CcBd (ends e).2 ⊆
    G (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
      G (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e)) ∩ interior (G (ends e).1 '' Tn e)) ∧
  (∀ e, G (ends e).1 '' Ab₀ e ⊆ interior (G (ends e).2 '' Cc (ends e).2) ∧
    Disjoint (G (ends e).1 '' Ab₁ e) (G (ends e).2 '' Cc (ends e).2)) ∧
  (∀ e, G (ends e).2 '' Bb e ⊆ interior (G (ends e).1 '' Sn e) ∧
    Disjoint (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)) (G (ends e).1 '' Tn e)) ∧
  ((⋃ w, G w '' Cc w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) ∧
  (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cc (ends e).1,
    ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cc (ends e).1, z ∉ G (ends e).1 '' Tn e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cc (ends e).1) y₀) ∧
  (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cc (ends e).1,
    ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cc (ends e).1, z ∉ G (ends e).1 '' Tn e →
      z ∈ connectedComponentIn (G (ends e).2 '' Bb e \ G (ends e).1 '' Cc (ends e).1) y₀) ∧
  ∀ e, ∃ (m : ℕ) (P : ℕ → Set M₂),
    (G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e = ⋃ i < m, P i) ∧
    (∀ i < m, IsPolyhedralSphere (n := 3) 1 (P i)) ∧
    (∀ i < m, ∀ j < m, i ≠ j → Disjoint (P i) (P j)) ∧
    ∀ i < m, P i ⊆ G (ends e).1 '' (Aa e \ (Ab₀ e ∪ Ab₁ e)) ∩
      G (ends e).2 '' (Bb e \ (Bb₀ e ∪ Bb₁ e))

end Frames

end DifferentialGeometry.Topology.PiecewiseLinear
