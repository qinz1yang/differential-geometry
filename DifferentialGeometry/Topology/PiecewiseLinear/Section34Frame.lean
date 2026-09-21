/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartLocalApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPastingManifold
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Endpoint
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# The Section 34 cut frame

The labelled vocabulary shared by the two halves of Section 34 of Moise: the eight kinds of cell
of a cut diagram, the typed incidence index sets, the cut, graph, carrier, exterior and trace
frames, and the elementary exporters that depend on no unproved input.

`IsPLCellOn d S B` says that `S` is a piecewise linear `d`-cell with *intrinsic* boundary `B`,
that is `S = u '' P` and `B = u '' (r '' stdSimplexBoundary d)`; ambient frontiers occur only in
`Section34Trace` and `Section34Exterior`, where the object traced on, the graph neighbourhood
`N'' = ⋃ V_v` and a carrier `H t`, is not a cell and has no intrinsic boundary.

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
whose bodies lie in the one skeleton `graphSkeletonSpace 𝒦`, because only a subdivision can
carry a regular neighbourhood inside a prescribed `W` and respect a free tolerance; face disks
and residual balls are indexed by the triangles and the tetrahedra of `𝒦` itself, because their
rims must lie in the one skeleton of `𝒦`.  Mixed incidence is therefore
`Section34Incident s t`, the vertices of the `𝒦'`-simplex `s` lying in the closed `𝒦`-simplex
`t`, and a vertex of `𝒦'` interior to an edge of `𝒦` is incident to exactly the two splitting
disks of the two `𝒦'`-edges it bounds, by the last two clauses of `Section34CutFrame`.

The face relation is the nesting ideal `section34Face src l = {m | src m ⊆ src l}` of the source
cells; the four incidences are exact intersections, and a non-incident pair meets in the empty
set, so a face disk can never sit inside a dual ball.

`Section34NormalPlus` is the configuration after step P5: the cut frame, the carrier control of
P0, the graph frame of P1 with `V_v = f₁ '' C_v`, the exterior clause `O_t ⊆ interior (H t)`,
the Lemma 11 trace certificate and the remaining normal-family clauses, Lemma 5(2), Lemma 5(5)
and the impossibility of the two operations.  `Section34FaceDiskFamily` and
`Section34ResidualPlus` are the outputs of steps P6 and P7, with all boundaries intrinsic.

Open question for the external reviewer: the digest's exact flags are stated for one complex,
`Pa ≃ {(t,v) : v ∈ t}`; with a subdivided one skeleton the pairs are mixed, `t` a tetrahedron of
`𝒦` and `v` a vertex of `𝒦'`, and the reading used here is `Section34Incident v t`.  Whether the
reviewer intends the same reading, and whether `Section34Trace` should ask for transversality
beyond a single intersection point, is not settled.
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

end Triangulation

section Frames

variable {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

def section34LabelSimplex {U : Set M₁}
    {𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U}
    (cr : Section34VertexIndex 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin 3))) :
    Section34CutLabelOf 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin 3))
  | .vertexBall w => cr w
  | .tetraBall t => t.1
  | .splitDisk e => e.1
  | .faceDisk s => s.1
  | .patch x => x.1.1.1
  | .faceArc a => a.1.1.1
  | .edgeArc i => i.1.1.1
  | .markedPoint p => p.1.1.1

def Section34CarrierControl (U : Set M₁)
    (𝒦 : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U) (h : M₁ → M₂) (η : M₁ → ℝ)
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂) : Prop :=
  (∀ t ∈ 𝒦.complex.faces, h '' Section34CarrierSupport 𝒦 t ⊆ interior (H t)) ∧
  (∀ t ∈ 𝒦.complex.faces, H t ⊆ h '' U) ∧
  (∀ y ∈ h '' U, ∃ V ∈ 𝓝[h '' U] y,
    {t | t ∈ 𝒦.complex.faces ∧ (H t ∩ V).Nonempty}.Finite) ∧
  ∀ t ∈ 𝒦.complex.faces, ∀ x ∈ Section34CarrierSupport 𝒦 t, ∀ y ∈ H t, ∀ z ∈ H t,
    dist y z < η x

def Section34CutFrame (U : Set M₁)
    (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
    (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁) : Prop :=
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
  ∀ e : Section34EdgeIndex 𝒦 𝒦', ∃ w w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' ∧
    e.1 = w.1 ∪ w'.1 ∧ src (.splitDisk e) = src (.vertexBall w) ∩ src (.vertexBall w')

def section34CutNeighborhood {U : Set M₁}
    {𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U}
    (src : Section34CutLabelOf 𝒦 𝒦' → Set M₁) : Set M₁ :=
  ⋃ w : Section34VertexIndex 𝒦 𝒦', src (.vertexBall w)

def section34FaceTorus {U : Set M₁}
    {𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U}
    (V : Section34VertexIndex 𝒦 𝒦' → Set M₂) (s : Section34SimplexIndex 𝒦 3) : Set M₂ :=
  ⋃ (a : Section34ArcIndex 𝒦 𝒦') (_ : a.1.1 = s), V a.1.2

def Section34GraphFrame (U W : Set M₁) (h : M₁ → M₂) (ψ : M₁ → ℝ)
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂)
    (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
    (src : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
    (cr : Section34VertexIndex 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin 3)))
    (f₁ : M₁ → M₂) : Prop :=
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
  (∀ σ : Finset (EuclideanSpace ℝ (Fin 3)), {w | cr w = σ}.Finite) ∧
  ∀ w : Section34VertexIndex 𝒦 𝒦',
    h '' src (.vertexBall w) ∪ f₁ '' src (.vertexBall w) ⊆ H (cr w)

def section34TetraObstacle {U : Set M₁}
    {𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U}
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fbl : Section34SimplexIndex 𝒦 3 → Set M₂) (t : Section34SimplexIndex 𝒦 4) : Set M₂ :=
  (⋃ (x : Section34PatchIndex 𝒦 𝒦') (_ : x.1.1 = t), tgtV x.1.2) ∪
    ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), fbl s

def Section34Exterior {U : Set M₁}
    (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U) (h : M₁ → M₂)
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂)
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
    (fbl : Section34SimplexIndex 𝒦 3 → Set M₂) : Prop :=
  (∀ t : Section34SimplexIndex 𝒦 4,
    section34TetraObstacle tgtV fbl t ⊆ interior (H t.1)) ∧
  (∀ w : Section34VertexIndex 𝒦 𝒦', h '' simplexBody 𝒦' w.1 ⊆ interior (tgtV w)) ∧
  ∀ (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦'),
    ¬ Section34Incident w.1 t.1 → ∀ y ∈ h '' simplexBody 𝒦' w.1, y ∈ H t.1 →
      y ∉ section34TetraObstacle tgtV fbl t ∧
        (connectedComponentIn (H t.1 \ section34TetraObstacle tgtV fbl t) y ∩
          frontier (H t.1)).Nonempty

def Section34Trace {U : Set M₁}
    (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
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
    (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
    (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂)
    (cr : Section34VertexIndex 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin 3))) (f₁ : M₁ → M₂)
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

def Section34FaceDiskFamily {U : Set M₁}
    (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
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

def Section34ResidualPlus {U : Set M₁}
    (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin 3)) 3 M₁ U)
    (H : Finset (EuclideanSpace ℝ (Fin 3)) → Set M₂)
    (tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂)
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

end Frames

end DifferentialGeometry.Topology.PiecewiseLinear
