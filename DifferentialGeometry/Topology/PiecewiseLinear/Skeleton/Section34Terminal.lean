/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Endpoint

/-!
# Sorry-first skeleton of the terminal half of Section 34

The assembly `section34CellDiagram` below proves the endpoint `Section34CellDiagram` for real
from the four leaves of this file; every `sorry` is a leaf and none sits inside an assembly.
The chain is: a normal family after step P5 (`exists_section34NormalFamily`), the exterior face
disks of step P6 (`exists_section34FaceDisks`), the residual tetrahedron balls of step P7
(`exists_section34ResidualBalls`), the target recognition of step P8
(`section34TargetRecognition`), then the three exporters, which are proved here.

Labels.  `Section34Label` is the sum of the eight kinds, `section34Dim` their dimension.

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

Incidence is not a separate combinatorial datum: the face relation is the nesting ideal
`section34Face src l = {m | src m ⊆ src l}` of the source cells, which is reflexive by
construction, and the boundary and intersection clauses are stated against it exactly as the
endpoint asks.  The four index types `Pa`, `Ar`, `Eg`, `Mk` are the incidence sets themselves,
with projections to the vertex, edge, face and tetrahedron types, so no cell is empty.
`IsPLCellOn d S B` says that `S` is a piecewise linear `d`-cell in a manifold with *intrinsic*
boundary `B`, that is `S = u '' P` and `B = u '' (r '' stdSimplexBoundary d)`; ambient frontiers
never occur, local finiteness is asked only in the subspaces `U` and `h '' U`, no family is
indexed by the stages of a tower, and every carrier is attached to a top cell.

The leaves, with content, owner and review state.

`exists_section34NormalFamily` (P0–P5, owner the lead's workers, unreviewed): the composite
leaf, and the endpoint of the next skeleton.  It produces the eight index types, the locally
finite source cut diagram as one presented family `src` with intrinsic boundaries `srcBd`,
its boundary decomposition, its exact pairwise intersections, the strict dimension drop along
nesting, local finiteness in `U`, the cover `⋃ src = U`, the four incidence inclusions, a top
cell above every label, the target neighbourhood pieces `V_v`, `E_e` fixed by P1, the carriers
of the top cells with `h '' src ⊆ car`, `V_v ⊆ car`, `car ⊆ h '' U`, the pairwise distance
bound (C0c) and local finiteness of the carriers in the subspace `h '' U`, and the normal
family of face balls `C_σ` with Lemma 5(2), Lemma 5(5) and the impossibility of Operation 1
and of Operation 2.  Deliberately absent, and to be added by the next skeleton before this
leaf is proved: the general position clauses 5(3) and 5(4), the homological generator clause
5(6) and the exterior marker clause 5(7).  Those four are what make the exterior choice in P6
forced, so `exists_section34FaceDisks` is the leaf of this file most likely to be false as it
now stands.

`exists_section34FaceDisks` (P6, owner the lead's workers, unreviewed): the exterior face disks
`Δ_σ ⊆ ∂C_σ`, each a piecewise linear 2-cell meeting the neighbourhood `⋃ V_v` exactly in its
own boundary, pairwise disjoint, meeting `V_v` in the arc `a''_{vσ}` for an incident pair and
not at all otherwise, meeting the splitting circle `∂E_e` in the single point `p''_{σe}` for an
incident pair and not at all otherwise, with the ends of each arc cut out by the splitting
disks.

`exists_section34ResidualBalls` (P7, owner the lead's workers, unreviewed): the residual
tetrahedron balls `R_t`, the patches `X''_{tv} = R_t ∩ V_v`, empty for a non incident vertex,
the exterior face disks recovered whole or not at all, distinct `R_t` meeting only in face
disks, the arcs `I''_{te} = R_t ∩ E_e` inside the splitting circle, the no other marked point
clause of page 245, and the carrier containment `R_t ⊆ H_t` that completes (C1).

`section34TargetRecognition` (P8, owner the lead's workers, unreviewed): the whole labelled
target family is a family of piecewise linear cells of the same dimensions, with intrinsic
boundary the union of its proper faces and with exact pairwise intersections, for the face
relation read off the source.

Proved here, not leaves: `IsPLCellOn.isCompact` and `IsPLCellOn.nonempty`;
`finite_face_of_locallyFinite`, the finiteness of a face set from local finiteness in `U` and
compactness of a cell; `carrier_subset_and_dist_lt_of_parent`, the parent carrier exporter,
which gives `hcarrier` and `hsmall` for every label from the top cell statements;
`exists_nhds_finite_of_subset_carrier`, the target local finiteness exporter, whose proof uses
`car l ⊆ h '' U` exactly where the reviewer's counterexample bites; and the packaging of the
eight kinds into the existential of `Section34CellDiagram`, including the parametrisations,
the charts and the carrier `fun l => car (par l)`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

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

inductive Section34Label (Vx Tt Ed Fc Pa Ar Eg Mk : Type u) : Type u
  | vertexBall (v : Vx)
  | tetraBall (t : Tt)
  | splitDisk (e : Ed)
  | faceDisk (s : Fc)
  | patch (x : Pa)
  | faceArc (a : Ar)
  | edgeArc (i : Eg)
  | markedPoint (p : Mk)

def section34Dim {Vx Tt Ed Fc Pa Ar Eg Mk : Type u} :
    Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → ℕ
  | .vertexBall _ => 3
  | .tetraBall _ => 3
  | .splitDisk _ => 2
  | .faceDisk _ => 2
  | .patch _ => 2
  | .faceArc _ => 1
  | .edgeArc _ => 1
  | .markedPoint _ => 0

def section34Cell {M : Type*} {Vx Tt Ed Fc Pa Ar Eg Mk : Type u}
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

theorem section34Dim_eq_three {Vx Tt Ed Fc Pa Ar Eg Mk : Type u}
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

section Exporters

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

theorem exists_nhds_finite_of_subset_carrier {Λ : Type*} {N : Type*} [TopologicalSpace N]
    (Y : Set N) (tc car : Λ → Set N) (htc : ∀ l, tc l ⊆ car l) (hY : ∀ l, car l ⊆ Y)
    (hLF : ∀ y ∈ Y, ∃ W ∈ 𝓝[Y] y, {l | (car l ∩ W).Nonempty}.Finite) :
    ∀ y ∈ ⋃ l, tc l, ∃ W ∈ 𝓝 y, {l | (tc l ∩ W).Nonempty}.Finite := by
  intro y hy
  obtain ⟨l₀, hl₀⟩ := mem_iUnion.mp hy
  obtain ⟨W, hW, hfin⟩ := hLF y (hY l₀ (htc l₀ hl₀))
  obtain ⟨V, hVopen, hyV, hVW⟩ := mem_nhdsWithin.mp hW
  refine ⟨V, hVopen.mem_nhds hyV, hfin.subset ?_⟩
  rintro l ⟨x, hx, hxV⟩
  exact ⟨x, htc l hx, hVW ⟨hxV, hY l (htc l hx)⟩⟩

end Exporters

section Diagram

variable {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {Vx Tt Ed Fc Pa Ar Eg Mk : Type u}

def Section34NormalFamily (U : Set M₁) (h : M₁ → M₂) (η : M₁ → ℝ)
    (arV : Ar → Vx) (arF : Ar → Fc) (mkE : Mk → Ed) (mkF : Mk → Fc)
    (paT : Pa → Tt) (paV : Pa → Vx) (egT : Eg → Tt) (egE : Eg → Ed)
    (src srcBd : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M₁)
    (car : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M₂)
    (tgtV tgtVBd : Vx → Set M₂) (tgtE tgtEBd : Ed → Set M₂)
    (fbl fblBd : Fc → Set M₂) : Prop :=
  (∀ l, IsPLCellOn (section34Dim l) (src l) (srcBd l)) ∧
  (∀ l, srcBd l = ⋃ m ∈ section34Face src l \ {l}, src m) ∧
  (∀ l m, src l ∩ src m = ⋃ k ∈ section34Face src l ∩ section34Face src m, src k) ∧
  (∀ l m, src m ⊆ src l → m = l ∨ section34Dim m < section34Dim l) ∧
  (∀ x ∈ U, ∃ W ∈ 𝓝 x, {l | (src l ∩ W).Nonempty}.Finite) ∧
  (⋃ l, src l) = U ∧
  (∀ a : Ar, src (.faceArc a) ⊆ src (.vertexBall (arV a)) ∩ src (.faceDisk (arF a))) ∧
  (∀ p : Mk, src (.markedPoint p) ⊆ src (.splitDisk (mkE p)) ∩ src (.faceDisk (mkF p))) ∧
  (∀ x : Pa, src (.patch x) ⊆ src (.tetraBall (paT x)) ∩ src (.vertexBall (paV x))) ∧
  (∀ i : Eg, src (.edgeArc i) ⊆ src (.tetraBall (egT i)) ∩ src (.splitDisk (egE i))) ∧
  (∀ l, ∃ m, section34Dim m = 3 ∧ src l ⊆ src m) ∧
  (∀ v : Vx, IsPLCellOn 3 (tgtV v) (tgtVBd v)) ∧
  (∀ e : Ed, IsPLCellOn 2 (tgtE e) (tgtEBd e)) ∧
  (∀ (e : Ed) (v : Vx), src (.splitDisk e) ⊆ src (.vertexBall v) → tgtE e ⊆ tgtVBd v) ∧
  (∀ v w : Vx, v ≠ w → tgtV v ∩ tgtV w ⊆ ⋃ e, tgtE e) ∧
  (∀ l, section34Dim l = 3 → h '' src l ⊆ car l) ∧
  (∀ v : Vx, tgtV v ⊆ car (.vertexBall v)) ∧
  (∀ l, section34Dim l = 3 → car l ⊆ h '' U) ∧
  (∀ l, section34Dim l = 3 → ∀ x ∈ src l, ∀ y ∈ car l, ∀ z ∈ car l, dist y z < η x) ∧
  (∀ y ∈ h '' U, ∃ W ∈ 𝓝[h '' U] y,
    {l | section34Dim l = 3 ∧ (car l ∩ W).Nonempty}.Finite) ∧
  (∀ s : Fc, IsPLCellOn 3 (fbl s) (fblBd s)) ∧
  (∀ (s : Fc) (v : Vx), (∀ a : Ar, arF a = s → arV a ≠ v) → fbl s ∩ tgtV v = ∅) ∧
  (∀ s t : Fc, s ≠ t → fbl s ∩ fbl t ⊆ interior (⋃ v, tgtV v)) ∧
  (∀ (s : Fc) (v : Vx) (J Dj : Set M₂), IsPLCellOn 2 Dj J → Dj ⊆ tgtVBd v →
    J ⊆ fblBd s → Dj ∩ fblBd s = J → (∀ e : Ed, Disjoint Dj (tgtE e)) →
    (∀ t : Fc, t ≠ s → Disjoint (Dj \ J) (fbl t)) → False) ∧
  ∀ (s : Fc) (v : Vx) (e : Ed) (B Bb Dj Jd : Set M₂),
    IsPLCellOn 1 B Bb → B ⊆ fblBd s → B ⊆ tgtVBd v → Bb ⊆ tgtEBd e →
    B ∩ (⋃ e' : Ed, tgtE e') = Bb → IsPLCellOn 2 Dj Jd → Dj ⊆ tgtVBd v →
    Jd ⊆ B ∪ tgtEBd e → (∀ t : Fc, Disjoint (Dj \ Jd) (fblBd t)) → False

def Section34FaceDiskFamily (arV : Ar → Vx) (arF : Ar → Fc) (mkE : Mk → Ed) (mkF : Mk → Fc)
    (tgtV : Vx → Set M₂) (tgtE tgtEBd : Ed → Set M₂) (fblBd : Fc → Set M₂)
    (tgtD tgtDBd : Fc → Set M₂) (tgtA tgtABd : Ar → Set M₂) (tgtP : Mk → Set M₂) : Prop :=
  (∀ s : Fc, IsPLCellOn 2 (tgtD s) (tgtDBd s)) ∧
  (∀ s : Fc, tgtD s ⊆ fblBd s) ∧
  (∀ s : Fc, tgtD s ∩ (⋃ v : Vx, tgtV v) = tgtDBd s) ∧
  (∀ s t : Fc, s ≠ t → Disjoint (tgtD s) (tgtD t)) ∧
  (∀ a : Ar, IsPLCellOn 1 (tgtA a) (tgtABd a)) ∧
  (∀ a : Ar, tgtDBd (arF a) ∩ tgtV (arV a) = tgtA a) ∧
  (∀ (s : Fc) (v : Vx), (∀ a : Ar, arF a = s → arV a ≠ v) → tgtD s ∩ tgtV v = ∅) ∧
  (∀ p : Mk, IsPLCellOn 0 (tgtP p) ∅) ∧
  (∀ p : Mk, tgtDBd (mkF p) ∩ tgtEBd (mkE p) = tgtP p) ∧
  (∀ (s : Fc) (e : Ed), (∀ p : Mk, mkF p = s → mkE p ≠ e) → tgtDBd s ∩ tgtEBd e = ∅) ∧
  ∀ a : Ar, tgtABd a = tgtA a ∩ ⋃ e : Ed, tgtE e

def Section34ResidualFamily (paT : Pa → Tt) (paV : Pa → Vx) (egT : Eg → Tt) (egE : Eg → Ed)
    (mkE : Mk → Ed) (src : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M₁)
    (car : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M₂)
    (tgtV : Vx → Set M₂) (tgtE tgtEBd : Ed → Set M₂) (tgtD : Fc → Set M₂)
    (tgtP : Mk → Set M₂) (tgtR tgtRBd : Tt → Set M₂) (tgtX tgtXBd : Pa → Set M₂)
    (tgtI tgtIBd : Eg → Set M₂) : Prop :=
  (∀ t : Tt, IsPLCellOn 3 (tgtR t) (tgtRBd t)) ∧
  (∀ x : Pa, IsPLCellOn 2 (tgtX x) (tgtXBd x)) ∧
  (∀ i : Eg, IsPLCellOn 1 (tgtI i) (tgtIBd i)) ∧
  (∀ x : Pa, tgtR (paT x) ∩ tgtV (paV x) = tgtX x) ∧
  (∀ (t : Tt) (v : Vx), (∀ x : Pa, paT x = t → paV x ≠ v) → tgtR t ∩ tgtV v = ∅) ∧
  (∀ (t : Tt) (s : Fc), src (.faceDisk s) ⊆ src (.tetraBall t) → tgtR t ∩ tgtD s = tgtD s) ∧
  (∀ (t : Tt) (s : Fc), ¬ (src (.faceDisk s) ⊆ src (.tetraBall t)) → tgtR t ∩ tgtD s = ∅) ∧
  (∀ t t' : Tt, t ≠ t' → tgtR t ∩ tgtR t' ⊆ ⋃ s : Fc, tgtD s) ∧
  (∀ i : Eg, tgtR (egT i) ∩ tgtE (egE i) = tgtI i) ∧
  (∀ i : Eg, tgtI i ⊆ tgtEBd (egE i)) ∧
  (∀ (i : Eg) (p : Mk), mkE p = egE i → tgtP p ⊆ tgtI i → tgtP p ⊆ tgtIBd i) ∧
  ∀ t : Tt, tgtR t ⊆ car (.tetraBall t)

variable {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {arV : Ar → Vx} {arF : Ar → Fc} {mkE : Mk → Ed} {mkF : Mk → Fc}
  {paT : Pa → Tt} {paV : Pa → Vx} {egT : Eg → Tt} {egE : Eg → Ed}
  {src srcBd : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M₁}
  {car : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M₂}
  {tgtV tgtVBd : Vx → Set M₂} {tgtE tgtEBd : Ed → Set M₂} {fbl fblBd : Fc → Set M₂}
  {tgtD tgtDBd : Fc → Set M₂} {tgtA tgtABd : Ar → Set M₂} {tgtP : Mk → Set M₂}
  {tgtR tgtRBd : Tt → Set M₂} {tgtX tgtXBd : Pa → Set M₂} {tgtI tgtIBd : Eg → Set M₂}

theorem exists_section34NormalFamily [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)]
    [HasGroupoid M₂ (plGroupoid 3)] (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h)) (hηc : ContinuousOn η U)
    (hηpos : ∀ x ∈ U, 0 < η x) :
    ∃ (Vx Tt Ed Fc Pa Ar Eg Mk : Type u) (arV : Ar → Vx) (arF : Ar → Fc) (mkE : Mk → Ed)
      (mkF : Mk → Fc) (paT : Pa → Tt) (paV : Pa → Vx) (egT : Eg → Tt) (egE : Eg → Ed)
      (src srcBd : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M₁)
      (car : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M₂)
      (tgtV tgtVBd : Vx → Set M₂) (tgtE tgtEBd : Ed → Set M₂) (fbl fblBd : Fc → Set M₂),
      Section34NormalFamily U h η arV arF mkE mkF paT paV egT egE src srcBd car tgtV tgtVBd
        tgtE tgtEBd fbl fblBd := by
  sorry

theorem exists_section34FaceDisks
    (hdata : Section34NormalFamily U h η arV arF mkE mkF paT paV egT egE src srcBd car
      tgtV tgtVBd tgtE tgtEBd fbl fblBd) :
    ∃ (tgtD tgtDBd : Fc → Set M₂) (tgtA tgtABd : Ar → Set M₂) (tgtP : Mk → Set M₂),
      Section34FaceDiskFamily arV arF mkE mkF tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA
        tgtABd tgtP := by
  sorry

theorem exists_section34ResidualBalls
    (hdata : Section34NormalFamily U h η arV arF mkE mkF paT paV egT egE src srcBd car
      tgtV tgtVBd tgtE tgtEBd fbl fblBd)
    (hdisk : Section34FaceDiskFamily arV arF mkE mkF tgtV tgtE tgtEBd fblBd tgtD tgtDBd
      tgtA tgtABd tgtP) :
    ∃ (tgtR tgtRBd : Tt → Set M₂) (tgtX tgtXBd : Pa → Set M₂) (tgtI tgtIBd : Eg → Set M₂),
      Section34ResidualFamily paT paV egT egE mkE src car tgtV tgtE tgtEBd tgtD tgtP tgtR
        tgtRBd tgtX tgtXBd tgtI tgtIBd := by
  sorry

theorem section34TargetRecognition
    (hdata : Section34NormalFamily U h η arV arF mkE mkF paT paV egT egE src srcBd car
      tgtV tgtVBd tgtE tgtEBd fbl fblBd)
    (hdisk : Section34FaceDiskFamily arV arF mkE mkF tgtV tgtE tgtEBd fblBd tgtD tgtDBd
      tgtA tgtABd tgtP)
    (hres : Section34ResidualFamily paT paV egT egE mkE src car tgtV tgtE tgtEBd tgtD tgtP
      tgtR tgtRBd tgtX tgtXBd tgtI tgtIBd)
    (tc tcBd : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M₂)
    (htc : tc = section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP)
    (htcBd : tcBd = section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd
      fun _ => ∅) :
    (∀ l, IsPLCellOn (section34Dim l) (tc l) (tcBd l)) ∧
      (∀ l, tcBd l = ⋃ m ∈ section34Face src l \ {l}, tc m) ∧
      ∀ l m, tc l ∩ tc m = ⋃ k ∈ section34Face src l ∩ section34Face src m, tc k := by
  sorry

end Diagram

theorem section34CellDiagram : Section34CellDiagram.{u} := by
  classical
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ U hU h hh η hηc hηpos
  obtain ⟨Vx, Tt, Ed, Fc, Pa, Ar, Eg, Mk, arV, arF, mkE, mkF, paT, paV, egT, egE, src,
    srcBd, car, tgtV, tgtVBd, tgtE, tgtEBd, fbl, fblBd, hdata⟩ :=
    exists_section34NormalFamily (η := η) hU hh hηc hηpos
  obtain ⟨tgtD, tgtDBd, tgtA, tgtABd, tgtP, hdisk⟩ := exists_section34FaceDisks hdata
  obtain ⟨tgtR, tgtRBd, tgtX, tgtXBd, tgtI, tgtIBd, hres⟩ :=
    exists_section34ResidualBalls hdata hdisk
  set tc : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M₂ :=
    section34Cell tgtV tgtR tgtE tgtD tgtX tgtA tgtI tgtP with htcdef
  set tcBd : Section34Label Vx Tt Ed Fc Pa Ar Eg Mk → Set M₂ :=
    section34Cell tgtVBd tgtRBd tgtEBd tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅) with htcbddef
  obtain ⟨htcell, htbd, htinter⟩ :=
    section34TargetRecognition hdata hdisk hres tc tcBd htcdef htcbddef
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hresCar⟩ := hres
  obtain ⟨hsc, hsbd, hsinter, hsdim, hsLF, hscover, -, -, -, -, hparent, -, -, -, -,
    hcarS, hcarV, hcarY, hsmall, hcarLF, -, -, -, -, -⟩ := hdata
  have hne : ∀ l, (src l).Nonempty := fun l => (hsc l).nonempty
  have hcpt : ∀ l, IsCompact (src l) := fun l => (hsc l).isCompact
  have hsub : ∀ l, src l ⊆ U := fun l => hscover ▸ subset_iUnion src l
  choose Pp rr uu hrr huu hsceq hsbdeq using hsc
  choose Qq ss vv hss hvv htceq htbdeq using htcell
  choose par hpar3 hparsub using hparent
  have htgtsub : ∀ l, tc l ⊆ tc (par l) := by
    intro l y hy
    have hmem : y ∈ ⋃ k ∈ section34Face src l ∩ section34Face src (par l), tc k :=
      mem_iUnion₂.mpr ⟨l, ⟨Subset.rfl, hparsub l⟩, hy⟩
    rw [← htinter l (par l)] at hmem
    exact hmem.2
  have hcarTop : ∀ l, tc (par l) ⊆ car (par l) := by
    intro l
    rcases section34Dim_eq_three (hpar3 l) with ⟨v, hv⟩ | ⟨t, ht⟩
    · rw [hv, htcdef]
      exact hcarV v
    · rw [ht, htcdef]
      exact hresCar t
  obtain ⟨hcarrier, hsmallfin⟩ :=
    carrier_subset_and_dist_lt_of_parent src tc car par h η hparsub htgtsub
      (fun l => union_subset (hcarS (par l) (hpar3 l)) (hcarTop l))
      (fun l => hsmall (par l) (hpar3 l))
  have hfacefin : ∀ m, (section34Face src m).Finite := fun m =>
    finite_face_of_locallyFinite U src m hne (hcpt m) hsub hsLF
  have hfib : ∀ m, {l | par l = m}.Finite := fun m =>
    (hfacefin m).subset fun l hl => hl ▸ hparsub l
  have hLFcar : ∀ y ∈ h '' U, ∃ W ∈ 𝓝[h '' U] y,
      {l | (car (par l) ∩ W).Nonempty}.Finite := by
    intro y hy
    obtain ⟨W, hW, hfin⟩ := hcarLF y hy
    refine ⟨W, hW, (hfin.biUnion fun m _ => hfib m).subset fun l hl => ?_⟩
    exact mem_iUnion₂.mpr ⟨par l, ⟨hpar3 l, hl⟩, rfl⟩
  have hLFt := exists_nhds_finite_of_subset_carrier (h '' U) tc (fun l => car (par l))
    (fun l => (htgtsub l).trans (hcarTop l)) (fun l => hcarY (par l) (hpar3 l)) hLFcar
  refine ⟨Section34Label Vx Tt Ed Fc Pa Ar Eg Mk, section34Dim, section34Face src, Pp, Qq,
    rr, ss, uu, vv, src, tc, fun l => car (par l), ?_, hrr, hss, huu, hvv, hsceq, htceq,
    fun l m hm => hsdim l m hm, fun l => (hsbdeq l).symm.trans (hsbd l),
    fun l => (htbdeq l).symm.trans (htbd l), hsinter, htinter,
    fun x hx => hsLF x (hscover ▸ hx), hLFt, hscover, hcarrier, hsmallfin⟩
  intro l
  cases l <;> simp [section34Dim]

end DifferentialGeometry.Topology.PiecewiseLinear
