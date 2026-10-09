import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeams
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ElementarizeProof

/-!
# Chapter-14 assembly, bridge B3: regular cut data → `EmbeddedCutSystem` → `TorusPresentation`

Lane ASM-B3 of `docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md` (§3 B3, §4 row §2;
external draft §(b) B3). The producer of the EXISTING `GC.Seifert.EmbeddedCutSystem W .withBoundary`
(`Seifert/EmbeddedPieces.lean:260–298`) from `RegularCutData`: finitely many `PieceFold`s covering `W`,
whole interior torus seams (`TorusSeam`) with the half collars they induce in their side pieces
(the two-sided equalities of B2 on all of `0 ≤ s < 1`), external half collars pulled back from the
ports `E` (`externalLift_eq` on the whole half-collar source), boundary exhaustion and the overlap law.
A self-seam (`side c true = side c false`) is allowed, so the piece maps need not be injective.

* `RegularCutData.toCutSystem`: the ports of a piece are the seam sides and external tori it owns,
  numbered by `Fintype.equivFin`; `sides_bijective` is the bijectivity of an equivalence; the
  matchings are identities and the seams are the given collars (no shrinking).
* `collar_disjoint`: two different seams by `seam_disjoint`; the two sides of ONE seam (also a
  self-seam) by injectivity of the seam on its source after a push to positive height
  (`portPoint_not_mem_portTarget_flip`); seam side against external torus by the port protection
  `external_seam_disjoint`; two external tori by `E.disjoint`.
* `external_local` (`isLocalDiffeomorphAt_externalLift`) from `externalLift_eq`: on the target of the
  external lift the piece map is `E.collar ∘ externalLift⁻¹` (a half-space local inverse), not from
  full rank.
* `cutMap_eq_cutMap_iff`: the kernel of the fold is exactly the seam relation (no third preimage).
* `exists_torusPresentation_of_regularCutData`: the frozen B3 statement, through
  `EmbeddedCutSystem.toTorusPresentation` (`:1297`) and `pieceDiffeomorph` (`:1443`).

Deviations from the frozen interface: `RegularCutData` has the extra field `external_seam_disjoint`
(port protection; design erratum E2, main's decision 2026-10-04), and `boundary_exhausted` is stated
as the equality of the boundary with the set of port tori instead of a pointwise iff (same content;
an iff field fails the `explicitVarsOfIff` linter on its projection). The B3 theorem text is
verbatim.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The producer-side data of B3: pieces, their seam half collars (B2-side outputs) and their
external half collars (pulled back from `E`), with the actual overlap law.

The last field `external_seam_disjoint` is not in the frozen interface (design erratum E2). Without
it B3 is false: on `W = T² × [0, 3]` take the pieces `T² × [0, 2]` and `T² × [2, 3]`, one seam
`(t, s) ↦ (t, 2 + s)` with target `T² × (1, 3)`, lifts `(t, h) ↦ (t, 2 ∓ h)`, ports
`E.collar 0 (t, h) = (t, 3h/2)`, `E.collar 1 (t, h) = (t, 3 − h/2)` and the same external lifts.
Every other field holds, but in any `TorusPresentation` some external collar has an open target
containing a point of `T² × {3}`, which meets the seam target `T² × (1, 3)`, against
`TorusPresentation.external_seam_disjoint`; no shrinking of the external collars avoids this. -/
structure RegularCutData (W : CompactCarrier.{u}) {n : ℕ} (E : BoundaryTori W n) where
  count : ℕ
  count_pos : 0 < count
  piece : Fin count → PieceFold W
  covers : ⋃ j, range (piece j).map = univ
  seamCount : ℕ
  seam : Fin seamCount → TorusSeam W
  seam_disjoint : Pairwise fun c d => Disjoint (seam c).collar.target (seam d).collar.target
  side : Fin seamCount → Bool → Fin count
  lift : (c : Fin seamCount) → (b : Bool) →
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
      (piece (side c b)).Piece ∞
  lift_source : ∀ c b, (lift c b).source = halfCollarSource
  lift_eq : ∀ c b t s (hs : 0 ≤ s), s < 1 →
    (piece (side c b)).map (lift c b (t, halfPoint s hs)) =
      (seam c).collar (t, if b then -s else s)
  externalOwner : Fin n → Fin count
  externalLift : (i : Fin n) →
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
      (piece (externalOwner i)).Piece ∞
  externalLift_source : ∀ i, (externalLift i).source = halfCollarSource
  externalLift_eq : ∀ i p, p ∈ halfCollarSource →
    (piece (externalOwner i)).map (externalLift i p) = E.collar i p
  boundary_exhausted : ∀ j, (𝓡∂ 3).boundary (piece j).Piece = {q |
    (∃ c b t, ∃ h : side c b = j, q = h ▸ lift c b (t, halfZero)) ∨
      (∃ i t, ∃ h : externalOwner i = j, q = h ▸ externalLift i (t, halfZero))}
  overlap : ∀ j j' q q', (piece j).map q = (piece j').map q' →
    (⟨j, q⟩ : Σ j, (piece j).Piece) = ⟨j', q'⟩ ∨ ∃ c t, (piece j).map q = (seam c).collar (t, 0)
  external_exhausted : W.model.boundary W.Carrier = E.image
  external_seam_disjoint : ∀ i c, Disjoint (E.collar i).target (seam c).collar.target

namespace RegularCutData

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : RegularCutData W E)

/-- The ports: the two sides of every seam, then the external tori. -/
abbrev Port := Fin D.seamCount × Bool ⊕ Fin n

/-- The piece owning a port. -/
def owner : D.Port → Fin D.count
  | .inl p => D.side p.1 p.2
  | .inr i => D.externalOwner i

/-- The half collar of a port, in its owning piece. -/
def portLift : (x : D.Port) →
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
      (D.piece (D.owner x)).Piece ∞
  | .inl p => D.lift p.1 p.2
  | .inr i => D.externalLift i

theorem portLift_source (x : D.Port) : (D.portLift x).source = halfCollarSource := by
  rcases x with ⟨c, b⟩ | i
  · exact D.lift_source c b
  · exact D.externalLift_source i

/-- The ports owned by the piece `j`. -/
abbrev OwnedPort (j : Fin D.count) := {x : D.Port // D.owner x = j}

/-- The number of boundary tori of the piece `j`. -/
def torusCount (j : Fin D.count) : ℕ := Fintype.card (D.OwnedPort j)

/-- The numbering of the ports of `j`. -/
def portEquiv (j : Fin D.count) : D.OwnedPort j ≃ Fin (D.torusCount j) :=
  Fintype.equivFin _

/-- The half collar of an owned port, in the piece `j`. -/
def ownedLift (j : Fin D.count) (y : D.OwnedPort j) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) (D.piece j).Piece ∞ :=
  Eq.rec (motive := fun k _ => PartialDiffeomorph halfCollarModel (𝓡∂ 3)
    (Torus × EuclideanHalfSpace 1) (D.piece k).Piece ∞) (D.portLift y.1) y.2

/-- The numbered half collars of the piece `j`. -/
def collar (j : Fin D.count) (l : Fin (D.torusCount j)) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) (D.piece j).Piece ∞ :=
  D.ownedLift j ((D.portEquiv j).symm l)

theorem collar_portEquiv (j : Fin D.count) (y : D.OwnedPort j) :
    D.collar j (D.portEquiv j y) = D.ownedLift j y := by
  simp only [collar, Equiv.symm_apply_apply]

theorem collar_portEquiv_mk (x : D.Port) :
    D.collar (D.owner x) (D.portEquiv (D.owner x) ⟨x, rfl⟩) = D.portLift x :=
  D.collar_portEquiv _ _

/-- The side numbering of a port. -/
def portSide (x : D.Port) : Σ j, Fin (D.torusCount j) :=
  ⟨D.owner x, D.portEquiv (D.owner x) ⟨x, rfl⟩⟩

theorem portSide_eq (x : D.Port) : D.portSide x =
    (Equiv.sigmaCongrRight D.portEquiv) ((Equiv.sigmaFiberEquiv D.owner).symm x) :=
  rfl

theorem bijective_portSide : Bijective D.portSide :=
  ((Equiv.sigmaFiberEquiv D.owner).symm.trans (Equiv.sigmaCongrRight D.portEquiv)).bijective

theorem collar_portSide (x : D.Port) :
    D.collar (D.portSide x).1 (D.portSide x).2 = D.portLift x :=
  D.collar_portEquiv _ _

theorem collar_source (j : Fin D.count) (l : Fin (D.torusCount j)) :
    (D.collar j l).source = halfCollarSource := by
  obtain ⟨y, rfl⟩ := (D.portEquiv j).surjective l
  rw [D.collar_portEquiv]
  obtain ⟨x, rfl⟩ := y
  exact D.portLift_source x

/-! ### The cut space and the targets of the ports -/

/-- The disjoint union of the pieces. -/
abbrev Cut := Σ j, (D.piece j).Piece

/-- The fold of the pieces into `W`. -/
def cutMap (z : D.Cut) : W.Carrier := (D.piece z.1).map z.2

/-- A point of the half collar of a port, in the cut space. -/
def portPoint (x : D.Port) (p : Torus × EuclideanHalfSpace 1) : D.Cut :=
  ⟨D.owner x, D.portLift x p⟩

/-- The half collar of a port, as a subset of the cut space. -/
def portTarget (x : D.Port) : Set D.Cut := D.portPoint x '' halfCollarSource

theorem portTarget_eq (x : D.Port) :
    D.portTarget x = Sigma.mk (D.owner x) '' (D.portLift x).target := by
  rw [← (D.portLift x).toPartialEquiv.image_source_eq_target, image_image]
  change D.portPoint x '' halfCollarSource = (fun p => D.portPoint x p) '' (D.portLift x).source
  rw [D.portLift_source]

theorem isOpen_portTarget (x : D.Port) : IsOpen (D.portTarget x) := by
  rw [D.portTarget_eq]
  exact isOpenMap_sigmaMk _ (D.portLift x).open_target

theorem continuousOn_portPoint (x : D.Port) : ContinuousOn (D.portPoint x) halfCollarSource := by
  have h := (D.portLift x).contMDiffOn.continuousOn
  rw [D.portLift_source] at h
  exact continuous_sigmaMk.comp_continuousOn h

theorem cutMap_portPoint_inl (c : Fin D.seamCount) (b : Bool) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    D.cutMap (D.portPoint (.inl (c, b)) p) =
      (D.seam c).collar (p.1, if b then -p.2.val 0 else p.2.val 0) := by
  have h := D.lift_eq c b p.1 (p.2.val 0) p.2.property hp
  rw [halfPoint_eq_self p.2 p.2.property rfl] at h
  exact h

theorem cutMap_portPoint_inr (i : Fin n) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) : D.cutMap (D.portPoint (.inr i) p) = E.collar i p :=
  D.externalLift_eq i p hp

theorem signed_mem_source (c : Fin D.seamCount) (b : Bool) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    (p.1, if b then -p.2.val 0 else p.2.val 0) ∈ (D.seam c).collar.source := by
  rw [(D.seam c).source_eq]
  have h0 : 0 ≤ p.2.val 0 := p.2.property
  have h1 : p.2.val 0 < 1 := hp
  cases b
  · exact ⟨by simp only [Bool.false_eq_true, ↓reduceIte]; linarith,
      by simp only [Bool.false_eq_true, ↓reduceIte]; linarith⟩
  · exact ⟨by simp only [↓reduceIte]; linarith, by simp only [↓reduceIte]; linarith⟩

theorem cutMap_portPoint_inl_mem (c : Fin D.seamCount) (b : Bool)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    D.cutMap (D.portPoint (.inl (c, b)) p) ∈ (D.seam c).collar.target := by
  rw [D.cutMap_portPoint_inl c b hp]
  exact (D.seam c).collar.map_source' (D.signed_mem_source c b hp)

theorem cutMap_portPoint_inr_mem (i : Fin n) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) : D.cutMap (D.portPoint (.inr i) p) ∈ (E.collar i).target := by
  rw [D.cutMap_portPoint_inr i hp]
  exact (E.collar i).map_source' ((E.source_eq i).symm ▸ hp)

/-- The two half collars of one seam meet nowhere in the cut space, also for a self-seam: a common
point would give, after a push to positive height, one point of the seam at heights of opposite
signs. -/
theorem portPoint_not_mem_portTarget_flip (c : Fin D.seamCount) {b b' : Bool} (hb : b ≠ b')
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    D.portPoint (.inl (c, b)) p ∉ D.portTarget (.inl (c, b')) := by
  have key : ∀ q ∈ halfCollarSource, 0 < q.2.val 0 →
      D.portPoint (.inl (c, b)) q ∉ D.portTarget (.inl (c, b')) := by
    rintro q hq hq0 ⟨q', hq', h⟩
    have hf := congrArg D.cutMap h
    rw [D.cutMap_portPoint_inl c b' hq', D.cutMap_portPoint_inl c b hq] at hf
    have hs := congrArg Prod.snd ((D.seam c).collar.toPartialEquiv.injOn
      (D.signed_mem_source c b' hq') (D.signed_mem_source c b hq) hf)
    have h0 : 0 ≤ q'.2.val 0 := q'.2.property
    cases b <;> cases b' <;> simp at hb hs <;> linarith
  intro hz
  let γ : ℝ → Torus × EuclideanHalfSpace 1 := fun ε => (p.1, clampHalf (p.2.val 0 + ε))
  have hγ : Continuous γ := by
    change Continuous fun ε : ℝ => (p.1, clampHalf (p.2.val 0 + ε))
    exact continuous_const.prodMk (continuous_clampHalf.comp (by fun_prop : Continuous fun ε : ℝ => p.2.val 0 + ε))
  have hγ0 : γ 0 = p := by
    refine Prod.ext rfl ?_
    change clampHalf (p.2.val 0 + 0) = p.2
    rw [add_zero, clampHalf_of_nonneg p.2.property]
    exact halfPoint_eq_self p.2 p.2.property rfl
  have hcont : ContinuousAt (fun ε => D.portPoint (.inl (c, b)) (γ ε)) 0 := by
    change ContinuousAt (D.portPoint (.inl (c, b)) ∘ γ) 0
    refine ContinuousAt.comp ?_ hγ.continuousAt
    rw [hγ0]
    exact (D.continuousOn_portPoint _).continuousAt (isOpen_halfCollarSource'.mem_nhds hp)
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), D.portPoint (.inl (c, b)) (γ ε) ∈ D.portTarget (.inl (c, b')) ∧
      γ ε ∈ halfCollarSource := by
    refine (hcont.eventually ((D.isOpen_portTarget _).mem_nhds ?_)).and
      (hγ.continuousAt.eventually (isOpen_halfCollarSource'.mem_nhds ?_))
    · change D.portPoint (.inl (c, b)) (γ 0) ∈ _
      rw [hγ0]
      exact hz
    · rw [hγ0]
      exact hp
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hδ2 : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  obtain ⟨h1, h2⟩ := hball hδ2
  refine key (γ (δ / 2)) h2 ?_ h1
  change 0 < max (p.2.val 0 + δ / 2) 0
  have h0 : 0 ≤ p.2.val 0 := p.2.property
  exact lt_max_of_lt_left (by linarith)

theorem portTarget_disjoint {x x' : D.Port} (hxx : x ≠ x') :
    Disjoint (D.portTarget x) (D.portTarget x') := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ hz
  rcases x with ⟨c, b⟩ | i <;> rcases x' with ⟨d, b'⟩ | i'
  · by_cases hcd : c = d
    · subst hcd
      exact D.portPoint_not_mem_portTarget_flip c (fun hb => hxx (by rw [hb])) hp hz
    · obtain ⟨p', hp', h⟩ := hz
      have hm := D.cutMap_portPoint_inl_mem d b' hp'
      rw [h] at hm
      exact (D.seam_disjoint hcd).le_bot ⟨D.cutMap_portPoint_inl_mem c b hp, hm⟩
  · obtain ⟨p', hp', h⟩ := hz
    have hm := D.cutMap_portPoint_inr_mem i' hp'
    rw [h] at hm
    exact (D.external_seam_disjoint i' c).le_bot ⟨hm, D.cutMap_portPoint_inl_mem c b hp⟩
  · obtain ⟨p', hp', h⟩ := hz
    have hm := D.cutMap_portPoint_inl_mem d b' hp'
    rw [h] at hm
    exact (D.external_seam_disjoint i d).le_bot ⟨D.cutMap_portPoint_inr_mem i hp, hm⟩
  · obtain ⟨p', hp', h⟩ := hz
    have hm := D.cutMap_portPoint_inr_mem i' hp'
    rw [h] at hm
    have hii : i ≠ i' := fun hi => hxx (by rw [hi])
    exact (E.disjoint hii).le_bot ⟨D.cutMap_portPoint_inr_mem i hp, hm⟩

theorem mk_mem_portTarget {j : Fin D.count} (y : D.OwnedPort j) {q : (D.piece j).Piece}
    (hq : q ∈ (D.ownedLift j y).target) : (⟨j, q⟩ : D.Cut) ∈ D.portTarget y.1 := by
  obtain ⟨x, rfl⟩ := y
  change q ∈ (D.portLift x).target at hq
  refine ⟨(D.portLift x).symm q, ?_, ?_⟩
  · rw [← D.portLift_source x]
    exact (D.portLift x).map_target' hq
  · change (⟨D.owner x, D.portLift x ((D.portLift x).symm q)⟩ : D.Cut) = ⟨D.owner x, q⟩
    rw [(D.portLift x).apply_symm_apply hq]

theorem collar_disjoint (j : Fin D.count) :
    Pairwise fun l l' => Disjoint (D.collar j l).target (D.collar j l').target := by
  intro l l' hll
  rw [Set.disjoint_left]
  intro q hq hq'
  have hne : ((D.portEquiv j).symm l).1 ≠ ((D.portEquiv j).symm l').1 := fun h =>
    hll ((D.portEquiv j).symm.injective (Subtype.ext h))
  exact (D.portTarget_disjoint hne).le_bot ⟨D.mk_mem_portTarget _ hq, D.mk_mem_portTarget _ hq'⟩

theorem boundary_eq (j : Fin D.count) :
    (𝓡∂ 3).boundary (D.piece j).Piece = ⋃ l, range fun t => D.collar j l (t, halfZero) := by
  rw [D.boundary_exhausted j]
  ext q
  rw [mem_iUnion]
  constructor
  · rintro (⟨c, b, t, h, rfl⟩ | ⟨i, t, h, rfl⟩)
    · subst h
      exact ⟨D.portEquiv (D.side c b) ⟨.inl (c, b), rfl⟩, t, by rw [D.collar_portEquiv]; rfl⟩
    · subst h
      exact ⟨D.portEquiv (D.externalOwner i) ⟨.inr i, rfl⟩, t, by rw [D.collar_portEquiv]; rfl⟩
  · rintro ⟨l, t, rfl⟩
    obtain ⟨y, rfl⟩ := (D.portEquiv j).surjective l
    rw [D.collar_portEquiv]
    obtain ⟨x, rfl⟩ := y
    rcases x with ⟨c, b⟩ | i
    · exact Or.inl ⟨c, b, t, rfl, rfl⟩
    · exact Or.inr ⟨i, t, rfl, rfl⟩

/-- `external_local` from the external half-collar equality: on the target of the external lift
the piece map is the external collar of `W` composed with the inverse lift. -/
theorem isLocalDiffeomorphAt_externalLift (i : Fin n) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    IsLocalDiffeomorphAt (𝓡∂ 3) W.model ∞ (D.piece (D.externalOwner i)).map
      (D.externalLift i p) := by
  have hps : p ∈ (D.externalLift i).source := (D.externalLift_source i).symm ▸ hp
  refine ⟨(D.externalLift i).symm.trans (E.collar i), ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.symm_source]
    refine ⟨(D.externalLift i).map_source' hps, ?_⟩
    change (D.externalLift i).symm (D.externalLift i p) ∈ (E.collar i).source
    rw [(D.externalLift i).symm_apply_apply hps, E.source_eq]
    exact hp
  · intro y hy
    rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.symm_source] at hy
    have hy1 : (D.externalLift i).symm y ∈ halfCollarSource := by
      rw [← D.externalLift_source i]
      exact (D.externalLift i).map_target' hy.1
    rw [PartialDiffeomorph.trans_apply, ← D.externalLift_eq i _ hy1,
      (D.externalLift i).apply_symm_apply hy.1]

theorem sumElim_portSide :
    Sum.elim (uncurry fun c b => D.portSide (.inl (c, b))) (fun i => D.portSide (.inr i)) =
      D.portSide := by
  funext x
  rcases x with ⟨c, b⟩ | i <;> rfl

/-- **B3, the cut system.** The existing `EmbeddedCutSystem` (`Seifert/EmbeddedPieces.lean:260`)
of a regular cut: the ports of a piece are the seam sides and external tori it owns, numbered by
`portEquiv`; the matchings are identities. -/
def toCutSystem : EmbeddedCutSystem W .withBoundary where
  count := D.count
  count_pos := D.count_pos
  Piece j := (D.piece j).Piece
  charts j := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) (D.piece j).Piece)
  manifold j := (inferInstance : IsManifold (𝓡∂ 3) ∞ (D.piece j).Piece)
  map j := (D.piece j).map
  smooth j := (D.piece j).smooth
  mfderiv_bijective j := (D.piece j).mfderiv_bijective
  covers := D.covers
  torusCount := D.torusCount
  collar := D.collar
  collar_source := D.collar_source
  collar_disjoint := D.collar_disjoint
  boundary_exhausted := D.boundary_eq
  seamCount := D.seamCount
  side c b := D.portSide (.inl (c, b))
  externalCount := n
  externalSide i := D.portSide (.inr i)
  sides_bijective := by
    rw [D.sumElim_portSide]
    exact D.bijective_portSide
  matching _ := Diffeomorph.refl torusModel Torus ∞
  seam c := (D.seam c).collar
  seam_source c := (D.seam c).source_eq
  seam_neg c t s hs h1 := by
    rw [D.collar_portSide]
    have h := D.lift_eq c true t (-s) (neg_nonneg.2 hs) (by linarith)
    simp only [↓reduceIte, neg_neg] at h
    exact h.symm
  seam_pos c t s hs h1 := by
    rw [D.collar_portSide]
    have h := D.lift_eq c false t s hs h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact h.symm
  seam_interior c := (D.seam c).target_interior
  external_local i t := by
    rw [D.collar_portSide]
    exact D.isLocalDiffeomorphAt_externalLift i (zero_mem_halfCollarSource t)
  overlap := D.overlap

theorem toCutSystem_sideTorus (x : D.Port) (t : Torus) :
    D.toCutSystem.sideTorus (D.portSide x) t = D.portPoint x (t, halfZero) :=
  (D.toCutSystem.sideCollar_apply (D.portSide x) (t, halfZero)).trans (by
    change (⟨(D.portSide x).1, D.collar (D.portSide x).1 (D.portSide x).2 (t, halfZero)⟩ :
      D.Cut) = _
    rw [D.collar_portSide]
    rfl)

theorem cutMap_portPoint_seam_zero (c : Fin D.seamCount) (b : Bool) (t : Torus) :
    D.cutMap (D.portPoint (.inl (c, b)) (t, halfZero)) = (D.seam c).collar (t, 0) := by
  rw [D.cutMap_portPoint_inl c b (zero_mem_halfCollarSource t)]
  cases b
  · rfl
  · change (D.seam c).collar (t, -(0 : ℝ)) = _
    rw [neg_zero]

variable {D} in
/-- **The kernel of the fold is the seam relation** (review D6 (4)): two points of the cut space
have the same image in `W` iff they are equal or are the two sides of one seam over one torus
point; in particular no point of `W` has three preimages. From `EmbeddedCutSystem.fold_eq_fold`
(boundary exhaustion, the local inverse at interior points and full rank). -/
theorem cutMap_eq_cutMap_iff {z z' : D.Cut} :
    D.cutMap z = D.cutMap z' ↔ z = z' ∨ ∃ c t,
      (z = D.portPoint (.inl (c, true)) (t, halfZero) ∧
        z' = D.portPoint (.inl (c, false)) (t, halfZero)) ∨
      (z = D.portPoint (.inl (c, false)) (t, halfZero) ∧
        z' = D.portPoint (.inl (c, true)) (t, halfZero)) := by
  constructor
  · intro h
    rcases D.toCutSystem.fold_eq_fold (x := z) (y := z') h with h1 | ⟨c, t, h2⟩
    · exact Or.inl h1
    · have hl : D.toCutSystem.leftPt c t = D.portPoint (.inl (c, true)) (t, halfZero) :=
        D.toCutSystem_sideTorus _ t
      have hr : D.toCutSystem.rightPt c t = D.portPoint (.inl (c, false)) (t, halfZero) :=
        D.toCutSystem_sideTorus _ t
      rw [hl, hr] at h2
      exact Or.inr ⟨c, t, h2⟩
  · rintro (rfl | ⟨c, t, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · rfl
    · rw [D.cutMap_portPoint_seam_zero, D.cutMap_portPoint_seam_zero]
    · rw [D.cutMap_portPoint_seam_zero, D.cutMap_portPoint_seam_zero]

/-- **B3, the torus presentation** (`EmbeddedCutSystem.toTorusPresentation`,
`Seifert/EmbeddedPieces.lean:1297`). -/
def toTorusPresentation : TorusPresentation W := D.toCutSystem.toTorusPresentation

@[simp]
theorem toTorusPresentation_components_count : D.toTorusPresentation.components.count = D.count :=
  rfl

@[simp]
theorem toTorusPresentation_externalCount : D.toTorusPresentation.externalCount = n :=
  rfl

@[simp]
theorem toTorusPresentation_pairing_count : D.toTorusPresentation.pairing.count = D.seamCount :=
  rfl

theorem toTorusPresentation_seam (c : Fin D.seamCount) :
    D.toTorusPresentation.seam c = (D.seam c).collar :=
  rfl

theorem toTorusPresentation_leftPiece (c : Fin D.seamCount) :
    D.toTorusPresentation.leftPiece c = D.side c true :=
  rfl

theorem toTorusPresentation_rightPiece (c : Fin D.seamCount) :
    D.toTorusPresentation.rightPiece c = D.side c false :=
  rfl

theorem toTorusPresentation_externalPiece (i : Fin n) :
    D.toTorusPresentation.externalPiece i = D.externalOwner i :=
  rfl

theorem toTorusPresentation_matching (c : Fin D.seamCount) :
    D.toTorusPresentation.pairing.matching c = Diffeomorph.refl torusModel Torus ∞ :=
  rfl

/-- The external tori of the presentation are those of `E`, on the whole half collar. -/
theorem toTorusPresentation_external_collar (i : Fin n) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) : D.toTorusPresentation.external.collar i p = E.collar i p := by
  refine (D.toCutSystem.toTorusPresentation_external_collar i p).trans
    ((D.toCutSystem.fold_sideCollar (D.toCutSystem.externalSide i) p).trans ?_)
  change (D.piece (D.portSide (.inr i)).1).map
    (D.collar (D.portSide (.inr i)).1 (D.portSide (.inr i)).2 p) = _
  rw [D.collar_portSide]
  exact D.externalLift_eq i p hp

/-- The component `j` of the presentation is the piece `j`
(`EmbeddedCutSystem.pieceDiffeomorph`, `Seifert/EmbeddedPieces.lean:1443`). -/
def pieceDiffeomorph (j : Fin D.count) :
    (D.piece j).Piece ≃ₘ⟮𝓡∂ 3, (D.toTorusPresentation.Component j).model⟯
      (D.toTorusPresentation.Component j).Carrier :=
  D.toCutSystem.pieceDiffeomorph j

theorem pieceDiffeomorph_apply (j : Fin D.count) (q : (D.piece j).Piece) :
    (D.pieceDiffeomorph j q).val = (⟨j, q⟩ : D.toCutSystem.Cut) :=
  rfl

end RegularCutData

/-- **B3 (producer of the existing `EmbeddedCutSystem`, `EmbeddedPieces.lean:260–298`).** Proves
`collar_disjoint`, `boundary_exhausted`, `sides_bijective` and `external_local` (the latter from
`externalLift_eq` and the half-space local inverse, NOT from full rank plus disjoint interiors);
self-seams (`side c true = side c false`) are allowed. Output through `toTorusPresentation`
(`:1297`) and `pieceDiffeomorph` (`:1443`), with each component identified with its piece. -/
theorem exists_torusPresentation_of_regularCutData {W : CompactCarrier.{u}} {n : ℕ}
    {E : BoundaryTori W n} (D : RegularCutData W E) :
    ∃ (T : TorusPresentation W) (hc : T.components.count = D.count),
      T.externalCount = n ∧ T.pairing.count = D.seamCount ∧
      (∀ i, Nonempty ((T.Component i).Carrier ≃ₘ⟮(T.Component i).model, 𝓡∂ 3⟯
        (D.piece (Fin.cast hc i)).Piece)) ∧
      (∀ c, ∃ c', T.seam c' = (D.seam c).collar) :=
  ⟨D.toTorusPresentation, rfl, rfl, rfl, fun i => ⟨(D.pieceDiffeomorph i).symm⟩,
    fun c => ⟨c, rfl⟩⟩

end GC.GraphManifold.Assembly
