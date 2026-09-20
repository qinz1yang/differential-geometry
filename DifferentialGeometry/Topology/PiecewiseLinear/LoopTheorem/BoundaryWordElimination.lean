/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Tactic.Group
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDiskBoundaryWord

/-!
# Boundary word elimination for the two candidate disks of a boundary arc cut

Moise's Lemma 2 cuts a normal singular two cell along a boundary arc.  Each of the two
relative directions of the cut produces two candidate disks rather than one, and the
selection between them is not geometric: it is the observation that the two candidate
boundary classes cannot both lie in the fixed normal subgroup while the original boundary
class avoids it.

Writing `σ`, `τ`, `ν`, `φ` for the path factors involved, the candidate boundary words are

* case 3: `σ * ν⁻¹` and `σ * φ * ν * τ`;
* case 4: `σ * ν` and `σ * τ⁻¹ * ν * φ⁻¹`;

and in both cases the original boundary word is `σ * τ * ν * φ`.  The word `σ * τ * ν * φ`
is not an extra assumption here: among the words in which each of the four letters occurs
exactly once with positive exponent it is, up to cyclic rotation, the only one lying in the
normal closure of the two candidates simultaneously for case 3 and for case 4.

Main results.

* `boundaryWord_caseThree` and `boundaryWord_caseFour`: the explicit elimination identities
  expressing `σ * τ * ν * φ` as a product of the two candidate words, their inverses and a
  single conjugate.  Both are identities in an arbitrary group.
* `boundaryWord_mem_of_caseThree_mem` and `boundaryWord_mem_of_caseFour_mem`: the form the
  consumers need, namely that both candidates lying in a normal subgroup forces the original
  boundary word into it.
* `boundaryWord_mem_normalClosure_caseThree` and `boundaryWord_mem_normalClosure_caseFour`:
  the equivalent membership in the normal closure of the two candidates.
* `notMem_or_notMem_of_caseThree` and `notMem_or_notMem_of_caseFour`: the contrapositive
  packaging, that an original boundary word avoiding the normal subgroup forces at least one
  candidate to avoid it.
* `exists_descends_and_notMem`, `exists_complexity_lt_and_notMem` and the two case specific
  forms `exists_descends_and_notMem_caseThree` and `exists_descends_and_notMem_caseFour`: the
  two candidate selection, producing a single candidate that both descends and avoids.
* `not_conjugacyClassMeets_or_of_caseThree`, `not_conjugacyClassMeets_or_of_caseFour` and
  `exists_descends_and_not_conjugacyClassMeets`: the same statements phrased through
  `conjugacyClassMeets`, the avoidance predicate actually carried by `NormalSystem`.

Two deliberate limitations.  First, `σ`, `τ`, `ν`, `φ` are elements of an arbitrary group:
geometrically they are paths, not loops at one basepoint, so a consumer has to supply the
group elements obtained after conjugating each factor by a connector to the basepoint.  That
bridge is a property of the chosen connectors and is not established here; nothing below
depends on the letters being individually represented by loops.

Second, the descent side is abstract over a predicate `descends`.  Coupling it directly to
`NormalSingularSetTriangulation.complexity_lt_of_injective_origin` and
`NormalSingularSetTriangulation.complexity_lt_of_card_lt_of_equiv_compl` would force the two
candidates to carry their own singular two cells and triangulations, so the statement would
gain geometric hypotheses without gaining content.  `exists_complexity_lt_and_notMem` is the
numeric specialization those two consumers feed: take `n` to be the old complexity and
`complexity` the complexity of the triangulation attached to a candidate.
-/

namespace DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordElimination

variable {G : Type*} [Group G]

/-- The case 3 elimination identity.  Cutting along a boundary arc in the first relative
direction produces the candidate boundary words `σ * ν⁻¹` and `σ * φ * ν * τ`, and the
original boundary word `σ * τ * ν * φ` is the first candidate times a single conjugate of
the second candidate times the inverse of the first. -/
theorem boundaryWord_caseThree (σ τ ν φ : G) :
    σ * τ * ν * φ =
      σ * ν⁻¹ * ((σ * φ)⁻¹ * (σ * φ * ν * τ * (σ * ν⁻¹)⁻¹) * (σ * φ)) := by
  group

/-- The case 4 elimination identity.  Cutting along a boundary arc in the second relative
direction produces the candidate boundary words `σ * ν` and `σ * τ⁻¹ * ν * φ⁻¹`, and the
original boundary word `σ * τ * ν * φ` is the first candidate times a single conjugate of
the inverse of the second candidate times the first. -/
theorem boundaryWord_caseFour (σ τ ν φ : G) :
    σ * τ * ν * φ =
      σ * ν * (φ⁻¹ * ((σ * τ⁻¹ * ν * φ⁻¹)⁻¹ * (σ * ν)) * φ) := by
  group

/-- Case 3 elimination.  If both candidate boundary words produced by the cut lie in the
normal subgroup `N`, then so does the original boundary word `σ * τ * ν * φ`. -/
theorem boundaryWord_mem_of_caseThree_mem {N : Subgroup G} [N.Normal] {σ τ ν φ : G}
    (h₁ : σ * ν⁻¹ ∈ N) (h₂ : σ * φ * ν * τ ∈ N) : σ * τ * ν * φ ∈ N := by
  rw [boundaryWord_caseThree]
  exact N.mul_mem h₁ (‹N.Normal›.conj_mem' _ (N.mul_mem h₂ (N.inv_mem h₁)) (σ * φ))

/-- Case 4 elimination.  If both candidate boundary words produced by the cut lie in the
normal subgroup `N`, then so does the original boundary word `σ * τ * ν * φ`. -/
theorem boundaryWord_mem_of_caseFour_mem {N : Subgroup G} [N.Normal] {σ τ ν φ : G}
    (h₁ : σ * ν ∈ N) (h₂ : σ * τ⁻¹ * ν * φ⁻¹ ∈ N) : σ * τ * ν * φ ∈ N := by
  rw [boundaryWord_caseFour]
  exact N.mul_mem h₁ (‹N.Normal›.conj_mem' _ (N.mul_mem (N.inv_mem h₂) h₁) φ)

/-- The case 3 elimination identity restated: the original boundary word lies in the normal
closure of the two candidate boundary words. -/
theorem boundaryWord_mem_normalClosure_caseThree (σ τ ν φ : G) :
    σ * τ * ν * φ ∈ Subgroup.normalClosure {σ * ν⁻¹, σ * φ * ν * τ} :=
  boundaryWord_mem_of_caseThree_mem (Subgroup.subset_normalClosure (by simp))
    (Subgroup.subset_normalClosure (by simp))

/-- The case 4 elimination identity restated: the original boundary word lies in the normal
closure of the two candidate boundary words. -/
theorem boundaryWord_mem_normalClosure_caseFour (σ τ ν φ : G) :
    σ * τ * ν * φ ∈ Subgroup.normalClosure {σ * ν, σ * τ⁻¹ * ν * φ⁻¹} :=
  boundaryWord_mem_of_caseFour_mem (Subgroup.subset_normalClosure (by simp))
    (Subgroup.subset_normalClosure (by simp))

/-- Consumer facing case 3 statement: if the original boundary word avoids the normal
subgroup `N`, then at least one of the two candidates produced by the cut avoids it. -/
theorem notMem_or_notMem_of_caseThree {N : Subgroup G} [N.Normal] {σ τ ν φ : G}
    (h : σ * τ * ν * φ ∉ N) : σ * ν⁻¹ ∉ N ∨ σ * φ * ν * τ ∉ N := by
  by_cases h₁ : σ * ν⁻¹ ∈ N
  · exact Or.inr fun h₂ => h (boundaryWord_mem_of_caseThree_mem h₁ h₂)
  · exact Or.inl h₁

/-- Consumer facing case 4 statement: if the original boundary word avoids the normal
subgroup `N`, then at least one of the two candidates produced by the cut avoids it. -/
theorem notMem_or_notMem_of_caseFour {N : Subgroup G} [N.Normal] {σ τ ν φ : G}
    (h : σ * τ * ν * φ ∉ N) : σ * ν ∉ N ∨ σ * τ⁻¹ * ν * φ⁻¹ ∉ N := by
  by_cases h₁ : σ * ν ∈ N
  · exact Or.inr fun h₂ => h (boundaryWord_mem_of_caseFour_mem h₁ h₂)
  · exact Or.inl h₁

/-- Two candidate selection.  Lemma 2 needs avoidance and strict descent for the *same*
candidate.  Given two candidates that both descend, an elimination identity for their
boundary words and an original boundary word avoiding `N`, some candidate both descends and
avoids `N`.  The descent side is an arbitrary predicate, so no geometry enters. -/
theorem exists_descends_and_notMem {α : Type*} {N : Subgroup G} {w : G} (descends : α → Prop)
    (word : α → G) (c₁ c₂ : α) (hd₁ : descends c₁) (hd₂ : descends c₂)
    (helim : word c₁ ∈ N → word c₂ ∈ N → w ∈ N) (hw : w ∉ N) :
    ∃ c, descends c ∧ word c ∉ N := by
  by_cases h₁ : word c₁ ∈ N
  · exact ⟨c₂, hd₂, fun h₂ => hw (helim h₁ h₂)⟩
  · exact ⟨c₁, hd₁, h₁⟩

/-- The numeric form of the two candidate selection, matching the complexity descent
consumers `NormalSingularSetTriangulation.complexity_lt_of_injective_origin` and
`NormalSingularSetTriangulation.complexity_lt_of_card_lt_of_equiv_compl`: take `n` to be the
complexity of the old triangulation and `complexity` the complexity of the triangulation
attached to a candidate. -/
theorem exists_complexity_lt_and_notMem {α : Type*} {N : Subgroup G} {w : G}
    (complexity : α → ℕ) (n : ℕ) (word : α → G) (c₁ c₂ : α) (hd₁ : complexity c₁ < n)
    (hd₂ : complexity c₂ < n) (helim : word c₁ ∈ N → word c₂ ∈ N → w ∈ N) (hw : w ∉ N) :
    ∃ c, complexity c < n ∧ word c ∉ N :=
  exists_descends_and_notMem (fun c => complexity c < n) word c₁ c₂ hd₁ hd₂ helim hw

/-- Two candidate selection for a case 3 cut: the elimination hypothesis is discharged by
`boundaryWord_mem_of_caseThree_mem`, so only the two candidate boundary words and the
descent of both candidates have to be supplied. -/
theorem exists_descends_and_notMem_caseThree {α : Type*} {N : Subgroup G} [N.Normal]
    {σ τ ν φ : G} (descends : α → Prop) (word : α → G) (c₁ c₂ : α) (hd₁ : descends c₁)
    (hd₂ : descends c₂) (hw₁ : word c₁ = σ * ν⁻¹) (hw₂ : word c₂ = σ * φ * ν * τ)
    (hw : σ * τ * ν * φ ∉ N) :
    ∃ c, descends c ∧ word c ∉ N :=
  exists_descends_and_notMem descends word c₁ c₂ hd₁ hd₂
    (fun h₁ h₂ => boundaryWord_mem_of_caseThree_mem (hw₁ ▸ h₁) (hw₂ ▸ h₂)) hw

/-- Two candidate selection for a case 4 cut: the elimination hypothesis is discharged by
`boundaryWord_mem_of_caseFour_mem`, so only the two candidate boundary words and the descent
of both candidates have to be supplied. -/
theorem exists_descends_and_notMem_caseFour {α : Type*} {N : Subgroup G} [N.Normal]
    {σ τ ν φ : G} (descends : α → Prop) (word : α → G) (c₁ c₂ : α) (hd₁ : descends c₁)
    (hd₂ : descends c₂) (hw₁ : word c₁ = σ * ν) (hw₂ : word c₂ = σ * τ⁻¹ * ν * φ⁻¹)
    (hw : σ * τ * ν * φ ∉ N) :
    ∃ c, descends c ∧ word c ∉ N :=
  exists_descends_and_notMem descends word c₁ c₂ hd₁ hd₂
    (fun h₁ h₂ => boundaryWord_mem_of_caseFour_mem (hw₁ ▸ h₁) (hw₂ ▸ h₂)) hw

/-- The case 3 selection through `conjugacyClassMeets`, the avoidance predicate carried by
`NormalSystem`.  A conjugacy class meets a normal subgroup exactly when one representative
lies in it, so avoidance of the class of the original boundary word forces avoidance of the
class of at least one candidate. -/
theorem not_conjugacyClassMeets_or_of_caseThree {N : Subgroup G} [N.Normal] (σ τ ν φ : G)
    (h : ¬conjugacyClassMeets (ConjClasses.mk (σ * τ * ν * φ)) N) :
    ¬conjugacyClassMeets (ConjClasses.mk (σ * ν⁻¹)) N ∨
      ¬conjugacyClassMeets (ConjClasses.mk (σ * φ * ν * τ)) N := by
  have hmk : ∀ g : G, conjugacyClassMeets (ConjClasses.mk g) N ↔ g ∈ N := fun g =>
    NormalSystem.conjugacyClassMeets_mk_iff_mem g N
  rcases notMem_or_notMem_of_caseThree (fun hm => h ((hmk _).mpr hm)) with h₁ | h₂
  · exact Or.inl fun hc => h₁ ((hmk _).mp hc)
  · exact Or.inr fun hc => h₂ ((hmk _).mp hc)

/-- The case 4 selection through `conjugacyClassMeets`, the avoidance predicate carried by
`NormalSystem`.  A conjugacy class meets a normal subgroup exactly when one representative
lies in it, so avoidance of the class of the original boundary word forces avoidance of the
class of at least one candidate. -/
theorem not_conjugacyClassMeets_or_of_caseFour {N : Subgroup G} [N.Normal] (σ τ ν φ : G)
    (h : ¬conjugacyClassMeets (ConjClasses.mk (σ * τ * ν * φ)) N) :
    ¬conjugacyClassMeets (ConjClasses.mk (σ * ν)) N ∨
      ¬conjugacyClassMeets (ConjClasses.mk (σ * τ⁻¹ * ν * φ⁻¹)) N := by
  have hmk : ∀ g : G, conjugacyClassMeets (ConjClasses.mk g) N ↔ g ∈ N := fun g =>
    NormalSystem.conjugacyClassMeets_mk_iff_mem g N
  rcases notMem_or_notMem_of_caseFour (fun hm => h ((hmk _).mpr hm)) with h₁ | h₂
  · exact Or.inl fun hc => h₁ ((hmk _).mp hc)
  · exact Or.inr fun hc => h₂ ((hmk _).mp hc)

/-- Two candidate selection phrased through `conjugacyClassMeets`.  This is the form a
Lemma 2 surgery producer consumes: the avoidance hypothesis it carries is avoidance of a
conjugacy class, and the conclusion delivers one candidate that both descends and whose
boundary class still avoids the normal subgroup. -/
theorem exists_descends_and_not_conjugacyClassMeets {α : Type*} {N : Subgroup G} [N.Normal]
    {w : G} (descends : α → Prop) (word : α → G) (c₁ c₂ : α) (hd₁ : descends c₁)
    (hd₂ : descends c₂) (helim : word c₁ ∈ N → word c₂ ∈ N → w ∈ N)
    (hw : ¬conjugacyClassMeets (ConjClasses.mk w) N) :
    ∃ c, descends c ∧ ¬conjugacyClassMeets (ConjClasses.mk (word c)) N := by
  have hmk : ∀ g : G, conjugacyClassMeets (ConjClasses.mk g) N ↔ g ∈ N := fun g =>
    NormalSystem.conjugacyClassMeets_mk_iff_mem g N
  obtain ⟨c, hc, hcn⟩ := exists_descends_and_notMem descends word c₁ c₂ hd₁ hd₂ helim
    (fun hm => hw ((hmk w).mpr hm))
  exact ⟨c, hc, fun hmeet => hcn ((hmk (word c)).mp hmeet)⟩

end DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordElimination
