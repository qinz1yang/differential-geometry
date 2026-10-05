import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyBoundaryApplications

/-!
# FC42 packet T4b, part 1: a regular cut from injective pieces

`exists_regularCutData_of_pieceEmbeddings` assembles a `RegularCutData W E` (B3 input) from
set-level data on finitely many INJECTIVE pieces:

* the pieces cover `W`;
* two-sided torus seams with pairwise disjoint collars, and for each seam side `b` a piece meeting
  the collar exactly in the closed side-`b` half collar (B2-side gives the lift);
* for each port a piece containing its collar target (B2 for ports gives the external lift);
* the model boundary of each piece lies on the zero tori of the seams it is a side of and on the
  ports it owns;
* two different pieces meet only on seam zero tori; the ports are the whole boundary of `W` and
  their collars avoid the seam collars.

The index types are arbitrary finite types; the lifts are chosen after reindexing by `Fin`, so no
transport of lifts along index equalities is needed.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **A regular cut from injective pieces.** -/
theorem exists_regularCutData_of_pieceEmbeddings {W : CompactCarrier.{u}} [Nonempty W.Carrier]
    {n : ℕ} (E : BoundaryTori W n) {ι σ : Type*} [Finite ι] [Finite σ]
    (Q : ι → PieceEmbedding W) (hcov : ⋃ j, range (Q j).map = univ)
    (S : σ → TorusSeam W)
    (hSdisj : Pairwise fun c d => Disjoint (S c).collar.target (S d).collar.target)
    (side : σ → Bool → ι)
    (hside : ∀ c b, range (Q (side c b)).map ∩ (S c).collar.target =
      (S c).collar '' {p | p ∈ signedCollarSource ∧ if b then p.2 ≤ 0 else 0 ≤ p.2})
    (own : Fin n → ι) (hown : ∀ i, (E.collar i).target ⊆ range (Q (own i)).map)
    (hbd : ∀ j (q : (Q j).Piece), (𝓡∂ 3).IsBoundaryPoint q →
      (∃ c b t, side c b = j ∧ (Q j).map q = (S c).collar (t, 0)) ∨
        (∃ i t, own i = j ∧ (Q j).map q = E.torusMap i t))
    (hover : ∀ j j', j ≠ j' → range (Q j).map ∩ range (Q j').map ⊆
      ⋃ c, range fun t => (S c).collar (t, 0))
    (hext : W.model.boundary W.Carrier = E.image)
    (hES : ∀ i c, Disjoint (E.collar i).target (S c).collar.target) :
    ∃ R : RegularCutData W E, ∀ j, ∃ j', R.piece j = (Q j').toPieceFold := by
  classical
  let eι := Finite.equivFin ι
  let eσ := Finite.equivFin σ
  have hL : ∀ (c : Fin (Nat.card σ)) (b : Bool), ∃ L : PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) (Q (eι.symm (eι (side (eσ.symm c) b)))).Piece ∞,
      L.source = halfCollarSource ∧ (∀ t, (𝓡∂ 3).IsBoundaryPoint (L (t, halfZero))) ∧
      ∀ t s (hs : 0 ≤ s), s < 1 →
        (Q (eι.symm (eι (side (eσ.symm c) b)))).map (L (t, halfPoint s hs)) =
          (S (eσ.symm c)).collar (t, if b then -s else s) := by
    intro c b
    obtain ⟨L, hsrc, -, hbdL, heq⟩ := exists_halfCollar_of_torusSeam_of_range (S (eσ.symm c))
      (Q (eι.symm (eι (side (eσ.symm c) b)))) b (by rw [Equiv.symm_apply_apply]; exact hside _ b)
    exact ⟨L, hsrc, hbdL, heq⟩
  choose L hLsrc hLbd hLeq using hL
  have hX : ∀ i : Fin n, ∃ L : PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) (Q (eι.symm (eι (own i)))).Piece ∞,
      L.source = halfCollarSource ∧ (∀ t, (𝓡∂ 3).IsBoundaryPoint (L (t, halfZero))) ∧
      ∀ p ∈ halfCollarSource, (Q (eι.symm (eι (own i)))).map (L p) = E.collar i p := by
    intro i
    obtain ⟨L, hsrc, -, hbdL, heq⟩ := exists_halfCollar_of_target_subset_range
      (Q (eι.symm (eι (own i)))) (E.collar i) (E.source_eq i)
      (by rw [Equiv.symm_apply_apply]; exact hown i)
    exact ⟨L, hsrc, hbdL, heq⟩
  choose X hXsrc hXbd hXeq using hX
  have hne : Nonempty ι := by
    obtain ⟨x⟩ := ‹Nonempty W.Carrier›
    have hx : x ∈ ⋃ j, range (Q j).map := hcov ▸ mem_univ x
    obtain ⟨j, -⟩ := mem_iUnion.mp hx
    exact ⟨j⟩
  have hcast : ∀ {j₁ j : Fin (Nat.card ι)} (h : j₁ = j) (q : (Q (eι.symm j)).Piece)
      (q₁ : (Q (eι.symm j₁)).Piece), (Q (eι.symm j)).map q = (Q (eι.symm j₁)).map q₁ →
        q = h ▸ q₁ := by
    intro j₁ j h q q₁ hqq
    subst h
    exact (Q (eι.symm j₁)).injective hqq
  refine ⟨{
    count := Nat.card ι
    count_pos := Nat.card_pos
    piece := fun j => (Q (eι.symm j)).toPieceFold
    covers := (eι.symm.surjective.iUnion_comp fun j => range (Q j).map).trans hcov
    seamCount := Nat.card σ
    seam := fun c => S (eσ.symm c)
    seam_disjoint := fun c d hcd => hSdisj (eσ.symm.injective.ne hcd)
    side := fun c b => eι (side (eσ.symm c) b)
    lift := L
    lift_source := hLsrc
    lift_eq := hLeq
    externalOwner := fun i => eι (own i)
    externalLift := X
    externalLift_source := hXsrc
    externalLift_eq := hXeq
    boundary_exhausted := ?_
    overlap := ?_
    external_exhausted := hext
    external_seam_disjoint := fun i c => hES i _ }, fun j => ⟨eι.symm j, rfl⟩⟩
  · intro j
    ext q
    constructor
    · intro hq
      rcases hbd (eι.symm j) q hq with ⟨c, b, t, hcb, hqc⟩ | ⟨i, t, hi, hqi⟩
      · left
        have h : eι (side (eσ.symm (eσ c)) b) = j := by
          rw [Equiv.symm_apply_apply, hcb, Equiv.apply_symm_apply]
        refine ⟨eσ c, b, t, h, hcast h q _ ?_⟩
        rw [hqc]
        refine Eq.trans ?_ (hLeq (eσ c) b t 0 le_rfl one_pos).symm
        rw [Equiv.symm_apply_apply]
        cases b
        · rfl
        · simp only [ite_true, neg_zero]
      · right
        have h : eι (own i) = j := by rw [hi, Equiv.apply_symm_apply]
        refine ⟨i, t, h, hcast h q _ ?_⟩
        rw [hqi]
        exact (hXeq i (t, halfZero) (zero_mem_halfCollarSource t)).symm
    · rintro (⟨c, b, t, h, rfl⟩ | ⟨i, t, h, rfl⟩)
      · subst h
        exact hLbd c b t
      · subst h
        exact hXbd i t
  · intro j j' q q' hqq
    by_cases hjj : j = j'
    · subst hjj
      left
      rw [(Q (eι.symm j)).injective hqq]
    · right
      have hx := hover (eι.symm j) (eι.symm j') (eι.symm.injective.ne hjj)
        ⟨mem_range_self q, ⟨q', hqq.symm⟩⟩
      obtain ⟨c, t, ht⟩ := mem_iUnion.mp hx
      refine ⟨eσ c, t, ?_⟩
      rw [Equiv.symm_apply_apply]
      exact ht.symm

end GC.GraphManifold.Assembly
