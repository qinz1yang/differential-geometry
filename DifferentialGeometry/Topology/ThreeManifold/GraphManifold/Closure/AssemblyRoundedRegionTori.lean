import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionTorusParam
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionFibrationApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyHalfCollarApplications

/-!
# FC42 packet T3: the boundary tori of the rounded circle region, their collars and owners

Review 40 §3.3 (T3) with the binding additions of review 42 (§4.4, §4.5, §5.3 "second").

* `exists_levelTorus_seams`: all level tori `T_c` (the boundary components of the rounded circle
  region, part 2) at once, with pairwise DISJOINT two-sided collars inside any prescribed open
  neighbourhood `V` of the new zero level `Z_R` (e.g. the protected neighbourhood of the shrunk ports,
  `exists_shrinkPorts_protectedNhds`), and `rounding ∘ proj (S_c (t, s)) = δ_c s`;
* `exists_levelTorus_subset_range_roundedRegionPiece`: each level torus lies in exactly one rounded
  piece `P_j` (its NEGATIVE-side owner), and `exists_negative_halfCollar` gives the half-collar lift
  of the collar's negative side into that piece;
* `exists_superlevel_halfCollar_owner`, `exists_positive_halfCollar_lift` (POSITIVE-side owner, review
  42 binding point 2): for a parameter family `Q` of pieces covering the closed superlevel side of a
  regular level inside an open set `U` around the collar, contained in it, and pairwise disjoint
  inside `U`, ONE fixed piece `Q k` owns the WHOLE positive half collar, with its half-collar lift.
  What T4 must supply: such a family (the cycle unions, non-ball vertices and edge-circle pieces),
  disjoint near `Z_R`; the B1-complement pieces are an instance (consumer file);
* `exists_boundaryTori_roundedRegionPiece`, `rawPiece_of_roundedRegionPiece`: the boundary tori of
  each piece `P_j` with half collars in the piece, exhausting `∂P_j`; hence every rounded piece is a
  Raw piece in the `hpiece` format of B3 (`exists_rawGraphPresentation_of_regularCutData`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-! ## The positive-side owner (generic) -/

section Owner

variable {W : CompactCarrier.{u}}

/-- **Positive-side owner.** Let `S` be a torus seam whose collar lies in an open set `U` with
`f (S (t, s)) = c + δ s`. A finite family of pieces that covers the closed superlevel side
`{c ≤ f}` inside `U`, lies in it inside `U`, and is pairwise disjoint inside `U`, has ONE member
`Q k` which meets the collar exactly in the whole positive half collar. -/
theorem exists_superlevel_halfCollar_owner {U : Set W.Carrier} {f : W.Carrier → ℝ} {c : ℝ}
    {m : ℕ} (Q : Fin m → PieceEmbedding W)
    (hcov : ∀ x ∈ U, c ≤ f x → x ∈ ⋃ k, range (Q k).map)
    (hsub : ∀ k, ∀ x ∈ range (Q k).map, x ∈ U → c ≤ f x)
    (hdisj : Pairwise fun k k' => Disjoint (range (Q k).map ∩ U) (range (Q k').map ∩ U))
    (S : TorusSeam W) {δ : ℝ} (hδ : 0 < δ) (hSU : S.collar.target ⊆ U)
    (hval : ∀ p ∈ signedCollarSource, f (S.collar p) = c + δ * p.2) :
    ∃ k, range (Q k).map ∩ S.collar.target =
      S.collar '' {p | p ∈ signedCollarSource ∧ (if false then p.2 ≤ 0 else 0 ≤ p.2)} := by
  classical
  let N : Set (Torus × ℝ) := {p | p ∈ signedCollarSource ∧ (if false then p.2 ≤ 0 else 0 ≤ p.2)}
  have hNsrc : N ⊆ S.collar.source := fun p hp => S.source_eq ▸ hp.1
  have hNU : ∀ p ∈ N, S.collar p ∈ U := fun p hp => hSU (S.collar.map_source (hNsrc hp))
  have hNf : ∀ p ∈ N, c ≤ f (S.collar p) := by
    intro p hp
    rw [hval p hp.1]
    have h2 : 0 ≤ p.2 := hp.2
    nlinarith
  have hNconn : IsPreconnected (S.collar '' N) := by
    have hN : N = univ ×ˢ Ico (0 : ℝ) 1 := by
      ext p
      simp only [N, signedCollarSource, mem_ofPred_eq, Bool.false_eq_true, ite_false, mem_prod,
        mem_univ, mem_Ico, true_and]
      constructor
      · rintro ⟨⟨-, h1⟩, h2⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by linarith, h2⟩, h1⟩
    have hpc : IsPreconnected N := by
      rw [hN]
      exact isPreconnected_univ.prod isPreconnected_Ico
    exact hpc.image _ (S.collar.contMDiffOn_toFun.continuousOn.mono hNsrc)
  let t₀ : Torus := (1, 1)
  have h0N : ((t₀, 0) : Torus × ℝ) ∈ N := by
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    change (0 : ℝ) ≤ 0
    exact le_rfl
  obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov _ (hNU _ h0N) (hNf _ h0N))
  refine ⟨k, ?_⟩
  have hsubk : S.collar '' N ⊆ range (Q k).map := by
    let t' : Set W.Carrier := ⋃ k' ∈ ({k}ᶜ : Set (Fin m)), range (Q k').map
    have hclosed : ∀ k', IsClosed (range (Q k').map) := fun k' => (Q k').isClosed_range
    have ht' : IsClosed t' := (Set.toFinite _).isClosed_biUnion fun k' _ => hclosed k'
    have hsub' : S.collar '' N ⊆ range (Q k).map ∪ t' := by
      rintro _ ⟨p', hp', rfl⟩
      obtain ⟨k', hk'⟩ := mem_iUnion.mp (hcov _ (hNU p' hp') (hNf p' hp'))
      by_cases hkk : k' = k
      · exact Or.inl (hkk ▸ hk')
      · exact Or.inr (mem_biUnion (show k' ∈ ({k}ᶜ : Set (Fin m)) from hkk) hk')
    intro y hy
    by_contra hnot
    obtain ⟨z, hzN, hzk, hzt⟩ := isPreconnected_closed_iff.mp hNconn _ _ (hclosed k) ht' hsub'
      ⟨_, ⟨_, h0N, rfl⟩, hk⟩ ⟨y, hy, (hsub' hy).resolve_left hnot⟩
    obtain ⟨k', hk', hzk'⟩ := mem_iUnion₂.mp hzt
    obtain ⟨p, hp, rfl⟩ := hzN
    exact (hdisj (show k ≠ k' from fun h => hk' (h ▸ rfl))).le_bot
      ⟨⟨hzk, hNU p hp⟩, ⟨hzk', hNU p hp⟩⟩
  ext y
  constructor
  · rintro ⟨hyQ, hyT⟩
    have hsrc : S.collar.invFun y ∈ signedCollarSource := S.source_eq ▸ S.collar.map_target' hyT
    refine ⟨S.collar.invFun y, ⟨hsrc, ?_⟩, S.collar.right_inv' hyT⟩
    have hf := hsub k y hyQ (hSU hyT)
    have hv := hval _ hsrc
    rw [show S.collar (S.collar.invFun y) = y from S.collar.right_inv' hyT] at hv
    change 0 ≤ (S.collar.invFun y).2
    by_contra hneg
    have hneg' := not_le.mp hneg
    nlinarith
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hsubk ⟨p, hp, rfl⟩, S.collar.map_source (hNsrc hp)⟩

/-- **Positive-side owner with its half-collar lift.** -/
theorem exists_positive_halfCollar_lift {U : Set W.Carrier} {f : W.Carrier → ℝ} {c : ℝ}
    {m : ℕ} (Q : Fin m → PieceEmbedding W)
    (hcov : ∀ x ∈ U, c ≤ f x → x ∈ ⋃ k, range (Q k).map)
    (hsub : ∀ k, ∀ x ∈ range (Q k).map, x ∈ U → c ≤ f x)
    (hdisj : Pairwise fun k k' => Disjoint (range (Q k).map ∩ U) (range (Q k').map ∩ U))
    (S : TorusSeam W) {δ : ℝ} (hδ : 0 < δ) (hSU : S.collar.target ⊆ U)
    (hval : ∀ p ∈ signedCollarSource, f (S.collar p) = c + δ * p.2) :
    ∃ (k : Fin m)
      (L : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) (Q k).Piece ∞),
      L.source = halfCollarSource ∧ L.target = (Q k).map ⁻¹' S.collar.target ∧
      (∀ t, (𝓡∂ 3).IsBoundaryPoint (L (t, halfZero))) ∧
      ∀ t s (hs : 0 ≤ s), s < 1 → (Q k).map (L (t, halfPoint s hs)) = S.collar (t, s) := by
  obtain ⟨k, hk⟩ := exists_superlevel_halfCollar_owner Q hcov hsub hdisj S hδ hSU hval
  obtain ⟨L, hsrc, htgt, hbd, heq⟩ := exists_halfCollar_of_torusSeam_of_range S (Q k) false hk
  exact ⟨k, L, hsrc, htgt, hbd, fun t s hs hs1 => heq t s hs hs1⟩

end Owner

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-! ## All level tori at once -/

/-- Pairwise disjoint open neighbourhoods of the level tori. -/
theorem exists_disjoint_nhds_levelTorus :
    ∃ N : ConnectedComponents R.BaseLevel → Set W.Carrier, (∀ c, IsOpen (N c)) ∧
      (∀ c, R.levelTorus c ⊆ N c) ∧ Pairwise fun c c' => Disjoint (N c) (N c') := by
  classical
  have hsep : ∀ c c' : ConnectedComponents R.BaseLevel, c ≠ c' →
      SeparatedNhds (R.levelTorus c) (R.levelTorus c') := fun c c' h =>
    SeparatedNhds.of_isCompact_isCompact (R.isCompact_levelTorus c) (R.isCompact_levelTorus c')
      (R.pairwise_disjoint_levelTorus h)
  choose A B hA hB hcA hcB hAB using hsep
  refine ⟨fun c => (⋂ (d : ConnectedComponents R.BaseLevel) (h : c ≠ d), A c d h) ∩
      ⋂ (d : ConnectedComponents R.BaseLevel) (h : d ≠ c), B d c h, fun c => ?_, fun c => ?_,
      fun c c' hcc' => ?_⟩
  · exact (isOpen_iInter_of_finite fun d => isOpen_iInter_of_finite fun h => hA c d h).inter
      (isOpen_iInter_of_finite fun d => isOpen_iInter_of_finite fun h => hB d c h)
  · exact subset_inter (subset_iInter₂ fun d h => hcA c d h) (subset_iInter₂ fun d h => hcB d c h)
  · exact (hAB c c' hcc').mono (inter_subset_left.trans (iInter₂_subset c' hcc'))
      (inter_subset_right.trans (iInter₂_subset c hcc'))

/-- **The boundary tori of the rounded region with pairwise disjoint two-sided collars**, inside any
prescribed open neighbourhood `V` of the new zero level. -/
theorem exists_levelTorus_seams (V : Set W.Carrier) (hV : IsOpen V) (hZV : R.roundedLevel ⊆ V) :
    ∃ (δ : ConnectedComponents R.BaseLevel → ℝ) (S : ConnectedComponents R.BaseLevel → TorusSeam W),
      (∀ c, 0 < δ c) ∧ (∀ c, (S c).collar.target ⊆ V ∩ R.domain) ∧
      (∀ c, range (fun t => (S c).collar (t, 0)) = R.levelTorus c) ∧
      Pairwise (fun c c' => Disjoint (S c).collar.target (S c').collar.target) ∧
      ∀ c, ∀ p ∈ signedCollarSource, R.roundedFunction ((S c).collar p) = δ c * p.2 := by
  obtain ⟨N, hNo, hTN, hNd⟩ := R.exists_disjoint_nhds_levelTorus
  have h := fun c => R.exists_levelTorus_seam c (V ∩ N c) (hV.inter (hNo c))
    (subset_inter ((R.levelTorus_subset_roundedLevel c).trans hZV) (hTN c))
  choose δ hδ S hS hrange hval using h
  refine ⟨δ, S, hδ, fun c x hx => ⟨(hS c hx).1.1, (hS c hx).2⟩, hrange, fun c c' hcc' => ?_, hval⟩
  exact (hNd hcc').mono (fun x hx => (hS c hx).1.2) (fun x hx => (hS c' hx).1.2)

/-! ## The negative side: the rounded pieces -/

/-- Each level torus lies in a rounded piece. -/
theorem exists_levelTorus_subset_range_roundedRegionPiece (c : ConnectedComponents R.BaseLevel) :
    ∃ j, R.levelTorus c ⊆ range (R.roundedRegionPiece j).map := by
  classical
  obtain ⟨x, hx⟩ := (R.isConnected_levelTorus c).nonempty
  have hxr : x ∈ ⋃ j, range (R.roundedRegionPiece j).map := by
    rw [R.iUnion_range_roundedRegionPiece]
    exact R.roundedLevel_subset_rounded (R.levelTorus_subset_roundedLevel c hx)
  obtain ⟨j, hj⟩ := mem_iUnion.mp hxr
  refine ⟨j, ?_⟩
  let t' : Set W.Carrier := ⋃ j' ∈ ({j}ᶜ : Set (ConnectedComponents R.roundedBase)),
    range (R.roundedRegionPiece j').map
  have hclosed : ∀ j', IsClosed (range (R.roundedRegionPiece j').map) := fun j' =>
    (R.roundedRegionPiece j').isClosed_range
  have ht' : IsClosed t' := (Set.toFinite _).isClosed_biUnion fun j' _ => hclosed j'
  have hsub : R.levelTorus c ⊆ range (R.roundedRegionPiece j).map ∪ t' := by
    intro y hy
    have hyr : y ∈ ⋃ j, range (R.roundedRegionPiece j).map := by
      rw [R.iUnion_range_roundedRegionPiece]
      exact R.roundedLevel_subset_rounded (R.levelTorus_subset_roundedLevel c hy)
    obtain ⟨j', hj'⟩ := mem_iUnion.mp hyr
    by_cases hjj : j' = j
    · exact Or.inl (hjj ▸ hj')
    · exact Or.inr (mem_biUnion (show j' ∈ ({j}ᶜ : Set (ConnectedComponents R.roundedBase)) from hjj)
        hj')
  intro y hy
  by_contra hnot
  obtain ⟨z, -, hzj, hzt⟩ := isPreconnected_closed_iff.mp (R.isConnected_levelTorus c).isPreconnected
    _ _ (hclosed j) ht' hsub ⟨x, hx, hj⟩ ⟨y, hy, (hsub hy).resolve_left hnot⟩
  obtain ⟨j', hj', hzj'⟩ := mem_iUnion₂.mp hzt
  exact (R.pairwise_disjoint_range_roundedRegionPiece (show j ≠ j' from fun h => hj' (h ▸ rfl))).le_bot
    ⟨hzj, hzj'⟩

/-- **Negative-side half collar.** For a torus seam whose collar lies in the domain with
`rounding ∘ proj (S (t, s)) = δ s`, the rounded piece containing a point of its zero section meets the
collar exactly in the negative half collar and carries its half-collar lift. -/
theorem exists_negative_halfCollar (S : TorusSeam W) {δ : ℝ} (hδ : 0 < δ)
    (hSd : S.collar.target ⊆ R.domain)
    (hval : ∀ p ∈ signedCollarSource, R.roundedFunction (S.collar p) = δ * p.2)
    (j : ConnectedComponents R.roundedBase) (t₀ : Torus)
    (hj : S.collar (t₀, 0) ∈ range (R.roundedRegionPiece j).map) :
    ∃ L : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
        (R.roundedRegionPiece j).Piece ∞,
      L.source = halfCollarSource ∧ L.target = (R.roundedRegionPiece j).map ⁻¹' S.collar.target ∧
      (∀ t, (𝓡∂ 3).IsBoundaryPoint (L (t, halfZero))) ∧
      ∀ t s (hs : 0 ≤ s), s < 1 →
        (R.roundedRegionPiece j).map (L (t, halfPoint s hs)) = S.collar (t, -s) := by
  classical
  let e := Finite.equivFin (ConnectedComponents R.roundedBase)
  obtain ⟨k, rfl⟩ := e.symm.surjective j
  let P : Fin (Nat.card (ConnectedComponents R.roundedBase)) → PieceEmbedding W :=
    fun k => R.roundedRegionPiece (e.symm k)
  have hunion : (⋃ k, range (P k).map) = {x | x ∈ R.domain ∧ R.roundedFunction x ≤ 0} := by
    rw [← R.rounded_eq_sublevel, ← R.iUnion_range_roundedRegionPiece]
    exact e.symm.surjective.iUnion_comp fun j => range (R.roundedRegionPiece j).map
  have hdisj : Pairwise fun k k' => Disjoint (range (P k).map) (range (P k').map) :=
    fun k k' hkk' => R.pairwise_disjoint_range_roundedRegionPiece (e.symm.injective.ne hkk')
  have hval' : ∀ p ∈ signedCollarSource, R.roundedFunction (S.collar p) = 0 + δ * p.2 :=
    fun p hp => (hval p hp).trans (zero_add _).symm
  have hrange := halfCollar_range_eq_of_sublevelPieces P hunion hdisj S hδ hSd hval' k t₀ hj
  obtain ⟨L, hsrc, htgt, hbd, heq⟩ := exists_halfCollar_of_torusSeam_of_range S (P k) true hrange
  exact ⟨L, hsrc, htgt, hbd, fun t s hs hs1 => heq t s hs hs1⟩

/-! ## The boundary tori of a rounded piece and its Raw presentation -/

/-- **Boundary tori of a rounded piece.** Every rounded piece carries a family of boundary tori with
half collars in the piece exhausting its boundary. -/
theorem exists_boundaryTori_roundedRegionPiece (j : ConnectedComponents R.roundedBase) :
    ∃ (n : ℕ) (E : BoundaryTori (R.roundedRegionPiece j).toCarrier n),
      (R.roundedRegionPiece j).toCarrier.model.boundary (R.roundedRegionPiece j).toCarrier.Carrier =
        E.image := by
  classical
  obtain ⟨δ, S, hδ, hS, hrange, hdisjS, hval⟩ :=
    R.exists_levelTorus_seams univ isOpen_univ (subset_univ _)
  let P := R.roundedRegionPiece j
  -- the level tori owned by `P`
  let Own := {c : ConnectedComponents R.BaseLevel // R.levelTorus c ⊆ range P.map}
  have hzero : ∀ c t, (S c).collar (t, 0) ∈ R.levelTorus c := fun c t => by
    rw [← hrange c]
    exact mem_range_self t
  have hL : ∀ c : Own, ∃ L : PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) P.Piece ∞,
      L.source = halfCollarSource ∧ L.target = P.map ⁻¹' (S c.1).collar.target ∧
      (∀ t, (𝓡∂ 3).IsBoundaryPoint (L (t, halfZero))) ∧
      ∀ t s (hs : 0 ≤ s), s < 1 → P.map (L (t, halfPoint s hs)) = (S c.1).collar (t, -s) :=
    fun c => R.exists_negative_halfCollar (S c.1) (hδ c.1) (fun x hx => (hS c.1 hx).2) (hval c.1) j
      (1, 1) (c.2 (hzero c.1 (1, 1)))
  choose L hLsrc hLtgt hLbd hLeq using hL
  let eo := Finite.equivFin Own
  have hbdry : ∀ (c : Own) (t : Torus), P.map (L c (t, halfZero)) = (S c.1).collar (t, 0) := by
    intro c t
    have h := hLeq c t 0 le_rfl one_pos
    rw [neg_zero] at h
    exact h
  refine ⟨Nat.card Own, ⟨fun i => L (eo.symm i), fun i => hLsrc (eo.symm i),
    fun i t => hLbd (eo.symm i) t, fun i i' hii' => ?_⟩, ?_⟩
  · change Disjoint (L (eo.symm i)).target (L (eo.symm i')).target
    rw [hLtgt, hLtgt]
    exact (hdisjS (fun h => hii' (eo.symm.injective (Subtype.ext h)))).preimage P.map
  · ext q
    constructor
    · intro hq
      have hq' : (𝓡∂ 3).IsBoundaryPoint (show P.Piece from q) := hq
      rw [roundedRegionPiece_isBoundaryPoint_iff] at hq'
      have hZ : P.map q ∈ R.roundedLevel := by
        rw [R.roundedLevel_eq]
        exact ⟨R.roundedRegionPiece_map_mem_domain j q, hq'⟩
      rw [← R.iUnion_levelTorus] at hZ
      obtain ⟨c, hc⟩ := mem_iUnion.mp hZ
      obtain ⟨j', hj'⟩ := R.exists_levelTorus_subset_range_roundedRegionPiece c
      have hjj : j' = j := by
        by_contra hne
        exact (R.pairwise_disjoint_range_roundedRegionPiece hne).le_bot
          ⟨hj' hc, mem_range_self q⟩
      subst hjj
      let c' : Own := ⟨c, hj'⟩
      rw [← hrange c] at hc
      obtain ⟨t, ht⟩ := hc
      refine mem_iUnion.mpr ⟨eo c', t, ?_⟩
      apply P.injective
      change P.map (L (eo.symm (eo c')) (t, halfZero)) = P.map q
      rw [eo.symm_apply_apply, hbdry c' t]
      exact ht
    · intro hq
      obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hq
      exact hLbd (eo.symm i) t

/-- **Every rounded piece is a Raw piece** in the `hpiece` format of B3. -/
theorem rawPiece_of_roundedRegionPiece (j : ConnectedComponents R.roundedBase) :
    ∃ X : CompactCarrier.{u}, Nonempty (RawGraphPresentation X) ∧
      Nonempty (X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (R.roundedRegionPiece j).Piece) := by
  obtain ⟨n, E, hb⟩ := R.exists_boundaryTori_roundedRegionPiece j
  exact R.rawPiece_of_roundedRegionPiece_of_boundaryTori j E hb

end CircleRegion

end GC.GraphManifold.Assembly
