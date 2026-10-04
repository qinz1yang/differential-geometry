import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Normalize
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardFactorOrientation
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.SphericalSpaceFormOrientationClosure
import DifferentialGeometry.Compat.Ch567.Topology.ThreeManifold.ConnectedSum.OppositeSumOrientation

/-!
# The split move M2 of the (S⁺) normalization

Lane N2 of `Seifert/Normalize.lean`. Let `j` be a split seam on side `b` of an elementary
presentation `E` of a closed `Q`: `V = seamPiece j b` is a solid torus `D² × S¹`, the host
`H = hostPiece j b` is `P × S¹` over a pants with boundary circles `c₀` (seam `j`), `c₁`, `c₂`,
and the meridian of `V` goes to the fibre of `H` (`IsSplitSeam.meridian_eq_fiber_true`,
`IsSplitSeam.meridian_eq_fiber_false`: `Δ = 0` forces equality of slopes).

The model. Let `γ ⊂ P` be a proper arc with both ends `a, b'` on `c₀` separating `c₁` from `c₂`,
cutting `P` into annuli `P₁ ∋ c₁` and `P₂ ∋ c₂`, and `c₀` into arcs `α₁, α₂`. The core of `V` runs
along `c₀` (its meridian is the fibre), so `V = D² × c₀` and the meridian discs over `a, b'` cut
it into the balls `D² × αᵢ`. The sphere `S = D_a ∪ γ × S¹ ∪ D_b'` cuts `R = H ∪ V` into
`Pᵢ × S¹ ∪ D² × αᵢ`; capping `S` turns this into `Pᵢ × S¹` filled along the fibre of its outer
torus, a solid torus `Vᵢ` with `∂Vᵢ = cᵢ × S¹` and meridian the fibre. So `R ≅ V₁ # V₂` rel `∂`.
Checks: `D² × S¹` filled along its fibre is `S³` (the fibre is a longitude, `Δ(μ_V, μ) = 1`),
not `S² × S¹`; `A × S¹` filled along the fibre on one side is the solid torus above, and on both
sides `S² × S¹`; `P × S¹` filled along the fibre on all three sides is `#² S² × S¹`.

The surgery. `V` touches only seam `j` (`eq_of_seamPiece_eq_of_isSplitSeam`), the host owns
exactly two further sides, both seam sides `s₁ ≠ s₂` of `Q` (`exists_hostPorts`), and the other
seams `O` number `n - 3` when `s₁, s₂` are different seams. If `S` separates, `Q ≅ A # B` with
`A = X₁ ∪_{s₁} V₁`, `B = X₂ ∪_{s₂} V₂` and counts `n_A + n_B = n - 1`; otherwise
`Q ≅ Q′ # S² × S¹`, `Q′ = X ∪_{s₁} V₁ ∪_{s₂} V₂`, `n′ = n - 1` (a self-seam `s₁ = s₂` of `H`
gives `Q′ = V₁ ∪ V₂`, `n = 2`). The library cannot yet build `A`, `B`, `Q′`: there is no gluing
constructor producing a closed manifold from a cut carrier and a pairing (presentations are only
of given manifolds), no connected sum of manifolds with boundary, and the fibre filling `p = 0`
is outside the `ConeFilling` models (`p ≥ 1`). This construction is the named input
`FibreFillingSphereSurgery`, stated with unoriented diffeomorphisms and exact counts.

`moveSplit_of_fibreFillingSphereSurgery` derives `MoveSplit`. Elementary presentations transport
along every diffeomorphism of closed manifolds with the same count
(`ElementaryPresentation.transport`, `.opposite`, `exists_of_diffeomorph`), keeping split seams
(`isSplitSeam_transport`, `isSplitSeam_opposite`); an orientation
reversing identification `Q ≅ A # B` is replaced by `Q ≅ A̅ # B̅` (`connectedSum_opposite`), and
`S² × S¹` and its opposite are standard factors (`isStandardFactor_ulift`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace ElementaryPresentation

section Transport

variable {W W' : CompactCarrier.{u}}

def transport (E : ElementaryPresentation W) (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) : ElementaryPresentation W' where
  toTorus := E.toTorus.transport e he
  kind := E.kind
  kind_mem := E.kind_mem
  piece i := (E.piece i).transport e he

def opposite (E : ElementaryPresentation W) : ElementaryPresentation W.opposite where
  toTorus := E.toTorus.opposite
  kind := E.kind
  kind_mem := E.kind_mem
  piece i := (E.piece i).opposite

@[simp]
theorem complexity_transport (E : ElementaryPresentation W)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) :
    (E.transport e he).complexity = E.complexity := rfl

@[simp]
theorem complexity_opposite (E : ElementaryPresentation W) :
    E.opposite.complexity = E.complexity := rfl

theorem isSplitSeam_transport (E : ElementaryPresentation W)
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation)
    (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.transport e he).IsSplitSeam j b ↔ E.IsSplitSeam j b := Iff.rfl

theorem isSplitSeam_opposite (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count)
    (b : Bool) : E.opposite.IsSplitSeam j b ↔ E.IsSplitSeam j b := Iff.rfl

end Transport

theorem exists_of_diffeomorph {M N : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier M)) (f : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier) :
    ∃ E' : ElementaryPresentation (NoCuts.carrier N), E'.complexity = E.complexity := by
  rcases f.preservesOrientation_or_preservesOrientation_opposite
    M.orientation N.orientation with hf | hf
  · exact ⟨E.transport f hf, rfl⟩
  · have hp : f.preservesOrientation M.orientation.opposite N.orientation := by
      simpa only [ManifoldOrientation.opposite_opposite] using
        Diffeomorph.preservesOrientation_opposite hf
    exact ⟨E.opposite.transport (W' := NoCuts.carrier N) f hp, rfl⟩

section Seams

variable {W : CompactCarrier.{u}}

theorem IsSplitSeam.meridian_eq_fiber_true {E : ElementaryPresentation W}
    {j : Fin E.toTorus.pairing.count} (h : E.IsSplitSeam j true) :
    torusUnit (E.toTorus.pairing.matching j) • meridianSlope = fiberSlope :=
  (PrimitiveSlope.delta_eq_zero_iff _ _).1 h.2.2

theorem IsSplitSeam.meridian_eq_fiber_false {E : ElementaryPresentation W}
    {j : Fin E.toTorus.pairing.count} (h : E.IsSplitSeam j false) :
    (torusUnit (E.toTorus.pairing.matching j))⁻¹ • meridianSlope = fiberSlope := by
  have hd := h.2.2
  rw [fillingDistance_false] at hd
  exact (PrimitiveSlope.delta_eq_zero_iff _ _).1 hd

def seamSide (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) :
    Bool → E.toTorus.Side
  | true => .inl j
  | false => .inr (.inl j)

theorem sidePiece_seamSide (E : ElementaryPresentation W) (j : Fin E.toTorus.pairing.count) :
    ∀ b, E.toTorus.sidePiece (E.seamSide j b) = E.seamPiece j b
  | true => rfl
  | false => rfl

theorem seamSide_eq_seamSide_iff (E : ElementaryPresentation W)
    {j j' : Fin E.toTorus.pairing.count} {b b' : Bool} :
    E.seamSide j b = E.seamSide j' b' ↔ j = j' ∧ b = b' := by
  cases b <;> cases b' <;> simp [seamSide]

theorem card_ownedSide_seamPiece (E : ElementaryPresentation W) {j : Fin E.toTorus.pairing.count}
    {b : Bool} (h : E.IsSplitSeam j b) :
    Fintype.card (E.toTorus.OwnedSide (E.seamPiece j b)) = 1 := by
  rw [(E.piece _).card_ownedSide, h.1]

theorem card_ownedSide_hostPiece (E : ElementaryPresentation W) {j : Fin E.toTorus.pairing.count}
    {b : Bool} (h : E.IsSplitSeam j b) :
    Fintype.card (E.toTorus.OwnedSide (E.hostPiece j b)) = 3 := by
  rw [(E.piece _).card_ownedSide, h.2.1]

theorem seamPiece_ne_hostPiece (E : ElementaryPresentation W) {j : Fin E.toTorus.pairing.count}
    {b : Bool} (h : E.IsSplitSeam j b) : E.seamPiece j b ≠ E.hostPiece j b := by
  intro he
  have h1 := h.1
  have h3 := h.2.1
  rw [he] at h1
  omega

theorem eq_of_seamPiece_eq_of_isSplitSeam (E : ElementaryPresentation W)
    {j j' : Fin E.toTorus.pairing.count} {b b' : Bool} (h : E.IsSplitSeam j b)
    (h' : E.seamPiece j' b' = E.seamPiece j b) : j' = j ∧ b' = b := by
  have hs : Subsingleton (E.toTorus.OwnedSide (E.seamPiece j b)) :=
    Fintype.card_le_one_iff_subsingleton.mp (E.card_ownedSide_seamPiece h).le
  have he := congrArg Subtype.val (Subsingleton.elim
    (⟨E.seamSide j' b', (E.sidePiece_seamSide j' b').trans h'⟩ :
      E.toTorus.OwnedSide (E.seamPiece j b))
    ⟨E.seamSide j b, E.sidePiece_seamSide j b⟩)
  exact (E.seamSide_eq_seamSide_iff).1 he

end Seams

section Closed

variable {Q : ConnectedClosedOrientedManifold.{u} 3}

theorem exists_seamSide_eq (E : ElementaryPresentation (NoCuts.carrier Q))
    (s : E.toTorus.Side) : ∃ j b, s = E.seamSide j b := by
  rcases s with k | k | k
  · exact ⟨k, true, rfl⟩
  · exact ⟨k, false, rfl⟩
  · have hk : (k : ℕ) < E.toTorus.externalCount := k.isLt
    have h0 := E.toTorus.externalCount_eq_zero
    omega

theorem exists_hostPorts (E : ElementaryPresentation (NoCuts.carrier Q))
    {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b) :
    ∃ p : Fin 2 → Fin E.toTorus.pairing.count × Bool, Function.Injective p ∧
      (∀ m, p m ≠ (j, !b)) ∧ (∀ m, E.seamPiece (p m).1 (p m).2 = E.hostPiece j b) ∧
      ∀ j' b', E.seamPiece j' b' = E.hostPiece j b → (j', b') = (j, !b) ∨ ∃ m, p m = (j', b') := by
  classical
  let H := E.hostPiece j b
  let e : E.toTorus.OwnedSide H ≃ Fin 3 := Fintype.equivFinOfCardEq (E.card_ownedSide_hostPiece h)
  let s₀ : E.toTorus.OwnedSide H := ⟨E.seamSide j !b, E.sidePiece_seamSide j !b⟩
  let side : Fin 2 → E.toTorus.OwnedSide H := fun m => e.symm ((e s₀).succAbove m)
  choose q hq using fun m => E.exists_seamSide_eq (side m).val
  choose c hc using hq
  let p : Fin 2 → Fin E.toTorus.pairing.count × Bool := fun m => (q m, c m)
  have hside : ∀ m, (side m).val = E.seamSide (p m).1 (p m).2 := fun m => hc m
  have hsideinj : Function.Injective side := fun m m' hm =>
    Fin.succAbove_right_injective (e.symm.injective hm)
  refine ⟨p, fun m m' hm => hsideinj (Subtype.ext ?_), fun m hm => ?_, fun m => ?_, ?_⟩
  · rw [hside m, hside m', hm]
  · have h0 : side m = s₀ := Subtype.ext ((hside m).trans (by rw [hm]))
    exact Fin.succAbove_ne (e s₀) m (e.symm_apply_eq.mp h0)
  · rw [← E.sidePiece_seamSide, ← hside m]
    exact (side m).property
  · intro j' b' hj'
    let t : E.toTorus.OwnedSide H := ⟨E.seamSide j' b', (E.sidePiece_seamSide j' b').trans hj'⟩
    by_cases ht : e t = e s₀
    · left
      have he := congrArg Subtype.val (e.injective ht)
      obtain ⟨rfl, rfl⟩ := (E.seamSide_eq_seamSide_iff).1 he
      rfl
    · right
      obtain ⟨m, hm⟩ := Fin.exists_succAbove_eq ht
      refine ⟨m, ?_⟩
      have hsm : side m = t := by
        change e.symm ((e s₀).succAbove m) = t
        rw [hm, e.symm_apply_apply]
      have hv := (hside m).symm.trans (congrArg Subtype.val hsm)
      obtain ⟨h1, h2⟩ := (E.seamSide_eq_seamSide_iff).1 hv
      exact Prod.ext h1 h2

end Closed

end ElementaryPresentation

open ElementaryPresentation

theorem isStandardFactor_ulift {X : ConnectedClosedOrientedManifold.{0} 3}
    (h : isStandardFactor X) : isStandardFactor X.ulift.{0, u} := by
  let f := (ClosedOrientedManifold.uliftOrientedDiffeomorph.{0, u}
    X.toClosedOrientedManifold).symm
  rcases h with ⟨G, ⟨e⟩⟩ | ⟨φ, hφ⟩
  · exact Or.inl ⟨G, ⟨f.trans e⟩⟩
  · exact Or.inr ⟨f.1.trans φ, Diffeomorph.preservesOrientation_trans f.2 hφ⟩

theorem seifertFactor_sphereTwoTimesCircle :
    SeifertFactor sphereTwoTimesCircleLift.ulift.{0, u} :=
  Or.inl (isStandardFactor_ulift isStandardFactor_sphereTwoTimesCircleLift)

theorem seifertFactor_sphereTwoTimesCircle_opposite :
    SeifertFactor sphereTwoTimesCircleLift.ulift.{0, u}.opposite :=
  Or.inl (isStandardFactor_opposite _
    (isStandardFactor_ulift isStandardFactor_sphereTwoTimesCircleLift))

theorem elementaryBelow_of_complexity_lt {n : ℕ} {A : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier A)) (h : E.complexity < n) :
    ElementaryBelow n A ∧ ElementaryBelow n A.opposite := by
  obtain ⟨E', hE'⟩ := E.exists_of_diffeomorph (N := A.opposite)
    (Diffeomorph.refl (𝓡 3) A.Carrier ∞)
  exact ⟨Or.inr ⟨E, h⟩, Or.inr ⟨E', hE'.trans_lt h⟩⟩

theorem splitsBelow_of_diffeomorph {Q : ConnectedClosedOrientedManifold.{u} 3}
    {E : ElementaryPresentation (NoCuts.carrier Q)} {A B : ConnectedClosedOrientedManifold.{u} 3}
    (d : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum A B).Carrier)
    (hA : ElementaryBelow E.complexity A ∧ ElementaryBelow E.complexity A.opposite)
    (hB : ElementaryBelow E.complexity B ∧ ElementaryBelow E.complexity B.opposite) :
    E.SplitsBelow := by
  rcases orientedDiffeomorph_or_opposite_of_diffeomorph Q (connectedSum A B) d with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact ⟨A, B, ⟨e.symm⟩, hA.1, hB.1⟩
  · obtain ⟨c⟩ := connectedSum_opposite A B
    exact ⟨A.opposite, B.opposite, ⟨(e.trans c).symm⟩, hA.2, hB.2⟩

def FibreFillingSphereSurgery : Prop :=
  ∀ (Q : ConnectedClosedOrientedManifold.{u} 3) (E : ElementaryPresentation (NoCuts.carrier Q))
    (j : Fin E.toTorus.pairing.count) (b : Bool), E.IsSplitSeam j b →
      (∃ (A B : ConnectedClosedOrientedManifold.{u} 3)
          (EA : ElementaryPresentation (NoCuts.carrier A))
          (EB : ElementaryPresentation (NoCuts.carrier B)),
        Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum A B).Carrier) ∧
          EA.complexity + EB.complexity + 1 = E.complexity) ∨
      ∃ (A : ConnectedClosedOrientedManifold.{u} 3)
        (EA : ElementaryPresentation (NoCuts.carrier A)),
        Nonempty (Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (connectedSum A sphereTwoTimesCircleLift.ulift.{0, u}).Carrier) ∧
          EA.complexity + 1 = E.complexity

theorem moveSplit_of_fibreFillingSphereSurgery (h : FibreFillingSphereSurgery.{u}) :
    MoveSplit.{u} := by
  intro Q E j b hs
  rcases h Q E j b hs with ⟨A, B, EA, EB, ⟨d⟩, hc⟩ | ⟨A, EA, ⟨d⟩, hc⟩
  · exact splitsBelow_of_diffeomorph d (elementaryBelow_of_complexity_lt EA (by omega))
      (elementaryBelow_of_complexity_lt EB (by omega))
  · exact splitsBelow_of_diffeomorph d (elementaryBelow_of_complexity_lt EA (by omega))
      ⟨Or.inl seifertFactor_sphereTwoTimesCircle,
        Or.inl seifertFactor_sphereTwoTimesCircle_opposite⟩

end GC.Seifert
