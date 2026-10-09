import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplit
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveAbsorb
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusCollarStraightening
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport

/-!
# Collar germs: straightening, shrinking and recollaring

Lane CS2, for the germ-level collar contract `ElementarizeOnSubCollar` (review 5, item 3.3).

Straightening. A diffeomorphism equal to the identity near a point of every preconnected open set
of a cover preserves the orientation (`preservesOrientation_of_preconnected_cover`). So the ambient
diffeomorphism of `exists_torusCollar_straightening`, taken with support in the inner half
`s < 1/2` of a collar target, is orientation preserving (`preservesOrientation_of_eqOn_inner`).
Composing one such map per torus, two families of boundary tori that agree on `T² × 0` up to
`ψ i` are related by an orientation preserving `Φ` with `Φ ∘ B₀ i = B₁ i ∘ (ψ i × id)` for
`s < δ` (`exists_boundaryTori_straightening`). Transporting an elementary presentation along `Φ`
gives the sub-collar clause (`ElementaryPresentation.exists_transport_subCollar`), and
`elementarizeOnSubCollar_of_torus_eq` reduces `ElementarizeOnSubCollar` to matching on `T² × 0`.

Shrinking. `halfSpaceScale δ` is `s ↦ δ s` on the half line. `TorusPresentation.shrink`
precomposes every half collar with it and every seam with `(t, s) ↦ (t, δ s)`. Gluing,
parameters, matchings, hence `torusMatrix`, `torusUnit` and filling distances, are unchanged
(`shrink_matching`, `shrink_torusUnit`, `ElementaryPresentation.shrink_fillingDistance`). The
reversal of a pairing survives any reparametrisation of the collar source that maps the zero
section to itself (`reversesBoundaryOrientation_comp`). Germ agreement for `s < δ` becomes full
agreement of the shrunk collars (`BoundaryTori.shrink_collar_eq_of_subCollar`,
`ElementaryPresentation.shrink_external_collar_eq_of_subCollar`). `TorusPresentation.reparam`
precomposes the collars of every side with a torus diffeomorphism `ψ s`, seams on the left side,
and replaces each matching by `ψ_R⁻¹ ∘ m ∘ ψ_L`.

Recollaring. `recollar` and `recollarReparam` turn product structures that agree with the
(reparametrised) piece collars only for `s < δ` into an elementary presentation of the same `W`
with the same seam count, on `(T.reparam ψ).shrink δ`. A product structure that matches the piece
collars only on `T² × 0` is straightened to a germ match (`exists_germ_trivialization`), so
`exists_elementary_of_torus_products` needs only the zero section. Any diffeomorphism of a piece
with `B × S¹` matches its boundary tori with those of the product up to a bijection of ports and
torus diffeomorphisms (`exists_port_of_diffeomorph`), so a presentation whose pieces are each
diffeomorphic to `Pₖ × S¹`, with `k` the number of owned sides, carries an elementary
presentation with the same seam count (`exists_elementary_of_forall_piece`). For a contraction
the kept pieces keep their products (`contractKeptDiffeomorph`, `card_contract_ownedSide_kept`),
which proves N3's `ContractionRecollar` (`contractionRecollar`).

Worked instance (one product piece through `ElementarizePiece`). From a product structure on
piece `i` matching its collars on `T² × 0` up to port diffeomorphisms, `trivPresentation` is the
one-piece presentation with the product collars, `trivPiece` its product structure, and
`exists_germ_elementary` gives the clause of `ElementarizePiece` at `(T, i)` for `s < δ`;
`exists_shrink_elementary_piece` gives it on the whole half collar for `T.shrink δ`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ}

theorem preservesOrientation_of_preconnected_cover (Φ : M ≃ₘ⟮I, I⟯ M)
    (o : ManifoldOrientation I M n)
    (h : ∀ y, Φ =ᶠ[𝓝 y] id ∨ ∃ U : Set M, IsOpen U ∧ IsPreconnected U ∧ y ∈ U ∧
      ∃ z ∈ U, Φ =ᶠ[𝓝 z] id) :
    Φ.preservesOrientation o o := by
  obtain ⟨O', hO'⟩ := exists_manifoldOrientation_diffeomorph_map Φ o
  have hbase : ∀ z, Φ =ᶠ[𝓝 z] id → O'.orientation z = o.orientation z := by
    intro z hz
    have hz0 : Φ z = z := hz.self_of_nhds
    have hzs : Φ.symm z = z := by
      conv_lhs => rw [← hz0]
      exact Φ.symm_apply_apply z
    have heq : (Φ.mfderivToContinuousLinearEquiv (by simp) z).toLinearEquiv =
        LinearEquiv.refl ℝ (TangentSpace I z) := by
      ext v
      change mfderiv I I (⇑Φ) z v = v
      rw [Filter.EventuallyEq.mfderiv_eq hz, mfderiv_id]
      rfl
    rw [hO']
    beta_reduce
    rw [hzs, heq]
    exact congrArg (fun q => q (o.orientation z))
      (Orientation.map_refl (ι := Fin n) (R := ℝ) (M := TangentSpace I z))
  have hprop : ∀ U : Set M, IsOpen U → IsPreconnected U → ∀ y ∈ U, ∀ z ∈ U,
      O'.orientation z = o.orientation z → O'.orientation y = o.orientation y := by
    intro U hU hUc y hy z hz hzo
    let V : TopologicalSpace.Opens M := ⟨U, hU⟩
    have : PreconnectedSpace V := Subtype.preconnectedSpace hUc
    have hV := ManifoldOrientation.eq_of_eq_at (O'.restrictOpen V) (o.restrictOpen V) ⟨z, hz⟩ hzo
    exact congrArg (fun q : ManifoldOrientation I V n => q.orientation ⟨y, hy⟩) hV
  have hall : ∀ y, O'.orientation y = o.orientation y := fun y =>
    (h y).elim (hbase y) fun ⟨U, hU, hUc, hy, z, hz, hzid⟩ =>
      hprop U hU hUc y hy z hz (hbase z hzid)
  intro x
  have h1 : Orientation.map (Fin n) (Φ.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (o.orientation x) = O'.orientation (Φ x) := by
    rw [hO']
    beta_reduce
    rw [Φ.symm_apply_apply]
  exact h1.trans (hall (Φ x))

end Orientation

section Scale

variable {δ : ℝ}

def halfSpaceScale (hδ : 0 < δ) :
    EuclideanHalfSpace 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ EuclideanHalfSpace 1 where
  toFun s := halfSpaceOneLift (δ * s.1 0)
  invFun s := halfSpaceOneLift (δ⁻¹ * s.1 0)
  left_inv s := by
    change halfSpaceOneLift (δ⁻¹ * max (δ * s.1 0) 0) = s
    rw [max_eq_left (mul_nonneg hδ.le s.2), inv_mul_cancel_left₀ hδ.ne']
    exact halfSpaceOneLift_coord s
  right_inv s := by
    change halfSpaceOneLift (δ * max (δ⁻¹ * s.1 0) 0) = s
    rw [max_eq_left (mul_nonneg (inv_nonneg.mpr hδ.le) s.2), mul_inv_cancel_left₀ hδ.ne']
    exact halfSpaceOneLift_coord s
  contMDiff_toFun := contMDiffOn_halfSpaceOneLift.comp_contMDiff
    ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_halfSpaceOneCoordinate)
    (fun s => mem_Ici.mpr (mul_nonneg hδ.le s.2))
  contMDiff_invFun := contMDiffOn_halfSpaceOneLift.comp_contMDiff
    ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_halfSpaceOneCoordinate)
    (fun s => mem_Ici.mpr (mul_nonneg (inv_nonneg.mpr hδ.le) s.2))

theorem halfSpaceScale_coord (hδ : 0 < δ) (s : EuclideanHalfSpace 1) :
    (halfSpaceScale hδ s).1 0 = δ * s.1 0 :=
  max_eq_left (mul_nonneg hδ.le s.2)

theorem halfSpaceScale_halfPoint (hδ : 0 < δ) (s : ℝ) (hs : 0 ≤ s) :
    halfSpaceScale hδ (halfPoint s hs) = halfPoint (δ * s) (mul_nonneg hδ.le hs) :=
  (halfPoint_eq_self _ _ (halfSpaceScale_coord hδ _).symm).symm

theorem halfSpaceScale_halfZero (hδ : 0 < δ) : halfSpaceScale hδ halfZero = halfZero :=
  (halfSpaceScale_halfPoint hδ 0 le_rfl).trans (halfPoint_eq_self _ _ (by simp [halfZero]; rfl))

def realScale (hδ : 0 < δ) : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ where
  toFun s := δ * s
  invFun s := δ⁻¹ * s
  left_inv s := inv_mul_cancel_left₀ hδ.ne' s
  right_inv s := mul_inv_cancel_left₀ hδ.ne' s
  contMDiff_toFun := (contDiff_const.mul contDiff_id).contMDiff
  contMDiff_invFun := (contDiff_const.mul contDiff_id).contMDiff

end Scale

section Collar

variable {δ : ℝ}
  {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] {HX : Type*} [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

def halfShrink (hδ : 0 < δ) : (X × EuclideanHalfSpace 1) ≃ₘ⟮IX.prod (𝓡∂ 1), IX.prod (𝓡∂ 1)⟯
    (X × EuclideanHalfSpace 1) :=
  (Diffeomorph.refl IX X ∞).prodCongr (halfSpaceScale hδ)

theorem halfShrink_apply (hδ : 0 < δ) (p : X × EuclideanHalfSpace 1) :
    halfShrink (IX := IX) hδ p = (p.1, halfSpaceScale hδ p.2) := rfl

theorem isOpen_collarSource : IsOpen {p : X × EuclideanHalfSpace 1 | p.2.1 0 < 1} :=
  isOpen_lt (((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).comp
    continuous_snd) continuous_const

theorem halfSpaceScale_mem (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : EuclideanHalfSpace 1}
    (hs : s.1 0 < 1) : (halfSpaceScale hδ s).1 0 < 1 := by
  rw [halfSpaceScale_coord]
  have := s.2
  nlinarith

theorem halfSpaceScale_lt (hδ : 0 < δ) {s : EuclideanHalfSpace 1} (hs : s.1 0 < 1) :
    (halfSpaceScale hδ s).1 0 < δ := by
  rw [halfSpaceScale_coord]
  nlinarith

def shrinkHalfCollar (hδ : 0 < δ)
    (c : PartialDiffeomorph (IX.prod (𝓡∂ 1)) J (X × EuclideanHalfSpace 1) N ∞) :
    PartialDiffeomorph (IX.prod (𝓡∂ 1)) J (X × EuclideanHalfSpace 1) N ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    ((halfShrink hδ).toPartialDiffeomorph.trans c) {p | p.2.1 0 < 1} isOpen_collarSource

theorem shrinkHalfCollar_apply (hδ : 0 < δ)
    (c : PartialDiffeomorph (IX.prod (𝓡∂ 1)) J (X × EuclideanHalfSpace 1) N ∞)
    (p : X × EuclideanHalfSpace 1) :
    shrinkHalfCollar hδ c p = c (p.1, halfSpaceScale hδ p.2) := rfl

theorem shrinkHalfCollar_source (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {c : PartialDiffeomorph (IX.prod (𝓡∂ 1)) J (X × EuclideanHalfSpace 1) N ∞}
    (hc : c.source = {p | p.2.1 0 < 1}) :
    (shrinkHalfCollar hδ c).source = {p | p.2.1 0 < 1} := by
  ext p
  refine ⟨fun hp => hp.2, fun hp => ⟨⟨mem_univ _, ?_⟩, hp⟩⟩
  change halfShrink hδ p ∈ c.source
  rw [hc]
  exact halfSpaceScale_mem hδ hδ1 hp

theorem shrinkHalfCollar_target_subset (hδ : 0 < δ)
    (c : PartialDiffeomorph (IX.prod (𝓡∂ 1)) J (X × EuclideanHalfSpace 1) N ∞) :
    (shrinkHalfCollar hδ c).target ⊆ c.target := by
  intro y hy
  have hs := (shrinkHalfCollar hδ c).map_target' hy
  rw [← (shrinkHalfCollar hδ c).right_inv' hy]
  exact c.map_source' hs.1.2

end Collar

section Signed

variable {δ : ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*}
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} {N : Type*} [TopologicalSpace N]
  [ChartedSpace G N]

def signedShrink (hδ : 0 < δ) : (Torus × ℝ) ≃ₘ⟮signedCollarModel, signedCollarModel⟯ (Torus × ℝ) :=
  (Diffeomorph.refl torusModel Torus ∞).prodCongr (realScale hδ)

theorem signedCollarSource_isOpen : IsOpen signedCollarSource :=
  (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)

def shrinkSignedCollar (hδ : 0 < δ) (c : PartialDiffeomorph signedCollarModel J (Torus × ℝ) N ∞) :
    PartialDiffeomorph signedCollarModel J (Torus × ℝ) N ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    ((signedShrink hδ).toPartialDiffeomorph.trans c) signedCollarSource signedCollarSource_isOpen

theorem shrinkSignedCollar_apply (hδ : 0 < δ)
    (c : PartialDiffeomorph signedCollarModel J (Torus × ℝ) N ∞) (p : Torus × ℝ) :
    shrinkSignedCollar hδ c p = c (p.1, δ * p.2) := rfl

theorem shrinkSignedCollar_source (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {c : PartialDiffeomorph signedCollarModel J (Torus × ℝ) N ∞}
    (hc : c.source = signedCollarSource) :
    (shrinkSignedCollar hδ c).source = signedCollarSource := by
  ext p
  refine ⟨fun hp => hp.2, fun hp => ⟨⟨mem_univ _, ?_⟩, hp⟩⟩
  change signedShrink hδ p ∈ c.source
  rw [hc]
  obtain ⟨h1, h2⟩ := hp
  change -1 < δ * p.2 ∧ δ * p.2 < 1
  constructor <;> nlinarith

theorem shrinkSignedCollar_target_subset (hδ : 0 < δ)
    (c : PartialDiffeomorph signedCollarModel J (Torus × ℝ) N ∞) :
    (shrinkSignedCollar hδ c).target ⊆ c.target := by
  intro y hy
  have hs := (shrinkSignedCollar hδ c).map_target' hy
  rw [← (shrinkSignedCollar hδ c).right_inv' hy]
  exact c.map_source' hs.1.2

end Signed

section Reparam

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*}
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} {N : Type*} [TopologicalSpace N]
  [ChartedSpace G N]

def torusReparam (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (c : PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞) :
    PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞ :=
  (φ.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans c

theorem torusReparam_apply (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (c : PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞)
    (p : Torus × EuclideanHalfSpace 1) : torusReparam φ c p = c (φ p.1, p.2) := rfl

theorem torusReparam_source (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    {c : PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞}
    (hc : c.source = halfCollarSource) : (torusReparam φ c).source = halfCollarSource := by
  ext p
  refine ⟨fun hp => ?_, fun hp => ⟨mem_univ _, ?_⟩⟩
  · have h1 : (φ p.1, p.2) ∈ c.source := hp.2
    rw [hc] at h1
    exact h1
  · change (φ p.1, p.2) ∈ c.source
    rw [hc]
    exact hp

theorem torusReparam_target_subset (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (c : PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞) :
    (torusReparam φ c).target ⊆ c.target := by
  intro y hy
  have hs := (torusReparam φ c).map_target' hy
  rw [← (torusReparam φ c).right_inv' hy]
  exact c.map_source' hs.2

def signedReparam (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (c : PartialDiffeomorph signedCollarModel J (Torus × ℝ) N ∞) :
    PartialDiffeomorph signedCollarModel J (Torus × ℝ) N ∞ :=
  (φ.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)).toPartialDiffeomorph.trans c

theorem signedReparam_source (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    {c : PartialDiffeomorph signedCollarModel J (Torus × ℝ) N ∞}
    (hc : c.source = signedCollarSource) : (signedReparam φ c).source = signedCollarSource := by
  ext p
  refine ⟨fun hp => ?_, fun hp => ⟨mem_univ _, ?_⟩⟩
  · have h1 : (φ p.1, p.2) ∈ c.source := hp.2
    rw [hc] at h1
    exact h1
  · change (φ p.1, p.2) ∈ c.source
    rw [hc]
    exact hp

theorem signedReparam_target_subset (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (c : PartialDiffeomorph signedCollarModel J (Torus × ℝ) N ∞) :
    (signedReparam φ c).target ⊆ c.target := by
  intro y hy
  have hs := (signedReparam φ c).map_target' hy
  rw [← (signedReparam φ c).right_inv' hy]
  exact c.map_source' hs.2

end Reparam

section Reversal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

theorem mdifferentiableAt_of_mem_source (c : PartialDiffeomorph I J M N ∞)
    {x : M} (hx : x ∈ c.source) : MDifferentiableAt I J c x :=
  (c.contMDiffOn.contMDiffAt (c.open_source.mem_nhds hx)).mdifferentiableAt (by simp)

end Reversal

theorem reversesBoundaryOrientation_comp {C : CompactCarrier.{u}}
    {l r : Torus × EuclideanHalfSpace 1 → C.Carrier} (h : ReversesBoundaryOrientation C l r)
    (S : (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
      (Torus × EuclideanHalfSpace 1)) (σ : Torus → Torus)
    (hS : ∀ t, S (t, halfZero) = (σ t, halfZero))
    (hl : ∀ t, MDifferentiableAt halfCollarModel C.model l (t, halfZero))
    (hr : ∀ t, MDifferentiableAt halfCollarModel C.model r (t, halfZero)) :
    ReversesBoundaryOrientation C (l ∘ S) (r ∘ S) := by
  intro t
  have key : ∀ y, y = (σ t, halfZero) → ∀ Dy : TangentSpace halfCollarModel (t, halfZero) ≃ₗ[ℝ]
      TangentSpace halfCollarModel y,
      ∃ L' : TangentSpace halfCollarModel (t, halfZero) ≃ₗ[ℝ] TangentSpace C.model (l y),
      ∃ R' : TangentSpace halfCollarModel (t, halfZero) ≃ₗ[ℝ] TangentSpace C.model (r y),
        (∀ v, L' v = mfderiv halfCollarModel C.model l y (Dy v)) ∧
        (∀ v, R' v = mfderiv halfCollarModel C.model r y (Dy v)) ∧
        Orientation.map (Fin 3) L'.symm (C.orientation.orientation (l y)) =
          -Orientation.map (Fin 3) R'.symm (C.orientation.orientation (r y)) := by
    intro y hy Dy
    subst hy
    obtain ⟨L, R, hL, hR, hLR⟩ := h (σ t)
    refine ⟨Dy.trans L, Dy.trans R, fun v => hL (Dy v), fun v => hR (Dy v), ?_⟩
    rw [LinearEquiv.trans_symm, LinearEquiv.trans_symm]
    have hmap (A : TangentSpace C.model (l (σ t, halfZero)) ≃ₗ[ℝ]
        TangentSpace halfCollarModel (σ t, halfZero)) (o : Orientation ℝ
          (TangentSpace C.model (l (σ t, halfZero))) (Fin 3)) :
        Orientation.map (Fin 3) (A.trans Dy.symm) o =
          Orientation.map (Fin 3) Dy.symm (Orientation.map (Fin 3) A o) := by
      induction o using Module.Ray.ind with
      | h v hv => rfl
    have hmap' (A : TangentSpace C.model (r (σ t, halfZero)) ≃ₗ[ℝ]
        TangentSpace halfCollarModel (σ t, halfZero)) (o : Orientation ℝ
          (TangentSpace C.model (r (σ t, halfZero))) (Fin 3)) :
        Orientation.map (Fin 3) (A.trans Dy.symm) o =
          Orientation.map (Fin 3) Dy.symm (Orientation.map (Fin 3) A o) := by
      induction o using Module.Ray.ind with
      | h v hv => rfl
    rw [hmap, hmap', hLR, Orientation.map_neg]
  have hSd : MDifferentiableAt halfCollarModel halfCollarModel S (t, halfZero) :=
    S.mdifferentiable (by simp) _
  have hl' : MDifferentiableAt halfCollarModel C.model l (S (t, halfZero)) := by
    rw [hS t]
    exact hl (σ t)
  have hr' : MDifferentiableAt halfCollarModel C.model r (S (t, halfZero)) := by
    rw [hS t]
    exact hr (σ t)
  obtain ⟨L', R', hL', hR', hLR'⟩ := key _ (hS t)
    (S.mfderivToContinuousLinearEquiv (by simp) (t, halfZero)).toLinearEquiv
  refine ⟨L', R', fun v => ?_, fun v => ?_, hLR'⟩
  · rw [mfderiv_comp (t, halfZero) hl' hSd]
    exact hL' v
  · rw [mfderiv_comp (t, halfZero) hr' hSd]
    exact hR' v


section Straighten

theorem isCompact_halfCollar_le :
    IsCompact {q : Torus × EuclideanHalfSpace 1 | q.2.1 0 ≤ 1 / 2} := by
  have hc : IsCompact ((univ : Set Torus) ×ˢ (halfSpaceOneLift '' Icc 0 (1 / 2))) :=
    isCompact_univ.prod (isCompact_Icc.image_of_continuousOn
      (contMDiffOn_halfSpaceOneLift.continuousOn.mono Icc_subset_Ici_self))
  refine hc.of_isClosed_subset (isClosed_le (((EuclideanSpace.proj 0).continuous.comp
    continuous_subtype_val).comp continuous_snd) continuous_const) fun q hq => ?_
  exact ⟨mem_univ _, q.2.1 0, ⟨q.2.2, hq⟩, halfSpaceOneLift_coord q.2⟩

theorem isPreconnected_collar_target {C : CompactCarrier.{u}}
    (c : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hc : c.source = halfCollarSource) : IsPreconnected c.target := by
  rw [← c.toPartialEquiv.image_source_eq_target]
  refine IsPreconnected.image ?_ _ c.contMDiffOn.continuousOn
  rw [hc]
  exact isPreconnected_halfCollarSource

theorem preservesOrientation_of_eqOn_inner {C : CompactCarrier.{u}}
    (c : PartialDiffeomorph halfCollarModel C.model (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hc : c.source = halfCollarSource) (Φ : C.Carrier ≃ₘ⟮C.model, C.model⟯ C.Carrier)
    (hΦ : EqOn Φ id (c.target ∩ c.symm ⁻¹' {q | q.2.1 0 < 1 / 2})ᶜ) :
    Φ.preservesOrientation C.orientation C.orientation := by
  have hcoord : Continuous fun q : Torus × EuclideanHalfSpace 1 => q.2.1 0 :=
    ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).comp continuous_snd
  refine preservesOrientation_of_preconnected_cover Φ C.orientation fun y => ?_
  by_cases hy : y ∈ c.target
  · refine Or.inr ⟨c.target, c.open_target, isPreconnected_collar_target c hc, hy, ?_⟩
    let q : Torus × EuclideanHalfSpace 1 := (torusBase, halfPoint (3 / 4) (by norm_num))
    have hq : q ∈ c.source := by
      rw [hc]
      change (3 / 4 : ℝ) < 1
      norm_num
    let N := c.target ∩ c.symm ⁻¹' {q | 1 / 2 < q.2.1 0}
    have hN : IsOpen N := c.symm.contMDiffOn.continuousOn.isOpen_inter_preimage c.open_target
      (isOpen_lt continuous_const hcoord)
    have hqN : c q ∈ N := by
      refine ⟨c.map_source' hq, ?_⟩
      change 1 / 2 < (c.symm (c q)).2.1 0
      rw [c.symm_apply_apply hq]
      change (1 / 2 : ℝ) < 3 / 4
      norm_num
    refine ⟨c q, c.map_source' hq, Filter.eventuallyEq_of_mem (hN.mem_nhds hqN) fun x hx => ?_⟩
    refine hΦ fun hxO => ?_
    have h1 : 1 / 2 < (c.symm x).2.1 0 := hx.2
    have h2 : (c.symm x).2.1 0 < 1 / 2 := hxO.2
    linarith
  · refine Or.inl ?_
    let K := c '' {q : Torus × EuclideanHalfSpace 1 | q.2.1 0 ≤ 1 / 2}
    have hKs : {q : Torus × EuclideanHalfSpace 1 | q.2.1 0 ≤ 1 / 2} ⊆ c.source := by
      intro q hq
      rw [hc]
      change q.2.1 0 < 1
      have : q.2.1 0 ≤ 1 / 2 := hq
      linarith
    have hK : IsCompact K := isCompact_halfCollar_le.image_of_continuousOn
      (c.contMDiffOn.continuousOn.mono hKs)
    have hyK : y ∉ K := by
      rintro ⟨q, hq, rfl⟩
      exact hy (c.map_source' (hKs hq))
    refine Filter.eventuallyEq_of_mem (hK.isClosed.isOpen_compl.mem_nhds hyK) fun x hx => ?_
    refine hΦ fun hxO => hx ⟨c.symm x, ?_, c.right_inv' hxO.1⟩
    have h2 : (c.symm x).2.1 0 < 1 / 2 := hxO.2
    exact h2.le

private theorem exists_single_straightening {W : CompactCarrier.{u}} {n : ℕ}
    (B₀ B₁ : BoundaryTori W n) (ψ : Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (h₀ : ∀ i t, B₀.collar i (t, halfZero) = B₁.collar i (ψ i t, halfZero)) (i : Fin n) :
    ∃ δ > (0 : ℝ), ∃ Φ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier,
      Φ.preservesOrientation W.orientation W.orientation ∧
      (∀ p : Torus × EuclideanHalfSpace 1, p.2.val 0 < δ →
        Φ (B₀.collar i p) = B₁.collar i (ψ i p.1, p.2)) ∧
      ∀ x, x ∉ (B₁.collar i).target → Φ x = x := by
  let c := B₁.collar i
  let c₁ := (Diffeomorph.prodCongr (ψ i)
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans c
  have hcoord : Continuous fun q : Torus × EuclideanHalfSpace 1 => q.2.1 0 :=
    ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).comp continuous_snd
  let O := c.target ∩ c.symm ⁻¹' {q | q.2.1 0 < 1 / 2}
  have hO : IsOpen O := c.symm.contMDiffOn.continuousOn.isOpen_inter_preimage c.open_target
    (isOpen_lt hcoord continuous_const)
  have hmem (t : Torus) : (t, halfZero) ∈ c.source := by
    rw [B₁.source_eq]
    exact zero_mem_halfCollarSource t
  have hK : range (fun p => B₀.collar i (p, halfZero)) ⊆ O := by
    rintro _ ⟨p, rfl⟩
    change B₀.collar i (p, halfZero) ∈ O
    rw [h₀]
    refine ⟨c.map_source' (hmem _), ?_⟩
    change (c.symm (c (ψ i p, halfZero))).2.1 0 < 1 / 2
    rw [c.symm_apply_apply (hmem _)]
    change (0 : ℝ) < 1 / 2
    norm_num
  have hsrc (p : Torus) : (p, halfZero) ∈ (B₀.collar i).source ∩ c₁.source := by
    refine ⟨?_, mem_univ _, hmem (ψ i p)⟩
    rw [B₀.source_eq]
    exact zero_mem_halfCollarSource p
  obtain ⟨δ, hδ, Φ, hΦ, hfix⟩ := exists_torusCollar_straightening (B₀.collar i) c₁ hsrc
    (fun p => h₀ i p) (fun p => B₀.boundary_zero i p) hO hK
  refine ⟨δ, hδ, Φ, preservesOrientation_of_eqOn_inner c (B₁.source_eq i) Φ hfix,
    fun p hp => hΦ p.1 p.2 hp, fun x hx => hfix fun hxO => hx hxO.1⟩

theorem exists_boundaryTori_straightening {W : CompactCarrier.{u}} {n : ℕ}
    (B₀ B₁ : BoundaryTori W n) (ψ : Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (h₀ : ∀ i t, B₀.collar i (t, halfZero) = B₁.collar i (ψ i t, halfZero)) :
    ∃ δ > (0 : ℝ), ∃ Φ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier,
      Φ.preservesOrientation W.orientation W.orientation ∧
      (∀ i p, p ∈ halfCollarSource → p.2.val 0 < δ →
        Φ (B₀.collar i p) = B₁.collar i (ψ i p.1, p.2)) ∧
      ∀ x, (∀ i, x ∉ (B₁.collar i).target) → Φ x = x := by
  choose δ hδ Φ hΦo hΦa hΦs using exists_single_straightening B₀ B₁ ψ h₀
  have hB₁ (i : Fin n) (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
      B₁.collar i (ψ i p.1, p.2) ∈ (B₁.collar i).target := by
    refine (B₁.collar i).map_source' ?_
    rw [B₁.source_eq]
    exact hp
  have hB₀ (i : Fin n) (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource)
      (hlt : p.2.val 0 < δ i) : B₀.collar i p ∈ (B₁.collar i).target := by
    by_contra hx
    have h1 := hΦs i _ hx
    rw [hΦa i p hlt] at h1
    exact hx (h1 ▸ hB₁ i p hp)
  have key : ∀ k ≤ n, ∃ ε > (0 : ℝ), ∃ Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier,
      Ψ.preservesOrientation W.orientation W.orientation ∧
      (∀ i : Fin n, i.val < k → ∀ p, p ∈ halfCollarSource → p.2.val 0 < ε →
        Ψ (B₀.collar i p) = B₁.collar i (ψ i p.1, p.2)) ∧
      ∀ x, (∀ i : Fin n, i.val < k → x ∉ (B₁.collar i).target) → Ψ x = x := by
    intro k
    induction k with
    | zero =>
      exact fun _ => ⟨1, one_pos, Diffeomorph.refl _ _ _,
        Diffeomorph.preservesOrientation_refl _, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun _ _ => rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨ε, hε, Ψ, hΨo, hΨa, hΨs⟩ := ih (Nat.le_of_succ_le hk)
      let j : Fin n := ⟨k, hk⟩
      refine ⟨min ε (δ j), lt_min hε (hδ j), Ψ.trans (Φ j),
        Diffeomorph.preservesOrientation_trans hΨo (hΦo j), fun i hi p hp hlt => ?_,
        fun x hx => ?_⟩
      · change Φ j (Ψ (B₀.collar i p)) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hik | hik
        · have hij : i ≠ j := fun e => by
            rw [e] at hik
            exact lt_irrefl _ hik
          rw [hΨa i hik p hp (lt_of_lt_of_le hlt (min_le_left _ _))]
          exact hΦs j _ fun hx => (B₁.disjoint hij).le_bot ⟨hB₁ i p hp, hx⟩
        · have hij : i = j := Fin.ext hik
          rw [hij]
          have hx := hB₀ j p hp (lt_of_lt_of_le hlt (min_le_right _ _))
          rw [hΨs _ fun i' hi' hx' => (B₁.disjoint (fun e => by
              rw [e] at hi'
              exact lt_irrefl k hi')).le_bot ⟨hx', hx⟩]
          exact hΦa j p (lt_of_lt_of_le hlt (min_le_right _ _))
      · change Φ j (Ψ x) = x
        rw [hΨs x fun i hi => hx i (Nat.lt_succ_of_lt hi)]
        exact hΦs j x (hx j (Nat.lt_succ_self k))
  obtain ⟨ε, hε, Ψ, hΨo, hΨa, hΨs⟩ := key n le_rfl
  exact ⟨ε, hε, Ψ, hΨo, fun i => hΨa i i.2, fun x hx => hΨs x fun i _ => hx i⟩

end Straighten

section Shrink

variable {δ : ℝ}

theorem halfShrink_zero (hδ : 0 < δ) (t : Torus) :
    halfShrink (IX := torusModel) hδ (t, halfZero) = (t, halfZero) := by
  change (t, halfSpaceScale hδ halfZero) = (t, halfZero)
  rw [halfSpaceScale_halfZero]

end Shrink

end GC.Seifert

namespace GC.GraphManifold

open GC.Seifert

section Shrink

variable {δ : ℝ}

def BoundaryTori.shrink {C : CompactCarrier.{u}} {n : ℕ}
    (B : BoundaryTori C n) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : BoundaryTori C n where
  collar i := shrinkHalfCollar hδ (B.collar i)
  source_eq i := shrinkHalfCollar_source hδ hδ1 (B.source_eq i)
  boundary_zero i t := by
    change C.model.IsBoundaryPoint (B.collar i (t, halfSpaceScale hδ halfZero))
    rw [halfSpaceScale_halfZero]
    exact B.boundary_zero i t
  disjoint _ _ hij := (B.disjoint hij).mono (shrinkHalfCollar_target_subset hδ _)
    (shrinkHalfCollar_target_subset hδ _)

namespace BoundaryTori

variable {C : CompactCarrier.{u}} {n : ℕ} (B : BoundaryTori C n) (hδ : 0 < δ) (hδ1 : δ ≤ 1)

theorem shrink_collar_apply (i : Fin n) (p : Torus × EuclideanHalfSpace 1) :
    (B.shrink hδ hδ1).collar i p = B.collar i (p.1, halfSpaceScale hδ p.2) := rfl

theorem shrink_torusMap (i : Fin n) : (B.shrink hδ hδ1).torusMap i = B.torusMap i := by
  funext t
  change B.collar i (t, halfSpaceScale hδ halfZero) = B.collar i (t, halfZero)
  rw [halfSpaceScale_halfZero]

theorem shrink_image : (B.shrink hδ hδ1).image = B.image := by
  simp only [BoundaryTori.image, shrink_torusMap]

theorem shrink_collar_eq_of_subCollar {B' : BoundaryTori C n}
    {ψ : Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)}
    (h : ∀ i p, p ∈ halfCollarSource → p.2.val 0 < δ →
      B.collar i p = B'.collar i (ψ i p.1, p.2)) (i : Fin n) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    (B.shrink hδ hδ1).collar i p = (B'.shrink hδ hδ1).collar i (ψ i p.1, p.2) :=
  h i (p.1, halfSpaceScale hδ p.2) (halfSpaceScale_mem hδ hδ1 hp) (halfSpaceScale_lt hδ hp)

end BoundaryTori

theorem TorusPairing.mdifferentiableAt_leftCollar {C : CompactCarrier.{u}} (P : TorusPairing C)
    (i : Fin P.count) (t : Torus) :
    MDifferentiableAt halfCollarModel C.model (P.leftCollar i) (t, halfZero) :=
  mdifferentiableAt_of_mem_source (P.leftCollar i)
    (by rw [P.left_source]; exact zero_mem_halfCollarSource t)

theorem TorusPairing.mdifferentiableAt_matchedRight {C : CompactCarrier.{u}} (P : TorusPairing C)
    (i : Fin P.count) (t : Torus) : MDifferentiableAt halfCollarModel C.model
      (fun p : Torus × EuclideanHalfSpace 1 => P.rightCollar i (P.matching i p.1, p.2))
      (t, halfZero) := by
  have hm : (P.matching i t, halfZero) ∈ (P.rightCollar i).source := by
    rw [P.right_source]
    exact zero_mem_halfCollarSource _
  exact MDifferentiableAt.comp (I' := halfCollarModel) (t, halfZero)
    (mdifferentiableAt_of_mem_source (P.rightCollar i) hm)
    (((P.matching i).contMDiff.prodMap contMDiff_id).mdifferentiableAt (by simp)
      (x := (t, halfZero)))

def TorusPairing.shrink {C : CompactCarrier.{u}} (P : TorusPairing C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : TorusPairing C where
  count := P.count
  gluing := P.gluing
  leftParam := P.leftParam
  rightParam := P.rightParam
  matching := P.matching
  matching_eq := P.matching_eq
  leftCollar i := shrinkHalfCollar hδ (P.leftCollar i)
  rightCollar i := shrinkHalfCollar hδ (P.rightCollar i)
  left_source i := shrinkHalfCollar_source hδ hδ1 (P.left_source i)
  right_source i := shrinkHalfCollar_source hδ hδ1 (P.right_source i)
  left_zero i t := by
    change P.leftCollar i (t, halfSpaceScale hδ halfZero) = _
    rw [halfSpaceScale_halfZero]
    exact P.left_zero i t
  right_zero i t := by
    change P.rightCollar i (t, halfSpaceScale hδ halfZero) = _
    rw [halfSpaceScale_halfZero]
    exact P.right_zero i t
  reversing i := reversesBoundaryOrientation_comp (P.reversing i) (halfShrink hδ) id
    (halfShrink_zero hδ) (P.mdifferentiableAt_leftCollar i) (P.mdifferentiableAt_matchedRight i)

theorem TorusPairing.shrink_matching {C : CompactCarrier.{u}}
    (P : TorusPairing C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (P.shrink hδ hδ1).matching = P.matching :=
  rfl

end Shrink

section Reparam

def BoundaryTori.reparam {C : CompactCarrier.{u}} {n : ℕ} (B : BoundaryTori C n)
    (φ : Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) : BoundaryTori C n where
  collar i := torusReparam (φ i) (B.collar i)
  source_eq i := torusReparam_source (φ i) (B.source_eq i)
  boundary_zero i t := B.boundary_zero i (φ i t)
  disjoint _ _ hij := (B.disjoint hij).mono (torusReparam_target_subset _ _)
    (torusReparam_target_subset _ _)

theorem BoundaryTori.reparam_torusMap {C : CompactCarrier.{u}} {n : ℕ} (B : BoundaryTori C n)
    (φ : Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) (i : Fin n) :
    (B.reparam φ).torusMap i = B.torusMap i ∘ φ i := rfl

theorem BoundaryTori.reparam_image {C : CompactCarrier.{u}} {n : ℕ} (B : BoundaryTori C n)
    (φ : Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) : (B.reparam φ).image = B.image := by
  unfold BoundaryTori.image
  refine iUnion_congr fun i => ?_
  rw [B.reparam_torusMap φ i]
  exact (φ i).surjective.range_comp _

def TorusPairing.reparam {C : CompactCarrier.{u}} (P : TorusPairing C)
    (ψL ψR : Fin P.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) : TorusPairing C where
  count := P.count
  gluing := P.gluing
  leftParam k := (ψL k).toHomeomorph.trans (P.leftParam k)
  rightParam k := (ψR k).toHomeomorph.trans (P.rightParam k)
  matching k := (ψL k).trans ((P.matching k).trans (ψR k).symm)
  matching_eq k t := by
    change P.gluing.attaching k (P.leftParam k (ψL k t)) =
      P.rightParam k (ψR k ((ψR k).symm (P.matching k (ψL k t))))
    rw [Diffeomorph.apply_symm_apply]
    exact P.matching_eq k (ψL k t)
  leftCollar k := torusReparam (ψL k) (P.leftCollar k)
  rightCollar k := torusReparam (ψR k) (P.rightCollar k)
  left_source k := torusReparam_source (ψL k) (P.left_source k)
  right_source k := torusReparam_source (ψR k) (P.right_source k)
  left_zero k t := P.left_zero k (ψL k t)
  right_zero k t := P.right_zero k (ψR k t)
  reversing k := by
    have hfun : (fun p : Torus × EuclideanHalfSpace 1 => P.rightCollar k
        (ψR k ((ψR k).symm (P.matching k (ψL k p.1))), p.2)) =
        (fun p : Torus × EuclideanHalfSpace 1 => P.rightCollar k (P.matching k p.1, p.2)) ∘
          ((ψL k).prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)) := by
      funext p
      change P.rightCollar k (ψR k ((ψR k).symm (P.matching k (ψL k p.1))), p.2) =
        P.rightCollar k (P.matching k (ψL k p.1), p.2)
      rw [Diffeomorph.apply_symm_apply]
    have h := reversesBoundaryOrientation_comp (P.reversing k)
      ((ψL k).prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)) (ψL k)
      (fun t => rfl) (P.mdifferentiableAt_leftCollar k) (P.mdifferentiableAt_matchedRight k)
    rw [← hfun] at h
    exact h

theorem TorusPairing.reparam_matching {C : CompactCarrier.{u}} (P : TorusPairing C)
    (ψL ψR : Fin P.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) (k : Fin P.count) :
    (P.reparam ψL ψR).matching k = (ψL k).trans ((P.matching k).trans (ψR k).symm) := rfl

end Reparam

end GC.GraphManifold

namespace GC.Seifert

section Shrink

variable {δ : ℝ}

namespace TorusPresentation

variable {W : CompactCarrier.{u}}

def shrink (T : TorusPresentation W) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : TorusPresentation W where
  cutCarrier := T.cutCarrier
  components := T.components
  pairing := T.pairing.shrink hδ hδ1
  externalCount := T.externalCount
  external := T.external.shrink hδ hδ1
  cutExternal := T.cutExternal.shrink hδ hδ1
  external_exhausted := by
    rw [BoundaryTori.shrink_image]
    exact T.external_exhausted
  cut_boundary_exhausted := by
    rw [BoundaryTori.shrink_image]
    exact T.cut_boundary_exhausted
  external_disjoint := by
    rw [BoundaryTori.shrink_image]
    exact T.external_disjoint
  reconstruction := T.reconstruction
  quotient_smooth := T.quotient_smooth
  quotient_oriented := T.quotient_oriented
  interiorImage := T.interiorImage
  interiorDiffeomorph := T.interiorDiffeomorph
  interior_map := T.interior_map
  seam i := shrinkSignedCollar hδ (T.seam i)
  seam_source i := shrinkSignedCollar_source hδ hδ1 (T.seam_source i)
  seam_zero i t := by
    change T.seam i (t, δ * 0) = _
    rw [mul_zero]
    exact T.seam_zero i t
  seam_positive i t s hs h1 := by
    change T.seam i (t, δ * s) = T.reconstruction (T.pairing.quotientMap (T.pairing.rightCollar i
      (T.pairing.matching i t, halfSpaceScale hδ (halfPoint s hs))))
    rw [halfSpaceScale_halfPoint]
    exact T.seam_positive i t (δ * s) _ (by nlinarith)
  seam_negative i t s hs h1 := by
    change T.seam i (t, δ * s) = T.reconstruction (T.pairing.quotientMap (T.pairing.leftCollar i
      (t, halfSpaceScale hδ (halfPoint (-s) (neg_nonneg.mpr hs)))))
    rw [halfSpaceScale_halfPoint]
    have e : halfPoint (δ * -s) (mul_nonneg hδ.le (neg_nonneg.mpr hs)) =
        halfPoint (-(δ * s)) (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hδ.le hs)) := by
      congr 1
      ring
    rw [e]
    exact T.seam_negative i t (δ * s) (mul_nonpos_of_nonneg_of_nonpos hδ.le hs) (by nlinarith)
  seam_interior i := (shrinkSignedCollar_target_subset hδ _).trans (T.seam_interior i)
  seam_disjoint _ _ hij := (T.seam_disjoint hij).mono (shrinkSignedCollar_target_subset hδ _)
    (shrinkSignedCollar_target_subset hδ _)
  marked_collar i p hp := T.marked_collar i _ (halfSpaceScale_mem hδ hδ1 hp)
  external_seam_disjoint i j := (T.external_seam_disjoint i j).mono
    (shrinkHalfCollar_target_subset hδ _) (shrinkSignedCollar_target_subset hδ _)
  leftPiece := T.leftPiece
  rightPiece := T.rightPiece
  left_owned := T.left_owned
  right_owned := T.right_owned
  externalPiece := T.externalPiece
  external_owned i := by
    rw [BoundaryTori.shrink_torusMap]
    exact T.external_owned i

variable (T : TorusPresentation W) (hδ : 0 < δ) (hδ1 : δ ≤ 1)

theorem shrink_pairing_count : (T.shrink hδ hδ1).pairing.count = T.pairing.count := rfl

theorem shrink_matching : (T.shrink hδ hδ1).pairing.matching = T.pairing.matching := rfl

theorem shrink_torusUnit (j : Fin T.pairing.count) :
    torusUnit ((T.shrink hδ hδ1).pairing.matching j) = torusUnit (T.pairing.matching j) := rfl

theorem shrink_externalCount : (T.shrink hδ hδ1).externalCount = T.externalCount := rfl

theorem shrink_external : (T.shrink hδ hδ1).external = T.external.shrink hδ hδ1 := rfl

theorem shrink_sideCollar :
    ∀ s : T.Side, (T.shrink hδ hδ1).sideCollar s = shrinkHalfCollar hδ (T.sideCollar s)
  | .inl _ => rfl
  | .inr (.inl _) => rfl
  | .inr (.inr _) => rfl

theorem shrink_sidePiece : ∀ s : T.Side, (T.shrink hδ hδ1).sidePiece s = T.sidePiece s
  | .inl _ => rfl
  | .inr (.inl _) => rfl
  | .inr (.inr _) => rfl

end TorusPresentation

def PlanarBase.shrink {k : ℕ} (P : PlanarBase.{u} k) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    PlanarBase.{u} k where
  surface := P.surface
  collar j := shrinkHalfCollar hδ (P.collar j)
  source_eq j := shrinkHalfCollar_source hδ hδ1 (P.source_eq j)
  boundary_zero j t := by
    change (SurfaceModel.model P.surface.kind).IsBoundaryPoint
      (P.collar j (t, halfSpaceScale hδ halfZero))
    rw [halfSpaceScale_halfZero]
    exact P.boundary_zero j t
  disjoint _ _ hij := (P.disjoint hij).mono (shrinkHalfCollar_target_subset hδ _)
    (shrinkHalfCollar_target_subset hδ _)
  boundary_exhausted := by
    rw [P.boundary_exhausted]
    refine iUnion_congr fun j => ?_
    congr 1
    funext t
    change P.collar j (t, halfZero) = P.collar j (t, halfSpaceScale hδ halfZero)
    rw [halfSpaceScale_halfZero]
  embedding := P.embedding
  isSmoothEmbedding := P.isSmoothEmbedding
  range_embedding := P.range_embedding
  embedding_collar j t := by
    change P.embedding (P.collar j (t, halfSpaceScale hδ halfZero)) = _
    rw [halfSpaceScale_halfZero]
    exact P.embedding_collar j t

namespace TorusPresentation

variable {W : CompactCarrier.{u}}

def shrinkPiece (T : TorusPresentation W) (i : Fin T.components.count) {k : ℕ}
    (B : PlanarBase.{u} k) (port : Fin k ≃ T.OwnedSide i)
    (Θ : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      T.cutCarrier.model⟯ T.components.piece i)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcollar : ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      T.pieceCollar i (port j) p = Θ (B.collar j (p.1.1, p.2), p.1.2)) :
    ProductFibredPiece (T.shrink hδ hδ1) i k where
  base := B.shrink hδ hδ1
  port := port.trans (Equiv.subtypeEquivRight fun s => by
    rw [shrink_sidePiece]
    exact Iff.rfl)
  trivialization := Θ
  collar_eq j p hp := Subtype.ext
    ((TorusPresentation.pieceCollar_apply _ _ _ hp).trans
      ((congrArg (fun c => c p) (shrink_sideCollar T hδ hδ1 (port j).val)).trans
        ((TorusPresentation.pieceCollar_apply T i (port j)
          (halfSpaceScale_mem hδ hδ1 hp)).symm.trans (congrArg Subtype.val
            (hcollar j _ (halfSpaceScale_mem hδ hδ1 hp) (halfSpaceScale_lt hδ hp))))))

def recollar (T : TorusPresentation W) (kind : Fin T.components.count → ℕ)
    (hkind : ∀ i, kind i ∈ ({1, 2, 3} : Finset ℕ)) (base : ∀ i, PlanarBase.{u} (kind i))
    (port : ∀ i, Fin (kind i) ≃ T.OwnedSide i)
    (triv : ∀ i, ((base i).surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
      (base i).surface.kind).prod (𝓡 1), T.cutCarrier.model⟯
        T.components.piece i)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcollar : ∀ i j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      T.pieceCollar i (port i j) p = triv i ((base i).collar j (p.1.1, p.2), p.1.2)) :
    ElementaryPresentation W where
  toTorus := T.shrink hδ hδ1
  kind := kind
  kind_mem := hkind
  piece i := T.shrinkPiece i (base i) (port i) (triv i) hδ hδ1 (hcollar i)

end TorusPresentation

end Shrink

section Adapter

theorem ElementaryPresentation.exists_transport_subCollar {W : CompactCarrier.{u}}
    (E : ElementaryPresentation W) {n : ℕ} (B : BoundaryTori W n)
    (h : E.toTorus.externalCount = n) (ψ : Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (h₀ : ∀ i t, E.toTorus.external.collar (Fin.cast h.symm i) (t, halfZero) =
      B.collar i (ψ i t, halfZero)) :
    ∃ δ > (0 : ℝ), ∃ Φ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier,
      ∃ hΦ : Φ.preservesOrientation W.orientation W.orientation,
        ∀ i p, p ∈ halfCollarSource → p.2.val 0 < δ →
          (E.transport Φ hΦ).toTorus.external.collar (Fin.cast h.symm i) p =
            B.collar i (ψ i p.1, p.2) := by
  subst h
  obtain ⟨δ, hδ, Φ, hΦ, hagree, -⟩ :=
    exists_boundaryTori_straightening E.toTorus.external B ψ h₀
  exact ⟨δ, hδ, Φ, hΦ, hagree⟩

theorem elementarizeOnSubCollar_of_torus_eq
    (h : ∀ (W : CompactCarrier.{u}) (G : RawGraphPresentation W),
      ∃ E : ElementaryPresentation W, ∃ h : E.toTorus.externalCount = G.externalCount,
        ∃ ψ : Fin G.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
          ∀ i t, E.toTorus.external.collar (Fin.cast h.symm i) (t, halfZero) =
            G.external.collar i (ψ i t, halfZero)) :
    ElementarizeOnSubCollar.{u} := by
  intro W G
  obtain ⟨E, hc, ψ, h₀⟩ := h W G
  obtain ⟨δ, hδ, Φ, hΦ, hagree⟩ := E.exists_transport_subCollar G.external hc ψ h₀
  exact ⟨E.transport Φ hΦ, hc, ψ, δ, hδ, hagree⟩

end Adapter

section Marks

variable {δ : ℝ}

def ElementaryPresentation.shrink {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : ElementaryPresentation W :=
  E.toTorus.recollar E.kind E.kind_mem (fun i => (E.piece i).base) (fun i => (E.piece i).port)
    (fun i => (E.piece i).trivialization) hδ hδ1 fun i j p hp _ => (E.piece i).collar_eq j p hp

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W) (hδ : 0 < δ) (hδ1 : δ ≤ 1)

theorem shrink_toTorus : (E.shrink hδ hδ1).toTorus = E.toTorus.shrink hδ hδ1 := rfl

theorem shrink_complexity : (E.shrink hδ hδ1).complexity = E.complexity := rfl

theorem shrink_matching :
    (E.shrink hδ hδ1).toTorus.pairing.matching = E.toTorus.pairing.matching := rfl

theorem shrink_fillingDistance (j : Fin E.toTorus.pairing.count) (b : Bool) :
    (E.shrink hδ hδ1).fillingDistance j b = E.fillingDistance j b := by
  cases b <;> rfl

theorem shrink_external_collar_eq_of_subCollar {n : ℕ} (B : BoundaryTori W n)
    (h : E.toTorus.externalCount = n) (ψ : Fin n → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (hsub : ∀ i p, p ∈ halfCollarSource → p.2.val 0 < δ →
      E.toTorus.external.collar (Fin.cast h.symm i) p = B.collar i (ψ i p.1, p.2))
    (i : Fin n) (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    (E.shrink hδ hδ1).toTorus.external.collar (Fin.cast h.symm i) p =
      (B.shrink hδ hδ1).collar i (ψ i p.1, p.2) :=
  hsub i (p.1, halfSpaceScale hδ p.2) (halfSpaceScale_mem hδ hδ1 hp) (halfSpaceScale_lt hδ hp)

end ElementaryPresentation

end Marks

section Product

def torusCollarReorder : (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel,
    circleCollarModel.prod (𝓡 1)⟯ ((Circle × EuclideanHalfSpace 1) × Circle) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun q := ((q.1.1, q.2), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
    (contMDiff_snd.comp contMDiff_fst)
  contMDiff_invFun := ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
    (contMDiff_snd.comp contMDiff_fst)

variable {S : CompactSurface.{u}} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} {N : Type*} [TopologicalSpace N]
  [ChartedSpace G N]

def trivCollar (b : PartialDiffeomorph circleCollarModel (SurfaceModel.model S.kind)
      (Circle × EuclideanHalfSpace 1) S.Carrier ∞)
    (Θ : (S.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model S.kind).prod (𝓡 1), J⟯ N) :
    PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞ :=
  torusCollarReorder.toPartialDiffeomorph.trans
    ((DifferentialGeometry.Topology.PartialDiffeomorph.prod b
      (Diffeomorph.refl (𝓡 1) Circle ∞).toPartialDiffeomorph).trans Θ.toPartialDiffeomorph)

theorem trivCollar_apply (b : PartialDiffeomorph circleCollarModel
      (SurfaceModel.model S.kind) (Circle × EuclideanHalfSpace 1) S.Carrier ∞)
    (Θ : (S.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model S.kind).prod (𝓡 1), J⟯ N)
    (p : Torus × EuclideanHalfSpace 1) : trivCollar b Θ p = Θ (b (p.1.1, p.2), p.1.2) := rfl

theorem trivCollar_source {b : PartialDiffeomorph circleCollarModel
      (SurfaceModel.model S.kind) (Circle × EuclideanHalfSpace 1) S.Carrier ∞}
    (hb : b.source = circleCollarSource)
    (Θ : (S.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model S.kind).prod (𝓡 1), J⟯ N) :
    (trivCollar b Θ).source = halfCollarSource := by
  ext p
  constructor
  · intro hp
    have h1 : (p.1.1, p.2) ∈ b.source := hp.2.1.1
    rw [hb] at h1
    exact h1
  · intro hp
    refine ⟨mem_univ _, ⟨⟨?_, mem_univ _⟩, mem_univ _⟩⟩
    change (p.1.1, p.2) ∈ b.source
    rw [hb]
    exact hp

theorem trivCollar_target_subset (b : PartialDiffeomorph circleCollarModel
      (SurfaceModel.model S.kind) (Circle × EuclideanHalfSpace 1) S.Carrier ∞)
    (Θ : (S.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model S.kind).prod (𝓡 1), J⟯ N) :
    (trivCollar b Θ).target ⊆ Θ '' (b.target ×ˢ univ) := by
  intro y hy
  have hs := (trivCollar b Θ).map_target' hy
  rw [← (trivCollar b Θ).right_inv' hy]
  exact ⟨_, ⟨b.map_source' hs.2.1.1, mem_univ _⟩, rfl⟩

end Product

namespace TorusPresentation

variable {W : CompactCarrier.{u}}

def trivBoundaryTori (T : TorusPresentation W) (i : Fin T.components.count) {k : ℕ}
    (B : PlanarBase.{u} k) (port : Fin k ≃ T.OwnedSide i)
    (ψ : Fin k → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (Θ : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      T.cutCarrier.model⟯ T.components.piece i)
    (h₀ : ∀ j (t : Torus), T.pieceCollar i (port j) (ψ j t, halfZero) =
      Θ (B.collar j (t.1, halfZero), t.2)) :
    BoundaryTori (GC.Topology.componentCarrier T.cutCarrier T.components i)
      (Fintype.card (T.OwnedSide i)) where
  collar r := trivCollar (B.collar (port.symm ((Fintype.equivFin _).symm r))) Θ
  source_eq r := trivCollar_source (B.source_eq _) Θ
  boundary_zero r t := by
    have e : trivCollar (B.collar (port.symm ((Fintype.equivFin _).symm r))) Θ
        (t, halfZero) = (T.pieceBoundaryTori i).collar r
          (ψ (port.symm ((Fintype.equivFin _).symm r)) t, halfZero) := by
      change Θ (B.collar _ (t.1, halfZero), t.2) = T.pieceCollar i ((Fintype.equivFin _).symm r)
        (ψ (port.symm ((Fintype.equivFin _).symm r)) t, halfZero)
      rw [← h₀, Equiv.apply_symm_apply]
    exact (congrArg (fun x : (GC.Topology.componentCarrier T.cutCarrier T.components i).Carrier =>
      (GC.Topology.componentCarrier T.cutCarrier T.components i).model.IsBoundaryPoint x)
        e).mpr ((T.pieceBoundaryTori i).boundary_zero r _)
  disjoint r r' h := by
    have hj : port.symm ((Fintype.equivFin _).symm r) ≠
        port.symm ((Fintype.equivFin _).symm r') := fun e =>
      h ((Fintype.equivFin _).symm.injective (port.symm.injective e))
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    obtain ⟨⟨a, z⟩, ha, rfl⟩ := trivCollar_target_subset _ Θ hx
    obtain ⟨⟨a', z'⟩, ha', he⟩ := trivCollar_target_subset _ Θ hx'
    have e := Θ.injective he
    have ha'' : a ∈ (B.collar (port.symm ((Fintype.equivFin _).symm r'))).target := by
      have := ha'.1
      rw [congrArg Prod.fst e] at this
      exact this
    exact (B.disjoint hj).le_bot ⟨ha.1, ha''⟩

variable (T : TorusPresentation W) (i : Fin T.components.count) {k : ℕ} (B : PlanarBase.{u} k)
  (port : Fin k ≃ T.OwnedSide i) (ψ : Fin k → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
  (Θ : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
    T.cutCarrier.model⟯ T.components.piece i)
  (h₀ : ∀ j (t : Torus), T.pieceCollar i (port j) (ψ j t, halfZero) =
    Θ (B.collar j (t.1, halfZero), t.2))

theorem trivBoundaryTori_collar_apply (r : Fin (Fintype.card (T.OwnedSide i)))
    (p : Torus × EuclideanHalfSpace 1) :
    (T.trivBoundaryTori i B port ψ Θ h₀).collar r p =
      Θ (B.collar (port.symm ((Fintype.equivFin _).symm r)) (p.1.1, p.2), p.1.2) := rfl

theorem trivBoundaryTori_collar_zero (r : Fin (Fintype.card (T.OwnedSide i))) (t : Torus) :
    (T.trivBoundaryTori i B port ψ Θ h₀).collar r (t, halfZero) =
      (T.pieceBoundaryTori i).collar r
        (ψ (port.symm ((Fintype.equivFin _).symm r)) t, halfZero) := by
  change Θ (B.collar _ (t.1, halfZero), t.2) = T.pieceCollar i ((Fintype.equivFin _).symm r)
    (ψ (port.symm ((Fintype.equivFin _).symm r)) t, halfZero)
  rw [← h₀, Equiv.apply_symm_apply]

theorem trivBoundaryTori_image :
    (T.trivBoundaryTori i B port ψ Θ h₀).image = (T.pieceBoundaryTori i).image := by
  unfold BoundaryTori.image
  refine iUnion_congr fun r => ?_
  have hfun : (T.trivBoundaryTori i B port ψ Θ h₀).torusMap r =
      (T.pieceBoundaryTori i).torusMap r ∘ ψ (port.symm ((Fintype.equivFin _).symm r)) :=
    funext fun t => trivBoundaryTori_collar_zero T i B port ψ Θ h₀ r t
  rw [hfun]
  exact (ψ _).surjective.range_comp _

def trivPresentation :
    TorusPresentation (GC.Topology.componentCarrier T.cutCarrier T.components i) :=
  { T.ofPiece i with
    external := T.trivBoundaryTori i B port ψ Θ h₀
    cutExternal := T.trivBoundaryTori i B port ψ Θ h₀
    external_exhausted := (T.pieceBoundaryTori_image i).trans
      (trivBoundaryTori_image T i B port ψ Θ h₀).symm
    cut_boundary_exhausted := by
      have h0 : (⋃ m : Fin (T.ofPiece i).pairing.count,
          (T.ofPiece i).pairing.gluing.block m) = ∅ := Set.iUnion_eq_empty.mpr fun m => m.elim0
      rw [h0, Set.empty_union]
      exact (T.pieceBoundaryTori_image i).trans (trivBoundaryTori_image T i B port ψ Θ h₀).symm
    external_disjoint := by
      have h0 : (⋃ m : Fin (T.ofPiece i).pairing.count,
          (T.ofPiece i).pairing.gluing.block m) = ∅ := Set.iUnion_eq_empty.mpr fun m => m.elim0
      rw [h0]
      exact Set.empty_disjoint _
    marked_collar := fun _ _ _ => rfl
    external_seam_disjoint := fun _ m => m.elim0
    external_owned := fun _ => Set.subset_univ _ }

def trivOwnedSide :
    T.OwnedSide i ≃ (T.trivPresentation i B port ψ Θ h₀).OwnedSide ⟨0, Nat.one_pos⟩ where
  toFun s := ⟨.inr (.inr (Fintype.equivFin _ s)), rfl⟩
  invFun s := match s with
    | ⟨.inl m, _⟩ => m.elim0
    | ⟨.inr (.inl m), _⟩ => m.elim0
    | ⟨.inr (.inr j), _⟩ => (Fintype.equivFin _).symm j
  left_inv s := Equiv.symm_apply_apply _ s
  right_inv s := by
    rcases s with ⟨m | m | j, h⟩
    · exact m.elim0
    · exact m.elim0
    · exact Subtype.ext (congrArg (fun j => Sum.inr (Sum.inr j)) (Equiv.apply_symm_apply _ j))

def trivPiece : ProductFibredPiece (T.trivPresentation i B port ψ Θ h₀) ⟨0, Nat.one_pos⟩ k where
  base := B
  port := port.trans (T.trivOwnedSide i B port ψ Θ h₀)
  trivialization := Θ.trans
    (topOpensDiffeomorph (I := T.cutCarrier.model) (T.components.piece i)).symm
  collar_eq j p hp := by
    apply Subtype.ext
    rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
    change Θ (B.collar (port.symm ((Fintype.equivFin _).symm (Fintype.equivFin _ (port j))))
      (p.1.1, p.2), p.1.2) = Θ (B.collar j (p.1.1, p.2), p.1.2)
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

include B port ψ Θ h₀ in
def trivElementary (hk : k ∈ ({1, 2, 3} : Finset ℕ)) :
    ElementaryPresentation (GC.Topology.componentCarrier T.cutCarrier T.components i) where
  toTorus := T.trivPresentation i B port ψ Θ h₀
  kind _ := k
  kind_mem _ := hk
  piece m := by
    have hm : m = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.mp m.2)
    rw [hm]
    exact T.trivPiece i B port ψ Θ h₀

include B port ψ Θ h₀ in
theorem exists_germ_elementary (hk : k ∈ ({1, 2, 3} : Finset ℕ)) :
    ∃ E : ElementaryPresentation (GC.Topology.componentCarrier T.cutCarrier T.components i),
      ∃ h : E.toTorus.externalCount = (T.ofPiece i).externalCount,
        ∃ ψ : Fin (T.ofPiece i).externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
          ∃ δ > (0 : ℝ), ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
            E.toTorus.external.collar (Fin.cast h.symm j) p =
              (T.ofPiece i).external.collar j (ψ j p.1, p.2) := by
  obtain ⟨δ, hδ, Φ, hΦ, hagree⟩ := (T.trivElementary i B port ψ Θ h₀ hk).exists_transport_subCollar
    (T.ofPiece i).external rfl (fun r => ψ (port.symm ((Fintype.equivFin _).symm r)))
    (trivBoundaryTori_collar_zero T i B port ψ Θ h₀)
  exact ⟨_, rfl, _, δ, hδ, hagree⟩

include B port ψ Θ h₀ in
theorem exists_germ_trivialization :
    ∃ δ > (0 : ℝ), ∃ Θ' : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
      B.surface.kind).prod (𝓡 1), T.cutCarrier.model⟯ T.components.piece i,
        ∀ j p, p ∈ halfCollarSource → p.2.val 0 < δ →
          T.pieceCollar i (port j) (ψ j p.1, p.2) = Θ' (B.collar j (p.1.1, p.2), p.1.2) := by
  obtain ⟨δ, hδ, Φ, -, hagree, -⟩ := exists_boundaryTori_straightening
    (T.trivBoundaryTori i B port ψ Θ h₀) (T.pieceBoundaryTori i)
    (fun r => ψ (port.symm ((Fintype.equivFin _).symm r)))
    (trivBoundaryTori_collar_zero T i B port ψ Θ h₀)
  refine ⟨δ, hδ, Θ.trans Φ, fun j p hp hlt => ?_⟩
  have e1 : port.symm ((Fintype.equivFin _).symm (Fintype.equivFin _ (port j))) = j := by simp
  have e2 : (Fintype.equivFin _).symm (Fintype.equivFin _ (port j)) = port j := by simp
  have e3 : T.pieceCollar i ((Fintype.equivFin _).symm (Fintype.equivFin _ (port j)))
      (ψ (port.symm ((Fintype.equivFin _).symm (Fintype.equivFin _ (port j)))) p.1, p.2) =
        T.pieceCollar i (port j) (ψ j p.1, p.2) := by
    rw [e1, e2]
  have h := hagree (Fintype.equivFin _ (port j)) p hp hlt
  exact e3.symm.trans
    (h.symm.trans (congrArg (fun j' => Φ (Θ (B.collar j' (p.1.1, p.2), p.1.2))) e1))

include B port Θ in
theorem exists_shrink_elementary_piece (h₁ : ∀ j (t : Torus),
      T.pieceCollar i (port j) (t, halfZero) = Θ (B.collar j (t.1, halfZero), t.2))
    (hk : k ∈ ({1, 2, 3} : Finset ℕ)) :
    ∃ δ, ∃ hδ : 0 < δ, ∃ hδ1 : δ ≤ 1,
      ∃ E : ElementaryPresentation (GC.Topology.componentCarrier (T.shrink hδ hδ1).cutCarrier
        (T.shrink hδ hδ1).components i),
      ∃ h : E.toTorus.externalCount = ((T.shrink hδ hδ1).ofPiece i).externalCount,
        ∃ ψ : Fin ((T.shrink hδ hδ1).ofPiece i).externalCount →
            (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
          ∀ j p, p ∈ halfCollarSource → E.toTorus.external.collar (Fin.cast h.symm j) p =
            ((T.shrink hδ hδ1).ofPiece i).external.collar j (ψ j p.1, p.2) := by
  obtain ⟨δ, hδ, Θ', hΘ'⟩ :=
    T.exists_germ_trivialization i B port (fun _ => Diffeomorph.refl torusModel Torus ∞) Θ h₁
  have hδ' : 0 < min δ 1 := lt_min hδ one_pos
  have hδ1 : min δ 1 ≤ 1 := min_le_right _ _
  let P := T.shrinkPiece i B port Θ' hδ' hδ1
    fun j p hp hlt => hΘ' j p hp (lt_of_lt_of_le hlt (min_le_left _ _))
  let E : ElementaryPresentation (GC.Topology.componentCarrier (T.shrink hδ' hδ1).cutCarrier
      (T.shrink hδ' hδ1).components i) :=
    { toTorus := (T.shrink hδ' hδ1).ofPiece i
      kind := fun _ => k
      kind_mem := fun _ => hk
      piece := fun m => by
        have hm : m = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.mp m.2)
        rw [hm]
        exact P.ofPiece }
  exact ⟨min δ 1, hδ', hδ1, E, rfl, fun _ => Diffeomorph.refl torusModel Torus ∞,
    fun _ _ _ => rfl⟩

end TorusPresentation

namespace TorusPresentation

variable {W : CompactCarrier.{u}}

def reparam (T : TorusPresentation W) (ψ : T.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)) :
    TorusPresentation W where
  cutCarrier := T.cutCarrier
  components := T.components
  pairing := T.pairing.reparam (fun k => ψ (.inl k)) (fun k => ψ (.inr (.inl k)))
  externalCount := T.externalCount
  external := T.external.reparam fun i => ψ (.inr (.inr i))
  cutExternal := T.cutExternal.reparam fun i => ψ (.inr (.inr i))
  external_exhausted := by
    rw [BoundaryTori.reparam_image]
    exact T.external_exhausted
  cut_boundary_exhausted := by
    rw [BoundaryTori.reparam_image]
    exact T.cut_boundary_exhausted
  external_disjoint := by
    rw [BoundaryTori.reparam_image]
    exact T.external_disjoint
  reconstruction := T.reconstruction
  quotient_smooth := T.quotient_smooth
  quotient_oriented := T.quotient_oriented
  interiorImage := T.interiorImage
  interiorDiffeomorph := T.interiorDiffeomorph
  interior_map := T.interior_map
  seam k := signedReparam (ψ (.inl k)) (T.seam k)
  seam_source k := signedReparam_source _ (T.seam_source k)
  seam_zero k t := T.seam_zero k (ψ (.inl k) t)
  seam_positive k t s hs h1 := by
    change T.seam k (ψ (.inl k) t, s) = T.reconstruction (T.pairing.quotientMap
      (T.pairing.rightCollar k (ψ (.inr (.inl k)) ((ψ (.inr (.inl k))).symm
        (T.pairing.matching k (ψ (.inl k) t))), halfPoint s hs)))
    rw [Diffeomorph.apply_symm_apply]
    exact T.seam_positive k _ s hs h1
  seam_negative k t s hs h1 := T.seam_negative k (ψ (.inl k) t) s hs h1
  seam_interior k := (signedReparam_target_subset _ _).trans (T.seam_interior k)
  seam_disjoint _ _ hij := (T.seam_disjoint hij).mono (signedReparam_target_subset _ _)
    (signedReparam_target_subset _ _)
  marked_collar i p hp := T.marked_collar i _ hp
  external_seam_disjoint i j := (T.external_seam_disjoint i j).mono
    (torusReparam_target_subset _ _) (signedReparam_target_subset _ _)
  leftPiece := T.leftPiece
  rightPiece := T.rightPiece
  left_owned := T.left_owned
  right_owned := T.right_owned
  externalPiece := T.externalPiece
  external_owned i := by
    rw [BoundaryTori.reparam_torusMap, Set.range_comp]
    exact (Set.image_subset_range _ _).trans (T.external_owned i)

variable (T : TorusPresentation W) (ψ : T.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))

theorem reparam_pairing_count : (T.reparam ψ).pairing.count = T.pairing.count := rfl

theorem reparam_matching (k : Fin T.pairing.count) : (T.reparam ψ).pairing.matching k =
    (ψ (.inl k)).trans ((T.pairing.matching k).trans (ψ (.inr (.inl k))).symm) := rfl

theorem reparam_externalCount : (T.reparam ψ).externalCount = T.externalCount := rfl

theorem reparam_external_collar_apply (i : Fin T.externalCount)
    (p : Torus × EuclideanHalfSpace 1) :
    (T.reparam ψ).external.collar i p = T.external.collar i (ψ (.inr (.inr i)) p.1, p.2) := rfl

theorem reparam_sideCollar :
    ∀ s : T.Side, (T.reparam ψ).sideCollar s = torusReparam (ψ s) (T.sideCollar s)
  | .inl _ => rfl
  | .inr (.inl _) => rfl
  | .inr (.inr _) => rfl

theorem reparam_sidePiece : ∀ s : T.Side, (T.reparam ψ).sidePiece s = T.sidePiece s
  | .inl _ => rfl
  | .inr (.inl _) => rfl
  | .inr (.inr _) => rfl

def reparamOwnedSide (i : Fin T.components.count) :
    T.OwnedSide i ≃ (T.reparam ψ).OwnedSide i :=
  Equiv.subtypeEquivRight fun s => by
    rw [reparam_sidePiece]
    exact Iff.rfl

variable {δ : ℝ}

def recollarReparam (kind : Fin T.components.count → ℕ)
    (hkind : ∀ i, kind i ∈ ({1, 2, 3} : Finset ℕ)) (base : ∀ i, PlanarBase.{u} (kind i))
    (port : ∀ i, Fin (kind i) ≃ T.OwnedSide i)
    (triv : ∀ i, ((base i).surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
      (base i).surface.kind).prod (𝓡 1), T.cutCarrier.model⟯
        T.components.piece i)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcollar : ∀ i j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      T.pieceCollar i (port i j) (ψ (port i j).val p.1, p.2) =
        triv i ((base i).collar j (p.1.1, p.2), p.1.2)) :
    ElementaryPresentation W :=
  (T.reparam ψ).recollar kind hkind base (fun i => (port i).trans (T.reparamOwnedSide ψ i)) triv
    hδ hδ1 fun i j p hp hlt => Subtype.ext
      ((TorusPresentation.pieceCollar_apply _ _ _ hp).trans
        ((congrArg (fun c => c p) (reparam_sideCollar T ψ (port i j).val)).trans
          ((TorusPresentation.pieceCollar_apply T i (port i j)
            (p := (ψ (port i j).val p.1, p.2)) hp).symm.trans
              (congrArg Subtype.val (hcollar i j p hp hlt)))))

theorem recollarReparam_toTorus (kind : Fin T.components.count → ℕ)
    (hkind : ∀ i, kind i ∈ ({1, 2, 3} : Finset ℕ)) (base : ∀ i, PlanarBase.{u} (kind i))
    (port : ∀ i, Fin (kind i) ≃ T.OwnedSide i)
    (triv : ∀ i, ((base i).surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
      (base i).surface.kind).prod (𝓡 1), T.cutCarrier.model⟯
        T.components.piece i)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcollar : ∀ i j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      T.pieceCollar i (port i j) (ψ (port i j).val p.1, p.2) =
        triv i ((base i).collar j (p.1.1, p.2), p.1.2)) :
    (T.recollarReparam ψ kind hkind base port triv hδ hδ1 hcollar).toTorus =
      (T.reparam ψ).shrink hδ hδ1 := rfl

theorem recollarReparam_complexity (kind : Fin T.components.count → ℕ)
    (hkind : ∀ i, kind i ∈ ({1, 2, 3} : Finset ℕ)) (base : ∀ i, PlanarBase.{u} (kind i))
    (port : ∀ i, Fin (kind i) ≃ T.OwnedSide i)
    (triv : ∀ i, ((base i).surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
      (base i).surface.kind).prod (𝓡 1), T.cutCarrier.model⟯
        T.components.piece i)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcollar : ∀ i j p, p ∈ halfCollarSource → p.2.val 0 < δ →
      T.pieceCollar i (port i j) (ψ (port i j).val p.1, p.2) =
        triv i ((base i).collar j (p.1.1, p.2), p.1.2)) :
    (T.recollarReparam ψ kind hkind base port triv hδ hδ1 hcollar).complexity =
      T.pairing.count := rfl

theorem exists_elementary_of_torus_products (kind : Fin T.components.count → ℕ)
    (hkind : ∀ i, kind i ∈ ({1, 2, 3} : Finset ℕ)) (base : ∀ i, PlanarBase.{u} (kind i))
    (port : ∀ i, Fin (kind i) ≃ T.OwnedSide i)
    (Θ : ∀ i, ((base i).surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
      (base i).surface.kind).prod (𝓡 1), T.cutCarrier.model⟯
        T.components.piece i)
    (h₀ : ∀ i j (t : Torus), T.pieceCollar i (port i j) (ψ (port i j).val t, halfZero) =
      Θ i ((base i).collar j (t.1, halfZero), t.2)) :
    ∃ δ, ∃ hδ : 0 < δ, ∃ hδ1 : δ ≤ 1, ∃ E : ElementaryPresentation W,
      E.toTorus = (T.reparam ψ).shrink hδ hδ1 ∧ E.complexity = T.pairing.count := by
  have hgerm := fun i => T.exists_germ_trivialization i (base i) (port i)
    (fun j => ψ (port i j).val) (Θ i) (h₀ i)
  choose δ hδ Θ' hΘ' using hgerm
  have hne : (Finset.univ : Finset (Fin T.components.count)).Nonempty :=
    ⟨⟨0, T.components.count_pos⟩, Finset.mem_univ _⟩
  let ε := min (Finset.univ.inf' hne δ) 1
  have hε : 0 < ε := lt_min ((Finset.lt_inf'_iff hne).mpr fun i _ => hδ i) one_pos
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεi (i : Fin T.components.count) : ε ≤ δ i :=
    (min_le_left _ _).trans (Finset.inf'_le δ (Finset.mem_univ i))
  exact ⟨ε, hε, hε1, T.recollarReparam ψ kind hkind base port Θ' hε hε1
    (fun i j p hp hlt => hΘ' i j p hp (lt_of_lt_of_le hlt (hεi i))), rfl, rfl⟩

end TorusPresentation

theorem subset_of_isPreconnected_of_subset_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*}
    [Finite ι] {F : ι → Set X} (hF : ∀ a, IsClosed (F a))
    (hd : Pairwise fun a b => Disjoint (F a) (F b)) {K : Set X} (hK : IsPreconnected K)
    (hKF : K ⊆ ⋃ a, F a) {a : ι} (ha : (K ∩ F a).Nonempty) : K ⊆ F a := by
  have hV : IsClosed (⋃ b ∈ ({a}ᶜ : Set ι), F b) :=
    (Set.toFinite _).isClosed_biUnion fun b _ => hF b
  have hdis : ∀ x, x ∈ F a → x ∉ ⋃ b ∈ ({a}ᶜ : Set ι), F b := by
    intro x hxa hxV
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp hxV
    exact (hd (Ne.symm (Set.mem_compl_singleton_iff.mp hb))).le_bot ⟨hxa, hxb⟩
  have hcover : K ⊆ F a ∪ ⋃ b ∈ ({a}ᶜ : Set ι), F b := by
    intro x hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hKF hx)
    by_cases hba : b = a
    · exact Or.inl (hba ▸ hb)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨b, Set.mem_compl_singleton_iff.mpr hba, hb⟩)
  have hempty : K ∩ (F a ∩ ⋃ b ∈ ({a}ᶜ : Set ι), F b) = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun x hx => hdis x hx.2.1 hx.2.2
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hK) (F a) _ (hF a) hV hcover hempty
    with h | h
  · exact h
  · obtain ⟨x, hxK, hxa⟩ := ha
    exact (hdis x hxa (h hxK)).elim

namespace TorusPresentation

variable {W : CompactCarrier.{u}}

theorem exists_port_of_diffeomorph (T : TorusPresentation W) (i : Fin T.components.count)
    {k : ℕ} (B : PlanarBase.{u} k) (hcard : Fintype.card (T.OwnedSide i) = k)
    (e : (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1),
      T.cutCarrier.model⟯ T.components.piece i) :
    ∃ port : Fin k ≃ T.OwnedSide i, ∃ ψ : Fin k → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus),
      ∀ j (t : Torus), T.pieceCollar i (port j) (ψ j t, halfZero) =
        e (B.collar j (t.1, halfZero), t.2) := by
  classical
  let BT := T.pieceBoundaryTori i
  let g : Fin k → Torus → B.surface.Carrier × Circle := fun j t => (B.collar j (t.1, halfZero), t.2)
  have hsrc (j : Fin k) (c : Circle) : (c, halfZero) ∈ (B.collar j).source := by
    rw [B.source_eq]
    change (0 : ℝ) < 1
    norm_num
  have hBsrc (r : Fin (Fintype.card (T.OwnedSide i))) (t : Torus) :
      (t, halfZero) ∈ (BT.collar r).source := by
    rw [BT.source_eq]
    exact zero_mem_halfCollarSource t
  have hg (j : Fin k) : ContMDiff torusModel ((SurfaceModel.model B.surface.kind).prod (𝓡 1)) ∞
      (g j) :=
    ((B.collar j).contMDiffOn.comp_contMDiff (contMDiff_fst.prodMk contMDiff_const)
      fun t => hsrc j t.1).prodMk contMDiff_snd
  have heg (j : Fin k) : Continuous (e ∘ g j) := e.continuous.comp (hg j).continuous
  let Ej : Fin k → Set (T.components.piece i) := fun j => range (e ∘ g j)
  let Fr : Fin (Fintype.card (T.OwnedSide i)) → Set (T.components.piece i) :=
    fun r => range (BT.torusMap r)
  have hEc (j : Fin k) : IsClosed (Ej j) := (isCompact_range (heg j)).isClosed
  have hFc (r : Fin (Fintype.card (T.OwnedSide i))) : IsClosed (Fr r) :=
    (isCompact_range (BT.torusMap_smooth r).continuous).isClosed
  have hFd : Pairwise fun r r' => Disjoint (Fr r) (Fr r') := by
    intro r r' h
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
    have h2 : BT.torusMap r' t' ∈ (BT.collar r').target := (BT.collar r').map_source' (hBsrc r' t')
    rw [ht'] at h2
    exact (BT.disjoint h).le_bot ⟨(BT.collar r).map_source' (hBsrc r t), h2⟩
  have hEd : Pairwise fun j j' => Disjoint (Ej j) (Ej j') := by
    intro j j' h
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
    have he := congrArg Prod.fst (e.injective ht')
    have h2 : (g j' t').1 ∈ (B.collar j').target := (B.collar j').map_source' (hsrc j' t'.1)
    rw [he] at h2
    exact (B.disjoint h).le_bot ⟨(B.collar j).map_source' (hsrc j t.1), h2⟩
  have hbdry : ((SurfaceModel.model B.surface.kind).prod (𝓡 1)).boundary
      (B.surface.Carrier × Circle) =
        (SurfaceModel.model B.surface.kind).boundary B.surface.Carrier ×ˢ (univ : Set Circle) :=
    ModelWithCorners.boundary_of_boundaryless_right
  have hpiece : T.cutCarrier.model.boundary (T.components.piece i) = BT.image :=
    T.pieceBoundaryTori_image i
  have himage := e.image_boundary (by simp)
  have hEF (j : Fin k) : Ej j ⊆ ⋃ r, Fr r := by
    rintro _ ⟨t, rfl⟩
    have hb : g j t ∈ ((SurfaceModel.model B.surface.kind).prod (𝓡 1)).boundary
        (B.surface.Carrier × Circle) := by
      rw [hbdry]
      exact ⟨B.boundary_zero j t.1, mem_univ _⟩
    have hx : e (g j t) ∈ T.cutCarrier.model.boundary (T.components.piece i) := by
      rw [← himage]
      exact ⟨g j t, hb, rfl⟩
    rw [hpiece] at hx
    exact hx
  have hFE (r : Fin (Fintype.card (T.OwnedSide i))) : Fr r ⊆ ⋃ j, Ej j := by
    rintro _ ⟨t, rfl⟩
    have hx : BT.torusMap r t ∈ T.cutCarrier.model.boundary (T.components.piece i) := by
      rw [hpiece]
      exact Set.mem_iUnion.mpr ⟨r, t, rfl⟩
    rw [← himage] at hx
    obtain ⟨y, hy, hye⟩ := hx
    rw [hbdry] at hy
    have hy1 := hy.1
    rw [B.boundary_exhausted] at hy1
    obtain ⟨j, c, hc⟩ := Set.mem_iUnion.mp hy1
    have hy' : (B.collar j (c, halfZero), y.2) = y := Prod.ext hc rfl
    exact Set.mem_iUnion.mpr ⟨j, (c, y.2), (congrArg e hy').trans hye⟩
  have hpt (j : Fin k) : e (g j (1, 1)) ∈ ⋃ r, Fr r := hEF j ⟨(1, 1), rfl⟩
  choose rj hrj using fun j => Set.mem_iUnion.mp (hpt j)
  have hsub1 (j : Fin k) : Ej j ⊆ Fr (rj j) :=
    subset_of_isPreconnected_of_subset_iUnion hFc hFd (isPreconnected_range (heg j)) (hEF j)
      ⟨_, ⟨(1, 1), rfl⟩, hrj j⟩
  have hsub2 (j : Fin k) : Fr (rj j) ⊆ Ej j :=
    subset_of_isPreconnected_of_subset_iUnion hEc hEd
      (isPreconnected_range (BT.torusMap_smooth (rj j)).continuous) (hFE _)
      ⟨_, hrj j, ⟨(1, 1), rfl⟩⟩
  have hinj : Function.Injective rj := by
    intro j j' h
    by_contra hne
    have h1 : Ej j ⊆ Ej j' := (hsub1 j).trans (h ▸ hsub2 j')
    exact (hEd hne).le_bot ⟨⟨(1, 1), rfl⟩, h1 ⟨(1, 1), rfl⟩⟩
  have hbij : Function.Bijective rj :=
    (Fintype.bijective_iff_injective_and_card rj).mpr ⟨hinj, by simp [hcard]⟩
  let port : Fin k ≃ T.OwnedSide i :=
    (Equiv.ofBijective rj hbij).trans (Fintype.equivFin _).symm
  have K1 (j : Fin k) (t : Torus) : ∃ t', e (g j t) = BT.collar (rj j) (t', halfZero) := by
    obtain ⟨t', ht'⟩ := hsub1 j ⟨t, rfl⟩
    exact ⟨t', ht'.symm⟩
  have K2 (j : Fin k) (t' : Torus) : ∃ t, BT.collar (rj j) (t', halfZero) = e (g j t) := by
    obtain ⟨t, ht⟩ := hsub2 j ⟨t', rfl⟩
    exact ⟨t, ht.symm⟩
  have hψ : ∀ j : Fin k, ∃ φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus,
      ∀ t, BT.collar (rj j) (φ t, halfZero) = e (g j t) := by
    intro j
    let c := BT.collar (rj j)
    let f : Torus → Torus := fun t => (c.symm (e (g j t))).1
    let finv : Torus → Torus := fun t' =>
      (((B.collar j).symm (e.symm (c (t', halfZero))).1).1, (e.symm (c (t', halfZero))).2)
    have hf (t : Torus) : c (f t, halfZero) = e (g j t) := by
      obtain ⟨t', ht'⟩ := K1 j t
      have h1 : c.symm (e (g j t)) = (t', halfZero) := by
        rw [ht']
        exact c.symm_apply_apply (hBsrc _ t')
      change c ((c.symm (e (g j t))).1, halfZero) = e (g j t)
      rw [h1]
      exact ht'.symm
    have hyz (t' : Torus) : ∃ t, e.symm (c (t', halfZero)) = g j t := by
      obtain ⟨t, ht⟩ := K2 j t'
      refine ⟨t, ?_⟩
      rw [ht]
      exact e.symm_apply_apply _
    have hback (t : Torus) : (((B.collar j).symm (g j t).1).1, (g j t).2) = t := by
      change (((B.collar j).symm (B.collar j (t.1, halfZero))).1, t.2) = t
      rw [(B.collar j).symm_apply_apply (hsrc j t.1)]
    have hleft (t : Torus) : finv (f t) = t := by
      have h1 : e.symm (c (f t, halfZero)) = g j t := by
        rw [hf t]
        exact e.symm_apply_apply _
      change (((B.collar j).symm (e.symm (c (f t, halfZero))).1).1,
        (e.symm (c (f t, halfZero))).2) = t
      rw [h1]
      exact hback t
    have hright (t' : Torus) : f (finv t') = t' := by
      obtain ⟨t, ht⟩ := hyz t'
      have h2 : finv t' = t := by
        change (((B.collar j).symm (e.symm (c (t', halfZero))).1).1,
          (e.symm (c (t', halfZero))).2) = t
        rw [ht]
        exact hback t
      have h3 : e (g j t) = c (t', halfZero) := by
        rw [← ht]
        exact e.apply_symm_apply _
      rw [h2]
      change (c.symm (e (g j t))).1 = t'
      rw [h3, c.symm_apply_apply (hBsrc _ t')]
    have hfs : ContMDiff torusModel torusModel ∞ f :=
      contMDiff_fst.comp (c.symm.contMDiffOn.comp_contMDiff (e.contMDiff.comp (hg j))
        fun t => hf t ▸ c.map_source' (hBsrc _ _))
    have hy : ContMDiff torusModel ((SurfaceModel.model B.surface.kind).prod (𝓡 1)) ∞
        (fun t' => e.symm (c (t', halfZero))) :=
      e.symm.contMDiff.comp (c.contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const)
        fun t' => hBsrc _ t')
    have hmem (t' : Torus) : (e.symm (c (t', halfZero))).1 ∈ (B.collar j).symm.source := by
      obtain ⟨t, ht⟩ := hyz t'
      rw [ht]
      exact (B.collar j).map_source' (hsrc j t.1)
    have hfinv : ContMDiff torusModel torusModel ∞ finv :=
      (contMDiff_fst.comp ((B.collar j).symm.contMDiffOn.comp_contMDiff
        (contMDiff_fst.comp hy) hmem)).prodMk (contMDiff_snd.comp hy)
    refine ⟨{ toFun := f
              invFun := finv
              left_inv := hleft
              right_inv := hright
              contMDiff_toFun := hfs
              contMDiff_invFun := hfinv }, hf⟩
  choose ψ hψ using hψ
  exact ⟨port, ψ, fun j t => hψ j t⟩

theorem exists_elementary_of_pieces_diffeomorph (T : TorusPresentation W)
    (kind : Fin T.components.count → ℕ) (hkind : ∀ i, kind i ∈ ({1, 2, 3} : Finset ℕ))
    (base : ∀ i, PlanarBase.{u} (kind i))
    (hcard : ∀ i, Fintype.card (T.OwnedSide i) = kind i)
    (e : ∀ i, ((base i).surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
      (base i).surface.kind).prod (𝓡 1), T.cutCarrier.model⟯
        T.components.piece i) :
    ∃ E : ElementaryPresentation W, E.complexity = T.pairing.count := by
  have hport := fun i => T.exists_port_of_diffeomorph i (base i) (hcard i) (e i)
  choose port ψ h₀ using hport
  let ψ' : ∀ i, T.OwnedSide i → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :=
    fun i s => ψ i ((port i).symm s)
  let Ψ : T.Side → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) := fun s => ψ' (T.sidePiece s) ⟨s, rfl⟩
  have hΨ : ∀ i (s : T.OwnedSide i), Ψ s.val = ψ' i s := by
    rintro i ⟨s, hs⟩
    subst hs
    rfl
  obtain ⟨δ, hδ, hδ1, E, -, hE⟩ := T.exists_elementary_of_torus_products Ψ kind hkind base port e
    fun i j t => by
      rw [hΨ i (port i j)]
      change T.pieceCollar i (port i j) (ψ i ((port i).symm (port i j)) t, halfZero) = _
      rw [Equiv.symm_apply_apply]
      exact h₀ i j t
  exact ⟨E, hE⟩

theorem exists_elementary_of_forall_piece (T : TorusPresentation W)
    (h : ∀ i, ∃ k, k ∈ ({1, 2, 3} : Finset ℕ) ∧ Fintype.card (T.OwnedSide i) = k ∧
      ∃ B : PlanarBase.{u} k, Nonempty (((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
        B.surface.kind).prod (𝓡 1), T.cutCarrier.model⟯
          T.components.piece i))) :
    ∃ E : ElementaryPresentation W, E.complexity = T.pairing.count := by
  choose kind hkind hcard base e using h
  exact T.exists_elementary_of_pieces_diffeomorph kind hkind base hcard fun i => (e i).some

end TorusPresentation

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W) (S : Finset (Fin T.components.count))
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected (Set.range (T.restrictMap S) \ T.crossingSurface S))

def contractKeptIndex (j : Fin Sᶜ.card) : Fin (T.contract S hext hk hconn).components.count :=
  j.castSucc

theorem mem_contract_keptPiece {j : Fin Sᶜ.card} {y : T.ContractCut S hext hk} :
    y ∈ (T.contract S hext hk hconn).components.piece (T.contractKeptIndex S hext hk hconn j) ↔
      y ∈ Sum.inl '' (T.subPieceOf Sᶜ j : Set (T.subCarrier Sᶜ).Carrier) := by
  change y ∈ (T.contractPiece S hext hk j.castSucc : Set (T.ContractCut S hext hk)) ↔ _
  rw [contractPiece_castSucc]

def contractKeptDiffeomorph (j : Fin Sᶜ.card) :
    (T.components.piece (T.subIndex Sᶜ j)) ≃ₘ⟮T.cutCarrier.model,
      (T.contract S hext hk hconn).cutCarrier.model⟯
        ((T.contract S hext hk hconn).components.piece
          (T.contractKeptIndex S hext hk hconn j)) where
  toFun x := ⟨Sum.inl ⟨x.val, T.piece_subset_subPiece Sᶜ (T.subIndex_mem Sᶜ j) x.property⟩,
    (T.mem_contract_keptPiece S hext hk hconn).mpr ⟨_, x.property, rfl⟩⟩
  invFun y := ⟨Sum.elim (fun a : (T.subCarrier Sᶜ).Carrier => a.val)
      (fun _ => (T.components.connected (T.subIndex Sᶜ j)).toNonempty.some.val) y.val, by
    obtain ⟨a, ha, he⟩ := (T.mem_contract_keptPiece S hext hk hconn).mp y.property
    rw [← he]
    exact ha⟩
  left_inv _ := rfl
  right_inv y := by
    obtain ⟨y, hy⟩ := y
    obtain ⟨a, ha, rfl⟩ := (T.mem_contract_keptPiece S hext hk hconn).mp hy
    rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    have h : ContMDiff T.cutCarrier.model T.cutCarrier.model ∞
        (fun x : T.components.piece (T.subIndex Sᶜ j) => (Sum.inl
          (⟨x.val, T.piece_subset_subPiece Sᶜ (T.subIndex_mem Sᶜ j) x.property⟩ :
            (T.subCarrier Sᶜ).Carrier) : T.ContractCut S hext hk)) :=
      ContMDiff.inl.comp ((ContMDiff.subtypeVal_comp_iff _ _).mp contMDiff_subtype_val)
    exact h
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    have h : ContMDiff T.cutCarrier.model T.cutCarrier.model ∞
        (Sum.elim (fun a : (T.subCarrier Sᶜ).Carrier => a.val)
          (fun _ => (T.components.connected (T.subIndex Sᶜ j)).toNonempty.some.val) :
            T.ContractCut S hext hk → T.cutCarrier.Carrier) :=
      ContMDiff.sumElim contMDiff_subtype_val contMDiff_const
    have h2 : ContMDiff (T.contract S hext hk hconn).cutCarrier.model T.cutCarrier.model ∞
        (fun y : (T.contract S hext hk hconn).cutCarrier.Carrier =>
          (Sum.elim (fun a : (T.subCarrier Sᶜ).Carrier => a.val)
            (fun _ => (T.components.connected (T.subIndex Sᶜ j)).toNonempty.some.val) :
              T.ContractCut S hext hk → T.cutCarrier.Carrier) y) := h
    exact h2.comp contMDiff_subtype_val

def contractKeptLift : (T.contract S hext hk hconn).Side → T.Side
  | .inl k => .inl (T.nonInternal S k).val
  | .inr (.inl k) => .inr (.inl (T.nonInternal S k).val)
  | .inr (.inr e) => .inr (.inr e)

theorem contractKeptLift_injective :
    Function.Injective (T.contractKeptLift S hext hk hconn) := by
  rintro (k | k | e) (k' | k' | e') h <;>
    simp only [contractKeptLift, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h
  · obtain rfl : k = k' :=
      (Fintype.equivFin (T.NonInternal S)).symm.injective (Subtype.ext h)
    rfl
  · obtain rfl : k = k' :=
      (Fintype.equivFin (T.NonInternal S)).symm.injective (Subtype.ext h)
    rfl
  · obtain rfl : e = e' := Sum.inr_injective h
    rfl

theorem castSucc_subIndexOf_eq_iff {j : Fin Sᶜ.card} {i : Fin T.components.count} (hi : i ∉ S) :
    (T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)).castSucc = j.castSucc ↔ i = T.subIndex Sᶜ j := by
  constructor
  · intro h
    rw [← Fin.castSucc_inj.mp h, subIndex_subIndexOf]
  · intro h
    refine congrArg Fin.castSucc (T.subIndex_injective Sᶜ ?_)
    rw [subIndex_subIndexOf, h]

theorem contract_sidePiece_eq_keptIndex_iff (j : Fin Sᶜ.card)
    (s : (T.contract S hext hk hconn).Side) :
    (T.contract S hext hk hconn).sidePiece s = T.contractKeptIndex S hext hk hconn j ↔
      T.sidePiece (T.contractKeptLift S hext hk hconn s) = T.subIndex Sᶜ j := by
  have hjS : T.subIndex Sᶜ j ∉ S := Finset.mem_compl.mp (T.subIndex_mem Sᶜ j)
  rcases s with k | k | e
  · change T.contractLeftPiece S k = j.castSucc ↔ T.leftPiece (T.nonInternal S k).val = _
    unfold contractLeftPiece
    split_ifs with hl
    · exact iff_of_false (Fin.castSucc_lt_last _).ne' fun h => hjS (h ▸ hl)
    · exact T.castSucc_subIndexOf_eq_iff S hl
  · change T.contractRightPiece S k = j.castSucc ↔ T.rightPiece (T.nonInternal S k).val = _
    unfold contractRightPiece
    split_ifs with hr
    · exact iff_of_false (Fin.castSucc_lt_last _).ne' fun h => hjS (h ▸ hr)
    · exact T.castSucc_subIndexOf_eq_iff S hr
  · exact T.castSucc_subIndexOf_eq_iff S (hext e)

theorem card_contract_ownedSide_kept (j : Fin Sᶜ.card) :
    Fintype.card ((T.contract S hext hk hconn).OwnedSide
      (T.contractKeptIndex S hext hk hconn j)) =
        Fintype.card (T.OwnedSide (T.subIndex Sᶜ j)) := by
  have hjS : T.subIndex Sᶜ j ∉ S := Finset.mem_compl.mp (T.subIndex_mem Sᶜ j)
  refine Fintype.card_congr (Equiv.ofBijective (fun s => ⟨T.contractKeptLift S hext hk hconn s.val,
    (T.contract_sidePiece_eq_keptIndex_iff S hext hk hconn j s.val).mp s.property⟩) ⟨?_, ?_⟩)
  · intro a b h
    exact Subtype.ext (T.contractKeptLift_injective S hext hk hconn (congrArg Subtype.val h))
  · rintro ⟨s, hs⟩
    rcases s with k | k | e
    · have hk' : ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) := fun h => hjS (hs ▸ h.1)
      let k'' : Fin (T.contract S hext hk hconn).pairing.count :=
        Fintype.equivFin (T.NonInternal S) ⟨k, hk'⟩
      have hlift : T.contractKeptLift S hext hk hconn (.inl k'') = .inl k := by
        change Sum.inl (T.nonInternal S (Fintype.equivFin (T.NonInternal S) ⟨k, hk'⟩)).val = _
        rw [nonInternal_equivFin]
      refine ⟨⟨.inl k'', (T.contract_sidePiece_eq_keptIndex_iff S hext hk hconn j _).mpr
        (hlift ▸ hs)⟩, Subtype.ext hlift⟩
    · have hk' : ¬(T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S) := fun h => hjS (hs ▸ h.2)
      let k'' : Fin (T.contract S hext hk hconn).pairing.count :=
        Fintype.equivFin (T.NonInternal S) ⟨k, hk'⟩
      have hlift : T.contractKeptLift S hext hk hconn (.inr (.inl k'')) = .inr (.inl k) := by
        change Sum.inr (Sum.inl (T.nonInternal S
          (Fintype.equivFin (T.NonInternal S) ⟨k, hk'⟩)).val) = _
        rw [nonInternal_equivFin]
      refine ⟨⟨.inr (.inl k''), (T.contract_sidePiece_eq_keptIndex_iff S hext hk hconn j _).mpr
        (hlift ▸ hs)⟩, Subtype.ext hlift⟩
    · exact ⟨⟨.inr (.inr e), (T.contract_sidePiece_eq_keptIndex_iff S hext hk hconn j _).mpr hs⟩,
        rfl⟩

end TorusPresentation

theorem exists_elementary_contract_of_diffeomorph {W : CompactCarrier.{u}}
    (E : ElementaryPresentation W)
    (S : Finset (Fin E.toTorus.components.count)) (hext : ∀ i, E.toTorus.externalPiece i ∉ S)
    (hk : E.toTorus.cutCarrier.kind = .withBoundary)
    (hconn : IsConnected (Set.range (E.toTorus.restrictMap S) \ E.toTorus.crossingSurface S))
    (k : ℕ) (hk3 : k ∈ ({1, 2, 3} : Finset ℕ))
    (hcard : Fintype.card ((E.toTorus.contract S hext hk hconn).OwnedSide
      (E.toTorus.contractLast S hext hk hconn)) = k)
    (B : PlanarBase.{u} k)
    (he : Nonempty ((B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model
      B.surface.kind).prod (𝓡 1),
        (E.toTorus.contract S hext hk hconn).cutCarrier.model⟯
          (E.toTorus.contract S hext hk hconn).components.piece
            (E.toTorus.contractLast S hext hk hconn))) :
    ∃ E' : ElementaryPresentation W,
      E'.complexity = (E.toTorus.contract S hext hk hconn).pairing.count := by
  refine (E.toTorus.contract S hext hk hconn).exists_elementary_of_forall_piece fun i => ?_
  induction i using Fin.lastCases with
  | last => exact ⟨k, hk3, hcard, B, he⟩
  | cast j =>
    exact ⟨E.kind (E.toTorus.subIndex Sᶜ j), E.kind_mem _,
      (E.toTorus.card_contract_ownedSide_kept S hext hk hconn j).trans
        (E.piece _).card_ownedSide, (E.piece _).base,
      ⟨(E.piece _).trivialization.trans (E.toTorus.contractKeptDiffeomorph S hext hk hconn j)⟩⟩

theorem contractionRecollar : ContractionRecollar.{u} :=
  fun _ E S hext hk hconn k hk3 hcard B he =>
    exists_elementary_contract_of_diffeomorph E S hext hk hconn k hk3 hcard B he

end GC.Seifert
