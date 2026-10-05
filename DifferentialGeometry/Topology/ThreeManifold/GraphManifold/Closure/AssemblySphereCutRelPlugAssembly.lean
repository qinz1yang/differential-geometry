import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugPorts

/-!
# Chapter-14 assembly, relative COMPARE G4: a placed solid-cap plug is a piece of `W`

Lane ASM-L2e, group G4. `SolidCapPlug.exists_placedPiece`: for every placement of a solid-cap plug
`Y` into two disjoint tubes of the capped carrier of a sphere cut `X` of `W` (the G2 shape: the
placement matches the A6-a shell charts of the two caps with the plug cap charts in solid-torus
coordinates), the plug is an injective `PieceFold` of `W`, diffeomorphic to the plug carrier, whose
two port lifts land on the inner radial collars `F (Ψ⁻¹ (φ t ((1 - ν s / 2) w, θ)))` of the placed
tubes and exhaust its boundary, with image the fold of the placed closed unit tubes together with
the seam sphere; the caps of `X` stay inside the radius `1 - ν` tubes.

The neck profile is `exists_neckProfile` (G3) with the two shell germs `s₀ 0 + μ 0 σ / 2` and
`-s₀ 1 + μ 1 σ / 2` (the plug germ is `2 r - 2`, the shells are `s₀ + μ (r - 1)`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The conjugation of the first circle factor of the torus (`ε = true`) or the identity. -/
def torusConj (ε : Bool) : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  if ε then circleInvDiffeo.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)
  else Diffeomorph.refl torusModel Torus ∞

theorem torusConj_snd (ε : Bool) (τ : Torus) : (torusConj ε τ).2 = τ.2 := by
  cases ε <;> rfl

theorem torusConj_fst (ε : Bool) (τ : Torus) :
    (if ε then (starRingEnd ℂ) ((torusConj ε τ).1 : ℂ) else ((torusConj ε τ).1 : ℂ)) =
      (τ.1 : ℂ) := by
  cases ε
  · rfl
  · change (starRingEnd ℂ) ((τ.1⁻¹ : Circle) : ℂ) = (τ.1 : ℂ)
    rw [Circle.coe_inv_eq_conj, Complex.conj_conj]

namespace SolidCapPlug

variable {P : CompactCarrier.{u}} (Y : SolidCapPlug P)
  {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  {X : SphereCutCapped W S E}
  {F : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞}
  (hFs : F.source = (⋃ j, range (X.capping.cap j))ᶜ)
  (hF : ∀ y, X.capping.core y ∈ F.source → F (X.capping.core y) = X.fold y)
  {Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier}
  {φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
    (PlaneLift.{u} × Circle) X.Q.Carrier ∞}
  {Θ : Fin 2 → solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}} {ε : Fin 2 → Bool} {r : Fin 2 → ℝ}
  (hΘ : ∀ t (x : solidSet.{u}), r t ≤ ‖x.val.1.down‖ → (Θ t x).val =
    if ε t then (ULift.up ((starRingEnd ℂ) x.val.1.down), x.val.2) else x.val)

/-- The port index of side `t`. -/
def portIndex (t : Fin 2) : Fin Y.portCount := Fin.cast Y.cut.hn (Y.port t)

theorem retained_portIndex (t : Fin 2) {q : Torus × EuclideanHalfSpace 1}
    (hq : q ∈ halfCollarSource) :
    Y.cut.capComplementFold (Y.cut.capping.retained.collar (Y.port t) q) =
      Y.ports.collar (Y.portIndex t) q :=
  Y.cut.capComplementFold_retained (Y.portIndex t) hq

include hΘ in
/-- **The placed plug on the port collars of the plug.** -/
theorem placedPlugMap_port (h : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ) (t : Fin 2) (p : Torus) {s : ℝ}
    (hs0 : 0 ≤ s) (hsd : s < Y.depth) (hs1 : s < 1) (hr : r t ≤ 3 * (1 - s / 2)) :
    Y.placedPlugMap F Ψ φ Θ h (Y.ports.collar (Y.portIndex t) (Y.marking t p, halfPoint s hs0)) =
      F (Ψ.symm (φ t (ULift.up ((1 - s / 2) •
        (if ε t then (starRingEnd ℂ) (p.1 : ℂ) else (p.1 : ℂ))), p.2))) := by
  have hq : (Y.marking t p, halfPoint s hs0) ∈ halfCollarSource := hs1
  rw [Y.placedPlugMap_of_not_mem F Ψ φ Θ h (Y.ports_not_mem_neckSet (Y.portIndex t) hq)]
  have hsrc := Y.cut.retained_mem_capComplement (Y.port t) hq
  have hsymm : Y.cut.capComplementFold.symm (Y.ports.collar (Y.portIndex t)
      (Y.marking t p, halfPoint s hs0)) =
      Y.cut.capping.retained.collar (Y.port t) (Y.marking t p, halfPoint s hs0) := by
    rw [← Y.retained_portIndex t hq]
    exact Y.cut.capComplementFold.left_inv hsrc
  rw [hsymm, Y.placedMap_retained hΘ t p hs0 hsd hs1 hr]

theorem portIndex_surjective : Surjective Y.portIndex := by
  intro i
  obtain ⟨t, ht⟩ := Y.port_bijective.2 (Fin.cast Y.cut.hn.symm i)
  exact ⟨t, by rw [portIndex, ht]; rfl⟩

include hFs hF hΘ in
/-- **G4, generic form (ASM-L2e): a placed solid-cap plug is a piece of `W`.** -/
theorem exists_placedPiece [ConnectedSpace P.Carrier] (hPk : P.kind = .withBoundary)
    (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source)
    (hφd : Disjoint (φ 0 '' {p | ‖p.1.down‖ ≤ 1}) (φ 1 '' {p | ‖p.1.down‖ ≤ 1}))
    {c : Fin 2 → PartialDiffeomorph (𝓡 3) X.Q.model E3 X.Q.Carrier ∞} {s₀ μ : Fin 2 → ℝ}
    (hs₀ : ∀ t, 0 < s₀ t) (hμ : ∀ t, 0 < μ t) (hsμ : ∀ t, s₀ t + μ t < 1)
    (hshell : ∀ t (z : sphere (0 : E3) 1) (r : ℝ) (hr : 1 ≤ r), r ≤ 2 →
      c t (r • (z : E3)) = X.capping.core (X.B.sphere (Fin.cast X.h2.symm t)
        (ULift.up z, halfPoint (s₀ t + μ t * (r - 1))
          (add_nonneg (hs₀ t).le (mul_nonneg (hμ t).le (sub_nonneg.mpr hr))))))
    (hball : ∀ t, c t '' ball 0 1 = range (X.capping.cap (Fin.cast X.h2.symm t)) ∪
      X.capping.core '' (X.B.sphere (Fin.cast X.h2.symm t) '' {p | p.2.val 0 < s₀ t}))
    (hr : ∀ t, r t < 3)
    (hmatch : ∀ t, ∀ x ∈ closedBall (0 : E3) 2,
      Ψ (c t x) = solidTubeFill (φ t) (Θ t (Y.solidChart t x)))
    {ν₀ : ℝ} (hν₀ : 0 < ν₀) :
    ∃ (Pc : PieceFold W) (_ : P.Carrier ≃ₘ⟮P.model, 𝓡∂ 3⟯ Pc.Piece) (ν : ℝ)
      (lift : Fin 2 → PartialDiffeomorph halfCollarModel (𝓡∂ 3)
        (Torus × EuclideanHalfSpace 1) Pc.Piece ∞),
      0 < ν ∧ ν ≤ ν₀ ∧ ν ≤ 1 ∧ (∀ t, (lift t).source = halfCollarSource) ∧
      (∀ t p, p ∈ halfCollarSource → Pc.map (lift t p) =
        F (Ψ.symm (φ t (ULift.up ((1 - ν * p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)))) ∧
      (𝓡∂ 3).boundary Pc.Piece = (⋃ t, range fun τ => lift t (τ, halfZero)) ∧
      Injective Pc.map ∧
      range Pc.map = F '' ((Ψ.symm '' ⋃ t, φ t '' {p | ‖p.1.down‖ ≤ 1}) ∩ F.source) ∪
        range (fun z => S.collar (z, 0)) ∧
      ∀ t, range (X.capping.cap (Fin.cast X.h2.symm t)) ⊆
        Ψ.symm '' (φ t '' {p | ‖p.1.down‖ < 1 - ν}) := by
  have hη := Y.germ_pos
  have hη1 := Y.germ_le
  -- the neck profile
  set g : ℝ := |μ 0 / 2 - μ 1 / 2|
  let a : ℝ := min Y.germ ((s₀ 0 + s₀ 1) / (g + 1))
  have hg0 : 0 ≤ g := abs_nonneg _
  have ha : 0 < a := lt_min hη (div_pos (by linarith [hs₀ 0, hs₀ 1]) (by linarith))
  have haη : a ≤ Y.germ := min_le_left _ _
  have hgap : g * a ≤ s₀ 0 - -s₀ 1 := by
    have h1 : a ≤ (s₀ 0 + s₀ 1) / (g + 1) := min_le_right _ _
    have h2 : g * a ≤ g * ((s₀ 0 + s₀ 1) / (g + 1)) := mul_le_mul_of_nonneg_left h1 hg0
    have h3' : g * ((s₀ 0 + s₀ 1) / (g + 1)) ≤ s₀ 0 + s₀ 1 := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith [hs₀ 0, hs₀ 1]
    linarith
  obtain ⟨h, hmono, h₀', h₁'⟩ := exists_neckProfile ha (half_pos (hμ 0)) (half_pos (hμ 1)) hgap
  have h₀ : ∀ σ, a ≤ σ → h σ = s₀ 0 + μ 0 / 2 * σ := h₀'
  have h₁ : ∀ σ, σ ≤ -a → h σ = -s₀ 1 + μ 1 / 2 * σ := h₁'
  -- the piece
  have hsm := fun y => Y.contMDiffAt_placedPlugMap hFs hF h3 hφd hs₀ hμ hshell hball hmatch h hsμ
    ha haη hmono h₀ h₁ y
  obtain ⟨Pc, e, he⟩ := exists_pieceFold_of_carrier P hPk (Y.placedPlugMap F Ψ φ Θ h)
    (fun y => (hsm y).1) (fun y => (hsm y).2)
  have hmap : ∀ y, Pc.map y = Y.placedPlugMap F Ψ φ Θ h (e.symm y) := by
    intro y
    rw [← he, e.apply_symm_apply]
  -- radius bounds of the placed cap balls
  have hK : ∀ t, ∃ R < (3 : ℝ), ∀ x ∈ closedBall (0 : E3) 2,
      ‖(Θ t (Y.solidChart t x)).val.1.down‖ ≤ R := by
    intro t
    have hsrc : closedBall (0 : E3) 2 ⊆ (Y.solidChart t).source := by
      rw [Y.solidChart_source]
      exact Y.capChart_source t
    have hcpt : IsCompact (Θ t '' (Y.solidChart t '' closedBall 0 2)) :=
      ((isCompact_closedBall 0 2).image_of_continuousOn
        ((Y.solidChart t).contMDiffOn.continuousOn.mono hsrc)).image (Θ t).continuous
    have hint : Θ t '' (Y.solidChart t '' closedBall 0 2) ⊆ (𝓡∂ 3).interior solidSet.{u} := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hv := Y.solidChart_target_interior t ((Y.solidChart t).map_source (hsrc hx))
      exact (((Θ t).isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp hv
    obtain ⟨R, hR, hRK⟩ := exists_radius_lt_of_isCompact hcpt hint
    exact ⟨R, hR, fun x hx => hRK _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩
  choose R hR3 hRK using hK
  -- the collar depth
  let ν : ℝ := min (min ν₀ (1 / 2)) (min Y.depth (min (min (2 * (1 - r 0 / 3))
    (2 * (1 - r 1 / 3))) (min ((1 - R 0 / 3) / 2) ((1 - R 1 / 3) / 2))))
  have hν : 0 < ν := lt_min (lt_min hν₀ (by norm_num)) (lt_min Y.depth_pos
    (lt_min (lt_min (by linarith [hr 0]) (by linarith [hr 1]))
      (lt_min (by linarith [hR3 0]) (by linarith [hR3 1]))))
  have hνν₀ : ν ≤ ν₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hν12 : ν ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hνd : ν ≤ Y.depth := (min_le_right _ _).trans (min_le_left _ _)
  have hνr : ∀ t, ν ≤ 2 * (1 - r t / 3) := by
    have h1 : ν ≤ min (2 * (1 - r 0 / 3)) (2 * (1 - r 1 / 3)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    intro t
    fin_cases t
    · exact h1.trans (min_le_left _ _)
    · exact h1.trans (min_le_right _ _)
  have hνR : ∀ t, ν ≤ (1 - R t / 3) / 2 := by
    have h1 : ν ≤ min ((1 - R 0 / 3) / 2) ((1 - R 1 / 3) / 2) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    intro t
    fin_cases t
    · exact h1.trans (min_le_left _ _)
    · exact h1.trans (min_le_right _ _)
  -- the port lifts
  let D : Fin 2 → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) := fun t =>
    (torusConj (ε t)).trans (Y.marking t)
  let C : Fin 2 → PartialDiffeomorph halfCollarModel P.model (Torus × EuclideanHalfSpace 1)
      P.Carrier ∞ := fun t =>
    ((D t).prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans
      (Y.ports.collar (Y.portIndex t))
  have hCs : ∀ t, (C t).source = {p | p.2.1 0 < 1} := by
    intro t
    ext p
    change (p ∈ univ ∧ ((D t) p.1, p.2) ∈ (Y.ports.collar (Y.portIndex t)).source) ↔ _
    rw [Y.ports.source_eq]
    simp only [mem_univ, true_and]
    rfl
  let lift : Fin 2 → PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
      Pc.Piece ∞ := fun t => (shrinkHalfCollar hν (C t)).trans e.toPartialDiffeomorph
  have hls : ∀ t, (lift t).source = halfCollarSource := by
    intro t
    change (shrinkHalfCollar hν (C t)).source ∩ _ = _
    rw [shrinkHalfCollar_source hν (by linarith) (hCs t)]
    exact inter_univ _
  have hlift_apply : ∀ t (p : Torus × EuclideanHalfSpace 1), lift t p =
      e (Y.ports.collar (Y.portIndex t) (D t p.1, halfSpaceScale hν p.2)) := fun _ _ => rfl
  refine ⟨Pc, e, ν, lift, hν, hνν₀, by linarith, hls, ?_, ?_, ?_, ?_, ?_⟩
  · -- the lift formula
    intro t p hp
    have hp1 : p.2.val 0 < 1 := hp
    have hp0 : 0 ≤ p.2.val 0 := p.2.2
    have hs0 : 0 ≤ ν * p.2.val 0 := mul_nonneg hν.le hp0
    have hsν : ν * p.2.val 0 < ν ∨ p.2.val 0 = 0 := by
      rcases hp0.lt_or_eq with hpos | hz
      · left
        nlinarith
      · right
        exact hz.symm
    have hslt : ν * p.2.val 0 ≤ ν := by nlinarith
    have hhalf : halfSpaceScale hν p.2 = halfPoint (ν * p.2.val 0) hs0 := by
      rw [← halfSpaceScale_halfPoint hν (p.2.val 0) hp0]
      congr 1
      exact (halfPoint_eq_self p.2 hp0 rfl).symm
    rw [hmap, hlift_apply, e.symm_apply_apply, hhalf]
    change Y.placedPlugMap F Ψ φ Θ h (Y.ports.collar (Y.portIndex t)
      (Y.marking t (torusConj (ε t) p.1), halfPoint (ν * p.2.val 0) hs0)) = _
    have hsd : ν * p.2.val 0 < Y.depth := by
      rcases hsν with hlt | hz
      · exact lt_of_lt_of_le hlt hνd
      · rw [hz, mul_zero]
        exact Y.depth_pos
    rw [Y.placedPlugMap_port hΘ h t _ hs0 hsd (by linarith)
      (by nlinarith [hνr t, hr t])]
    rw [torusConj_fst, torusConj_snd]
  · -- the boundary
    ext x
    constructor
    · intro hx
      have hb : P.model.IsBoundaryPoint (e.symm x) := by
        have hx' : (𝓡∂ 3).IsBoundaryPoint (e (e.symm x)) := by
          rw [e.apply_symm_apply]
          exact hx
        exact ((e.isLocalDiffeomorph (e.symm x)).isBoundaryPoint_iff (by simp)).mpr hx'
      have hbm : e.symm x ∈ P.model.boundary P.Carrier := hb
      rw [Y.boundary_eq] at hbm
      obtain ⟨i, τ', hτ'⟩ := mem_iUnion.mp hbm
      obtain ⟨t, rfl⟩ := Y.portIndex_surjective i
      refine mem_iUnion.mpr ⟨t, (D t).symm τ', ?_⟩
      change lift t ((D t).symm τ', halfZero) = x
      rw [hlift_apply, halfSpaceScale_halfZero, Diffeomorph.apply_symm_apply]
      change e (Y.ports.torusMap (Y.portIndex t) τ') = x
      rw [hτ', e.apply_symm_apply]
    · intro hx
      obtain ⟨t, τ, rfl⟩ := mem_iUnion.mp hx
      change (𝓡∂ 3).IsBoundaryPoint (lift t (τ, halfZero))
      rw [hlift_apply, halfSpaceScale_halfZero]
      exact ((e.isLocalDiffeomorph _).isBoundaryPoint_iff (by simp)).mp
        (Y.ports.boundary_zero (Y.portIndex t) ((D t) τ))
  · -- injectivity
    intro y₁ y₂ hy
    rw [hmap, hmap] at hy
    exact e.symm.injective (Y.injective_placedPlugMap hFs hF h3 hφd hs₀ hμ hshell hball hmatch h
      hsμ ha haη hmono h₀ h₁ hy)
  · -- the image
    rw [← Y.range_placedPlugMap hFs hF h3 hφd hs₀ hμ hshell hball hmatch h hsμ haη hmono h₀ h₁]
    ext w
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, (hmap y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e y, by rw [hmap, e.symm_apply_apply]⟩
  · -- the caps stay inside the thinner tubes
    intro t w hw
    have hmem : w ∈ c t '' ball 0 1 := by
      rw [hball t]
      exact Or.inl hw
    obtain ⟨x, hx, rfl⟩ := hmem
    have hx2 : x ∈ closedBall (0 : E3) 2 :=
      ball_subset_closedBall (ball_subset_ball (by norm_num) hx)
    refine ⟨solidTubeFill (φ t) (Θ t (Y.solidChart t x)), ?_, ?_⟩
    · refine ⟨(ULift.up ((Θ t (Y.solidChart t x)).val.1.down / 3),
        (Θ t (Y.solidChart t x)).val.2), ?_, rfl⟩
      change ‖(Θ t (Y.solidChart t x)).val.1.down / 3‖ < 1 - ν
      rw [norm_div, Complex.norm_ofNat]
      have := hRK t x hx2
      have := hνR t
      linarith
    · rw [← hmatch t x hx2, Diffeomorph.symm_apply_apply]

end SolidCapPlug

end GC.GraphManifold.Assembly
