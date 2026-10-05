import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelAdapterDrill
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelAdapterOpens
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlaceApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlaceExtend
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutOrientCharts

/-!
# Chapter-14 assembly, relative COMPARE side adapters (c): the separating placement

Lane ASM-L2f, group G1. For a sphere-cut-capped carrier `X` and the component of the cut sphere
`t`, with a raw presentation of that component:

* `solidTubeFill_mem_image`: the fill of the solid torus lies in the closed unit tube.
* `SphereCutCapped.exists_sidePlacement`: the relative drill (`exists_relativeRawAmbientExcision`)
  of the component, the placement G2 (`exists_solidPlacement`) of the shell chart of `t` (A6-a,
  `componentShellChart`) onto the fill of a given solid ball chart in the drilled tube, extended by
  the identity (`exists_extend_of_isCompact`); everything read in the capped carrier, the support
  inside the component.
* `SphereCutCapped.spherePiece_cast_ne`: with two components the cut spheres are apart.
* `exists_separatingPlacement`: the frozen G5 side adapter (ASM-L2e `Targets.lean`, verbatim): the
  two side placements composed (their supports lie in the two distinct components).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The fill of the solid torus lies in the closed unit tube. -/
theorem solidTubeFill_mem_image {H M : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E3 H} [TopologicalSpace M] [ChartedSpace H M]
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) I (PlaneLift.{u} × Circle) M ∞)
    (x : solidSet.{u}) :
    solidTubeFill φ x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} := by
  refine ⟨(ULift.up (x.val.1.down / 3), x.val.2), ?_, rfl⟩
  have hx := (mem_solidSet_iff x.val).mp x.property
  change ‖x.val.1.down / 3‖ ≤ 1
  rw [norm_div, Complex.norm_ofNat]
  linarith

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E) (DQ : X.Q.Components)

/-- With two components, the two cut spheres lie in distinct components (any number of ports). -/
theorem spherePiece_cast_ne [ConnectedSpace W.Carrier] (h2 : DQ.count = 2) :
    X.spherePiece DQ (Fin.cast X.h2.symm 0) ≠ X.spherePiece DQ (Fin.cast X.h2.symm 1) := by
  have hb := (Fintype.bijective_iff_surjective_and_card (X.spherePiece DQ)).mpr
    ⟨X.spherePiece_surjective DQ, by simp [X.h2, h2]⟩
  intro he
  have := congrArg Fin.val (hb.1 he)
  simp at this

/-- The shell chart restricted to the component, read in the component, has interior target. -/
theorem componentShellChart_target_subset_interior (t : Fin 2) :
    (X.componentShellChart DQ t).target ⊆
      (GC.Topology.componentCarrier X.Q DQ (X.spherePiece DQ (Fin.cast X.h2.symm t))).model.interior
        (GC.Topology.componentCarrier X.Q DQ (X.spherePiece DQ (Fin.cast X.h2.symm t))).Carrier := by
  intro y hy
  have hy' : y ∈ Subtype.val ⁻¹' (X.shellChartCore t).target := by
    rw [componentShellChart, codRestrictOpens_target] at hy
    exact hy
  have hval : y.val ∈ X.Q.model.interior X.Q.Carrier :=
    X.shellChart_target_subset t hy'.1
  exact (mem_interior_val_iff (I := X.Q.model) (x := y)).mp hval

/-- **One side.** The drill of the component of the cut sphere `t` and the placement of its shell
chart onto the fill of the solid ball chart `v` in the drilled tube, read in the capped carrier. -/
theorem exists_sidePlacement (t : Fin 2)
    (R : RawGraphPresentation
      (GC.Topology.componentCarrier X.Q DQ (X.spherePiece DQ (Fin.cast X.h2.symm t))))
    (v : PartialDiffeomorph (𝓡 3) (𝓡∂ 3) E3 solidSet.{u} ∞)
    (hv : closedBall 0 2 ⊆ v.source) (hvI : v.target ⊆ (𝓡∂ 3).interior solidSet.{u}) :
    ∃ (Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier) (K : Set X.Q.Carrier)
      (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
        (PlaneLift.{u} × Circle) X.Q.Carrier ∞)
      (L : CompactCarrier.{u}) (η : L.Carrier → X.Q.Carrier)
      (Γ : PartialDiffeomorph halfCollarModel L.model (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
      (Θ : solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}) (ε : Bool) (r : ℝ),
      IsCompact K ∧ K ⊆ X.Q.interior ∧
      K ⊆ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t)) ∧ (∀ x, x ∉ K → Ψ x = x) ∧
      {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source ∧
      φ.target ⊆ X.Q.interior ∧
      φ.target ⊆ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t)) ∧
      L.kind = .withBoundary ∧ ConnectedSpace L.Carrier ∧
      Nonempty (RawGraphPresentation L) ∧
      IsSmoothEmbedding L.model X.Q.model ∞ η ∧
      (∀ x, Bijective (mfderiv L.model X.Q.model η x)) ∧
      range η = (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t)) : Set X.Q.Carrier) \
        (φ '' {p | ‖p.1.down‖ < 1}) ∧
      Γ.source = halfCollarSource ∧
      (∀ p, p ∈ halfCollarSource →
        η (Γ p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) ∧
      η '' L.model.boundary L.Carrier =
        (X.Q.model.boundary X.Q.Carrier ∩ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t))) ∪
          range (fun τ : Torus => φ (ULift.up (τ.1 : ℂ), τ.2)) ∧
      r < 3 ∧
      (∀ x : solidSet.{u}, r ≤ ‖x.val.1.down‖ → (Θ x).val =
        if ε then (ULift.up ((starRingEnd ℂ) x.val.1.down), x.val.2) else x.val) ∧
      ∀ x ∈ closedBall (0 : E3) 2, Ψ (X.shellChart t x) = solidTubeFill φ (Θ (v x)) := by
  let i := X.spherePiece DQ (Fin.cast X.h2.symm t)
  let C := GC.Topology.componentCarrier X.Q DQ i
  have : ConnectedSpace C.Carrier := DQ.connected i
  obtain ⟨φ', h3', hI', L, η', R', he, δ, hδ, O, -, hLk, hLc, hη', hrange', hbij', hb', -, -, -,
    -, hnew'⟩ := exists_relativeRawAmbientExcision C R
  have hc' : closedBall 0 2 ⊆ (X.componentShellChart DQ t).source := by
    rw [X.componentShellChart_source]
    exact X.closedBall_subset_shellCore t
  obtain ⟨ε, Ψ', Θ, K', r, hK', hK'I, hfix', hr, hΘ, hmatch'⟩ :=
    exists_solidPlacement φ' h3' hI' (X.componentShellChart DQ t) hc'
      (X.componentShellChart_target_subset_interior DQ t) v hv hvI
  have hne : Nonempty (DQ.piece i) :=
    ⟨⟨X.shellChart t 0, X.shellChart_image_subset DQ t ⟨0, mem_closedBall_self (by norm_num), rfl⟩⟩⟩
  -- the drilled data, retyped on the open subset `DQ.piece i` of the capped carrier
  let φo : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model (PlaneLift.{u} × Circle)
    (DQ.piece i) ∞ := φ'
  let ηo : L.Carrier → DQ.piece i := η'
  let Ψo : DQ.piece i ≃ₘ⟮X.Q.model, X.Q.model⟯ DQ.piece i := Ψ'
  let Ko : Set (DQ.piece i) := K'
  have h3o : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φo.source := h3'
  have hIo : φo.target ⊆ X.Q.model.interior (DQ.piece i) := hI'
  have hηo : IsSmoothEmbedding L.model X.Q.model ∞ ηo := hη'
  have hbijo : ∀ x, Bijective (mfderiv L.model X.Q.model ηo x) := hbij'
  have hrangeo : range ηo = (φo '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ := hrange'
  have hbo : ηo '' L.model.boundary L.Carrier = X.Q.model.boundary (DQ.piece i) ∪
      range (fun τ : Torus => φo (ULift.up (τ.1 : ℂ), τ.2)) := hb'
  have hKo : IsCompact Ko := hK'
  have hKIo : Ko ⊆ X.Q.model.interior (DQ.piece i) := hK'I
  have hfixo : ∀ x, x ∉ Ko → Ψo x = x := hfix'
  obtain ⟨Ψ, hΨU, hΨfix⟩ := exists_extend_of_isCompact (I := X.Q.model) (DQ.piece i) Ψo Ko hKo
    hfixo
  refine ⟨Ψ, Subtype.val '' Ko, pushOpens (DQ.piece i) hne φo, L, Subtype.val ∘ ηo,
    R'.external.collar (Fin.cast he.symm (Fin.last (R.externalCount))), Θ, ε, r,
    hKo.image continuous_subtype_val, ?_, ?_, hΨfix, ?_, ?_, pushOpens_target_subset _ _ _,
    hLk, hLc, ⟨R'⟩, isSmoothEmbedding_val_comp _ ηo hηo,
    fun x => bijective_mfderiv_val_comp _ ηo x (hbijo x), ?_, R'.external.source_eq _, ?_, ?_,
    hr, hΘ, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_interior_val_iff (I := X.Q.model) (x := x)).mpr (hKIo hx)
  · rintro _ ⟨x, -, rfl⟩
    exact x.property
  · rw [pushOpens_source]
    exact h3o
  · exact pushOpens_target_subset_interior _ _ _ hIo
  · rw [range_val_comp _ ηo _ hrangeo, pushOpens_image]
  · intro p hp
    change (η' _).val = (φ' _).val
    rw [hnew' p hp]
  · rw [image_val_comp_boundary _ ηo hbo, ← range_comp]
    rfl
  · intro x hx
    have hxs : x ∈ X.shellCore t := X.closedBall_subset_shellCore t hx
    rw [← X.componentShellChart_val DQ t hxs]
    refine (hΨU (X.componentShellChart DQ t x)).trans ?_
    change (Ψ' (X.componentShellChart DQ t x)).val = _
    rw [hmatch' x hx]
    rfl

end SphereCutCapped

/-- **G5 side adapter (separating)**, the frozen text of ASM-L2e (`Targets.lean`), verbatim. -/
theorem exists_separatingPlacement (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
    (X : SphereCutCapped W S E) (DQ : X.Q.Components) (h2 : DQ.count = 2)
    (R : ∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i))
    (v : Fin 2 → PartialDiffeomorph (𝓡 3) (𝓡∂ 3) E3 solidSet.{u} ∞)
    (hv : ∀ t, closedBall 0 2 ⊆ (v t).source)
    (hvI : ∀ t, (v t).target ⊆ (𝓡∂ 3).interior solidSet.{u}) :
    ∃ (Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier) (K : Set X.Q.Carrier)
      (φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
        (PlaneLift.{u} × Circle) X.Q.Carrier ∞)
      (L : Fin 2 → CompactCarrier.{u}) (η : ∀ t, (L t).Carrier → X.Q.Carrier)
      (Γ : ∀ t, PartialDiffeomorph halfCollarModel (L t).model
        (Torus × EuclideanHalfSpace 1) (L t).Carrier ∞)
      (c : Fin 2 → PartialDiffeomorph (𝓡 3) X.Q.model E3 X.Q.Carrier ∞) (s₀ μ : Fin 2 → ℝ)
      (hs₀ : ∀ t, 0 < s₀ t) (hμ : ∀ t, 0 < μ t)
      (Θ : Fin 2 → solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}) (ε : Fin 2 → Bool)
      (r : Fin 2 → ℝ),
      IsCompact K ∧ K ⊆ X.Q.interior ∧ (∀ x, x ∉ K → Ψ x = x) ∧
      (∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source) ∧
      (∀ t, (φ t).target ⊆ X.Q.interior) ∧
      (∀ t, (φ t).target ⊆ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t))) ∧
      Disjoint (φ 0 '' {p | ‖p.1.down‖ ≤ 1}) (φ 1 '' {p | ‖p.1.down‖ ≤ 1}) ∧
      (∀ t, (L t).kind = .withBoundary) ∧ (∀ t, ConnectedSpace (L t).Carrier) ∧
      (∀ t, Nonempty (RawGraphPresentation (L t))) ∧
      (∀ t, IsSmoothEmbedding (L t).model X.Q.model ∞ (η t)) ∧
      (∀ t x, Bijective (mfderiv (L t).model X.Q.model (η t) x)) ∧
      (∀ t, range (η t) =
        (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t)) : Set X.Q.Carrier) \
          (φ t '' {p | ‖p.1.down‖ < 1})) ∧
      (∀ t, (Γ t).source = halfCollarSource) ∧
      (∀ t p, p ∈ halfCollarSource →
        η t (Γ t p) = φ t (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) ∧
      (∀ t, η t '' (L t).model.boundary (L t).Carrier =
        (X.Q.model.boundary X.Q.Carrier ∩ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t))) ∪
          range (fun τ : Torus => φ t (ULift.up (τ.1 : ℂ), τ.2))) ∧
      (∀ t, s₀ t + μ t < 1) ∧ (∀ t, closedBall 0 2 ⊆ (c t).source) ∧
      (∀ t (z : sphere (0 : E3) 1) (r : ℝ) (hr : 1 ≤ r), r ≤ 2 →
        c t (r • (z : E3)) = X.capping.core (X.B.sphere (Fin.cast X.h2.symm t)
          (ULift.up z, halfPoint (s₀ t + μ t * (r - 1))
            (add_nonneg (hs₀ t).le (mul_nonneg (hμ t).le (sub_nonneg.mpr hr)))))) ∧
      (∀ t, c t '' ball 0 1 = range (X.capping.cap (Fin.cast X.h2.symm t)) ∪
        X.capping.core '' (X.B.sphere (Fin.cast X.h2.symm t) '' {p | p.2.val 0 < s₀ t})) ∧
      (∀ t, r t < 3) ∧
      (∀ t (x : solidSet.{u}), r t ≤ ‖x.val.1.down‖ → (Θ t x).val =
        if ε t then (ULift.up ((starRingEnd ℂ) x.val.1.down), x.val.2) else x.val) ∧
      ∀ t, ∀ x ∈ closedBall (0 : E3) 2, Ψ (c t x) = solidTubeFill (φ t) (Θ t (v t x)) := by
  have hside := fun t : Fin 2 =>
    X.exists_sidePlacement DQ t (R _) (v t) (hv t) (hvI t)
  choose Ψ K φ L η Γ Θ ε r hK hKI hKp hfix h3 hφI hφp hLk hLc hLR hη hηb hηr hΓs hΓ hLb hr hΘ
    hmatch using hside
  have hne := X.spherePiece_cast_ne DQ h2
  have hdisj : Disjoint (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm 0)) : Set X.Q.Carrier)
      (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm 1))) := DQ.disjoint hne
  -- a point of a component is not moved by the extension of the other side
  have hother0 : ∀ y ∈ (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm 0)) : Set X.Q.Carrier),
      Ψ 1 y = y := fun y hy => hfix 1 y fun hk => disjoint_left.mp hdisj hy (hKp 1 hk)
  have hother1 : ∀ y ∈ (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm 1)) : Set X.Q.Carrier),
      Ψ 0 y = y := fun y hy => hfix 0 y fun hk => disjoint_left.mp hdisj (hKp 0 hk) hy
  have hfill : ∀ t (y : solidSet.{u}),
      solidTubeFill (φ t) y ∈ (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t)) :
        Set X.Q.Carrier) := by
    intro t y
    obtain ⟨p, hp, hpe⟩ := solidTubeFill_mem_image (φ t) y
    rw [← hpe]
    refine hφp t ((φ t).map_source (h3 t ?_))
    change ‖p.1.down‖ ≤ 3
    have : ‖p.1.down‖ ≤ 1 := hp
    linarith
  refine ⟨(Ψ 0).trans (Ψ 1), K 0 ∪ K 1, φ, L, η, Γ, X.shellChart, X.shellBase, X.shellSlope,
    X.shellBase_pos, X.shellSlope_pos, Θ, ε, r, (hK 0).union (hK 1),
    union_subset (hKI 0) (hKI 1), ?_, h3, hφI, hφp, ?_, hLk, hLc, hLR, hη, hηb, hηr, hΓs, hΓ,
    hLb, X.shellBase_add_slope_lt_one, X.closedBall_subset_shellChart_source, ?_,
    X.shellChart_image_ball, hr, hΘ, ?_⟩
  · intro x hx
    change Ψ 1 (Ψ 0 x) = x
    rw [hfix 0 x fun h => hx (Or.inl h), hfix 1 x fun h => hx (Or.inr h)]
  · rw [disjoint_iff_forall_ne]
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ he
    have hp3 : p ∈ (φ 0).source := h3 0 (by
      change ‖p.1.down‖ ≤ 3
      have : ‖p.1.down‖ ≤ 1 := hp
      linarith)
    have hq3 : q ∈ (φ 1).source := h3 1 (by
      change ‖q.1.down‖ ≤ 3
      have : ‖q.1.down‖ ≤ 1 := hq
      linarith)
    exact disjoint_left.mp hdisj (hφp 0 ((φ 0).map_source hp3))
      (he ▸ hφp 1 ((φ 1).map_source hq3))
  · intro t z s hs hs2
    exact (X.exists_shell t).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1
      z s hs hs2
  · intro t x hx
    change Ψ 1 (Ψ 0 (X.shellChart t x)) = _
    have hmem := X.shellChart_image_subset DQ t ⟨x, hx, rfl⟩
    rcases Fin.exists_fin_two.mp ⟨t, rfl⟩ with rfl | rfl
    · rw [hmatch 0 x hx, hother0 _ (hfill 0 _)]
    · rw [hother1 _ hmem, hmatch 1 x hx]

end GC.GraphManifold.Assembly
