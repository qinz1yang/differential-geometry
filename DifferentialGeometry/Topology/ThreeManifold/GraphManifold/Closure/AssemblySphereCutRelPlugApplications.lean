import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugFibre
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugAssembly

/-!
# Chapter-14 assembly, relative COMPARE G4: the bounded fibre plug is a piece of `W`

Lanes ASM-L2e / ASM-L2e2, group G4 (frozen text of `build-logs/scratch/ASM-L2e/Targets.lean`).

* `exists_fibrePlugPiece`: the bounded fibre plug (Raw, connected, with boundary) with the solid
  charts of its two cap ball charts; for every placement of the two capped cut spheres of a
  sphere-cut-capped carrier into two disjoint tubes, the plug is an injective piece of `W` with its
  two port lifts on the radial collars of the placed tubes. Proof: the inhabitant
  `exists_fibreSolidCapPlug` of `SolidCapPlug` and the generic `SolidCapPlug.exists_placedPiece`.
* `PieceFold.image_boundary_of_placedLifts` and the consumer `exists_fibrePlugPiece_boundaryImage`:
  the boundary of the placed plug piece is the fold of the two placed unit tube boundaries.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **G4 (ASM-L2e, frozen text).** There is the bounded fibre plug `P` (Raw, connected, with
boundary) with two ball charts `v t` of the solid torus (its two capped sides in solid coordinates)
such that, for EVERY placement of the two capped cut spheres of a sphere-cut-capped carrier into two
disjoint tubes (G2 shape: `Ψ (c t x) = solidTubeFill (φ t) (Θ t (v t x))` on the closed radius-two
ball, `c t` the A6-a shell charts), the plug is a piece of `W`: an injective `PieceFold`
diffeomorphic to `P`, whose two port lifts land on the radial collars
`F (Ψ⁻¹ (φ t ((1 - ν s / 2) w, θ)))` of the tubes and exhaust its boundary, with the stated image;
the caps stay inside the radius `1 - ν` tubes. -/
theorem exists_fibrePlugPiece :
    ∃ (P : CompactCarrier.{u}) (v : Fin 2 → PartialDiffeomorph (𝓡 3) (𝓡∂ 3) E3 solidSet.{u} ∞),
      Nonempty (RawGraphPresentation P) ∧ P.kind = .withBoundary ∧ ConnectedSpace P.Carrier ∧
      (∀ t, closedBall 0 2 ⊆ (v t).source) ∧
      (∀ t, (v t).target ⊆ (𝓡∂ 3).interior solidSet.{u}) ∧
      ∀ {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
        (X : SphereCutCapped W S E)
        (F : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞),
        F.source = (⋃ j, range (X.capping.cap j))ᶜ →
        (∀ y, X.capping.core y ∈ F.source → F (X.capping.core y) = X.fold y) →
        ∀ (Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier)
          (φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
            (PlaneLift.{u} × Circle) X.Q.Carrier ∞),
        (∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source) →
        (∀ t, (φ t).target ⊆ X.Q.interior) →
        Disjoint (φ 0 '' {p | ‖p.1.down‖ ≤ 1}) (φ 1 '' {p | ‖p.1.down‖ ≤ 1}) →
        ∀ (c : Fin 2 → PartialDiffeomorph (𝓡 3) X.Q.model E3 X.Q.Carrier ∞) (s₀ μ : Fin 2 → ℝ)
          (hs₀ : ∀ t, 0 < s₀ t) (hμ : ∀ t, 0 < μ t),
        (∀ t, s₀ t + μ t < 1) →
        (∀ t, closedBall 0 2 ⊆ (c t).source) →
        (∀ t (z : sphere (0 : E3) 1) (r : ℝ) (hr : 1 ≤ r), r ≤ 2 →
          c t (r • (z : E3)) = X.capping.core (X.B.sphere (Fin.cast X.h2.symm t)
            (ULift.up z, halfPoint (s₀ t + μ t * (r - 1))
              (add_nonneg (hs₀ t).le (mul_nonneg (hμ t).le (sub_nonneg.mpr hr)))))) →
        (∀ t, c t '' ball 0 1 = range (X.capping.cap (Fin.cast X.h2.symm t)) ∪
          X.capping.core '' (X.B.sphere (Fin.cast X.h2.symm t) '' {p | p.2.val 0 < s₀ t})) →
        ∀ (Θ : Fin 2 → solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}) (ε : Fin 2 → Bool)
          (r : Fin 2 → ℝ),
        (∀ t, r t < 3) →
        (∀ t (x : solidSet.{u}), r t ≤ ‖x.val.1.down‖ → (Θ t x).val =
          if ε t then (ULift.up ((starRingEnd ℂ) x.val.1.down), x.val.2) else x.val) →
        (∀ t, ∀ x ∈ closedBall (0 : E3) 2, Ψ (c t x) = solidTubeFill (φ t) (Θ t (v t x))) →
        ∀ {ν₀ : ℝ}, 0 < ν₀ →
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
  obtain ⟨P, Y, hR, hPk, hconn⟩ := exists_fibreSolidCapPlug.{u}
  refine ⟨P, Y.solidChart, hR, hPk, hconn, fun t => ?_, Y.solidChart_target_interior, ?_⟩
  · rw [Y.solidChart_source]
    exact Y.capChart_source t
  · intro W S n E X F hFs hF Ψ φ h3 _ hφd c s₀ μ hs₀ hμ hsμ _ hshell hball Θ ε r hr hΘ hmatch
      ν₀ hν₀
    exact Y.exists_placedPiece hFs hF hΘ hPk h3 hφd hs₀ hμ hsμ hshell hball hr hmatch hν₀

/-- The boundary of a piece whose boundary is exhausted by two port lifts on the radial collars of
two placed tubes is the fold of the two placed unit tube boundaries. -/
theorem PieceFold.image_boundary_of_placedLifts {W : CompactCarrier.{u}} {Q : CompactCarrier.{u}}
    (F : PartialDiffeomorph Q.model W.model Q.Carrier W.Carrier ∞)
    (Ψ : Q.Carrier ≃ₘ⟮Q.model, Q.model⟯ Q.Carrier)
    (φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) Q.model
      (PlaneLift.{u} × Circle) Q.Carrier ∞)
    (Pc : PieceFold W) (ν : ℝ)
    (lift : Fin 2 → PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) Pc.Piece ∞)
    (hl : ∀ t p, p ∈ halfCollarSource → Pc.map (lift t p) =
      F (Ψ.symm (φ t (ULift.up ((1 - ν * p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))))
    (hPb : (𝓡∂ 3).boundary Pc.Piece = ⋃ t, range fun τ => lift t (τ, halfZero)) :
    Pc.map '' (𝓡∂ 3).boundary Pc.Piece =
      ⋃ t, range fun τ : Torus => F (Ψ.symm (φ t (ULift.up (τ.1 : ℂ), τ.2))) := by
  have hz : ∀ t (τ : Torus), Pc.map (lift t (τ, halfZero)) =
      F (Ψ.symm (φ t (ULift.up (τ.1 : ℂ), τ.2))) := by
    intro t τ
    have hmem : (τ, halfZero) ∈ halfCollarSource := show (0 : ℝ) < 1 by norm_num
    rw [hl t _ hmem]
    have h0 : (1 - ν * (halfZero : EuclideanHalfSpace 1).val 0 / 2) = 1 := by
      rw [show (halfZero : EuclideanHalfSpace 1).val 0 = 0 from rfl]
      ring
    rw [h0, one_smul]
  rw [hPb, image_iUnion]
  refine iUnion_congr fun t => ?_
  rw [← range_comp]
  exact congrArg range (funext fun τ => hz t τ)

/-- **Consumer (G4).** For every placement, the placed bounded fibre plug is an injective piece of
`W` whose boundary is the fold of the two placed unit tube boundaries and whose image contains the
seam sphere. -/
theorem exists_fibrePlugPiece_boundaryImage :
    ∃ (P : CompactCarrier.{u}) (v : Fin 2 → PartialDiffeomorph (𝓡 3) (𝓡∂ 3) E3 solidSet.{u} ∞),
      Nonempty (RawGraphPresentation P) ∧ (∀ t, closedBall 0 2 ⊆ (v t).source) ∧
      ∀ {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
        (X : SphereCutCapped W S E)
        (F : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞),
        F.source = (⋃ j, range (X.capping.cap j))ᶜ →
        (∀ y, X.capping.core y ∈ F.source → F (X.capping.core y) = X.fold y) →
        ∀ (Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier)
          (φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
            (PlaneLift.{u} × Circle) X.Q.Carrier ∞),
        (∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source) →
        (∀ t, (φ t).target ⊆ X.Q.interior) →
        Disjoint (φ 0 '' {p | ‖p.1.down‖ ≤ 1}) (φ 1 '' {p | ‖p.1.down‖ ≤ 1}) →
        ∀ (c : Fin 2 → PartialDiffeomorph (𝓡 3) X.Q.model E3 X.Q.Carrier ∞) (s₀ μ : Fin 2 → ℝ)
          (hs₀ : ∀ t, 0 < s₀ t) (hμ : ∀ t, 0 < μ t),
        (∀ t, s₀ t + μ t < 1) →
        (∀ t, closedBall 0 2 ⊆ (c t).source) →
        (∀ t (z : sphere (0 : E3) 1) (r : ℝ) (hr : 1 ≤ r), r ≤ 2 →
          c t (r • (z : E3)) = X.capping.core (X.B.sphere (Fin.cast X.h2.symm t)
            (ULift.up z, halfPoint (s₀ t + μ t * (r - 1))
              (add_nonneg (hs₀ t).le (mul_nonneg (hμ t).le (sub_nonneg.mpr hr)))))) →
        (∀ t, c t '' ball 0 1 = range (X.capping.cap (Fin.cast X.h2.symm t)) ∪
          X.capping.core '' (X.B.sphere (Fin.cast X.h2.symm t) '' {p | p.2.val 0 < s₀ t})) →
        ∀ (Θ : Fin 2 → solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}) (ε : Fin 2 → Bool)
          (r : Fin 2 → ℝ),
        (∀ t, r t < 3) →
        (∀ t (x : solidSet.{u}), r t ≤ ‖x.val.1.down‖ → (Θ t x).val =
          if ε t then (ULift.up ((starRingEnd ℂ) x.val.1.down), x.val.2) else x.val) →
        (∀ t, ∀ x ∈ closedBall (0 : E3) 2, Ψ (c t x) = solidTubeFill (φ t) (Θ t (v t x))) →
        ∃ Pc : PieceFold W, Injective Pc.map ∧
          Pc.map '' (𝓡∂ 3).boundary Pc.Piece =
            (⋃ t, range fun τ : Torus => F (Ψ.symm (φ t (ULift.up (τ.1 : ℂ), τ.2)))) ∧
          range (fun z => S.collar (z, 0)) ⊆ range Pc.map := by
  obtain ⟨P, v, hR, -, -, hv, -, hplug⟩ := exists_fibrePlugPiece.{u}
  refine ⟨P, v, hR, hv, ?_⟩
  intro W S n E X F hFs hF Ψ φ h3 hφI hφd c s₀ μ hs₀ hμ hsμ hc hshell hball Θ ε r hr hΘ hmatch
  obtain ⟨Pc, -, ν, lift, -, -, -, -, hl, hPb, hPi, hPr, -⟩ :=
    hplug X F hFs hF Ψ φ h3 hφI hφd c s₀ μ hs₀ hμ hsμ hc hshell hball Θ ε r hr hΘ hmatch
      zero_lt_one
  refine ⟨Pc, hPi, PieceFold.image_boundary_of_placedLifts F Ψ φ Pc ν lift hl hPb, ?_⟩
  rw [hPr]
  exact subset_union_right

end GC.GraphManifold.Assembly
