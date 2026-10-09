import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugPiece

/-!
# Chapter-14 assembly, relative COMPARE G4: the ports of the placed plug

Lane ASM-L2e, group G4. On the two port collars of the plug, the placed plug is the radial collar
of the placed tube, read from the inside: `F (Ψ⁻¹ (φ t ((1 - s/2) w, θ)))` up to the marking of
the plug port and the conjugation of the placement.

* `seamRadius_one_neg`: the radius of the solid collar.
* `placedMap_retained`: the placed plug on the retained port collars of the plug.
* `ports_not_mem_neckSet`: the port collars of the plug avoid its neck.
* `placedPlugMap_port`: the placed plug on the port collars.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem seamRadius_one_neg (s : ℝ) : seamRadius 1 (-s) = 3 * (1 - s / 2) := by
  simp only [seamRadius, Nat.cast_one, inv_one, Real.rpow_one]
  ring

namespace SolidCapPlug

variable {P : CompactCarrier.{u}} (Y : SolidCapPlug P)
  {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  {X : SphereCutCapped W S E}
  {Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier}
  {φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
    (PlaneLift.{u} × Circle) X.Q.Carrier ∞}
  {Θ : Fin 2 → solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u}} {ε : Fin 2 → Bool} {r : Fin 2 → ℝ}
  (hΘ : ∀ t (x : solidSet.{u}), r t ≤ ‖x.val.1.down‖ → (Θ t x).val =
    if ε t then (ULift.up ((starRingEnd ℂ) x.val.1.down), x.val.2) else x.val)

include hΘ in
/-- **The placed plug on the retained ports**: the inner radial collar of the placed tube. -/
theorem placedMap_retained (t : Fin 2) (p : Torus) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < Y.depth)
    (hs1 : s < 1) (hr : r t ≤ 3 * (1 - s / 2)) :
    Y.placedMap Ψ φ Θ (Y.cut.capping.retained.collar (Y.port t) (Y.marking t p, halfPoint s hs0)) =
      Ψ.symm (φ t (ULift.up ((1 - s / 2) •
        (if ε t then (starRingEnd ℂ) (p.1 : ℂ) else (p.1 : ℂ))), p.2)) := by
  rw [← Y.solid_collar t p s hs0 hsd]
  set q := solidCollar 1 (p, halfPoint s hs0)
  rw [Y.placedMap_of_mem Ψ φ Θ t (Y.solid t q).property]
  change Ψ.symm (solidTubeFill (φ t) (Θ t ((Y.solid t).symm (Y.solid t q)))) = _
  rw [Diffeomorph.symm_apply_apply]
  have hqv : q.val = (ULift.up (seamRadius 1 (-s) • (p.1 : ℂ)), p.2) := by
    have := solidCollar_apply_val 1 (q := (p, halfPoint s hs0)) hs1
    simpa [halfPoint_val_zero] using this
  have hqn : ‖q.val.1.down‖ = 3 * (1 - s / 2) := by
    rw [hqv, seamRadius_one_neg]
    change ‖(3 * (1 - s / 2) : ℝ) • (p.1 : ℂ)‖ = _
    rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hΘq := hΘ t q (by rw [hqn]; exact hr)
  unfold solidTubeFill
  rw [hΘq]
  congr 1
  rcases hε : ε t
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hqv, seamRadius_one_neg]
    apply congrArg (φ t)
    apply Prod.ext
    · apply ULift.ext
      change (3 * (1 - s / 2) : ℝ) • (p.1 : ℂ) / 3 = (1 - s / 2 : ℝ) • (p.1 : ℂ)
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    · rfl
  · simp only [↓reduceIte]
    rw [hqv, seamRadius_one_neg]
    apply congrArg (φ t)
    apply Prod.ext
    · apply ULift.ext
      change (starRingEnd ℂ) ((3 * (1 - s / 2) : ℝ) • (p.1 : ℂ)) / 3 =
        (1 - s / 2 : ℝ) • (starRingEnd ℂ) (p.1 : ℂ)
      rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    · rfl

/-- A port half collar of the plug cut never meets a cut-sphere half collar. -/
theorem tori_ne_sphere {j : Fin Y.cut.B.torusCount} {k : Fin Y.cut.B.sphereCount}
    {q : Torus × EuclideanHalfSpace 1} (hq : q ∈ halfCollarSource)
    {p : ClosureSphere.{u} × EuclideanHalfSpace 1} (hp : p ∈ sphereHalfCollarSource) :
    Y.cut.B.tori.collar j q ≠ Y.cut.B.sphere k p := by
  intro he
  have h1 : Y.cut.B.tori.collar j q ∈ (Y.cut.B.tori.collar j).target :=
    (Y.cut.B.tori.collar j).map_source (by rw [Y.cut.B.tori.source_eq]; exact hq)
  have h2 : Y.cut.B.sphere k p ∈ (Y.cut.B.sphere k).target :=
    (Y.cut.B.sphere k).map_source (by rw [Y.cut.B.sphere_source]; exact hp)
  exact Set.disjoint_left.mp (Y.cut.B.cross_disjoint j k) h1 (he ▸ h2)

/-- **The port collars of the plug avoid its neck.** -/
theorem ports_not_mem_neckSet (i : Fin Y.portCount) {q : Torus × EuclideanHalfSpace 1}
    (hq : q ∈ halfCollarSource) : Y.ports.collar i q ∉ Y.neckSet := by
  rintro ⟨⟨z, σ⟩, ⟨-, hσL, hσU⟩, he⟩
  have hη := Y.germ_le
  have hport : Y.ports.collar i q = Y.cut.fold (Y.cut.B.tori.collar (Fin.cast Y.cut.hn.symm i) q) :=
    (Y.cut.tori i q hq).symm
  have hs1 : |σ| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, Y.cut.fold (Y.cut.B.sphere (Fin.cast Y.cut.h2.symm k)
      (z, halfPoint |σ| (abs_nonneg σ))) = Y.seam.collar (z, σ) := by
    rcases le_or_gt 0 σ with hσ | hσ
    · refine ⟨0, ?_⟩
      rw [Y.cut.spheres 0 z |σ| (abs_nonneg σ) hs1]
      simp [abs_of_nonneg hσ]
    · refine ⟨1, ?_⟩
      rw [Y.cut.spheres 1 z |σ| (abs_nonneg σ) hs1]
      simp [abs_of_neg hσ]
  have hfold := hk.trans (he.trans hport)
  have hsrc : ∀ z' : ClosureSphere.{u}, (z', halfZero) ∈ sphereHalfCollarSource := by
    intro z'
    change (0 : ℝ) < 1
    norm_num
  rcases Y.cut.fold_eq hfold with h | ⟨z', ⟨-, h⟩ | ⟨-, h⟩⟩
  · exact Y.tori_ne_sphere hq (show (z, halfPoint |σ| (abs_nonneg σ)) ∈ sphereHalfCollarSource
      from hs1) h.symm
  · exact Y.tori_ne_sphere hq (hsrc z') h
  · exact Y.tori_ne_sphere hq (hsrc z') h

end SolidCapPlug

end GC.GraphManifold.Assembly
