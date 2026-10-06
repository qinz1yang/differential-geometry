/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTheoremMain
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordCoordinates

set_option autoImplicit false

/-!
# Fixture FX2 (basic data): the standard solid torus in the standard `S³`

`M = S³` (standard oriented closed 3-manifold), `W = {‖z‖ ≤ ‖w‖}` (closed solid torus
`≅ closedDisk × S¹`), boundary torus = Clifford torus, bicollar `σ((j,x),s) = cliffordSeam(x,-s)`.
No Ricci-flow data.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1
open GC.Endpoint

/-- The ambient closed oriented 3-manifold `S³`. -/
abbrev M_FX2 : Type := SphereCarrier.{0}

/-- The closed solid torus `{‖z‖ ≤ ‖w‖}`. -/
def W_FX2 : Set M_FX2 := {p | cliffordHeight p ≤ 0}

theorem isClosed_W_FX2 : IsClosed W_FX2 :=
  isClosed_le contMDiff_cliffordHeight.continuous continuous_const

/-- Flip of the collar coordinate (so that `s ≥ 0` is the solid-torus side). -/
def flip_FX2 : (Unit × Torus) × ℝ ≃ₜ Torus × ℝ where
  toFun p := (p.1.2, -p.2)
  invFun q := (((), q.1), -q.2)
  left_inv := fun ⟨⟨u, x⟩, s⟩ => by simp
  right_inv := fun ⟨x, s⟩ => by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The bicollar of `∂W` in `M`. -/
def σ_FX2 : OpenPartialHomeomorph ((Unit × Torus) × ℝ) M_FX2 :=
  flip_FX2.toOpenPartialHomeomorph.trans (cliffordSeam.{0}).toOpenPartialHomeomorph

theorem σ_FX2_source : σ_FX2.source = {p | -1 < p.2 ∧ p.2 < 1} := by
  ext p
  have h1 : (cliffordSeam.{0}).toOpenPartialHomeomorph.source = signedCollarSource := rfl
  simp only [σ_FX2, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
    Homeomorph.toOpenPartialHomeomorph_apply, h1, signedCollarSource, mem_inter_iff, mem_univ,
    mem_preimage, mem_setOf_eq, true_and]
  change (-1 < -p.2 ∧ -p.2 < 1) ↔ _
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem σ_FX2_apply (p : (Unit × Torus) × ℝ) : σ_FX2 p = cliffordSeamMap (p.1.2, -p.2) := rfl

theorem cliffordHeight_σ_FX2 {p : (Unit × Torus) × ℝ} (hp : p ∈ σ_FX2.source) :
    cliffordHeight (σ_FX2 p) = -p.2 := by
  rw [σ_FX2_source] at hp
  rw [σ_FX2_apply, cliffordHeight_cliffordSeamMap, seamClamp_of_mem (by linarith [hp.2])
    (by linarith [hp.1])]

theorem hside_FX2 : ∀ p ∈ σ_FX2.source, σ_FX2 p ∈ W_FX2 ↔ 0 ≤ p.2 := by
  intro p hp
  change cliffordHeight (σ_FX2 p) ≤ 0 ↔ _
  rw [cliffordHeight_σ_FX2 hp]
  constructor <;> intro h <;> linarith

theorem hfront_FX2 :
    W_FX2 \ range (fun x : Unit × Torus => σ_FX2 (x, 0)) ⊆ interior W_FX2 := by
  rintro p ⟨hp, hnr⟩
  have hlt : cliffordHeight p < 0 := by
    refine lt_of_le_of_ne hp fun h0 => hnr ?_
    have hmem : p ∈ cliffordSeamTarget.{0} := by
      have h₁ := norm_sphereFirst_sq_eq p
      have h₂ := norm_sphereSecond_sq_eq p
      rw [h0] at h₁ h₂
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [h, norm_zero] at h₁
        norm_num at h₁
      · rw [h, norm_zero] at h₂
        norm_num at h₂
    refine ⟨((), (cliffordSeamInv.{0} p).1), ?_⟩
    have := (cliffordSeam.{0}).right_inv hmem
    change cliffordSeamMap (((cliffordSeamInv.{0} p).1), -(0:ℝ)) = p
    have hs : (cliffordSeamInv.{0} p).2 = 0 := h0
    rw [neg_zero, ← hs]
    exact this
  exact interior_maximal (fun q hq => le_of_lt hq)
    (isOpen_lt contMDiff_cliffordHeight.continuous continuous_const) hlt

end GC.LongTime.CuspP1
