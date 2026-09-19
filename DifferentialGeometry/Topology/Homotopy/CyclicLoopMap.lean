/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.FundamentalGroup.BasepointChange
import DifferentialGeometry.Topology.FundamentalGroup.LoopPower

/-! Triviality of loop maps whose cyclic generator is nullhomotopic. -/

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X}

theorem loopZPow_homotopic_refl {p : Path x x} (hp : p.Homotopic (Path.refl x)) (k : ℤ) :
    (loopZPow p k).Homotopic (Path.refl x) := by
  apply Path.Homotopic.Quotient.eq.mp
  change (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (loopZPow p k)) :
    FundamentalGroup X x) = 1
  have hp' : (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) :
      FundamentalGroup X x) = 1 := Path.Homotopic.Quotient.eq.mpr hp
  rw [fromPath_loopZPow, hp', one_zpow]

theorem map_homotopic_refl_of_generating_loop (f : C(X, Y)) {p : Path x x}
    (hgen : ∀ q : Path x x, ∃ k : ℤ, q.Homotopic (loopZPow p k))
    (hp : (p.map f.continuous).Homotopic (Path.refl (f x)))
    (hy : Joined x y) (q : Path y y) :
    (q.map f.continuous).Homotopic (Path.refl (f y)) := by
  obtain ⟨r⟩ := hy
  obtain ⟨k, hk⟩ := hgen ((r.trans q).trans r.symm)
  have hmap := hk.map f
  rw [loopZPow_map] at hmap
  have hnull := hmap.trans (loopZPow_homotopic_refl hp k)
  apply Path.Homotopic.Quotient.eq.mp
  change (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (q.map f.continuous)) :
    FundamentalGroup Y (f y)) = (1 : FundamentalGroup Y (f y))
  apply (fundamentalGroupChangeBasepoint (r.map f.continuous)).injective
  rw [map_one]
  have heq := Path.Homotopic.Quotient.eq.mpr hnull
  simpa only [Path.map_trans, ← Path.map_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.mk''_eq_mk,
    fundamentalGroupChangeBasepoint_apply,
    FundamentalGroup.one_def, Path.Homotopic.Quotient.mk_refl] using heq

end DifferentialGeometry.Topology
