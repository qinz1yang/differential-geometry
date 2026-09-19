/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homotopy.SquareBoundary
import DifferentialGeometry.Topology.LoopSpace.BasedNaturality
import DifferentialGeometry.Topology.LoopSpace.Rotation

/-! Free and based nullhomotopies of loops. -/

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem pathToCircle_nullhomotopic_iff (p : Path x x) :
    (pathToCircle p).Nullhomotopic ↔ p.Homotopic (Path.refl x) := by
  constructor
  · rintro ⟨y, ⟨H⟩⟩
    let r : Path x y := {
      toFun := fun t => H (t, 0)
      continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
      source' := (H.apply_zero 0).trans (pathToCircle_zero p)
      target' := H.apply_one 0 }
    have hcomm := square_boundary_homotopic p (Path.refl y) r r
      (⟨fun z : unitInterval × unitInterval => H (z.1, ((z.2 : ℝ) : loopCircle)),
        H.continuous.comp (continuous_fst.prodMk
          ((AddCircle.continuous_mk' (1 : ℝ)).comp
            (continuous_subtype_val.comp continuous_snd)))⟩ :
        C(unitInterval × unitInterval, X))
      (fun s => (H.apply_zero _).trans (pathToCircle_coe p s))
      (fun s => H.apply_one _) (fun _ => rfl) (fun t => by
        change H (t, ((1 : ℝ) : loopCircle)) = H (t, 0)
        rw [AddCircle.coe_period])
    apply Path.Homotopic.Quotient.eq.mp
    have heq := congrArg
      (fun q : Path.Homotopic.Quotient x y => q.trans (Path.Homotopic.Quotient.mk r).symm)
      (Path.Homotopic.Quotient.eq.mpr hcomm)
    simpa only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl,
      Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_refl,
      Path.Homotopic.Quotient.trans_symm] using heq
  · intro h
    have hconst := basedPathCircleHomeomorph_refl (P := X) x
    change pathToCircle (Path.refl x) = ContinuousMap.const loopCircle x at hconst
    exact ⟨x, hconst ▸ pathToCircle_homotopic h⟩

end DifferentialGeometry.Topology
