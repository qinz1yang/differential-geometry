import DifferentialGeometry.Geometry.Comparison.PairedPacket

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X]

theorem PairedComparisonPacket.extend {β : ℝ} {z x y : X} {a b : ι → X}
    (hpacket : PairedComparisonPacket β {z} a b)
    (hnew : Real.pi - β < comparisonAngleNegCurvature 1 (dist z x) (dist z y) (dist x y))
    (hcross : ∀ i, ∀ u ∈ ({a i, b i} : Set X), ∀ v ∈ ({x, y} : Set X),
      Real.pi / 2 - β < comparisonAngleNegCurvature 1 (dist z u) (dist z v) (dist u v)) :
    PairedComparisonPacket β {z} (fun i : Option ι => i.elim x a)
      (fun i : Option ι => i.elim y b) := by
  constructor
  · intro p hp i
    have hpz : p = z := mem_singleton_iff.mp hp
    subst p
    cases i with
    | none => exact hnew
    | some i => exact hpacket.opposite z (mem_singleton _) i
  · intro p hp i j hij u hu v hv
    have hpz : p = z := mem_singleton_iff.mp hp
    subst p
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        rw [comparisonAngleNegCurvature_comm, dist_comm u v]
        exact hcross j v hv u hu
    | some i =>
      cases j with
      | none => exact hcross i u hu v hv
      | some j =>
        exact hpacket.cross z (mem_singleton _) i j (fun h => hij (congrArg some h)) u hu v hv

end DifferentialGeometry.Geometry.Comparison.Toponogov
