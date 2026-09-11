import DifferentialGeometry.Topology.LoopSpace.Basic
import Mathlib.Topology.Homotopy.HomotopyGroup



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X] {x : X}




theorem genLoop_homotopic_iff_joined (p q : GenLoop N X x) :
    GenLoop.Homotopic p q ↔ Joined p q := by
  constructor
  · rintro ⟨H⟩
    let F : C(unitInterval, GenLoop N X x) :=
      ⟨fun t => ⟨H.toHomotopy.curry t, fun y hy =>
        (H.eq_fst t hy).trans (GenLoop.boundary p y hy)⟩,
        H.toHomotopy.curry.continuous.subtype_mk _⟩
    refine ⟨⟨F, ?_, ?_⟩⟩
    · apply GenLoop.ext
      intro y
      exact H.apply_zero y
    · apply GenLoop.ext
      intro y
      exact H.apply_one y
  · rintro ⟨P⟩
    let F : C(unitInterval, C(N → unitInterval, X)) :=
      ⟨fun t => (P t).val, continuous_subtype_val.comp P.continuous⟩
    refine ⟨⟨⟨F.uncurry, ?_, ?_⟩, ?_⟩⟩
    · intro y
      change (P 0) y = p y
      rw [P.source]
    · intro y
      change (P 1) y = q y
      rw [P.target]
    · intro t y hy
      change (P t) y = p y
      rw [GenLoop.boundary (P t) y hy, GenLoop.boundary p y hy]



theorem genLoopHomeomorph_homotopic_iff {K Y : Type*} [TopologicalSpace Y] {y : Y}
    (e : GenLoop N X x ≃ₜ GenLoop K Y y) (p q : GenLoop N X x) :
    GenLoop.Homotopic (e p) (e q) ↔ GenLoop.Homotopic p q := by
  rw [genLoop_homotopic_iff_joined, genLoop_homotopic_iff_joined]
  constructor
  · intro h
    simpa only [e.symm_apply_apply] using h.map e.symm.continuous
  · exact fun h => h.map e.continuous



def homotopyGroupIteratedLoopEquiv {K : Type*} (x : X) :
    HomotopyGroup K (GenLoop N X x) GenLoop.const ≃ HomotopyGroup (K ⊕ N) X x :=
  Quotient.congr (GenLoop.genLoopGenLoopEquiv (M := K) (N := N) x).toEquiv
    (fun p q => (genLoopHomeomorph_homotopic_iff
      (GenLoop.genLoopGenLoopEquiv (M := K) (N := N) x) p q).symm)

end DifferentialGeometry.Topology
