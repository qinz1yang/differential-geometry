import DifferentialGeometry.Topology.Homotopy.PathModel
import DifferentialGeometry.Topology.Homotopy.BasedMap
import DifferentialGeometry.Topology.Homotopy.Adjunction
import DifferentialGeometry.Topology.Homotopy.Reindex
import DifferentialGeometry.Topology.LoopSpace.BasedNaturality
import Mathlib.Logic.Equiv.Fin.Basic







noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {Q : Type*} [TopologicalSpace Q]


def basedCircleConstant (q : Q) : basedCircleLoop q := ⟨FreeLoop.constants q, rfl⟩


def genLoopCircleHomeomorph (q : Q) : GenLoop (Fin 1) Q q ≃ₜ basedCircleLoop q :=
  (genLoopPathHomeomorph (Fin 1) q).trans (basedPathCircleHomeomorph q)


theorem genLoopCircleHomeomorph_const (q : Q) :
    genLoopCircleHomeomorph q GenLoop.const = basedCircleConstant q := by
  change basedPathCircleHomeomorph q (genLoopPathHomeomorph (Fin 1) q GenLoop.const) = _
  rw [genLoopPathHomeomorph_const]
  apply Subtype.ext
  exact basedPathCircleHomeomorph_refl q


theorem genLoopCircleHomeomorph_symm_constant (q : Q) :
    (genLoopCircleHomeomorph q).symm (basedCircleConstant q) = GenLoop.const := by
  rw [← genLoopCircleHomeomorph_const q]
  exact (genLoopCircleHomeomorph q).symm_apply_apply _



def basedCircleHomotopyGroupMulEquiv (n : ℕ) (q : Q) :
    HomotopyGroup (Fin (n + 1)) (basedCircleLoop q) (basedCircleConstant q) ≃*
      HomotopyGroup (Fin (n + 1) ⊕ Fin 1) Q q :=
  (homotopyGroupBasedHomeomorphMulEquiv (N := Fin (n + 1))
    (genLoopCircleHomeomorph q).symm (basedCircleConstant q) GenLoop.const
      (genLoopCircleHomeomorph_symm_constant q)).trans
    (homotopyGroupIteratedLoopMulEquiv (K := Fin (n + 1)) (N := Fin 1) q)



def basedCirclePiTwoMulEquiv (q : Q) :
    HomotopyGroup (Fin 2) (basedCircleLoop q) (basedCircleConstant q) ≃*
      HomotopyGroup (Fin 3) Q q :=
  (basedCircleHomotopyGroupMulEquiv 1 q).trans
    (homotopyGroupReindexMulEquiv (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3) q)


def basedCirclePiOneMulEquiv (q : Q) :
    HomotopyGroup (Fin 1) (basedCircleLoop q) (basedCircleConstant q) ≃*
      HomotopyGroup (Fin 2) Q q :=
  (basedCircleHomotopyGroupMulEquiv 0 q).trans
    (homotopyGroupReindexMulEquiv (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2) q)

end DifferentialGeometry.Topology
