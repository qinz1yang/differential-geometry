import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1CycleNeckData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelNormalFormApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1Necks

/-!
# Chapter-14 assembly, item L1: a ball–handle cycle with product rims is a solid torus

Lane ASM-L1b3. G3b′ `BallHandleCycle.exists_cycleNormalForm_of_rimProduct` (T1′ of lane ASM-L1e3
followed by `BallHandleCycle.cycleNormalForm_of_neckData`) and the final L1 theorem
`exists_solidTorus_of_ballHandleCycle_of_rimProduct` (the normal form glued to the model normal
form, `BallHandleCycle.nonempty_diffeomorph_of_cycleNormalForm`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **G3b′ (new form, lead 2026-10-04).** -/
theorem BallHandleCycle.exists_cycleNormalForm_of_rimProduct {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) (hprod : C.RimProduct)
    (hint : ∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)) :
    ∃ ε : ℝ, Nonempty (CycleNormalForm W.model W.Carrier C.len ε (range C.union.map)) := by
  obtain ⟨ε, hε, hε', N, hsrc, hdisj, hball, hhandle, hunion, hpieces, hfillet, hprodN, hsb⟩ :=
    C.exists_necks_of_rimProduct hprod hint
  exact ⟨ε, C.cycleNormalForm_of_neckData hε hε' N hsrc hdisj hball hhandle hunion hpieces
    hfillet hprodN hsb⟩

/-- **L1, final form** (verbatim from `build-logs/scratch/ASM-TOR/T4Targets.lean`). -/
theorem exists_solidTorus_of_ballHandleCycle_of_rimProduct {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) (hprod : C.RimProduct)
    (hint : ∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)) :
    Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
      C.union.Piece) := by
  obtain ⟨ε, ⟨N⟩⟩ := C.exists_cycleNormalForm_of_rimProduct hprod hint
  exact C.nonempty_diffeomorph_of_cycleNormalForm N

end GC.GraphManifold.Assembly
