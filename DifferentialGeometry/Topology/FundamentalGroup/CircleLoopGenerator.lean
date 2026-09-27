/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.ZMultiples
import DifferentialGeometry.Topology.FundamentalGroup.LoopPower
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.BasedCircle

namespace DifferentialGeometry.Topology

open AddSubgroup Set

noncomputable def circleGeneratorPath : Path (0 : loopCircle) (0 : loopCircle) where
  toFun t := ((t : ℝ) : loopCircle)
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  source' := rfl
  target' := AddCircle.coe_period (1 : ℝ)

theorem circleGeneratorPath_apply (t : unitInterval) :
    circleGeneratorPath t = ((t : ℝ) : loopCircle) := rfl

noncomputable def unitRealPath : Path (0 : ℝ) (1 : ℝ) where
  toFun t := (t : ℝ)
  continuous_toFun := continuous_subtype_val
  source' := rfl
  target' := rfl

theorem circleQuotientCovering :
    IsAddQuotientCoveringMap ((↑) : ℝ → loopCircle) (zmultiples (1 : ℝ)) :=
  AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)

def circleFiberZero : ((↑) : ℝ → loopCircle) ⁻¹' {(0 : loopCircle)} := ⟨0, rfl⟩

def circleFiberOne : ((↑) : ℝ → loopCircle) ⁻¹' {(0 : loopCircle)} :=
  ⟨1, AddCircle.coe_period (1 : ℝ)⟩

theorem monodromy_circleGeneratorPath :
    circleQuotientCovering.isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk circleGeneratorPath) circleFiberZero = circleFiberOne := by
  refine circleQuotientCovering.isCoveringMap.monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk unitRealPath) ?_
  rfl

theorem fundamentalGroupToMulOpposite_circleGeneratorPath :
    circleQuotientCovering.fundamentalGroupToMulOpposite circleFiberZero
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath)) =
      MulOpposite.op (Multiplicative.ofAdd (⟨1, mem_zmultiples (1 : ℝ)⟩ : zmultiples (1 : ℝ))) := by
  rw [IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff,
    monodromy_circleGeneratorPath]
  simp only [MulOpposite.unop_op, circleFiberZero, circleFiberOne]
  exact add_zero (1 : ℝ)

theorem exists_zpow_fundamentalGroup_loopCircle (a : FundamentalGroup loopCircle 0) :
    ∃ k : ℤ,
      a = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath) ^ k := by
  set s : FundamentalGroup loopCircle 0 :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath) with hs
  set φ := circleQuotientCovering.fundamentalGroupToMulOpposite circleFiberZero with hφ
  obtain ⟨x, hx⟩ := (φ a).unop.toAdd.2
  refine ⟨x, circleQuotientCovering.fundamentalGroupToMulOpposite_injective circleFiberZero ?_⟩
  rw [map_zpow, hs, fundamentalGroupToMulOpposite_circleGeneratorPath, ← MulOpposite.op_zpow,
    ← ofAdd_zsmul]
  refine MulOpposite.unop_injective (Subtype.ext ?_)
  change ((Multiplicative.toAdd (MulOpposite.unop (φ a)) : zmultiples (1 : ℝ)) : ℝ) =
    ((x • (⟨1, mem_zmultiples (1 : ℝ)⟩ : zmultiples (1 : ℝ)) : zmultiples (1 : ℝ)) : ℝ)
  rw [← hx]
  simp

theorem exists_homotopic_loopZPow_circleGeneratorPath (m : Path (0 : loopCircle) 0) :
    ∃ k : ℤ, m.Homotopic (loopZPow circleGeneratorPath k) :=
  exists_homotopic_loopZPow_of_forall_exists_zpow exists_zpow_fundamentalGroup_loopCircle m

variable {Q : Type*} [TopologicalSpace Q] [T2Space Q] {q : Q}

theorem exists_homotopic_loopZPow_of_bijective (G : C(loopCircle, Q))
    (hbij : Function.Bijective G) (hq : G 0 = q) (ℓ : Path q q)
    (hℓ : ∀ t : unitInterval, ℓ t = G ((t : ℝ) : loopCircle)) (m : Path q q) :
    ∃ k : ℤ, m.Homotopic (loopZPow ℓ k) := by
  set h : loopCircle ≃ₜ Q :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G hbij) G.continuous with hh
  set hc : C(loopCircle, Q) := (h : C(loopCircle, Q)) with hhc
  have hcoe : ∀ z : loopCircle, hc z = G z := fun _ => rfl
  have hq' : q = h 0 := hq.symm
  have hzero : (0 : loopCircle) = h.symm q := by
    rw [hq', h.symm_apply_apply]
  set m' : Path (0 : loopCircle) (0 : loopCircle) :=
    (m.map h.symm.continuous).cast hzero hzero with hm'
  obtain ⟨k, hk⟩ := exists_homotopic_loopZPow_circleGeneratorPath m'
  refine ⟨k, ?_⟩
  have hmap := (hk.map hc).pathCast hq' hq'
  have hleft : ((m'.map hc.continuous).cast hq' hq') = m := by
    refine Path.ext (funext fun t => ?_)
    change hc (m' t) = m t
    rw [hm']
    change hc (h.symm (m t)) = m t
    exact h.apply_symm_apply _
  have hgen : (circleGeneratorPath.map hc.continuous).cast hq' hq' = ℓ := by
    refine Path.ext (funext fun t => ?_)
    change hc (((t : ℝ) : loopCircle)) = ℓ t
    rw [hℓ t, hcoe]
  have hright :
      (((loopZPow circleGeneratorPath k).map hc.continuous).cast hq' hq') =
        loopZPow ℓ k := by
    rw [loopZPow_map, loopZPow_cast, hgen]
  rw [hleft, hright] at hmap
  exact hmap

end DifferentialGeometry.Topology
