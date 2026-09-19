/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LoopSpace.BasedCircle
import DifferentialGeometry.Topology.PiecewiseLinear.SlabWedgeEndpointPush

/-!
# Homotopies of endpoint-moving slab wedge pushes
-/

open Set ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable section

noncomputable def positiveBufferedWedgeHomotopy (c ρ : ℝ) :
    ContinuousMap.Homotopy (ContinuousMap.id (ℝ × ℝ × ℝ))
      (positiveBufferedWedgePushHomeomorph c ρ : C(ℝ × ℝ × ℝ, ℝ × ℝ × ℝ)) where
  toFun z := z.2 + (z.1 : ℝ) • (positiveBufferedWedgePush c ρ z.2 - z.2)
  continuous_toFun := continuous_snd.add ((continuous_subtype_val.comp continuous_fst).smul
    (((positiveBufferedWedgePushHomeomorph c ρ).continuous.comp continuous_snd).sub
      continuous_snd))
  map_zero_left p := by simp
  map_one_left p := by simp

noncomputable def negativeBufferedWedgeHomotopy (c ρ : ℝ) :
    ContinuousMap.Homotopy (ContinuousMap.id (ℝ × ℝ × ℝ))
      (negativeBufferedWedgePushHomeomorph c ρ : C(ℝ × ℝ × ℝ, ℝ × ℝ × ℝ)) where
  toFun z := z.2 + (z.1 : ℝ) • (negativeBufferedWedgePush c ρ z.2 - z.2)
  continuous_toFun := continuous_snd.add ((continuous_subtype_val.comp continuous_fst).smul
    (((negativeBufferedWedgePushHomeomorph c ρ).continuous.comp continuous_snd).sub
      continuous_snd))
  map_zero_left p := by simp
  map_one_left p := by simp

@[simp]
theorem positiveBufferedWedgeHomotopy_apply (c ρ : ℝ)
    (z : unitInterval × (ℝ × ℝ × ℝ)) :
    positiveBufferedWedgeHomotopy c ρ z =
      z.2 + (z.1 : ℝ) • (positiveBufferedWedgePush c ρ z.2 - z.2) := rfl

@[simp]
theorem negativeBufferedWedgeHomotopy_apply (c ρ : ℝ)
    (z : unitInterval × (ℝ × ℝ × ℝ)) :
    negativeBufferedWedgeHomotopy c ρ z =
      z.2 + (z.1 : ℝ) • (negativeBufferedWedgePush c ρ z.2 - z.2) := rfl

theorem positiveBufferedWedgeHomotopy_fst (c ρ : ℝ)
    (z : unitInterval × (ℝ × ℝ × ℝ)) :
    (positiveBufferedWedgeHomotopy c ρ z).1 = z.2.1 := by
  rw [positiveBufferedWedgeHomotopy_apply]
  change z.2.1 + (z.1 : ℝ) * ((positiveBufferedWedgePush c ρ z.2).1 - z.2.1) = z.2.1
  rw [positiveBufferedWedgePush_fst]
  simp

theorem negativeBufferedWedgeHomotopy_fst (c ρ : ℝ)
    (z : unitInterval × (ℝ × ℝ × ℝ)) :
    (negativeBufferedWedgeHomotopy c ρ z).1 = z.2.1 := by
  rw [negativeBufferedWedgeHomotopy_apply]
  change z.2.1 + (z.1 : ℝ) * ((negativeBufferedWedgePush c ρ z.2).1 - z.2.1) = z.2.1
  rw [negativeBufferedWedgePush_fst]
  simp

theorem mapsTo_positiveBufferedWedgeHomotopy_fstFiber (c ρ a : ℝ) (t : unitInterval) :
    MapsTo (fun p => positiveBufferedWedgeHomotopy c ρ (t, p))
      {p : ℝ × ℝ × ℝ | p.1 = a} {p : ℝ × ℝ × ℝ | p.1 = a} := by
  intro p hp
  simpa only [mem_ofPred_eq, positiveBufferedWedgeHomotopy_fst] using hp

theorem mapsTo_negativeBufferedWedgeHomotopy_fstFiber (c ρ a : ℝ) (t : unitInterval) :
    MapsTo (fun p => negativeBufferedWedgeHomotopy c ρ (t, p))
      {p : ℝ × ℝ × ℝ | p.1 = a} {p : ℝ × ℝ × ℝ | p.1 = a} := by
  intro p hp
  simpa only [mem_ofPred_eq, negativeBufferedWedgeHomotopy_fst] using hp

theorem positiveBufferedWedgeHomotopy_eq_of_not_mem_support (c ρ : ℝ) (t : unitInterval)
    {p : ℝ × ℝ × ℝ} (hp : p ∉ bufferedSlabWedgeSupport c ρ) :
    positiveBufferedWedgeHomotopy c ρ (t, p) = p := by
  rw [positiveBufferedWedgeHomotopy_apply,
    eqOn_positiveBufferedWedgePush_id_compl_support c ρ hp]
  simp

theorem negativeBufferedWedgeHomotopy_eq_of_not_mem_support (c ρ : ℝ) (t : unitInterval)
    {p : ℝ × ℝ × ℝ} (hp : p ∉ bufferedSlabWedgeSupport c ρ) :
    negativeBufferedWedgeHomotopy c ρ (t, p) = p := by
  rw [negativeBufferedWedgeHomotopy_apply,
    eqOn_negativeBufferedWedgePush_id_compl_support c ρ hp]
  simp

noncomputable def positiveBufferedWedgeFreeLoopHomotopy (c ρ : ℝ)
    (γ : DifferentialGeometry.Topology.freeLoop (ℝ × ℝ × ℝ)) :
    γ.Homotopy ((positiveBufferedWedgePushHomeomorph c ρ :
      C(ℝ × ℝ × ℝ, ℝ × ℝ × ℝ)).comp γ) where
  toFun z := positiveBufferedWedgeHomotopy c ρ (z.1, γ z.2)
  continuous_toFun := (positiveBufferedWedgeHomotopy c ρ).continuous_toFun.comp
    (continuous_fst.prodMk (γ.continuous.comp continuous_snd))
  map_zero_left θ := by simp
  map_one_left θ := by simp

noncomputable def negativeBufferedWedgeFreeLoopHomotopy (c ρ : ℝ)
    (γ : DifferentialGeometry.Topology.freeLoop (ℝ × ℝ × ℝ)) :
    γ.Homotopy ((negativeBufferedWedgePushHomeomorph c ρ :
      C(ℝ × ℝ × ℝ, ℝ × ℝ × ℝ)).comp γ) where
  toFun z := negativeBufferedWedgeHomotopy c ρ (z.1, γ z.2)
  continuous_toFun := (negativeBufferedWedgeHomotopy c ρ).continuous_toFun.comp
    (continuous_fst.prodMk (γ.continuous.comp continuous_snd))
  map_zero_left θ := by simp
  map_one_left θ := by simp

theorem positiveBufferedWedgePush_freeLoop_homotopic (c ρ : ℝ)
    (γ : DifferentialGeometry.Topology.freeLoop (ℝ × ℝ × ℝ)) :
    γ.Homotopic ((positiveBufferedWedgePushHomeomorph c ρ :
      C(ℝ × ℝ × ℝ, ℝ × ℝ × ℝ)).comp γ) :=
  ⟨positiveBufferedWedgeFreeLoopHomotopy c ρ γ⟩

theorem negativeBufferedWedgePush_freeLoop_homotopic (c ρ : ℝ)
    (γ : DifferentialGeometry.Topology.freeLoop (ℝ × ℝ × ℝ)) :
    γ.Homotopic ((negativeBufferedWedgePushHomeomorph c ρ :
      C(ℝ × ℝ × ℝ, ℝ × ℝ × ℝ)).comp γ) :=
  ⟨negativeBufferedWedgeFreeLoopHomotopy c ρ γ⟩

noncomputable def positiveBufferedWedgeBasedLoop {x : ℝ × ℝ × ℝ} (c ρ : ℝ)
    (γ : DifferentialGeometry.Topology.basedCircleLoop x)
    (hx : x ∉ bufferedSlabWedgeSupport c ρ) :
    DifferentialGeometry.Topology.basedCircleLoop x := by
  refine ⟨(positiveBufferedWedgePushHomeomorph c ρ :
    C(ℝ × ℝ × ℝ, ℝ × ℝ × ℝ)).comp γ.val, ?_⟩
  change positiveBufferedWedgePush c ρ (γ.val 0) = x
  rw [γ.property, eqOn_positiveBufferedWedgePush_id_compl_support c ρ hx]
  rfl

noncomputable def negativeBufferedWedgeBasedLoop {x : ℝ × ℝ × ℝ} (c ρ : ℝ)
    (γ : DifferentialGeometry.Topology.basedCircleLoop x)
    (hx : x ∉ bufferedSlabWedgeSupport c ρ) :
    DifferentialGeometry.Topology.basedCircleLoop x := by
  refine ⟨(negativeBufferedWedgePushHomeomorph c ρ :
    C(ℝ × ℝ × ℝ, ℝ × ℝ × ℝ)).comp γ.val, ?_⟩
  change negativeBufferedWedgePush c ρ (γ.val 0) = x
  rw [γ.property, eqOn_negativeBufferedWedgePush_id_compl_support c ρ hx]
  rfl

noncomputable def positiveBufferedWedgeBasedLoopHomotopy {x : ℝ × ℝ × ℝ} (c ρ : ℝ)
    (γ : DifferentialGeometry.Topology.basedCircleLoop x)
    (hx : x ∉ bufferedSlabWedgeSupport c ρ) :
    γ.val.Homotopy (positiveBufferedWedgeBasedLoop c ρ γ hx).val :=
  positiveBufferedWedgeFreeLoopHomotopy c ρ γ.val

noncomputable def negativeBufferedWedgeBasedLoopHomotopy {x : ℝ × ℝ × ℝ} (c ρ : ℝ)
    (γ : DifferentialGeometry.Topology.basedCircleLoop x)
    (hx : x ∉ bufferedSlabWedgeSupport c ρ) :
    γ.val.Homotopy (negativeBufferedWedgeBasedLoop c ρ γ hx).val :=
  negativeBufferedWedgeFreeLoopHomotopy c ρ γ.val

theorem positiveBufferedWedgeBasedLoopHomotopy_fixed {x : ℝ × ℝ × ℝ} (c ρ : ℝ)
    (γ : DifferentialGeometry.Topology.basedCircleLoop x)
    (hx : x ∉ bufferedSlabWedgeSupport c ρ) (t : unitInterval) :
    positiveBufferedWedgeBasedLoopHomotopy c ρ γ hx (t, 0) = x := by
  change positiveBufferedWedgeHomotopy c ρ (t, γ.val 0) = x
  rw [γ.property, positiveBufferedWedgeHomotopy_eq_of_not_mem_support c ρ t hx]

theorem negativeBufferedWedgeBasedLoopHomotopy_fixed {x : ℝ × ℝ × ℝ} (c ρ : ℝ)
    (γ : DifferentialGeometry.Topology.basedCircleLoop x)
    (hx : x ∉ bufferedSlabWedgeSupport c ρ) (t : unitInterval) :
    negativeBufferedWedgeBasedLoopHomotopy c ρ γ hx (t, 0) = x := by
  change negativeBufferedWedgeHomotopy c ρ (t, γ.val 0) = x
  rw [γ.property, negativeBufferedWedgeHomotopy_eq_of_not_mem_support c ρ t hx]

end

end DifferentialGeometry.Topology.PiecewiseLinear
