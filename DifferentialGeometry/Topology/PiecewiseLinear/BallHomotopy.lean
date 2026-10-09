/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import Mathlib.Analysis.Convex.Contractible

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLBall.contractibleSpace {n : ℕ} {D : Set E} (hD : IsPLBall n D) :
    ContractibleSpace D := by
  obtain ⟨r, hr⟩ := hD
  let _ : ContractibleSpace (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1))) :=
    (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin (n + 1))).contractibleSpace
      ⟨_, Convexity.StdSimplex.single_mem_coordinateSet ℝ (0 : Fin (n + 1))⟩
  exact hr.homeomorph.symm.contractibleSpace

theorem IsPLBall.nullhomotopic_inclusion {n : ℕ} {D A S : Set E} (hD : IsPLBall n D)
    (hAD : A ⊆ D) (hDS : D ⊆ S) :
    (⟨Set.inclusion (hAD.trans hDS), continuous_inclusion _⟩ : C(A, S)).Nullhomotopic := by
  let _ := hD.contractibleSpace
  let i : C(A, D) := ⟨Set.inclusion hAD, continuous_inclusion hAD⟩
  let j : C(D, S) := ⟨Set.inclusion hDS, continuous_inclusion hDS⟩
  exact ((id_nullhomotopic D).comp_left i).comp_right j

theorem IsPLBall.nullhomotopic_inclusion_of_cylinder {n : ℕ} {D J S : Set E}
    (hD : IsPLBall n D) (hDS : D ⊆ S) (hJS : J ⊆ S) {ρ : E × ℝ → E}
    (hρ : ContinuousOn ρ (J ×ˢ Icc (0 : ℝ) 1))
    (hρS : MapsTo ρ (J ×ˢ Icc (0 : ℝ) 1) S)
    (hzero : ∀ x ∈ J, ρ (x, 0) = x) (hone : ∀ x ∈ J, ρ (x, 1) ∈ D) :
    (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic := by
  let _ := hD.contractibleSpace
  let i : C(J, S) := ⟨Set.inclusion hJS, continuous_inclusion hJS⟩
  let j : C(D, S) := ⟨Set.inclusion hDS, continuous_inclusion hDS⟩
  let g : C(J, D) :=
    ⟨fun x => ⟨ρ (x, 1), hone x x.2⟩,
      (hρ.comp_continuous (continuous_subtype_val.prodMk continuous_const)
        (fun x => ⟨x.2, zero_le_one, le_rfl⟩)).subtype_mk _⟩
  let H : ContinuousMap.Homotopy i (j.comp g) :=
    { toFun := fun p => ⟨ρ (p.2, p.1), hρS ⟨p.2.2, p.1.2⟩⟩
      continuous_toFun := (hρ.comp_continuous
        ((continuous_subtype_val.comp continuous_snd).prodMk
          (continuous_subtype_val.comp continuous_fst))
        (fun p => ⟨p.2.2, p.1.2⟩)).subtype_mk _
      map_zero_left := fun x => Subtype.ext (hzero x x.2)
      map_one_left := fun _ => rfl }
  obtain ⟨c, hc⟩ := ((id_nullhomotopic D).comp_left g).comp_right j
  exact ⟨c, (show i.Homotopic (j.comp g) from ⟨H⟩).trans hc⟩

end DifferentialGeometry.Topology.PiecewiseLinear
