/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimTransfer
import DifferentialGeometry.Topology.Homotopy.ConvexProduct

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsLocallyFiniteRegularNeighborhoodOf.carriesFundamentalGroupOnto
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {N J U : Set X}
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := n) N J U) :
    CarriesFundamentalGroupOnto J N := by
  have hJN : J ⊆ N := subset_interior_iff_mem_nhdsSet.mpr hN.mem_nhdsSet |>.trans
    interior_subset
  let r := hN.strongDeformationRetract
  let e : J ≃ₜ {x : N | (x : X) ∈ J} :=
    { toFun := fun x => ⟨⟨x, hJN x.2⟩, x.2⟩
      invFun := fun x => ⟨x.1.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let H : N ≃ₕ J := r.toHomotopyEquiv.trans e.symm.toHomotopyEquiv
  refine ⟨hJN, fun hsub b => ?_⟩
  apply (bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse H
    (⟨inclusion hsub, continuous_inclusion hsub⟩ : C(J, N)) ?_ b).2
  intro x
  apply Subtype.ext
  change ((r.retraction (inclusion hsub x) : N) : X) = (x : X)
  exact congrArg Subtype.val (r.retraction_eq (x := inclusion hsub x) x.2)

private theorem annulus_level_carries_of_core
    {X : Type*} [TopologicalSpace X] {A J T : Set X}
    (φ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1) ≃ₜ A)
    (hJT : CarriesFundamentalGroupOnto J T) (hJ : J.Nonempty)
    (hJA : J ⊆ A) (hAT : A ⊆ T) (t : Icc (0 : ℝ) 1) :
    CarriesFundamentalGroupOnto (range fun x => ((φ (x, t) : A) : X)) T := by
  let C := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank']
    norm_num
  have : PathConnectedSpace C := isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere hrank 0 zero_le_one)
  have : PathConnectedSpace (Icc (0 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩)
  have : PathConnectedSpace A := φ.surjective.pathConnectedSpace φ.continuous
  let a : C(J, A) := ⟨inclusion hJA, continuous_inclusion hJA⟩
  let f : C(A, T) := ⟨inclusion hAT, continuous_inclusion hAT⟩
  let g : C(C, A) := ⟨fun x => φ (x, t),
    φ.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let H : A ≃ₕ C := φ.symm.toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex C (convex_Icc 0 1) t)
  have hleft : Function.LeftInverse H g := fun x => congrArg Prod.fst (φ.symm_apply_apply _)
  obtain ⟨j, hj⟩ := hJ
  have hfa : Function.Surjective (FundamentalGroup.map (f.comp a) ⟨j, hj⟩) :=
    hJT.2 (hJA.trans hAT) ⟨j, hj⟩
  let E := range fun x => ((φ (x, t) : A) : X)
  have hET : E ⊆ T := by
    rintro x ⟨y, rfl⟩
    exact hAT (φ (y, t)).2
  let k : C(C, E) := ⟨fun x => ⟨φ (x, t), x, rfl⟩,
    (continuous_subtype_val.comp g.continuous).subtype_mk _⟩
  refine ⟨hET, ?_⟩
  rintro hsub ⟨b, y, rfl⟩ γ
  have hg := (bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse H g hleft y).2
  obtain ⟨ℓ, hℓ⟩ := surjective_fundamentalGroup_map_comp_of_surjective_comp
    a g f ⟨j, hj⟩ y hfa hg γ
  refine ⟨FundamentalGroup.map k y ℓ, ?_⟩
  rw [← hℓ]
  exact (DFunLike.congr_fun (fundamentalGroup_map_continuousMap_comp k
    (⟨inclusion hsub, continuous_inclusion hsub⟩ : C(E, T)) y) ℓ).symm

theorem IsAnnulusOn.boundaries_carry_of_core
    {X : Type*} [TopologicalSpace X] {A A₀ A₁ J T : Set X}
    (hann : IsAnnulusOn A A₀ A₁) (hJT : CarriesFundamentalGroupOnto J T)
    (hJ : J.Nonempty) (hJA : J ⊆ A) (hAT : A ⊆ T) :
    CarriesFundamentalGroupOnto A₀ T ∧ CarriesFundamentalGroupOnto A₁ T := by
  obtain ⟨φ, h₀, h₁⟩ := hann
  have heq (t : Icc (0 : ℝ) 1) :
      Subtype.val '' (φ '' {p | (p.2 : ℝ) = t}) =
        range (fun x => ((φ (x, t) : A) : X)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      have ht : p.2 = t := Subtype.ext hp
      exact ⟨p.1, by rw [← ht]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨φ (y, t), ⟨(y, t), rfl, rfl⟩, rfl⟩
  rw [h₀, h₁, heq ⟨0, by norm_num⟩, heq ⟨1, by norm_num⟩]
  exact ⟨annulus_level_carries_of_core φ hJT hJ hJA hAT _,
    annulus_level_carries_of_core φ hJT hJ hJA hAT _⟩

end DifferentialGeometry.Topology.PiecewiseLinear
