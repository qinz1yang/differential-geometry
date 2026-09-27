/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Torus
import DifferentialGeometry.Topology.Homotopy.FreeLoopNullhomotopy
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.LoopSpace.BasedNaturality
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorus
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_ne_one_map_eq_one_of_multiplicative_intProd
    (f : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ) :
    ∃ k, k ≠ 1 ∧ f k = 1 := by
  let u : Multiplicative ℤ × Multiplicative ℤ := (Multiplicative.ofAdd 1, 1)
  let w : Multiplicative ℤ × Multiplicative ℤ := (1, Multiplicative.ofAdd 1)
  obtain ⟨a, ha⟩ : ∃ a : ℤ, f u = Multiplicative.ofAdd a := ⟨Multiplicative.toAdd (f u), rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, f w = Multiplicative.ofAdd b := ⟨Multiplicative.toAdd (f w), rfl⟩
  by_cases hab : a = 0 ∧ b = 0
  · refine ⟨u, fun h => ?_, ?_⟩
    · have h1 := congrArg (fun z => Multiplicative.toAdd z.1) h
      simp [u] at h1
    · rw [ha, hab.1]
      rfl
  · refine ⟨u ^ b * w ^ (-a), fun h => hab ?_, ?_⟩
    · have h1 : b = 0 := by simpa [u, w] using congrArg (fun z => Multiplicative.toAdd z.1) h
      have h2 : a = 0 := by simpa [u, w] using congrArg (fun z => Multiplicative.toAdd z.2) h
      exact ⟨h2, h1⟩
    · rw [map_mul, map_zpow, map_zpow, ha, hb]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_zpow, toAdd_ofAdd, toAdd_one, smul_eq_mul]
      ring

theorem mem_interior_of_homeomorph_closedBall_prod_sphere
    {S : Set (EuclideanSpace ℝ (Fin 3))}
    (φ : S ≃ₜ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
    (v : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hv : ‖(v : EuclideanSpace ℝ (Fin 2))‖ < 1) :
    (φ.symm (v, θ) : EuclideanSpace ℝ (Fin 3)) ∈ interior S := by
  let B : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 2)) :=
    ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
  let H := EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)
  let M := B × Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let e : H ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [H, Module.finrank_prod])
  let _ : ChartedSpace H M := inferInstanceAs
    (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1))) M)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) H := e.symm.toHomeomorph.chartedSpace
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M :=
    ChartedSpace.comp (EuclideanSpace ℝ (Fin 3)) H M
  let f : M → EuclideanSpace ℝ (Fin 3) := fun z =>
    φ.symm (⟨z.1, Metric.ball_subset_closedBall z.1.2⟩, z.2)
  have hf : Continuous f :=
    continuous_subtype_val.comp (φ.symm.continuous.comp
      (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd))
  have hfi : Function.Injective f := by
    rintro ⟨a, α⟩ ⟨b, β⟩ hab
    have h := φ.symm.injective (Subtype.ext hab)
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) h.2
  have hopen : IsOpen (range f) := by
    rw [← image_univ]
    exact isOpenMap_of_continuous_injective (E := EuclideanSpace ℝ (Fin 3)) hf hfi univ
      isOpen_univ
  have hvB : (v : EuclideanSpace ℝ (Fin 2)) ∈ B := mem_ball_zero_iff.mpr hv
  refine interior_maximal ?_ hopen ⟨(⟨v, hvB⟩, θ), rfl⟩
  rintro _ ⟨z, rfl⟩
  exact (φ.symm _).2

theorem IsPLTorus.exists_nontrivial_fundamentalGroup_kernel_in_solidTorus
    {T S : Set (EuclideanSpace ℝ (Fin 3))} (hT : IsPLTorus T)
    (hS : IsTopologicalSolidTorus S) (hTS : T ⊆ interior S) :
    ∃ (x : T) (g : FundamentalGroup T x), g ≠ 1 ∧
      FundamentalGroup.map (⟨Set.inclusion hTS, continuous_inclusion hTS⟩ :
        C(T, interior S)) x g = 1 := by
  obtain ⟨-, ⟨ψ⟩⟩ := hT
  obtain ⟨φ⟩ := hS
  let i : C(T, interior S) := ⟨Set.inclusion hTS, continuous_inclusion hTS⟩
  have hTS' : T ⊆ S := hTS.trans interior_subset
  let s : C(T, S) := ⟨Set.inclusion hTS', continuous_inclusion hTS'⟩
  let q : C(T, Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    ⟨fun x => (φ (s x)).2, continuous_snd.comp (φ.continuous.comp s.continuous)⟩
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    Metric.mem_closedBall_self zero_le_one
  let j : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, interior S) :=
    ⟨fun θ => ⟨φ.symm (⟨0, h0⟩, θ),
      mem_interior_of_homeomorph_closedBall_prod_sphere φ _ θ (by simp)⟩,
      (continuous_subtype_val.comp (φ.symm.continuous.comp
        (continuous_const.prodMk continuous_id))).subtype_mk _⟩
  have hball (t : unitInterval) (x : T) :
      (1 - (t : ℝ)) • ((φ (s x)).1 : EuclideanSpace ℝ (Fin 2)) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    have h1 := mem_closedBall_zero_iff.mp (φ (s x)).1.2
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr t.2.2)]
    nlinarith [t.2.1, t.2.2, norm_nonneg ((φ (s x)).1 : EuclideanSpace ℝ (Fin 2))]
  have hint (t : unitInterval) (x : T) :
      (φ.symm (⟨_, hball t x⟩, (φ (s x)).2) : EuclideanSpace ℝ (Fin 3)) ∈ interior S := by
    rcases eq_or_lt_of_le t.2.1 with ht | ht
    · have hv : (⟨(1 - (t : ℝ)) • ((φ (s x)).1 : EuclideanSpace ℝ (Fin 2)), hball t x⟩ :
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) = (φ (s x)).1 :=
        Subtype.ext (by simp [← ht])
      rw [hv, Prod.mk.eta, φ.symm_apply_apply]
      exact hTS x.2
    · apply mem_interior_of_homeomorph_closedBall_prod_sphere
      have h1 := mem_closedBall_zero_iff.mp (φ (s x)).1.2
      rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr t.2.2)]
      nlinarith [mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr h1)]
  let F : ContinuousMap.Homotopy i (j.comp q) :=
    { toFun := fun p => ⟨φ.symm (⟨_, hball p.1 p.2⟩, (φ (s p.2)).2), hint p.1 p.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk (continuous_subtype_val.comp (φ.symm.continuous.comp
          (Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_))) _
        · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
            (continuous_subtype_val.comp (continuous_fst.comp
              (φ.continuous.comp (s.continuous.comp continuous_snd))))
        · exact continuous_snd.comp (φ.continuous.comp (s.continuous.comp continuous_snd))
      map_zero_left := fun x => by
        apply Subtype.ext
        have hv : (⟨(1 - ((0 : unitInterval) : ℝ)) • ((φ (s x)).1 : EuclideanSpace ℝ (Fin 2)),
            hball 0 x⟩ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) = (φ (s x)).1 :=
          Subtype.ext (by simp)
        change (φ.symm (⟨_, hball 0 x⟩, (φ (s x)).2) : EuclideanSpace ℝ (Fin 3)) = x
        rw [hv, Prod.mk.eta, φ.symm_apply_apply]
        rfl
      map_one_left := fun x => by
        apply Subtype.ext
        have hv : (⟨(1 - ((1 : unitInterval) : ℝ)) • ((φ (s x)).1 : EuclideanSpace ℝ (Fin 2)),
            hball 1 x⟩ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) = ⟨0, h0⟩ :=
          Subtype.ext (by simp)
        change (φ.symm (⟨_, hball 1 x⟩, (φ (s x)).2) : EuclideanSpace ℝ (Fin 3)) =
          φ.symm (⟨0, h0⟩, (φ (s x)).2)
        rw [hv] }
  obtain ⟨c, hc⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let c' : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := ⟨c, hc⟩
  let x : T := ψ.symm (c', c')
  let eT : FundamentalGroup T x ≃* Multiplicative ℤ × Multiplicative ℤ :=
    (fundamentalGroupMulEquivOfHomotopyEquiv ψ.toHomotopyEquiv x (ψ x) rfl).trans
      (fundamentalGroupTorusEquivIntProd (ψ x))
  let eCirc : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
    (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
      change z ∈ Metric.sphere (0 : ℂ) 1 ↔
        Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
        Complex.orthonormalBasisOneI.repr.norm_map]).symm
  let eC : FundamentalGroup (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (q x) ≃*
      Multiplicative ℤ :=
    (fundamentalGroupMulEquivOfHomotopyEquiv eCirc.toHomotopyEquiv (q x) (eCirc (q x)) rfl).trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (eCirc (q x)) 1).trans
        fundamentalGroupCircleEquivInt)
  obtain ⟨k, hk, hfk⟩ := exists_ne_one_map_eq_one_of_multiplicative_intProd
    ((eC.toMonoidHom.comp (FundamentalGroup.map q x)).comp eT.symm.toMonoidHom)
  refine ⟨x, eT.symm k, fun h => hk (by rw [← eT.apply_symm_apply k, h, map_one]), ?_⟩
  have hq : FundamentalGroup.map q x (eT.symm k) = 1 := by
    apply eC.injective
    rw [map_one]
    simpa using hfk
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective (eT.symm k)
  rw [← hp] at hq ⊢
  apply Path.Homotopic.Quotient.eq.mpr
  apply (pathToCircle_nullhomotopic_iff (p.map i.continuous)).mp
  rw [pathToCircle_natural]
  have hqnull : (q.comp (pathToCircle p)).Nullhomotopic := by
    rw [← pathToCircle_natural]
    exact (pathToCircle_nullhomotopic_iff (p.map q.continuous)).mpr
      (Path.Homotopic.Quotient.eq.mp hq)
  obtain ⟨y, hy⟩ := hqnull.comp_right j
  exact ⟨y, (ContinuousMap.Homotopic.comp ⟨F⟩
    (ContinuousMap.Homotopic.refl (pathToCircle p))).trans hy⟩

end DifferentialGeometry.Topology.PiecewiseLinear
