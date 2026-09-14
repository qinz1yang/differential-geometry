import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassMinimalHypotheses
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassNoncompactDuality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassInputReduction
import DifferentialGeometry.Topology.FundamentalGroup.Sphere
import DifferentialGeometry.Topology.Homology.EuclideanLocalVanishing
import DifferentialGeometry.Topology.Homology.EuclideanLocalTop
import DifferentialGeometry.Topology.Homology.Homotopy
import DifferentialGeometry.Topology.Homology.SpherePuncture
import DifferentialGeometry.Topology.Homology.SphereTopHomology

noncomputable section

open CategoryTheory Module Set

universe u

namespace DifferentialGeometry.Topology

theorem injective_of_surjective_intLinearMap_int (φ : ℤ →ₗ[ℤ] ℤ)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  have hmul : ∀ m : ℤ, φ m = m * φ 1 := by
    intro m
    have h := map_zsmul φ m (1 : ℤ)
    rw [show m • (1 : ℤ) = m by simp, smul_eq_mul] at h
    exact h
  have hone : φ 1 ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := hφ 1
    rw [hmul m, h0, mul_zero] at hm
    exact one_ne_zero hm.symm
  intro a b hab
  have hzero : φ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  rw [hmul (a - b)] at hzero
  rcases mul_eq_zero.mp hzero with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hone

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem injective_subsingletonInclusion_of_subsingleton_localTopHomology_succ (n : ℕ)
    (hd : finrank ℝ E = n + 2) (M : Type u) [TopologicalSpace M] [T1Space M]
    [ChartedSpace E M] (x : M) :
    Function.Injective (integralSingularHomologyMap (n + 2)
      (singularSubspaceInclusion ({x}ᶜ : Set M))) := by
  have hloc : Subsingleton (integralLocalHomology (n + 3) x) :=
    integralManifoldLocal_subsingleton E n (n + 3) hd (by omega) M x
  intro a b hab
  have hex := LinearMap.exact_iff.mp
    (integralRelative_exact_subspace (X := M) (n + 2) ({x}ᶜ))
  have hmem : a - b ∈ LinearMap.ker (integralSingularHomologyMap (n + 2)
      (singularSubspaceInclusion ({x}ᶜ : Set M))) :=
    LinearMap.mem_ker.mpr (by rw [map_sub, hab, sub_self])
  rw [hex] at hmem
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hmem
  rw [hloc.allEq c 0, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

theorem nonempty_linearEquiv_int_of_subsingleton_compl_singleton (n : ℕ)
    (hd : finrank ℝ E = n + 2) (M : Type u) [TopologicalSpace M] [T1Space M]
    [ChartedSpace E M] (x : M)
    (hsurj : Function.Surjective (integralAbsoluteToRelative (n + 2) ({x}ᶜ : Set M)))
    (h : Subsingleton (integralSingularHomology (n + 2) ({x}ᶜ : Set M))) :
    Nonempty (integralSingularHomology (n + 2) M ≃ₗ[ℤ] ℤ) := by
  have hinj : Function.Injective (integralAbsoluteToRelative (n + 2) ({x}ᶜ : Set M)) := by
    intro a b hab
    have hex := LinearMap.exact_iff.mp
      (integralRelative_exact_absolute (X := M) (n + 2) ({x}ᶜ))
    have hmem : a - b ∈ LinearMap.ker (integralAbsoluteToRelative (n + 2) ({x}ᶜ : Set M)) :=
      LinearMap.mem_ker.mpr (by rw [map_sub, hab, sub_self])
    rw [hex] at hmem
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hmem
    rw [h.allEq c 0, map_zero] at hc
    exact sub_eq_zero.mp hc.symm
  exact ⟨(LinearEquiv.ofBijective (integralAbsoluteToRelative (n + 2) ({x}ᶜ : Set M))
    ⟨hinj, hsurj⟩).trans (integralManifoldLocalTopEquiv E n hd M x)⟩

theorem subsingleton_compl_singleton_of_nonempty_linearEquiv_int (n : ℕ)
    (hd : finrank ℝ E = n + 2) (M : Type u) [TopologicalSpace M] [T1Space M]
    [ChartedSpace E M] (x : M)
    (hsurj : Function.Surjective (integralAbsoluteToRelative (n + 2) ({x}ᶜ : Set M)))
    (he : Nonempty (integralSingularHomology (n + 2) M ≃ₗ[ℤ] ℤ)) :
    Subsingleton (integralSingularHomology (n + 2) ({x}ᶜ : Set M)) := by
  obtain ⟨e⟩ := he
  have hincl := injective_subsingletonInclusion_of_subsingleton_localTopHomology_succ
    (E := E) n hd M x
  let g := integralManifoldLocalTopEquiv E n hd M x
  let ψ : ℤ →ₗ[ℤ] ℤ := g.toLinearMap.comp
    ((integralAbsoluteToRelative (n + 2) ({x}ᶜ : Set M)).comp e.symm.toLinearMap)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨c, hc⟩ := hsurj (g.symm y)
    refine ⟨e c, ?_⟩
    rw [show ψ (e c) = g ((integralAbsoluteToRelative (n + 2) ({x}ᶜ : Set M))
      (e.symm (e c))) from rfl, LinearEquiv.symm_apply_apply, hc, LinearEquiv.apply_symm_apply]
  have hinjψ : Function.Injective ψ := injective_of_surjective_intLinearMap_int ψ hψ
  have hker : LinearMap.ker (integralAbsoluteToRelative (n + 2) ({x}ᶜ : Set M)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro a ha
    have h2 : ψ (e a) = 0 := by
      rw [show ψ (e a) = g ((integralAbsoluteToRelative (n + 2) ({x}ᶜ : Set M))
        (e.symm (e a))) from rfl, LinearEquiv.symm_apply_apply, ha, map_zero]
    have h3 : e a = 0 := hinjψ (by rw [h2, map_zero])
    exact e.injective (by rw [h3, map_zero])
  have hzero : integralSingularHomologyMap (n + 2)
      (singularSubspaceInclusion ({x}ᶜ : Set M)) = 0 := by
    have hex := LinearMap.exact_iff.mp
      (integralRelative_exact_absolute (X := M) (n + 2) ({x}ᶜ))
    exact LinearMap.range_eq_bot.mp (by rw [← hex, hker])
  exact ⟨fun a b => hincl (by simp [hzero])⟩

theorem subsingleton_compl_singleton_iff_nonempty_linearEquiv_int (n : ℕ)
    (hd : finrank ℝ E = n + 2) (M : Type u) [TopologicalSpace M] [T1Space M]
    [ChartedSpace E M] (x : M)
    (hsurj : Function.Surjective (integralAbsoluteToRelative (n + 2) ({x}ᶜ : Set M))) :
    Subsingleton (integralSingularHomology (n + 2) ({x}ᶜ : Set M)) ↔
      Nonempty (integralSingularHomology (n + 2) M ≃ₗ[ℤ] ℤ) :=
  ⟨fun h => nonempty_linearEquiv_int_of_subsingleton_compl_singleton n hd M x hsurj h,
    fun he => subsingleton_compl_singleton_of_nonempty_linearEquiv_int n hd M x hsurj he⟩

theorem nonempty_linearEquiv_int_sphereThree :
    Nonempty (integralSingularHomology 3 SphereThree ≃ₗ[ℤ] ℤ) :=
  ⟨integralSphereTopHomologyEquiv 2 (EuclideanSpace ℝ (Fin 4)) (by simp)⟩

theorem not_nonempty_linearEquiv_int_euclideanThree :
    ¬ Nonempty (integralSingularHomology 3 (EuclideanSpace ℝ (Fin 3)) ≃ₗ[ℤ] ℤ) := by
  rintro ⟨e⟩
  have hsub := integralSingularHomology_subsingleton_of_contractible 3 (by norm_num)
    (EuclideanSpace ℝ (Fin 3))
  exact zero_ne_one (e.symm.injective (hsub.allEq _ _))

theorem subsingleton_integralSingularHomology_three_compl_singleton_sphereThree
    (v : SphereThree) :
    Subsingleton (integralSingularHomology 3 ({v}ᶜ : Set SphereThree)) :=
  integralSingularHomology_subsingleton_of_punctured_sphere 3 (by norm_num) v

theorem surjective_integralAbsoluteToRelative_three_compl_singleton_sphereThree
    (v : SphereThree) :
    Function.Surjective (integralAbsoluteToRelative 3 ({v}ᶜ : Set SphereThree)) := by
  have hconn : integralRelativeConnecting 2 ({v}ᶜ : Set SphereThree) = 0 := by
    have hsub := integralSingularHomology_subsingleton_of_punctured_sphere 2 (by norm_num) v
    exact LinearMap.ext fun a => hsub.allEq _ 0
  have hex := LinearMap.exact_iff.mp (integralRelative_exact_relative (X := SphereThree) 2 ({v}ᶜ))
  exact LinearMap.range_eq_top.mp (by rw [← hex, hconn, LinearMap.ker_zero])

theorem subsingleton_integralSingularHomology_three_compl_singleton_sphereThree_iff
    (v : SphereThree) :
    Subsingleton (integralSingularHomology 3 ({v}ᶜ : Set SphereThree)) ↔
      Nonempty (integralSingularHomology 3 SphereThree ≃ₗ[ℤ] ℤ) :=
  subsingleton_compl_singleton_iff_nonempty_linearEquiv_int
    (E := EuclideanSpace ℝ (Fin 3)) 1 (by simp) SphereThree v
    (surjective_integralAbsoluteToRelative_three_compl_singleton_sphereThree v)

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology
open scoped Manifold ContDiff

theorem subsingleton_compl_singleton_three_of_infiniteCyclicTopHomology
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (x₀ : M) (hpd : noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M))
    (he : Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ)) :
    Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3) := by
  obtain ⟨e⟩ := he
  let e' : integralSingularHomology 3 M ≃ₗ[ℤ] ℤ := e
  let g' : integralRelativeHomology 3 ({x₀}ᶜ : Set M) ≃ₗ[ℤ] ℤ :=
    localIntegralHomologyEquivInt (M := M) x₀
  have hsurj : Function.Surjective (integralAbsoluteToRelative 3 ({x₀}ᶜ : Set M)) :=
    absoluteToRelative_surjective_of_noncompactPoincareDuality_punctured x₀ hpd
  let ψ : ℤ →ₗ[ℤ] ℤ := g'.toLinearMap.comp
    ((integralAbsoluteToRelative 3 ({x₀}ᶜ : Set M)).comp e'.symm.toLinearMap)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨c, hc⟩ := hsurj (g'.symm y)
    refine ⟨e' c, ?_⟩
    change g' ((integralAbsoluteToRelative 3 ({x₀}ᶜ : Set M)) (e'.symm (e' c))) = y
    rw [LinearEquiv.symm_apply_apply, hc, LinearEquiv.apply_symm_apply]
  have hinjψ : Function.Injective ψ := injective_of_surjective_intLinearMap_int ψ hψ
  have hrange : LinearMap.range (integralSingularHomologyMap 3
      (singularSubspaceInclusion ({x₀}ᶜ : Set M))) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro c hc
    have hc0 : integralAbsoluteToRelative 3 ({x₀}ᶜ : Set M) c = 0 := by
      refine LinearMap.mem_ker.mp ?_
      rw [LinearMap.exact_iff.mp (integralRelative_exact_absolute (X := M) 3 ({x₀}ᶜ))]
      exact hc
    have h2 : ψ (e' c) = 0 := by
      change g' ((integralAbsoluteToRelative 3 ({x₀}ᶜ : Set M)) (e'.symm (e' c))) = 0
      rw [LinearEquiv.symm_apply_apply, hc0, map_zero]
    have h3 : e' c = 0 := hinjψ (by rw [h2, map_zero])
    exact e'.injective (by rw [h3, map_zero])
  have hinj : Function.Injective (integralAbsoluteToRelative 3 ({x₀}ᶜ : Set M)) := by
    intro a b hab
    have hsub : a - b ∈ LinearMap.range (integralSingularHomologyMap 3
        (singularSubspaceInclusion ({x₀}ᶜ : Set M))) := by
      rw [← LinearMap.exact_iff.mp (integralRelative_exact_absolute (X := M) 3 ({x₀}ᶜ))]
      exact LinearMap.mem_ker.mpr (by rw [map_sub, hab, sub_self])
    rw [hrange, Submodule.mem_bot] at hsub
    exact sub_eq_zero.mp hsub
  exact (subsingleton_integralHomology_compl_singleton_three_iff_injective_absoluteToRelative
    x₀).mpr hinj

theorem nonempty_integralHomology_linearEquiv_int_of_punctured_subsingleton
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (x₀ : M) (h₃ : Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3))
    (hsurj : Function.Surjective (absoluteToRelative M ({x₀}ᶜ) 3)) :
    Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ) :=
  ⟨(LinearEquiv.ofBijective ((absoluteToRelative M ({x₀}ᶜ) 3).hom)
      ⟨absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ h₃, hsurj⟩).trans
    (localIntegralHomologyEquivInt (M := M) x₀)⟩

theorem nonempty_integralHomology_linearEquiv_int_of_noncompactThreeManifoldTopHomologyVanishing
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [ConnectedSpace M] [T2Space M] (x₀ : M)
    (hv : noncompactThreeManifoldTopHomologyVanishing.{u})
    (hsurj : Function.Surjective (absoluteToRelative M ({x₀}ᶜ) 3)) :
    Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ) :=
  nonempty_integralHomology_linearEquiv_int_of_punctured_subsingleton x₀
    (subsingleton_integralHomology_compl_singleton_of_noncompactThreeManifoldTopHomologyVanishing
      hv x₀) hsurj

theorem exists_unique_fundamentalClass_of_noncompactPoincareDuality_of_infiniteCyclicTopHomology
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (o : TangentOrientationSection M) (x₀ : M) (htransport : localClassTransport o)
    (hpd : noncompactPoincareDualityTwoOne ({x₀}ᶜ : Set M))
    (he : Nonempty (IntegralHomology M 3 ≃ₗ[ℤ] ℤ)) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x :=
  exists_unique_fundamentalClass_of_puncturedVanishing_through_connecting (x := x₀) (o := o)
    ⟨subsingleton_integralHomology_compl_singleton_two_of_noncompactPoincareDuality_of_simplyConnected
        x₀ hpd,
      subsingleton_compl_singleton_three_of_infiniteCyclicTopHomology x₀ hpd he⟩
    htransport

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
