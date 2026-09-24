import DifferentialGeometry.Topology.LevelSet.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Topology.LevelSet.Regular
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import DifferentialGeometry.Topology.LevelSet.Disk.StrictLevels
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic

section

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem isPreconnected_regular_level_on_ball_of_strict_levels
    {R : ℝ} (hR : 0 < R) {f : Plane → ℝ} (c : ℝ)
    (hf : ContinuousOn f (ball (0 : Plane) R))
    (hreg : ∀ p ∈ ball (0 : Plane) R, f p = c → ContDiffAt ℝ 1 f p)
    (hdf : ∀ p ∈ ball (0 : Plane) R, f p = c → fderiv ℝ f p ≠ 0)
    (hp : IsPreconnected (ball (0 : Plane) R ∩ {x | c < f x}))
    (hn : IsPreconnected (ball (0 : Plane) R ∩ {x | f x < c})) :
    IsPreconnected (ball (0 : Plane) R ∩ {x | f x = c}) := by
  let D := ball (0 : Plane) R
  let : LocallyPathConnectedSpace D := (convex_ball (0 : Plane) R).locallyPathConnectedSpace
  let : ContractibleSpace D := (convex_ball (0 : Plane) R).contractibleSpace
    ⟨0, mem_ball_self hR⟩
  let F : D → ℝ := fun x => f x
  have hF : Continuous F := hf.domRestrict
  have himage (S : Set Plane) : Subtype.val '' (Subtype.val ⁻¹' S : Set D) = D ∩ S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxD, hxS⟩
      exact ⟨⟨x, hxD⟩, hxS, rfl⟩
  have hp' : IsPreconnected {x : D | c < F x} := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    change IsPreconnected (Subtype.val '' (Subtype.val ⁻¹' {x | c < f x} : Set D))
    rw [himage]
    exact hp
  have hn' : IsPreconnected {x : D | F x < c} := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    change IsPreconnected (Subtype.val '' (Subtype.val ⁻¹' {x | f x < c} : Set D))
    rw [himage]
    exact hn
  have hclosure : {x : D | F x = c} ⊆ closure {x | c < F x} ∩ closure {x | F x < c} := by
    intro x hx
    have hfx : f x = c := hx
    obtain ⟨hplus, hminus⟩ :=
      DifferentialGeometry.Analysis.mem_closure_strict_levels_of_fderiv_ne_zero
      (by simp : Module.finrank ℝ Plane = 2) (hreg x x.property hx) (hdf x x.property hx)
      isOpen_ball x.property
    have hpcl : (x : Plane) ∈ closure (D ∩ {y | c < f y}) := by
      change (x : Plane) ∈ closure {y | y ∈ ball (0 : Plane) R ∧ c < f y}
      simpa only [hfx] using hplus
    have hncl : (x : Plane) ∈ closure (D ∩ {y | f y < c}) := by
      change (x : Plane) ∈ closure {y | y ∈ ball (0 : Plane) R ∧ f y < c}
      simpa only [hfx] using hminus
    constructor
    · rw [_root_.Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
      change (x : Plane) ∈ closure (Subtype.val '' {y : D | c < F y})
      have heq : Subtype.val '' {y : D | c < F y} = D ∩ {y | c < f y} := by
        exact himage {y | c < f y}
      rwa [heq]
    · rw [_root_.Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
      change (x : Plane) ∈ closure (Subtype.val '' {y : D | F y < c})
      have heq : Subtype.val '' {y : D | F y < c} = D ∩ {y | f y < c} := by
        exact himage {y | f y < c}
      rwa [heq]
  have hlevel := Continuous.isPreconnected_level_of_sign_connectedness hF c hp' hn' hclosure
  have heq : Subtype.val '' {x : D | F x = c} = D ∩ {x | f x = c} := by
    exact himage {y | f y = c}
  rw [← heq]
  exact hlevel.image Subtype.val continuous_subtype_val.continuousOn

theorem joinedIn_regular_level_on_ball_of_strict_levels
    {R : ℝ} (hR : 0 < R) {f : Plane → ℝ} (c : ℝ)
    (hf : ContinuousOn f (ball (0 : Plane) R))
    (hreg : ∀ p ∈ ball (0 : Plane) R, f p = c → ContDiffAt ℝ 1 f p)
    (hdf : ∀ p ∈ ball (0 : Plane) R, f p = c → fderiv ℝ f p ≠ 0)
    (hp : IsPreconnected (ball (0 : Plane) R ∩ {x | c < f x}))
    (hn : IsPreconnected (ball (0 : Plane) R ∩ {x | f x < c}))
    {x y : Plane} (hx : x ∈ ball (0 : Plane) R ∩ {x | f x = c})
    (hy : y ∈ ball (0 : Plane) R ∩ {x | f x = c}) :
    JoinedIn (ball (0 : Plane) R ∩ {x | f x = c}) x y := by
  let S := ball (0 : Plane) R ∩ {x | f x = c}
  have hS : IsPreconnected S :=
    isPreconnected_regular_level_on_ball_of_strict_levels hR c hf hreg hdf hp hn
  let : LocallyPathConnectedSpace S :=
    DifferentialGeometry.Analysis.locallyPathConnectedSpace_level_of_fderiv_ne_zero
      (by simp : Module.finrank ℝ Plane = 2) isOpen_ball c hreg hdf
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp ⟨⟨x, hx⟩, hS⟩
  let : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
  have hpS : IsPathConnected S := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  exact hpS.joinedIn x hx y hy

end DifferentialGeometry.Topology

end

end

section

set_option autoImplicit false
noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem sphere_inter_coordinate_level_eq_pair {R c : ℝ} (hR : 0 ≤ R) (hc : |c| ≤ R) :
    sphere (0 : Plane) R ∩ {x | x 0 = c} =
      {(!₂[c, Real.sqrt (R ^ 2 - c ^ 2)] : Plane), !₂[c, -Real.sqrt (R ^ 2 - c ^ 2)]} := by
  have hnon : 0 ≤ R ^ 2 - c ^ 2 := by
    have hsq := pow_le_pow_left₀ (abs_nonneg c) hc 2
    rw [sq_abs] at hsq
    linarith
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    change x 0 = c at hxc
    have hnorm : ‖x‖ = R := mem_sphere_zero_iff_norm.mp hx
    have hsq : x 0 ^ 2 + x 1 ^ 2 = R ^ 2 := by
      have h := EuclideanSpace.real_norm_sq_eq x
      simpa only [Fin.sum_univ_two, hnorm] using h.symm
    have hsqrt : Real.sqrt (R ^ 2 - c ^ 2) = |x 1| := by
      rw [show R ^ 2 - c ^ 2 = x 1 ^ 2 by rw [hxc] at hsq; linarith,
        Real.sqrt_sq_eq_abs]
    by_cases h1 : 0 ≤ x 1
    · left
      ext i
      fin_cases i <;> simp [hxc, hsqrt, abs_of_nonneg h1]
    · right
      apply mem_singleton_iff.mpr
      ext i
      fin_cases i <;> simp [hxc, hsqrt, abs_of_neg (lt_of_not_ge h1)]
  · rintro (rfl | hx)
    · constructor
      · rw [mem_sphere_zero_iff_norm]
        apply (sq_eq_sq₀ (norm_nonneg _) hR).mp
        simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Real.sq_sqrt hnon]
      · simp
    · rw [mem_singleton_iff] at hx
      subst x
      constructor
      · rw [mem_sphere_zero_iff_norm]
        apply (sq_eq_sq₀ (norm_nonneg _) hR).mp
        simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Real.sq_sqrt hnon]
      · simp

theorem sphere_inter_level_eq_pair_of_boundary_coordinate
    {R : ℝ} (hR : 0 ≤ R) {f : Plane → ℝ}
    (hboundary : ∀ x ∈ sphere (0 : Plane) R, f x = x 0) {c : ℝ} (hc : |c| ≤ R) :
    sphere (0 : Plane) R ∩ {x | f x = c} =
      {(!₂[c, Real.sqrt (R ^ 2 - c ^ 2)] : Plane), !₂[c, -Real.sqrt (R ^ 2 - c ^ 2)]} := by
  rw [← sphere_inter_coordinate_level_eq_pair hR hc]
  ext x
  constructor
  · rintro ⟨hx, hf⟩
    exact ⟨hx, (hboundary x hx).symm.trans hf⟩
  · rintro ⟨hx, hf⟩
    exact ⟨hx, (hboundary x hx).trans hf⟩

theorem exists_mem_ball_level_of_boundary_coordinate
    {R c : ℝ} (hc : -R < c ∧ c < R) {f : Plane → ℝ}
    (hf : ContinuousOn f (closedBall (0 : Plane) R))
    (hboundary : ∀ x ∈ sphere (0 : Plane) R, f x = x 0) :
    ∃ x ∈ ball (0 : Plane) R, f x = c := by
  have hR : 0 < R := by linarith [hc.1, hc.2]
  let γ : ℝ → Plane := fun t => !₂[t, 0]
  have hγ : Continuous γ := by fun_prop
  have hγnorm (t : ℝ) : ‖γ t‖ = |t| := by
    have heq : γ t = EuclideanSpace.single 0 t := by ext i; fin_cases i <;> simp [γ]
    rw [heq, PiLp.norm_single, Real.norm_eq_abs]
  have hmap : MapsTo γ (Icc (-R) R) (closedBall (0 : Plane) R) := by
    intro t ht
    rw [mem_closedBall_zero_iff, hγnorm]
    exact abs_le.mpr ht
  have hfc : ContinuousOn (f ∘ γ) (Icc (-R) R) := hf.comp hγ.continuousOn hmap
  have hends (t : ℝ) (ht : |t| = R) : f (γ t) = t := by
    have hs : γ t ∈ sphere (0 : Plane) R := by rw [mem_sphere_zero_iff_norm, hγnorm, ht]
    simpa only [γ, PiLp.toLp_apply, Matrix.cons_val_zero] using hboundary (γ t) hs
  have hl : f (γ (-R)) = -R := hends _ (by rw [abs_neg, abs_of_pos hR])
  have hr : f (γ R) = R := hends _ (abs_of_pos hR)
  obtain ⟨t, ht, htc⟩ := intermediate_value_Icc (by linarith : -R ≤ R) hfc
    (show c ∈ Icc ((f ∘ γ) (-R)) ((f ∘ γ) R) by
      simpa only [Function.comp_apply, hl, hr, mem_Icc] using And.intro hc.1.le hc.2.le)
  have htL : -R < t := lt_of_le_of_ne ht.1 (by
    intro heq
    have h := htc
    rw [heq.symm, Function.comp_apply, hl] at h
    linarith [hc.1])
  have htR : t < R := lt_of_le_of_ne ht.2 (by
    intro heq
    have h := htc
    rw [heq, Function.comp_apply, hr] at h
    linarith [hc.2])
  exact ⟨γ t, mem_ball_zero_iff.mpr (hγnorm t ▸ abs_lt.mpr ⟨htL, htR⟩), htc⟩

end DifferentialGeometry.Topology

end

end

section

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem isConnected_regular_level_on_ball_of_maximum_minimum_principle
    {R : ℝ} (hR : 0 < R) {f : Plane → ℝ}
    (hf : ContinuousOn f (closedBall (0 : Plane) R))
    (hboundary : ∀ x ∈ sphere (0 : Plane) R, f x = x 0)
    (hreg : ContDiffOn ℝ 1 f (ball (0 : Plane) R))
    (hdf : ∀ p ∈ ball (0 : Plane) R, fderiv ℝ f p ≠ 0)
    (hmax : ∀ Ω : Set (closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, f x ≤ c) → ∀ x ∈ Ω, f x ≤ c)
    (hmin : ∀ Ω : Set (closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, c ≤ f x) → ∀ x ∈ Ω, c ≤ f x)
    {c : ℝ} (hc : -R < c ∧ c < R) :
    IsConnected (ball (0 : Plane) R ∩ {x | f x = c}) := by
  obtain ⟨x, hx, hfx⟩ := exists_mem_ball_level_of_boundary_coordinate hc hf hboundary
  exact ⟨⟨x, hx, hfx⟩, isPreconnected_regular_level_on_ball_of_strict_levels hR c
    (hf.mono ball_subset_closedBall) (fun p hp _ => hreg.contDiffAt (isOpen_ball.mem_nhds hp))
    (fun p hp _ => hdf p hp)
    (isPreconnected_ball_superlevel_of_maximum_principle hR hf hboundary hmax c)
    (isPreconnected_ball_sublevel_of_minimum_principle hR hf hboundary hmin c)⟩

theorem isPathConnected_regular_level_on_ball_of_maximum_minimum_principle
    {R : ℝ} (hR : 0 < R) {f : Plane → ℝ}
    (hf : ContinuousOn f (closedBall (0 : Plane) R))
    (hboundary : ∀ x ∈ sphere (0 : Plane) R, f x = x 0)
    (hreg : ContDiffOn ℝ 1 f (ball (0 : Plane) R))
    (hdf : ∀ p ∈ ball (0 : Plane) R, fderiv ℝ f p ≠ 0)
    (hmax : ∀ Ω : Set (closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, f x ≤ c) → ∀ x ∈ Ω, f x ≤ c)
    (hmin : ∀ Ω : Set (closedBall (0 : Plane) R), IsOpen Ω → IsCompact (closure Ω) →
      Ω ⊆ {x | ‖(x : Plane)‖ = R}ᶜ → ∀ c : ℝ,
        (∀ x ∈ frontier Ω, c ≤ f x) → ∀ x ∈ Ω, c ≤ f x)
    {c : ℝ} (hc : -R < c ∧ c < R) :
    IsPathConnected (ball (0 : Plane) R ∩ {x | f x = c}) := by
  have hconn := isConnected_regular_level_on_ball_of_maximum_minimum_principle
    hR hf hboundary hreg hdf hmax hmin hc
  let S := ball (0 : Plane) R ∩ {x | f x = c}
  let : LocallyPathConnectedSpace S :=
    DifferentialGeometry.Analysis.locallyPathConnectedSpace_level_of_fderiv_ne_zero
      (by simp : Module.finrank ℝ Plane = 2) isOpen_ball c
      (fun p hp _ => hreg.contDiffAt (isOpen_ball.mem_nhds hp)) (fun p hp _ => hdf p hp)
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hconn
  let : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

end DifferentialGeometry.Topology

end

end

section

set_option autoImplicit false
noncomputable section

open Set Metric Filter
open scoped Topology

namespace DifferentialGeometry.Topology

theorem le_of_le_frontier_of_no_localMax
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} {Ω : Set X}
    (hf : ContinuousOn f (closure Ω)) (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (hmax : ∀ x ∈ Ω, ¬ IsLocalMax f x) {a : ℝ}
    (hbd : ∀ x ∈ frontier Ω, f x ≤ a) : ∀ x ∈ Ω, f x ≤ a := by
  intro x hx
  by_contra hxa
  have hax : a < f x := lt_of_not_ge hxa
  obtain ⟨p, hp, hpmax⟩ := hc.exists_isMaxOn ⟨x, subset_closure hx⟩ hf
  have hxp : f x ≤ f p := hpmax (subset_closure hx)
  have hpΩ : p ∈ Ω := by
    by_contra hpnot
    have hpfr : p ∈ frontier Ω := ⟨hp, by simpa only [hΩ.interior_eq] using hpnot⟩
    exact (not_le_of_gt (hax.trans_le hxp)) (hbd p hpfr)
  exact hmax p hpΩ (hpmax.isLocalMax (mem_of_superset (hΩ.mem_nhds hpΩ) subset_closure))

theorem le_of_frontier_le_of_no_localMin
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} {Ω : Set X}
    (hf : ContinuousOn f (closure Ω)) (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (hmin : ∀ x ∈ Ω, ¬ IsLocalMin f x) {a : ℝ}
    (hbd : ∀ x ∈ frontier Ω, a ≤ f x) : ∀ x ∈ Ω, a ≤ f x := by
  have h := le_of_le_frontier_of_no_localMax hf.neg hΩ hc
    (fun x hx hmax => hmin x hx (by simpa only [Pi.neg_apply, neg_neg] using hmax.neg))
    (fun x hx => neg_le_neg (hbd x hx))
  intro x hx
  exact neg_le_neg_iff.mp (h x hx)

theorem fderiv_eq_zero_of_localMax_restrict_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {R : ℝ} {p : closedBall (0 : E) R}
    (hp : (p : E) ∈ ball (0 : E) R)
    (hmax : IsLocalMax (fun x : closedBall (0 : E) R => f x) p) : fderiv ℝ f p = 0 := by
  have hlocal : IsLocalMax f (p : E) := by
    have hmap : Filter.map (Subtype.val : closedBall (0 : E) R → E) (𝓝 p) = 𝓝 (p : E) := by
      rw [map_nhds_subtype_val, nhdsWithin_eq_nhds]
      exact mem_of_superset (isOpen_ball.mem_nhds hp) ball_subset_closedBall
    change ∀ᶠ x in 𝓝 (p : E), f x ≤ f p
    rw [← hmap]
    exact hmax
  exact hlocal.fderiv_eq_zero

theorem maximum_principle_closedBall_of_fderiv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {R : ℝ} (hf : ContinuousOn f (closedBall (0 : E) R))
    (hdf : ∀ p ∈ ball (0 : E) R, fderiv ℝ f p ≠ 0)
    {Ω : Set (closedBall (0 : E) R)} (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (hsub : Ω ⊆ {x | ‖(x : E)‖ = R}ᶜ) {a : ℝ}
    (hbd : ∀ x ∈ frontier Ω, f x ≤ a) : ∀ x ∈ Ω, f x ≤ a := by
  have hfc : Continuous (fun x : closedBall (0 : E) R => f x) := hf.domRestrict
  apply le_of_le_frontier_of_no_localMax hfc.continuousOn hΩ hc _ hbd
  intro p hp hmax
  have hpball : (p : E) ∈ ball (0 : E) R := mem_ball_zero_iff.mpr
    (lt_of_le_of_ne (mem_closedBall_zero_iff.mp p.property) (hsub hp))
  exact hdf p hpball (fderiv_eq_zero_of_localMax_restrict_closedBall hpball hmax)

theorem minimum_principle_closedBall_of_fderiv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {R : ℝ} (hf : ContinuousOn f (closedBall (0 : E) R))
    (hdf : ∀ p ∈ ball (0 : E) R, fderiv ℝ f p ≠ 0)
    {Ω : Set (closedBall (0 : E) R)} (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (hsub : Ω ⊆ {x | ‖(x : E)‖ = R}ᶜ) {a : ℝ}
    (hbd : ∀ x ∈ frontier Ω, a ≤ f x) : ∀ x ∈ Ω, a ≤ f x := by
  have hdfneg : ∀ p ∈ ball (0 : E) R, fderiv ℝ (fun x => -f x) p ≠ 0 := by
    intro p hp
    change fderiv ℝ (-f) p ≠ 0
    rw [fderiv_neg]
    exact neg_ne_zero.mpr (hdf p hp)
  have h := maximum_principle_closedBall_of_fderiv_ne_zero hf.neg hdfneg hΩ hc hsub
    (a := -a) (fun x hx => neg_le_neg (hbd x hx))
  intro x hx
  exact neg_le_neg_iff.mp (h x hx)

end DifferentialGeometry.Topology

end

end

section

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ContDiff

namespace DifferentialGeometry.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem isPathConnected_level_of_noncritical_disk_coordinate
    {R : ℝ} (hR : 0 < R) {f : Plane → ℝ}
    (hf : ContinuousOn f (closedBall (0 : Plane) R))
    (hboundary : ∀ x ∈ sphere (0 : Plane) R, f x = x 0)
    (hreg : ContDiffOn ℝ 1 f (ball (0 : Plane) R))
    (hdf : ∀ p ∈ ball (0 : Plane) R, fderiv ℝ f p ≠ 0)
    {c : ℝ} (hc : -R < c ∧ c < R) :
    IsPathConnected (ball (0 : Plane) R ∩ {x | f x = c}) := by
  exact isPathConnected_regular_level_on_ball_of_maximum_minimum_principle hR hf hboundary hreg hdf
    (fun Ω hΩ hcompact hsub a hbd => maximum_principle_closedBall_of_fderiv_ne_zero
      hf hdf hΩ hcompact hsub hbd)
    (fun Ω hΩ hcompact hsub a hbd => minimum_principle_closedBall_of_fderiv_ne_zero
      hf hdf hΩ hcompact hsub hbd) hc

theorem isConnected_level_of_noncritical_disk_coordinate
    {R : ℝ} (hR : 0 < R) {f : Plane → ℝ}
    (hf : ContinuousOn f (closedBall (0 : Plane) R))
    (hboundary : ∀ x ∈ sphere (0 : Plane) R, f x = x 0)
    (hreg : ContDiffOn ℝ 1 f (ball (0 : Plane) R))
    (hdf : ∀ p ∈ ball (0 : Plane) R, fderiv ℝ f p ≠ 0)
    {c : ℝ} (hc : -R < c ∧ c < R) :
    IsConnected (ball (0 : Plane) R ∩ {x | f x = c}) :=
  (isPathConnected_level_of_noncritical_disk_coordinate hR hf hboundary hreg hdf hc).isConnected

end DifferentialGeometry.Topology

end

end
