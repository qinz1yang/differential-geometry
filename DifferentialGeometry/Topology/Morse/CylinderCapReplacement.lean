import DifferentialGeometry.Topology.Morse.CylinderCap
import DifferentialGeometry.Topology.Morse.ExtremumIndex
import DifferentialGeometry.Topology.Morse.ConstantGerm
import DifferentialGeometry.Topology.Morse.Naturality
import Mathlib.Data.Set.Card

open Set Metric
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Morse

section

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  {F : Type*} {f : M → F} {Ψ : E × ℝ → F} {h : F → ℝ} {a b : ℝ}

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem isCriticalPointAt_cylinderCap_replacement_iff
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {x : E} (hx : x ∈ φ.source)
    (ha : a ≠ 0) (hheight : ∀ p, h (Ψ p) = b + p.2)
    (hnear : f =ᶠ[nhds (φ x)] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ φ.symm) :
    IsCriticalPointAt I (h ∘ f) (φ x) ↔ x = 0 := by
  let g : E → ℝ := fun y => (EuclideanGeometry.cylinderCap a y).2 + b
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)).add contDiff_const
  have heq : h ∘ f =ᶠ[nhds (φ x)] g ∘ φ.symm := by
    filter_upwards [hnear] with y hy
    change h (f y) = (EuclideanGeometry.cylinderCap a (φ.symm y)).2 + b
    rw [hy]
    exact (hheight _).trans (add_comm _ _)
  have hi := φ.symm.isLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ (φ.map_source hx)
  have hc := (isCriticalPointAt_congr_of_eventuallyEq heq).trans
    (isCriticalPointAt_comp_iff (hi.mdifferentiableAt (by simp))
      (hg.contMDiff.mdifferentiableAt (by simp))
      (hi.mfderivToContinuousLinearEquiv (by simp)).surjective)
  have hpoint : φ.symm (φ x) = x := φ.left_inv hx
  rw [hpoint] at hc
  exact hc.trans ((isCriticalPointAt_add_const_iff
    (fun y : E => (EuclideanGeometry.cylinderCap a y).2) b x).trans
      (isCriticalPointAt_cylinderCap_snd_iff ha x))

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem criticalPoints_cylinderCap_replacement
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hballφ : closedBall (0 : E) 1 ⊆ φ.source)
    {D : Set M} (hD : IsClosed D) (hφD : φ '' closedBall (0 : E) 1 = D)
    {e : M → F} (hfix : EqOn f e Dᶜ)
    (ha : a ≠ 0) (hheight : ∀ p, h (Ψ p) = b + p.2)
    (hnear : ∀ y ∈ D, f =ᶠ[nhds y] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ φ.symm) :
    criticalPoints I (h ∘ f) = (criticalPoints I (h ∘ e) \ D) ∪ {φ 0} := by
  have hzero : (0 : E) ∈ closedBall (0 : E) 1 := mem_closedBall_self zero_le_one
  have hcenter : φ 0 ∈ D := hφD.subset (mem_image_of_mem φ hzero)
  ext y
  change IsCriticalPointAt I (h ∘ f) y ↔
    (IsCriticalPointAt I (h ∘ e) y ∧ y ∉ D) ∨ y = φ 0
  by_cases hy : y ∈ D
  · obtain ⟨x, hx, rfl⟩ := hφD.symm.subset hy
    have hc := isCriticalPointAt_cylinderCap_replacement_iff φ (hballφ hx)
      ha hheight (hnear (φ x) hy)
    constructor
    · intro hh
      exact Or.inr (congrArg φ (hc.mp hh))
    · rintro (hh | hh)
      · exact False.elim (hh.2 hy)
      · exact hc.mpr (φ.injOn (hballφ hx) (hballφ hzero) hh)
  · have heq : f =ᶠ[nhds y] e := Filter.eventuallyEq_of_mem
      (hD.isOpen_compl.mem_nhds hy) hfix
    have hc := isCriticalPointAt_congr_of_eventuallyEq (I := I) (heq.fun_comp h)
    constructor
    · intro hh
      exact Or.inl ⟨hc.mp hh, hy⟩
    · rintro (hh | hh)
      · exact hc.mpr hh.1
      · exact False.elim (hy (hh ▸ hcenter))

theorem isNondegenerateCriticalPointAt_cylinderCap_replacement
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (hzero : (0 : E) ∈ φ.source)
    (ha : a ≠ 0) (hheight : ∀ p, h (Ψ p) = b + p.2)
    (hnear : f =ᶠ[nhds (φ 0)] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ φ.symm) :
    IsNondegenerateCriticalPointAt I (h ∘ f) (φ 0) := by
  let g : E → ℝ := fun y => (EuclideanGeometry.cylinderCap a y).2 + b
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)).add contDiff_const
  have heq : h ∘ f =ᶠ[nhds (φ 0)] g ∘ φ.symm := by
    filter_upwards [hnear] with y hy
    change h (f y) = (EuclideanGeometry.cylinderCap a (φ.symm y)).2 + b
    rw [hy]
    exact (hheight _).trans (add_comm _ _)
  have hi := φ.symm.isLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ (φ.map_source hzero)
  apply (isNondegenerateCriticalPointAt_congr_of_eventuallyEq heq).mpr
  apply (isNondegenerateCriticalPointAt_comp_model_iff
    (hg.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (hi.contMDiffAt.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    (hi.mfderivToContinuousLinearEquiv (by simp)).bijective).mpr
  have hpoint : φ.symm (φ 0) = 0 := φ.left_inv hzero
  rw [hpoint]
  exact (isNondegenerateCriticalPointAt_add_const_iff
    (fun y : E => (EuclideanGeometry.cylinderCap a y).2) b 0).mpr
      (isNondegenerateCriticalPointAt_cylinderCap_snd ha)

variable {e : M → F}

theorem isNondegenerateCriticalPointAt_cylinderCap_replacement_of_critical
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hballφ : closedBall (0 : E) 1 ⊆ φ.source)
    {D : Set M} (hD : IsClosed D) (hφD : φ '' closedBall (0 : E) 1 = D)
    (hfix : EqOn f e Dᶜ)
    (ha : a ≠ 0) (hheight : ∀ p, h (Ψ p) = b + p.2)
    (hnear : ∀ y ∈ D, f =ᶠ[nhds y] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ φ.symm)
    (hnd : ∀ y ∉ D, IsCriticalPointAt I (h ∘ e) y → IsNondegenerateCriticalPointAt I (h ∘ e) y)
    {y : M} (hy : IsCriticalPointAt I (h ∘ f) y) :
    IsNondegenerateCriticalPointAt I (h ∘ f) y := by
  have hc := criticalPoints_cylinderCap_replacement φ hballφ hD hφD hfix ha hheight hnear
  have hym : y ∈ criticalPoints I (h ∘ f) := hy
  rw [hc] at hym
  rcases hym with hyold | hycenter
  · have heq : f =ᶠ[nhds y] e := Filter.eventuallyEq_of_mem
      (hD.isOpen_compl.mem_nhds hyold.2) hfix
    exact (isNondegenerateCriticalPointAt_congr_of_eventuallyEq (heq.fun_comp h)).mpr
      (hnd y hyold.2 hyold.1)
  · have hzero : (0 : E) ∈ closedBall (0 : E) 1 := mem_closedBall_self zero_le_one
    have hcenter : φ 0 ∈ D := hφD.subset ⟨0, hzero, rfl⟩
    rw [mem_singleton_iff.mp hycenter]
    exact isNondegenerateCriticalPointAt_cylinderCap_replacement φ (hballφ hzero)
      ha hheight (hnear _ hcenter)

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem injOn_criticalPoints_cylinderCap_replacement
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hballφ : closedBall (0 : E) 1 ⊆ φ.source)
    {D : Set M} (hD : IsClosed D) (hφD : φ '' closedBall (0 : E) 1 = D)
    (hfix : EqOn f e Dᶜ)
    (ha : a ≠ 0) (hheight : ∀ p, h (Ψ p) = b + p.2)
    (hnear : ∀ y ∈ D, f =ᶠ[nhds y] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ φ.symm)
    (hinj : InjOn (h ∘ e) (criticalPoints I (h ∘ e) \ D))
    (hvalue : b - a ∉ (h ∘ e) '' (criticalPoints I (h ∘ e) \ D)) :
    InjOn (h ∘ f) (criticalPoints I (h ∘ f)) := by
  have hc := criticalPoints_cylinderCap_replacement φ hballφ hD hφD hfix ha hheight hnear
  have hzero : (0 : E) ∈ closedBall (0 : E) 1 := mem_closedBall_self zero_le_one
  have hcenter : φ 0 ∈ D := hφD.subset ⟨0, hzero, rfl⟩
  have hbase : h (f (φ 0)) = b - a := by
    have hv := (hnear _ hcenter).self_of_nhds
    change f (φ 0) = Ψ (EuclideanGeometry.cylinderCap a (φ.symm (φ 0))) at hv
    have hi : φ.symm (φ 0) = 0 := φ.left_inv (hballφ hzero)
    rw [hi, EuclideanGeometry.cylinderCap_zero] at hv
    rw [hv, hheight]
    ring
  intro x hx y hy hxy
  rw [hc] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · apply hinj hx hy
    simpa only [Function.comp_apply, hfix hx.2, hfix hy.2] using hxy
  · have hy' : y = φ 0 := mem_singleton_iff.mp hy
    have hv : h (e x) = b - a := by
      change h (f x) = h (f y) at hxy
      rwa [hfix hx.2, hy', hbase] at hxy
    exact False.elim (hvalue ⟨x, hx, hv⟩)
  · have hx' : x = φ 0 := mem_singleton_iff.mp hx
    have hv : h (e y) = b - a := by
      change h (f x) = h (f y) at hxy
      rw [hx', hbase, hfix hy.2] at hxy
      exact hxy.symm
    exact False.elim (hvalue ⟨y, hy, hv⟩)
  · exact (mem_singleton_iff.mp hx).trans (mem_singleton_iff.mp hy).symm

omit [I.Boundaryless] [IsManifold I ∞ M] in
theorem ncard_criticalPoints_cylinderCap_replacement
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hballφ : closedBall (0 : E) 1 ⊆ φ.source)
    {D : Set M} (hD : IsClosed D) (hφD : φ '' closedBall (0 : E) 1 = D)
    (hfix : EqOn f e Dᶜ)
    (ha : a ≠ 0) (hheight : ∀ p, h (Ψ p) = b + p.2)
    (hnear : ∀ y ∈ D, f =ᶠ[nhds y] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ φ.symm)
    (hfinite : (criticalPoints I (h ∘ e)).Finite) :
    (criticalPoints I (h ∘ f)).ncard + (criticalPoints I (h ∘ e) ∩ D).ncard =
      (criticalPoints I (h ∘ e)).ncard + 1 := by
  have hc := criticalPoints_cylinderCap_replacement φ hballφ hD hφD hfix ha hheight hnear
  have hzero : (0 : E) ∈ closedBall (0 : E) 1 := mem_closedBall_self zero_le_one
  have hcenter : φ 0 ∈ D := hφD.subset ⟨0, hzero, rfl⟩
  rw [hc, union_singleton, ncard_insert_of_notMem (fun h => h.2 hcenter) hfinite.sdiff]
  have h := ncard_inter_add_ncard_sdiff_eq_ncard (criticalPoints I (h ∘ e)) D hfinite
  omega

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  {F : Type*} {f : M → F} {Ψ : E × ℝ → F} {h : F → ℝ} {a b : ℝ}

theorem isLocalMin_cylinderCap_replacement
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (hzero : (0 : E) ∈ φ.source)
    (ha : 0 ≤ a) (hheight : ∀ p, h (Ψ p) = b + p.2)
    (hnear : f =ᶠ[nhds (φ 0)] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ φ.symm) :
    IsLocalMin (h ∘ f) (φ 0) := by
  have hself : f (φ 0) = Ψ (EuclideanGeometry.cylinderCap a (φ.symm (φ 0))) :=
    hnear.self_of_nhds
  have hback : φ.symm (φ 0) = 0 := φ.left_inv hzero
  rw [hback, EuclideanGeometry.cylinderCap_zero] at hself
  have hbase : h (f (φ 0)) = b - a := by
    rw [hself, hheight]
    ring
  filter_upwards [hnear] with y hy
  change h (f (φ 0)) ≤ h (f y)
  rw [hbase, hy]
  change b - a ≤ h (Ψ (EuclideanGeometry.cylinderCap a (φ.symm y)))
  rw [hheight, EuclideanGeometry.cylinderCap_snd]
  nlinarith [mul_nonneg ha (sq_nonneg ‖φ.symm y‖)]

theorem isLocalMax_cylinderCap_replacement
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) (hzero : (0 : E) ∈ φ.source)
    (ha : a ≤ 0) (hheight : ∀ p, h (Ψ p) = b + p.2)
    (hnear : f =ᶠ[nhds (φ 0)] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ φ.symm) :
    IsLocalMax (h ∘ f) (φ 0) := by
  have hself : f (φ 0) = Ψ (EuclideanGeometry.cylinderCap a (φ.symm (φ 0))) :=
    hnear.self_of_nhds
  have hback : φ.symm (φ 0) = 0 := φ.left_inv hzero
  rw [hback, EuclideanGeometry.cylinderCap_zero] at hself
  have hbase : h (f (φ 0)) = b - a := by
    rw [hself, hheight]
    ring
  filter_upwards [hnear] with y hy
  change h (f y) ≤ h (f (φ 0))
  rw [hbase, hy]
  change h (Ψ (EuclideanGeometry.cylinderCap a (φ.symm y))) ≤ b - a
  rw [hheight, EuclideanGeometry.cylinderCap_snd]
  nlinarith [mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg ‖φ.symm y‖)]

theorem criticalPoints_with_index_cylinderCap_replacement
    {E H M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    {F : Type*} {e f : M → F} {Ψ : E × ℝ → F} {h : F → ℝ} {a b : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (h ∘ f))
    (φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hballφ : closedBall (0 : E) 1 ⊆ φ.source)
    {D : Set M} (hD : IsClosed D) (hφD : φ '' closedBall (0 : E) 1 = D)
    (hfix : EqOn f e Dᶜ)
    (ha : a ≠ 0) (hheight : ∀ p, h (Ψ p) = b + p.2)
    (hnear : ∀ y ∈ D, f =ᶠ[nhds y] (Ψ ∘ EuclideanGeometry.cylinderCap a) ∘ φ.symm)
    {k : ℕ} (hk : 0 < k) (hkdim : k < Module.finrank ℝ E) :
    {y | IsCriticalPointAt I (h ∘ f) y ∧ sigNeg (chartHessianAt
      (fun z => h (f ((extChartAt I y).symm z))) (extChartAt I y y)) = k} =
    {y | IsCriticalPointAt I (h ∘ e) y ∧ sigNeg (chartHessianAt
      (fun z => h (e ((extChartAt I y).symm z))) (extChartAt I y y)) = k} \ D := by
  have hzero : (0 : E) ∈ closedBall (0 : E) 1 := mem_closedBall_self zero_le_one
  have hcenter : φ 0 ∈ D := hφD.subset ⟨0, hzero, rfl⟩
  have hnd := isNondegenerateCriticalPointAt_cylinderCap_replacement φ (hballφ hzero)
    ha hheight (hnear _ hcenter)
  have hnindex : sigNeg (chartHessianAt
      (fun z => h (f ((extChartAt I (φ 0)).symm z))) (extChartAt I (φ 0) (φ 0))) ≠ k := by
    rcases le_total 0 a with hapos | haneg
    · have hm := isLocalMin_cylinderCap_replacement φ (hballφ hzero) hapos hheight
        (hnear _ hcenter)
      have hi := minimum_morse_index_eq_zero hf hnd hm
      dsimp only [Function.comp_apply] at hi
      rw [hi]
      exact ne_of_lt hk
    · have hm := isLocalMax_cylinderCap_replacement φ (hballφ hzero) haneg hheight
        (hnear _ hcenter)
      have hi := maximum_morse_index_eq_finrank hf hnd hm
      dsimp only [Function.comp_apply] at hi
      rw [hi]
      exact ne_of_gt hkdim
  have hcrit := criticalPoints_cylinderCap_replacement φ hballφ hD hφD hfix ha hheight hnear
  ext y
  by_cases hy : y ∈ D
  · constructor
    · rintro ⟨hycrit, hyindex⟩
      have hym : y ∈ criticalPoints I (h ∘ f) := hycrit
      rw [hcrit] at hym
      rcases hym with hh | hh
      · exact False.elim (hh.2 hy)
      · exact False.elim (hnindex (mem_singleton_iff.mp hh ▸ hyindex))
    · exact fun hh => False.elim (hh.2 hy)
  · have heq : f =ᶠ[nhds y] e := Filter.eventuallyEq_of_mem
        (hD.isOpen_compl.mem_nhds hy) hfix
    have hcp := isCriticalPointAt_congr_of_eventuallyEq (I := I) (heq.fun_comp h)
    have hess := DifferentialGeometry.Morse.chartHessianAt_eq_of_eventuallyEq_add_const
      (I := I) (f := h ∘ e) (g := h ∘ f) BoundarylessManifold.isInteriorPoint
      (b := 0) (by simpa only [add_zero] using heq.fun_comp h)
    simp only [mem_ofPred_eq, mem_sdiff, hy, not_false_eq_true, and_true]
    dsimp only [Function.comp_apply] at hess
    rw [hcp, hess]

end DifferentialGeometry.Topology.Morse
