/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismAnnulusChart
import DifferentialGeometry.Topology.PiecewiseLinear.RadialAnnulusSqueeze
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryAnnulusEmbedding
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.Homeomorph.ConjugateFamily

open Set Metric Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem exists_halfAnnulus_param_of_isClosedEmbedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1} → M)
    (hψ : IsClosedEmbedding ψ) (hψbd : range ψ ⊆ (𝓡∂ 3).boundary M) :
    ∃ e : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} →
        BoundaryManifold (𝓡∂ 3) M,
      Continuous e ∧ Function.Injective e ∧
        (fun b : BoundaryManifold (𝓡∂ 3) M => (b : M)) '' range e = range ψ := by
  classical
  have hpos : ∀ v : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, 0 < ‖v.val‖ :=
    fun v => by linarith [v.2.1]
  have hun : ∀ v : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1},
      ‖‖v.val‖⁻¹ • v.val‖ = 1 := fun v => by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hpos v).ne']
  let u : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} →
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := fun v =>
    ⟨‖v.val‖⁻¹ • v.val, mem_closedBall_zero_iff.mpr (hun v).le⟩
  let s : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} → Icc (0 : ℝ) 1 := fun v =>
    ⟨2 * ‖v.val‖ - 1, by linarith [v.2.1], by linarith [v.2.2]⟩
  let z : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} →
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) := fun v =>
    prismBallHomeomorph.symm (u v, s v)
  have hzbd : ∀ v, (z v).val.1 ∈ stdSimplexBoundary 2 := by
    intro v
    refine (prismBallHomeomorph_mem_sphere_iff (z v)).mp ?_
    change (prismBallHomeomorph (prismBallHomeomorph.symm (u v, s v))).1.val ∈ _
    rw [Homeomorph.apply_symm_apply]
    exact mem_sphere_zero_iff_norm.mpr (hun v)
  let zz : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} →
      {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
        z.val ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1} := fun v =>
    ⟨z v, hzbd v, (z v).2.2⟩
  let e : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} →
      BoundaryManifold (𝓡∂ 3) M := fun v => ⟨ψ (zz v), hψbd ⟨zz v, rfl⟩⟩
  have hnc : Continuous fun v : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} =>
      ‖v.val‖ := continuous_norm.comp continuous_subtype_val
  have huc : Continuous u :=
    ((hnc.inv₀ fun v => (hpos v).ne').smul continuous_subtype_val).subtype_mk _
  have hsc : Continuous s :=
    ((continuous_const.mul hnc).sub continuous_const).subtype_mk _
  have hzzc : Continuous zz :=
    (prismBallHomeomorph.symm.continuous.comp (huc.prodMk hsc)).subtype_mk _
  refine ⟨e, (hψ.continuous.comp hzzc).subtype_mk _, fun v w hvw => ?_, ?_⟩
  · have h1 : zz v = zz w := hψ.injective (congrArg Subtype.val hvw)
    have h2 : z v = z w := congrArg Subtype.val h1
    have h3 : (u v, s v) = (u w, s w) := prismBallHomeomorph.symm.injective h2
    have hs : ‖v.val‖ = ‖w.val‖ := by
      have := congrArg (fun p => (p.2 : ℝ)) h3
      change 2 * ‖v.val‖ - 1 = 2 * ‖w.val‖ - 1 at this
      linarith
    have hu : ‖v.val‖⁻¹ • v.val = ‖w.val‖⁻¹ • w.val :=
      congrArg (fun p : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 =>
        (p.1 : EuclideanSpace ℝ (Fin 2))) h3
    rw [hs] at hu
    exact Subtype.ext (smul_right_injective _ (inv_ne_zero (hpos w).ne') hu)
  · ext p
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      exact ⟨zz v, rfl⟩
    · rintro ⟨q, rfl⟩
      set wt := prismBallHomeomorph q.val with hwt
      have hw1 : ‖wt.1.val‖ = 1 := mem_sphere_zero_iff_norm.mp
        ((prismBallHomeomorph_mem_sphere_iff q.val).mpr q.2.1)
      have ht := wt.2.2
      set x : EuclideanSpace ℝ (Fin 2) := ((1 + (wt.2 : ℝ)) / 2) • wt.1.val with hx
      have hxn : ‖x‖ = (1 + (wt.2 : ℝ)) / 2 := by
        rw [hx, norm_smul, hw1, mul_one, Real.norm_of_nonneg (by linarith [ht.1])]
      let v : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} :=
        ⟨x, by rw [hxn]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
      refine ⟨e v, ⟨v, rfl⟩, ?_⟩
      have huv : u v = wt.1 := by
        apply Subtype.ext
        change ‖x‖⁻¹ • x = wt.1.val
        rw [hxn, hx, smul_smul, inv_mul_cancel₀ (by linarith [ht.1]), one_smul]
      have hsv : s v = wt.2 := by
        apply Subtype.ext
        change 2 * ‖x‖ - 1 = wt.2
        rw [hxn]
        ring
      have hzv : zz v = q := by
        apply Subtype.ext
        change prismBallHomeomorph.symm (u v, s v) = q.val
        rw [huv, hsv, Prod.mk.eta, hwt, Homeomorph.symm_apply_apply]
      change ψ (zz v) = ψ q
      rw [hzv]

theorem exists_openPartialHomeomorph_of_halfAnnulus_embedding {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (e : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} → S) (he : Continuous e)
    (hinj : Function.Injective e) :
    ∃ Φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S,
      Φ.source = {x | 1 < ‖x‖ ∧ ‖x‖ < 2} ∧
      ∀ v : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1}, 1 / 2 < ‖v.val‖ →
        ‖v.val‖ < 1 → Φ ((2 : ℝ) • v.val) = e v := by
  classical
  set U : Set (EuclideanSpace ℝ (Fin 2)) := {x | 1 < ‖x‖ ∧ ‖x‖ < 2} with hUdef
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hhalf : ∀ x : EuclideanSpace ℝ (Fin 2), ‖(1 / 2 : ℝ) • x‖ = ‖x‖ / 2 := fun x => by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    ring
  have hmem : ∀ x ∈ U, 1 / 2 ≤ ‖(1 / 2 : ℝ) • x‖ ∧ ‖(1 / 2 : ℝ) • x‖ ≤ 1 := by
    intro x hx
    rw [hhalf]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  let v₀ : {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1} :=
    ⟨EuclideanSpace.single 0 1, by norm_num⟩
  let F : EuclideanSpace ℝ (Fin 2) → S := fun x =>
    if h : 1 / 2 ≤ ‖(1 / 2 : ℝ) • x‖ ∧ ‖(1 / 2 : ℝ) • x‖ ≤ 1 then e ⟨(1 / 2 : ℝ) • x, h⟩ else e v₀
  have hFU : ∀ x (hx : x ∈ U), F x = e ⟨(1 / 2 : ℝ) • x, hmem x hx⟩ := fun x hx =>
    dite_eq_left (hmem x hx)
  have hFc : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : U.domRestrict F = e ∘ (fun x : U => (⟨(1 / 2 : ℝ) • x.val, hmem x.val x.2⟩ :
        {x : EuclideanSpace ℝ (Fin 2) // 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1})) := by
      funext x
      exact hFU x.val x.2
    rw [h]
    have hc0 : Continuous (fun x : U => (1 / 2 : ℝ) • x.val) :=
      continuous_subtype_val.const_smul (1 / 2 : ℝ)
    exact he.comp (hc0.subtype_mk fun x => hmem x.val x.2)
  have hFinj : InjOn F U := by
    intro x hx y hy hxy
    rw [hFU x hx, hFU y hy] at hxy
    have h := congrArg Subtype.val (hinj hxy)
    exact smul_right_injective _ (by norm_num : (1 / 2 : ℝ) ≠ 0) h
  have hopen : IsOpenMap (U.domRestrict F) := by
    intro V hV
    have hV' : IsOpen (Subtype.val '' V) := hU.isOpenMap_subtype_val V hV
    have hVU : Subtype.val '' V ⊆ U := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have himage : U.domRestrict F '' V = F '' (Subtype.val '' V) := by
      rw [← image_comp]
      rfl
    rw [himage]
    exact DifferentialGeometry.Topology.isOpen_image_of_continuousOn_injOn
      (E := EuclideanSpace ℝ (Fin 2)) hV' (hFc.mono hVU) (hFinj.mono hVU)
  refine ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict (hFinj.toPartialEquiv F U) hFc hopen hU,
    rfl, fun v h1 h2 => ?_⟩
  have hx : (2 : ℝ) • v.val ∈ U := by
    change 1 < ‖(2 : ℝ) • v.val‖ ∧ ‖(2 : ℝ) • v.val‖ < 2
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    exact ⟨by linarith, by linarith⟩
  change F ((2 : ℝ) • v.val) = e v
  rw [hFU _ hx]
  congr 1
  apply Subtype.ext
  change (1 / 2 : ℝ) • (2 : ℝ) • v.val = v.val
  rw [smul_smul]
  norm_num

theorem exists_isotopy_radial_of_annulus_chart {S : Type*} [TopologicalSpace S] [T2Space S]
    (Φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (hΦ : {x : EuclideanSpace ℝ (Fin 2) | 1 < ‖x‖ ∧ ‖x‖ < 2} ⊆ Φ.source)
    {r₁ r₂ q₁ q₂ : ℝ} (h1 : 1 < r₁) (h12 : r₁ < r₂) (h2 : r₂ < 2) (g1 : 1 < q₁)
    (g12 : q₁ < q₂) (g2 : q₂ < 2) :
    ∃ J : ℝ → S ≃ₜ S, Continuous (fun p : ℝ × S => J p.1 p.2) ∧
      Continuous (fun p : ℝ × S => (J p.1).symm p.2) ∧ J 0 = Homeomorph.refl S ∧
      J 1 '' (Φ '' {x | r₁ ≤ ‖x‖ ∧ ‖x‖ ≤ r₂}) = Φ '' {x | q₁ ≤ ‖x‖ ∧ ‖x‖ ≤ q₂} := by
  obtain ⟨R, hRc, hRi, hR0, α, β, hα, hαβ, hβ, hRfix, hR1⟩ :=
    exists_isotopy_radial_annulus h1 h12 h2 g1 g12 g2
  set C : Set (EuclideanSpace ℝ (Fin 2)) := {x | α ≤ ‖x‖ ∧ ‖x‖ ≤ β} with hCdef
  have hCc : IsCompact C :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) β).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    fun x hx => mem_closedBall_zero_iff.mpr hx.2
  have hCs : C ⊆ Φ.symm.target := by
    rw [OpenPartialHomeomorph.symm_target]
    intro x hx
    exact hΦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsub : {x : EuclideanSpace ℝ (Fin 2) | α < ‖x‖ ∧ ‖x‖ < β} ⊆ C :=
    fun x hx => ⟨hx.1.le, hx.2.le⟩
  have hfix : ∀ t, EqOn (R t) id Cᶜ ∧ EqOn (R t).symm id Cᶜ := fun t =>
    ⟨(hRfix t).1.mono (compl_subset_compl.mpr hsub),
      (hRfix t).2.mono (compl_subset_compl.mpr hsub)⟩
  obtain ⟨J, hJc, hJi, hJe, -⟩ := Φ.symm.exists_conjugate_homeomorph_family R hRc hRi hCc hCs hfix
  have hJ0 : J 0 = Homeomorph.refl S := by
    refine Homeomorph.ext fun y => ?_
    rw [(hJe 0 y).1, hR0]
    by_cases hy : y ∈ Φ.target
    · rw [Φ.symm.conjugateMap_of_mem _ hy]
      exact Φ.right_inv hy
    · exact Φ.symm.conjugateMap_of_notMem _ hy
  have hJΦ : ∀ x ∈ Φ.source, J 1 (Φ x) = Φ (R 1 x) := by
    intro x hx
    rw [(hJe 1 (Φ x)).1, Φ.symm.conjugateMap_of_mem _ (Φ.map_source hx)]
    change Φ (R 1 (Φ.symm (Φ x))) = Φ (R 1 x)
    rw [Φ.left_inv hx]
  refine ⟨J, hJc, hJi, hJ0, ?_⟩
  rw [← hR1, ← image_comp, ← image_comp]
  refine image_congr fun x hx => ?_
  exact hJΦ x (hΦ ⟨by linarith [hx.1], by linarith [hx.2]⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
