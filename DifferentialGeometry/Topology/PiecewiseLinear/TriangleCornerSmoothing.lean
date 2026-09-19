/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CornerBandSmoothing
import DifferentialGeometry.Topology.Homeomorph.DisjointFamily

/-! Simultaneous relative smoothing at all vertices of a planar triangle. -/

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def triangleAffineCycle : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) where
  toFun p := (1 - 3 * p.2 / 2 - p.1 / 2, 1 - p.2 / 2 + p.1 / 2)
  invFun p := (3 * p.2 / 2 - p.1 / 2 - 1, 1 - p.2 / 2 - p.1 / 2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  contMDiff_toFun := (show ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
    (1 - 3 * p.2 / 2 - p.1 / 2, 1 - p.2 / 2 + p.1 / 2)) by fun_prop).contMDiff
  contMDiff_invFun := (show ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
    (3 * p.2 / 2 - p.1 / 2 - 1, 1 - p.2 / 2 - p.1 / 2)) by fun_prop).contMDiff

noncomputable def triangleVertexChart (i : Fin 3) : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) :=
  ![Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞,
    triangleAffineCycle, triangleAffineCycle.symm] i

theorem triangleVertexChart_apply (i : Fin 3) (p : ℝ × ℝ) :
    triangleVertexChart i p = ![p,
      (1 - 3 * p.2 / 2 - p.1 / 2, 1 - p.2 / 2 + p.1 / 2),
      (3 * p.2 / 2 - p.1 / 2 - 1, 1 - p.2 / 2 - p.1 / 2)] i := by
  fin_cases i <;> rfl

def standardTriangleBoundary : Set (ℝ × ℝ) :=
  {p | p.1 ≤ p.2 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ 1 ∧
    (p.2 = p.1 ∨ p.2 = -p.1 ∨ p.2 = 1)}

theorem triangleVertexChart_mem_standardTriangleBoundary_iff (i : Fin 3) (p : ℝ × ℝ) :
    triangleVertexChart i p ∈ standardTriangleBoundary ↔ p ∈ standardTriangleBoundary := by
  rw [triangleVertexChart_apply]
  fin_cases i
  · rfl
  all_goals
    norm_num [standardTriangleBoundary]
    constructor <;> rintro ⟨h₁, h₂, h₃, h₄ | h₄ | h₄⟩ <;>
      refine ⟨by linarith, by linarith, by linarith, ?_⟩
    all_goals first | exact Or.inl (by linarith) | exact Or.inr (Or.inl (by linarith)) |
      exact Or.inr (Or.inr (by linarith))

theorem mem_standardTriangleBoundary_iff_of_snd_lt {p : ℝ × ℝ} (hp : p.2 < 1) :
    p ∈ standardTriangleBoundary ↔ p.2 = |p.1| := by
  change (p.1 ≤ p.2 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ 1 ∧
    (p.2 = p.1 ∨ p.2 = -p.1 ∨ p.2 = 1)) ↔ p.2 = |p.1|
  rcases le_total 0 p.1 with hx | hx
  · rw [abs_of_nonneg hx]
    constructor
    · rintro ⟨h₁, h₂, h₃, h₄ | h₄ | h₄⟩ <;> linarith
    · intro h
      exact ⟨by linarith, by linarith, hp.le, Or.inl h⟩
  · rw [abs_of_nonpos hx]
    constructor
    · rintro ⟨h₁, h₂, h₃, h₄ | h₄ | h₄⟩ <;> linarith
    · intro h
      exact ⟨by linarith, by linarith, hp.le, Or.inr (Or.inl h)⟩

theorem pairwise_disjoint_triangleVertexChart_preimage_ball {r : ℝ} (hr : r ≤ 1 / 4) :
    Pairwise fun i j : Fin 3 =>
      Disjoint (triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) r)
        (triangleVertexChart j ⁻¹' ball (0 : ℝ × ℝ) r) := by
  intro i j hij
  apply disjoint_left.mpr
  intro p hi hj
  have hi' : |(triangleVertexChart i p).1| < r ∧
      |(triangleVertexChart i p).2| < r := by
    simpa only [mem_preimage, mem_ball, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, max_lt_iff] using hi
  have hj' : |(triangleVertexChart j p).1| < r ∧
      |(triangleVertexChart j p).2| < r := by
    simpa only [mem_preimage, mem_ball, dist_zero_right, Prod.norm_def,
      Real.norm_eq_abs, max_lt_iff] using hj
  obtain ⟨hix₁, hix₂⟩ := abs_lt.mp hi'.1
  obtain ⟨hiy₁, hiy₂⟩ := abs_lt.mp hi'.2
  obtain ⟨hjx₁, hjx₂⟩ := abs_lt.mp hj'.1
  obtain ⟨hjy₁, hjy₂⟩ := abs_lt.mp hj'.2
  fin_cases i <;> fin_cases j <;>
    norm_num [triangleVertexChart_apply] at * <;> linarith

theorem exists_isotopy_smoothing_triangle_corners {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 8) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η / 8 ∧
      ∃ G : ℝ → (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
        Continuous (fun q : ℝ × (ℝ × ℝ) => G q.1 q.2) ∧
        Continuous (fun q : ℝ × (ℝ × ℝ) => (G q.1).symm q.2) ∧
        G 0 = Homeomorph.refl (ℝ × ℝ) ∧
        (∀ t, EqOn (G t) id
          (⋃ i : Fin 3, triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) η)ᶜ ∧
          EqOn (G t).symm id
            (⋃ i : Fin 3, triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) η)ᶜ) ∧
        ∃ d : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
          (∀ p, d p = (p.1, Real.smoothAbs δ p.1 + p.2)) ∧
          (∀ i : Fin 3, ∀ p : ℝ × ℝ, |p.2| ≤ η / 8 →
            cornerShear p ∈ ball (0 : ℝ × ℝ) (2 * η) →
            G 1 ((triangleVertexChart i).symm (cornerShear p)) =
              (triangleVertexChart i).symm (d p)) ∧
          (∀ i : Fin 3, MapsTo (G 1)
            (triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) (2 * η))
            (triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) (2 * η)) ∧
            MapsTo (G 1).symm
              (triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) (2 * η))
              (triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) (2 * η))) ∧
          ∀ i : Fin 3, ∀ p ∈ triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) (2 * η),
            p ∈ standardTriangleBoundary →
            G 1 p = (triangleVertexChart i).symm (d ((triangleVertexChart i p).1, 0)) := by
  obtain ⟨δ, hδ, hδη, H, hH, hHi, hH0, hfix, _, d, hd, hframe, _, _⟩ :=
    exists_isotopy_smoothing_cornerShear hη
  let f (i : Fin 3) (t : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    ((triangleVertexChart i).toHomeomorph.trans (H t)).trans
      (triangleVertexChart i).symm.toHomeomorph
  let U (i : Fin 3) : Set (ℝ × ℝ) :=
    triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) (2 * η)
  have hf (i : Fin 3) : Continuous (fun q : ℝ × (ℝ × ℝ) => f i q.1 q.2) :=
    (triangleVertexChart i).symm.continuous.comp
      (hH.comp (continuous_fst.prodMk ((triangleVertexChart i).continuous.comp continuous_snd)))
  have hfi (i : Fin 3) : Continuous (fun q : ℝ × (ℝ × ℝ) => (f i q.1).symm q.2) :=
    (triangleVertexChart i).symm.continuous.comp
      (hHi.comp (continuous_fst.prodMk ((triangleVertexChart i).continuous.comp continuous_snd)))
  have hfsmall (i : Fin 3) (t : ℝ) {p : ℝ × ℝ}
      (hp : triangleVertexChart i p ∉ ball (0 : ℝ × ℝ) η) : f i t p = p := by
    change (triangleVertexChart i).symm (H t (triangleVertexChart i p)) = p
    rw [(hfix t).1 hp, id_eq, Diffeomorph.symm_apply_apply]
  have hffix (i : Fin 3) (t : ℝ) : EqOn (f i t) id (U i)ᶜ := by
    intro p hp
    exact hfsmall i t (fun h => hp (ball_subset_ball (by linarith : η ≤ 2 * η) h))
  obtain ⟨G, hG, hGi, hGF, hGfix, hGid⟩ :=
    Homeomorph.exists_gluing_family_of_pairwise_disjoint f U hf hfi hffix
      (pairwise_disjoint_triangleVertexChart_preimage_ball (by linarith))
  have hframeG (i : Fin 3) (p : ℝ × ℝ) (hu : |p.2| ≤ η / 8)
      (hp : cornerShear p ∈ ball (0 : ℝ × ℝ) (2 * η)) :
      G 1 ((triangleVertexChart i).symm (cornerShear p)) =
        (triangleVertexChart i).symm (d p) := by
    have hm : (triangleVertexChart i).symm (cornerShear p) ∈ U i := by
      change triangleVertexChart i ((triangleVertexChart i).symm (cornerShear p)) ∈
        ball (0 : ℝ × ℝ) (2 * η)
      rwa [Diffeomorph.apply_symm_apply]
    rw [hGF i 1 hm]
    change (triangleVertexChart i).symm
      (H 1 (triangleVertexChart i ((triangleVertexChart i).symm (cornerShear p)))) = _
    rw [Diffeomorph.apply_symm_apply, hframe p hu]
  have hfixed (t : ℝ) : EqOn (G t) id
      (⋃ i : Fin 3, triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) η)ᶜ := by
    intro p hp
    by_cases hpU : p ∈ ⋃ i, U i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hpU
      rw [hGF i t hi]
      exact hfsmall i t (fun hi => hp (mem_iUnion.mpr ⟨i, hi⟩))
    · exact (hGfix t).1 hpU
  refine ⟨δ, hδ, hδη, G, hG, hGi, hGid 0 ?_, ?_, d, hd, hframeG, ?_, ?_⟩
  · intro i
    apply Homeomorph.ext
    intro p
    change (triangleVertexChart i).symm (H 0 (triangleVertexChart i p)) = p
    rw [hH0, Homeomorph.refl_apply, id_eq, Diffeomorph.symm_apply_apply]
  · intro t
    refine ⟨hfixed t, fun p hp => ?_⟩
    apply (G t).injective
    rw [(G t).apply_symm_apply, id_eq, hfixed t hp]
    rfl
  · intro i
    constructor
    · intro p hp
      by_contra hn
      have heq : f i 1 (G 1 p) = G 1 p := hffix i 1 hn
      have hpre : G 1 p = p := (f i 1).injective (heq.trans (hGF i 1 hp))
      exact hn (hpre.symm ▸ hp)
    · intro p hp
      have hx : (f i 1).symm p ∈ U i := by
        by_contra hn
        have hh := hffix i 1 hn
        rw [(f i 1).apply_symm_apply, id_eq] at hh
        exact hn (hh ▸ hp)
      have heq : G 1 ((f i 1).symm p) = p :=
        (hGF i 1 hx).trans ((f i 1).apply_symm_apply p)
      have hh := congrArg (G 1).symm heq
      rw [(G 1).symm_apply_apply] at hh
      exact hh ▸ hx
  · intro i p hp hB
    have hsmall : (triangleVertexChart i p).2 < 1 := by
      have hnorm := (norm_snd_le (triangleVertexChart i p)).trans_lt
        (show ‖triangleVertexChart i p‖ < 2 * η by
          simpa only [mem_preimage, mem_ball, dist_zero_right] using hp)
      have hle := le_abs_self (triangleVertexChart i p).2
      rw [Real.norm_eq_abs] at hnorm
      linarith
    have hgraph := (mem_standardTriangleBoundary_iff_of_snd_lt hsmall).mp
      ((triangleVertexChart_mem_standardTriangleBoundary_iff i p).mpr hB)
    have heq : cornerShear ((triangleVertexChart i p).1, 0) = triangleVertexChart i p := by
      apply Prod.ext
      · rfl
      · change |(triangleVertexChart i p).1| + 0 = (triangleVertexChart i p).2
        rw [add_zero, hgraph]
    have hh := hframeG i ((triangleVertexChart i p).1, 0)
      (by simp only [abs_zero]; positivity) (heq.symm ▸ hp)
    rwa [heq, Diffeomorph.symm_apply_apply] at hh

theorem exists_triangleVertexChart_snd_eq_one {p : ℝ × ℝ}
    (hp : p ∈ standardTriangleBoundary) (hn : ∀ i : Fin 3, triangleVertexChart i p ≠ 0) :
    ∃ i : Fin 3, (triangleVertexChart i p).2 = 1 ∧ |(triangleVertexChart i p).1| < 1 := by
  have hleft : p ≠ (-1, 1) := by
    intro h
    apply hn 1
    rw [h, triangleVertexChart_apply]
    norm_num
  have hright : p ≠ (1, 1) := by
    intro h
    apply hn 2
    change (3 * p.2 / 2 - p.1 / 2 - 1, 1 - p.2 / 2 - p.1 / 2) = 0
    rw [h]
    norm_num
  have hzero : p ≠ (0, 0) := hn 0
  obtain ⟨h₁, h₂, h₃, h₄ | h₄ | h₄⟩ := hp
  · have hx : 0 < p.1 := by
      by_contra h
      have he : p = (0, 0) := Prod.ext (by linarith) (by linarith)
      exact hzero he
    have hx' : p.1 < 1 := by
      by_contra h
      exact hright (Prod.ext (by linarith) (by linarith))
    refine ⟨1, ?_, ?_⟩ <;> rw [triangleVertexChart_apply] <;> norm_num
    · linarith
    · rw [abs_lt]
      constructor <;> linarith
  · have hx : p.1 < 0 := by
      by_contra h
      exact hzero (Prod.ext (by linarith) (by linarith))
    have hx' : -1 < p.1 := by
      by_contra h
      exact hleft (Prod.ext (by linarith) (by linarith))
    refine ⟨2, ?_, ?_⟩
    · change 1 - p.2 / 2 - p.1 / 2 = 1
      linarith
    · change |3 * p.2 / 2 - p.1 / 2 - 1| < 1
      rw [abs_lt]
      constructor <;> linarith
  · refine ⟨0, h₄, ?_⟩
    change |p.1| < 1
    rw [abs_lt]
    constructor
    · by_contra h
      exact hleft (Prod.ext (by linarith) h₄)
    · by_contra h
      exact hright (Prod.ext (by linarith) h₄)

theorem exists_isotopy_smoothing_triangle_boundary {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 8) :
    ∃ δ : ℝ, 0 < δ ∧ δ < η / 8 ∧
      ∃ G : ℝ → (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
        Continuous (fun q : ℝ × (ℝ × ℝ) => G q.1 q.2) ∧
        Continuous (fun q : ℝ × (ℝ × ℝ) => (G q.1).symm q.2) ∧
        G 0 = Homeomorph.refl (ℝ × ℝ) ∧
        (∀ t, EqOn (G t) id
          (⋃ i : Fin 3, triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) η)ᶜ ∧
          EqOn (G t).symm id
            (⋃ i : Fin 3, triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) η)ᶜ) ∧
        ∃ d : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
          (∀ p, d p = (p.1, Real.smoothAbs δ p.1 + p.2)) ∧
          (∀ i : Fin 3, ∀ p : ℝ × ℝ, |p.2| ≤ η / 8 →
            cornerShear p ∈ ball (0 : ℝ × ℝ) (2 * η) →
            G 1 ((triangleVertexChart i).symm (cornerShear p)) =
              (triangleVertexChart i).symm (d p)) ∧
          ∀ p ∈ G 1 '' standardTriangleBoundary,
            ∃ e : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ), ∃ V : Set (ℝ × ℝ),
              IsOpen V ∧ p ∈ V ∧
              ∀ q ∈ V, (q ∈ G 1 '' standardTriangleBoundary ↔ (e q).2 = 0) := by
  obtain ⟨δ, hδ, hδη, G, hG, hGi, hG0, hfix, d, hd, hframe, hmaps, hboundary⟩ :=
    exists_isotopy_smoothing_triangle_corners hη hηsmall
  refine ⟨δ, hδ, hδη, G, hG, hGi, hG0, hfix, d, hd, hframe, ?_⟩
  let U (i : Fin 3) : Set (ℝ × ℝ) :=
    triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) (2 * η)
  let F : Set (ℝ × ℝ) :=
    ⋃ i : Fin 3, triangleVertexChart i ⁻¹' closedBall (0 : ℝ × ℝ) η
  have hF : IsClosed F := isClosed_iUnion_of_finite fun i =>
    isClosed_closedBall.preimage (triangleVertexChart i).continuous
  have hfixF (q : ℝ × ℝ) (hq : q ∉ F) :
      G 1 q = q ∧ (G 1).symm q = q := by
    have hout : q ∉ ⋃ i : Fin 3, triangleVertexChart i ⁻¹' ball (0 : ℝ × ℝ) η := by
      intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact hq (mem_iUnion.mpr ⟨i, ball_subset_closedBall hi⟩)
    exact ⟨(hfix 1).1 hout, (hfix 1).2 hout⟩
  intro p hp
  by_cases hpU : p ∈ ⋃ i, U i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hpU
    refine ⟨(triangleVertexChart i).trans d.symm, U i,
      isOpen_ball.preimage (triangleVertexChart i).continuous, hi, ?_⟩
    intro q hq
    change q ∈ G 1 '' standardTriangleBoundary ↔
      (d.symm (triangleVertexChart i q)).2 = 0
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxU : x ∈ U i := by
        simpa only [Homeomorph.symm_apply_apply] using (hmaps i).2 hq
      rw [hboundary i x hxU hx, Diffeomorph.apply_symm_apply,
        Diffeomorph.symm_apply_apply]
    · intro hz
      let x := (d.symm (triangleVertexChart i q)).1
      have hxd : (triangleVertexChart i q).1 = x := by
        have hh := congrArg Prod.fst (hd (d.symm (triangleVertexChart i q)))
        rwa [Diffeomorph.apply_symm_apply] at hh
      have hx : |x| < 2 * η := by
        rw [← hxd]
        exact (norm_fst_le (triangleVertexChart i q)).trans_lt (by
          simpa only [U, mem_preimage, mem_ball, dist_zero_right] using hq)
      have hxball : cornerShear (x, 0) ∈ ball (0 : ℝ × ℝ) (2 * η) := by
        simpa only [cornerShear_apply, add_zero, mem_ball, dist_zero_right,
          Prod.norm_def, Real.norm_eq_abs, abs_abs, max_self] using hx
      have hxB : cornerShear (x, 0) ∈ standardTriangleBoundary := by
        apply (mem_standardTriangleBoundary_iff_of_snd_lt (by
          change |x| + 0 < 1
          linarith)).mpr
        exact add_zero _
      have heq : (x, 0) = d.symm (triangleVertexChart i q) := Prod.ext rfl hz.symm
      refine ⟨(triangleVertexChart i).symm (cornerShear (x, 0)), ?_, ?_⟩
      · apply (triangleVertexChart_mem_standardTriangleBoundary_iff i _).mp
        rwa [Diffeomorph.apply_symm_apply]
      · rw [hframe i (x, 0) (by simp only [abs_zero]; positivity) hxball,
          heq, Diffeomorph.apply_symm_apply, Diffeomorph.symm_apply_apply]
  · have hpF : p ∉ F := by
      intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact hpU (mem_iUnion.mpr ⟨i, closedBall_subset_ball (by linarith : η < 2 * η) hi⟩)
    have hpB : p ∈ standardTriangleBoundary := by
      obtain ⟨x, hx, hxp⟩ := hp
      have hh := congrArg (G 1).symm hxp
      rw [(G 1).symm_apply_apply, (hfixF p hpF).2] at hh
      exact hh ▸ hx
    have hn (i : Fin 3) : triangleVertexChart i p ≠ 0 := by
      intro hi
      apply hpU
      refine mem_iUnion.mpr ⟨i, ?_⟩
      change triangleVertexChart i p ∈ ball (0 : ℝ × ℝ) (2 * η)
      rw [hi, mem_ball, dist_self]
      positivity
    obtain ⟨i, hi, hi'⟩ := exists_triangleVertexChart_snd_eq_one hpB hn
    let a : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := Diffeomorph.graphShear
      (show ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)) from contDiff_const) contDiff_zero_fun
    let V : Set (ℝ × ℝ) := Fᶜ ∩
      {q | |(triangleVertexChart i q).1| < (triangleVertexChart i q).2}
    refine ⟨(triangleVertexChart i).trans a, V, hF.isOpen_compl.inter
      (isOpen_lt (triangleVertexChart i).continuous.fst.abs
        (triangleVertexChart i).continuous.snd), ⟨hpF, by
          change |(triangleVertexChart i p).1| < (triangleVertexChart i p).2
          rwa [hi]⟩, ?_⟩
    intro q hq
    have hqB : q ∈ G 1 '' standardTriangleBoundary ↔ q ∈ standardTriangleBoundary := by
      constructor
      · rintro ⟨x, hx, hxq⟩
        have hh := congrArg (G 1).symm hxq
        rw [(G 1).symm_apply_apply, (hfixF q hq.1).2] at hh
        exact hh ▸ hx
      · intro h
        exact ⟨q, h, (hfixF q hq.1).1⟩
    rw [hqB, ← triangleVertexChart_mem_standardTriangleBoundary_iff i q]
    change triangleVertexChart i q ∈ standardTriangleBoundary ↔
      (a (triangleVertexChart i q)).2 = 0
    rw [show (a (triangleVertexChart i q)).2 = (triangleVertexChart i q).2 - 1 by
      dsimp only [a]
      rw [Diffeomorph.graphShear_apply, add_zero], sub_eq_zero]
    have hstrict : |(triangleVertexChart i q).1| < (triangleVertexChart i q).2 := hq.2
    have hx := le_abs_self (triangleVertexChart i q).1
    have hnx := neg_le_abs (triangleVertexChart i q).1
    constructor
    · rintro ⟨_, _, _, h | h | h⟩ <;> linarith
    · intro h
      exact ⟨by linarith, by linarith, h.le, Or.inr (Or.inr h)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
