/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcPatternEnds
import DifferentialGeometry.Topology.PiecewiseLinear.Prism
import Mathlib.Topology.MetricSpace.Thickening

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_pos_box_subset_of_coreSegment_subset
    {N : Set ((ℝ × ℝ) × ℝ)} (hN : IsOpen N) {τ : ℝ} (hτ : 0 < τ)
    (hcore : coreSegment τ ⊆ N) :
    ∃ δ > 0, (Icc (-δ) δ ×ˢ Icc (-δ) δ) ×ˢ Icc (-δ) (τ + δ) ⊆ N := by
  obtain ⟨δ, hδ, hδN⟩ := (isCompact_coreSegment τ).exists_cthickening_subset_open hN hcore
  refine ⟨δ, hδ, fun p hp => hδN ?_⟩
  let z := max 0 (min τ p.2)
  have hz0 : 0 ≤ z := le_max_left _ _
  have hzτ : z ≤ τ := max_le hτ.le (min_le_left _ _)
  have hdist : |p.2 - z| ≤ δ := by
    dsimp [z]
    rcases le_total p.2 0 with h | h
    · rw [min_eq_right (h.trans hτ.le), max_eq_left h]
      rw [sub_zero, abs_of_nonpos h]
      linarith [hp.2.1]
    · rw [max_eq_right (le_min hτ.le h)]
      rcases le_total p.2 τ with h' | h'
      · rw [min_eq_right h', sub_self, abs_zero]
        exact hδ.le
      · rw [min_eq_left h', abs_of_nonneg (sub_nonneg.mpr h')]
        linarith [hp.2.2]
  apply mem_cthickening_of_dist_le p ((0, 0), z) δ (coreSegment τ) ⟨rfl, hz0, hzτ⟩
  simp only [Prod.dist_eq, Real.dist_eq, sub_zero, max_le_iff]
  exact ⟨⟨abs_le.mpr hp.1.1, abs_le.mpr hp.1.2⟩, hdist⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_disk_collar_of_arcPatternChart
    {S C F B β A : Set E} (hFS : F ⊆ S)
    {Φ : (ℝ × ℝ) × ℝ → E} {N : Set ((ℝ × ℝ) × ℝ)} {Ω : Set E} {τ : ℝ}
    (hN : IsOpen N) (hΩ : IsOpen Ω) (hΦ : IsPLHomeomorphOn Φ N (S ∩ Ω))
    (hτ : 0 < τ) (hcore : coreSegment τ ⊆ N) (hβ : Φ '' coreSegment τ = β)
    (hC : ∀ p ∈ N, Φ p ∈ C ↔ 0 ≤ p.1.2)
    (hF : ∀ p ∈ N, Φ p ∈ F ↔ p.1.2 = 0)
    (hB : ∀ p ∈ N, Φ p ∈ B ↔ p.1.1 = 0 ∧ 0 ≤ p.1.2 ∧ 0 ≤ p.2 ∧ p.2 ≤ τ)
    (hA : ∀ p ∈ N, p.1.1 = 0 → 0 ≤ p.1.2 → p.2 = 0 ∨ p.2 = τ → Φ p ∈ A) :
    ∃ (P W : Set E) (ρ : E × ℝ → E), IsPLBall 2 P ∧ P ⊆ F ∧
      P ∈ 𝓝ˢ[F] β ∧ W ⊆ C ∧ IsPLHomeomorphOn ρ (P ×ˢ Icc (0 : ℝ) 1) W ∧
      (∀ x ∈ P, ρ (x, 0) = x) ∧ W ∩ F = P ∧
      W ∩ B = ρ '' (β ×ˢ Icc (0 : ℝ) 1) ∧
      ρ '' ({Φ 0, Φ ((0, 0), τ)} ×ˢ Icc (0 : ℝ) 1) ⊆ A := by
  classical
  obtain ⟨δ, hδ, hboxN⟩ := exists_pos_box_subset_of_coreSegment_subset hN hτ hcore
  let J := Icc (-δ) δ ×ˢ Icc (-δ) (τ + δ)
  have hJ : IsPLBall 2 J := isPLBall_two_prod (isPLBall_Icc (by linarith))
    (isPLBall_Icc (by linarith))
  let e : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) × ℝ :=
    { toFun := fun u => ((u.1, 0), u.2)
      map_add' := by intro u v; ext <;> simp
      map_smul' := by intro t u; ext <;> simp }
  have he : IsPLHomeomorphOn e J (e '' J) := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hJ.isPolyhedron
      ((isPiecewiseAffineOn_of_affine e.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hJ.isPolyhedron (subset_univ _))
    apply InjOn.bijOn_image
    intro u _ v _ huv
    exact Prod.ext (congrArg (fun p => p.1.1) huv)
      (congrArg (fun p : (ℝ × ℝ) × ℝ => p.2) huv)
  have heN : e '' J ⊆ N := by
    rintro _ ⟨u, hu, rfl⟩
    exact hboxN ⟨⟨hu.1, by change -δ ≤ 0 ∧ 0 ≤ δ; constructor <;> linarith⟩, hu.2⟩
  have hepoly : IsPolyhedron (e '' J) := (hJ.of_isPLHomeomorphOn he).isPolyhedron
  let g := Φ ∘ e
  let P := g '' J
  have hg : IsPLHomeomorphOn g J P := by
    simpa only [g, P, image_comp] using he.trans (hΦ.restrict hepoly heN)
  have hP : IsPLBall 2 P := hJ.of_isPLHomeomorphOn hg
  have hPF : P ⊆ F := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hF (e u) (heN ⟨u, hu, rfl⟩)).mpr rfl
  let f : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] (ℝ × ℝ) × ℝ :=
    { toFun := fun q => ((q.1.1, δ * q.2), q.1.2)
      map_add' := by intro u v; ext <;> simp [mul_add]
      map_smul' := by intro t u; ext <;> simp [mul_left_comm] }
  let T := f '' (J ×ˢ Icc (0 : ℝ) 1)
  have hJI : IsPLBall 3 (J ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_three_prod hJ (isPLBall_Icc zero_lt_one)
  have hf : IsPLHomeomorphOn f (J ×ˢ Icc (0 : ℝ) 1) T := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hJI.isPolyhedron
      ((isPiecewiseAffineOn_of_affine f.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hJI.isPolyhedron (subset_univ _))
    apply InjOn.bijOn_image
    intro u _ v _ huv
    apply Prod.ext
    · exact Prod.ext (congrArg (fun p => p.1.1) huv)
        (congrArg (fun p : (ℝ × ℝ) × ℝ => p.2) huv)
    · exact mul_left_cancel₀ hδ.ne' (congrArg (fun p => p.1.2) huv)
  have hfN : T ⊆ N := by
    rintro _ ⟨q, hq, rfl⟩
    apply hboxN
    refine ⟨⟨hq.1.1, ?_⟩, hq.1.2⟩
    change -δ ≤ δ * q.2 ∧ δ * q.2 ≤ δ
    constructor
    · exact (by linarith : -δ ≤ 0).trans (mul_nonneg hδ.le hq.2.1)
    · nlinarith [hq.2.2]
  have hT : IsPLBall 3 T := hJI.of_isPLHomeomorphOn hf
  let W := Φ '' T
  have hΦT : IsPLHomeomorphOn Φ T W := hΦ.restrict hT.isPolyhedron hfN
  let ρ : E × ℝ → E := fun q => Φ (f (Function.invFunOn g J q.1, q.2))
  have hρ : IsPLHomeomorphOn ρ (P ×ˢ Icc (0 : ℝ) 1) W :=
    ((hg.symm.prodMap (isPLBall_Icc zero_lt_one).isPolyhedron.isPLHomeomorphOn_id).trans hf)
      |>.trans hΦT
  have hformula (u : ℝ × ℝ) (hu : u ∈ J) (t : ℝ) :
      ρ (g u, t) = Φ ((u.1, δ * t), u.2) := by
    dsimp [ρ]
    rw [hg.bijOn.injOn.leftInvOn_invFunOn hu]
    rfl
  have hbottom : ∀ x ∈ P, ρ (x, 0) = x := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hformula u hu]
    simp only [mul_zero]
    rfl
  have hWC : W ⊆ C := by
    rintro _ ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    apply (hC (f q) (hfN ⟨q, hq, rfl⟩)).mpr
    exact mul_nonneg hδ.le hq.2.1
  have hWF : W ∩ F = P := by
    apply Subset.antisymm
    · rintro x ⟨⟨p, ⟨q, hq, rfl⟩, rfl⟩, hxF⟩
      have hz : δ * q.2 = 0 := (hF (f q) (hfN ⟨q, hq, rfl⟩)).mp hxF
      have hq2 : q.2 = 0 := (mul_eq_zero.mp hz).resolve_left hδ.ne'
      refine ⟨q.1, hq.1, ?_⟩
      change Φ (e q.1) = Φ (f q)
      congr 1
      ext <;> simp [e, f, hq2]
    · intro x hx
      exact ⟨hbottom x hx ▸ hρ.bijOn.mapsTo ⟨hx, le_rfl, zero_le_one⟩, hPF hx⟩
  have hcoreJ (z : ℝ) (hz : z ∈ Icc (0 : ℝ) τ) : (0, z) ∈ J :=
    ⟨⟨by linarith, hδ.le⟩, by constructor <;> linarith [hz.1, hz.2]⟩
  have hβP : β ⊆ P := by
    rw [← hβ]
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨(0, p.2), hcoreJ p.2 hp.2, ?_⟩
    apply congrArg Φ
    exact Prod.ext (Prod.mk_zero_zero.trans hp.1.symm) rfl
  have hWB : W ∩ B = ρ '' (β ×ˢ Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro x ⟨⟨p, ⟨q, hq, rfl⟩, rfl⟩, hxB⟩
      have hqB := (hB (f q) (hfN ⟨q, hq, rfl⟩)).mp hxB
      have hu : q.1.1 = 0 := hqB.1
      refine ⟨(g q.1, q.2), ⟨?_, hq.2⟩, ?_⟩
      · rw [← hβ]
        exact ⟨e q.1, ⟨by ext <;> simp [e, hu], hqB.2.2⟩, rfl⟩
      · exact hformula q.1 hq.1 q.2
    · rintro x ⟨q, hq, rfl⟩
      refine ⟨hρ.bijOn.mapsTo ⟨hβP hq.1, hq.2⟩, ?_⟩
      obtain ⟨p, hp, hpq⟩ := hβ.symm.subset hq.1
      have heq : g (0, p.2) = q.1 := by
        rw [← hpq]
        apply congrArg Φ
        exact Prod.ext (Prod.mk_zero_zero.trans hp.1.symm) rfl
      change ρ (q.1, q.2) ∈ B
      rw [← heq, hformula (0, p.2) (hcoreJ p.2 hp.2)]
      have hm := hfN ⟨((0, p.2), q.2), ⟨hcoreJ p.2 hp.2, hq.2⟩, rfl⟩
      exact (hB _ hm).mpr ⟨rfl, mul_nonneg hδ.le hq.2.1, hp.2⟩
  have hends : ρ '' ({Φ 0, Φ ((0, 0), τ)} ×ˢ Icc (0 : ℝ) 1) ⊆ A := by
    rintro x ⟨q, hq, rfl⟩
    have hline (z : ℝ) (hz : z = 0 ∨ z = τ) : ρ (Φ ((0, 0), z), q.2) ∈ A := by
      have hzI : z ∈ Icc (0 : ℝ) τ := by
        rcases hz with rfl | rfl <;> constructor <;> linarith
      change ρ (g (0, z), q.2) ∈ A
      rw [hformula (0, z) (hcoreJ z hzI)]
      exact hA _ (hfN ⟨((0, z), q.2), ⟨hcoreJ z hzI, hq.2⟩, rfl⟩)
        rfl (mul_nonneg hδ.le hq.2.1) hz
    rcases hq.1 with hq0 | hqτ
    · rw [show q = (Φ 0, q.2) from Prod.ext hq0 rfl]
      exact hline 0 (Or.inl rfl)
    · rw [show q = (Φ ((0, 0), τ), q.2) from Prod.ext hqτ rfl]
      exact hline τ (Or.inr rfl)
  let O := (Ioo (-δ) δ ×ˢ Ioo (-δ) δ) ×ˢ Ioo (-δ) (τ + δ)
  have hO : IsOpen O := (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo
  obtain ⟨U, hU, hUeq⟩ := hΦ.exists_image_eq_inter hO
  have hβU : β ⊆ Ω ∩ U := by
    rw [← hβ]
    rintro _ ⟨p, hp, rfl⟩
    have hp0 : p.1 = (0, 0) := hp.1
    have hpO : p ∈ O := by
      refine ⟨?_, ?_⟩
      · rw [hp0]
        constructor <;> constructor <;> linarith
      · constructor <;> linarith [hp.2.1, hp.2.2]
    exact (hUeq.subset ⟨p, ⟨hcore hp, hpO⟩, rfl⟩).2
  have hUP : (Ω ∩ U) ∩ F ⊆ P := by
    rintro x ⟨hxU, hxF⟩
    obtain ⟨p, hp, rfl⟩ := hUeq.symm.subset ⟨hFS hxF, hxU⟩
    have hp0 := (hF p hp.1).mp hxF
    refine ⟨(p.1.1, p.2), ⟨Ioo_subset_Icc_self hp.2.1.1,
      Ioo_subset_Icc_self hp.2.2⟩, ?_⟩
    apply congrArg Φ
    exact Prod.ext (Prod.ext rfl hp0.symm) rfl
  exact ⟨P, W, ρ, hP, hPF, mem_nhdsSetWithin.mpr ⟨Ω ∩ U, hΩ.inter hU, hβU, hUP⟩,
    hWC, hρ, hbottom, hWF, hWB, hends⟩

end DifferentialGeometry.Topology.PiecewiseLinear
