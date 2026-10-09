/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.Boundary.DefiningCollar
import DifferentialGeometry.Topology.Manifold.Boundary.SmoothMap
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.OneHandleModelAttachment
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.SmoothEmbedding

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem exists_diffeomorph_boundary_of_isSmoothEmbedding_plane
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] (f : EuclideanSpace ℝ (Fin 2) → M)
    (hf : IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ f) (hfbd : range f ⊆ (𝓡∂ 3).boundary M) :
    ∃ (fB : EuclideanSpace ℝ (Fin 2) → BoundaryManifold (𝓡∂ 3) M)
      (g : BoundaryManifold (𝓡∂ 3) M → EuclideanSpace ℝ (Fin 2))
      (Vb : TopologicalSpace.Opens (BoundaryManifold (𝓡∂ 3) M)),
      (∀ w, (fB w : M) = f w) ∧ (Vb : Set (BoundaryManifold (𝓡∂ 3) M)) = range fB ∧
      (∀ w, g (fB w) = w) ∧
      ContMDiff (𝓡 2) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ fB ∧
      (∀ S : Set (EuclideanSpace ℝ (Fin 2)), IsOpen S → IsOpen (fB '' S)) ∧
      ∀ b ∈ Vb, ContMDiffAt (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡 2) ∞ g b := by
  classical
  let B := BoundaryManifold (𝓡∂ 3) M
  let fB : EuclideanSpace ℝ (Fin 2) → B := fun x => ⟨f x, hfbd ⟨x, rfl⟩⟩
  have hfBs : ContMDiff (𝓡 2) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ fB :=
    (DifferentialGeometry.Manifold.Boundary.contMDiff_boundary_iff le_rfl).mpr hf.contMDiff
  have hfBinj : Function.Injective fB := fun x y h =>
    hf.isEmbedding.injective (congrArg Subtype.val h)
  have hincl : ContMDiff (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡∂ 3) ∞
      (boundaryInclusion (𝓡∂ 3) M) := boundaryInclusion_contMDiff
  have hmf : ∀ x, Function.Injective (mfderiv (𝓡 2)
      (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) fB x) := by
    intro x v w hvw
    have h1 := DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
      (𝓡 2) (𝓡∂ 3) f x (hf.isImmersion.isImmersionAt x)
    have hcomp : mfderiv (𝓡 2) (𝓡∂ 3) (boundaryInclusion (𝓡∂ 3) M ∘ fB) x =
        (mfderiv (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡∂ 3)
          (boundaryInclusion (𝓡∂ 3) M) (fB x)).comp
          (mfderiv (𝓡 2) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) fB x) :=
      mfderiv_comp x ((hincl (fB x)).mdifferentiableAt (by simp))
        ((hfBs x).mdifferentiableAt (by simp))
    change Function.Injective (mfderiv (𝓡 2) (𝓡∂ 3) (boundaryInclusion (𝓡∂ 3) M ∘ fB) x) at h1
    rw [hcomp, ContinuousLinearMap.coe_comp] at h1
    exact h1.of_comp hvw
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) =
      Module.finrank ℝ (HasSmoothBoundary.boundaryE (I := 𝓡∂ 3)) := by
    have h := HasSmoothBoundary.finrank_boundaryE_succ (I := 𝓡∂ 3)
    simp only [finrank_euclideanSpace, Fintype.card_fin] at h ⊢
    omega
  obtain ⟨Vb, Φ, hVb, hΦ, -⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_onto_range_of_injective_immersion
      fB hfBs hfBinj hmf hdim
  let g : B → EuclideanSpace ℝ (Fin 2) := fun b => if h : b ∈ Vb then Φ.symm ⟨b, h⟩ else 0
  have hfBV : ∀ x, fB x ∈ Vb := fun x => by
    rw [← SetLike.mem_coe, hVb]
    exact ⟨x, rfl⟩
  refine ⟨fB, g, Vb, fun w => rfl, hVb, fun x => ?_, hfBs, fun S hS => ?_, fun b hb => ?_⟩
  · have hΦx : Φ x = ⟨fB x, hfBV x⟩ := Subtype.ext (hΦ x)
    simp only [g, dite_eq_left (hfBV x), ← hΦx, Diffeomorph.symm_apply_apply]
  · have heq : fB '' S = Subtype.val '' (Φ '' S) := by
      ext b
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨Φ x, ⟨x, hx, rfl⟩, hΦ x⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, (hΦ x).symm⟩
    rw [heq]
    exact Vb.isOpen.isOpenMap_subtype_val _ (Φ.toHomeomorph.isOpenMap _ hS)
  · have hres : (fun x : Vb => g x) = Φ.symm := by
      funext x
      simp only [g, dite_eq_left x.2]
    have h := Φ.symm.contMDiff ⟨b, hb⟩
    rw [← hres] at h
    exact contMDiffAt_subtype_iff.mp h

theorem exists_oneHandleCollar_of_isSmoothEmbedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    (F : Fin 2 → EuclideanSpace ℝ (Fin 2) → M)
    (hF : ∀ j, IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (F j))
    (hFbd : ∀ j, range (F j) ⊆ (𝓡∂ 3).boundary M)
    (hdisj : Disjoint (range (F 0)) (range (F 1))) :
    ∃ (a : ℝ) (V : Set M) (θ : M → EuclideanSpace ℝ (Fin 2) × ℝ)
      (Θ : EuclideanSpace ℝ (Fin 2) × ℝ → M),
      0 < a ∧ a ≤ 1 / 2 ∧ IsOpen V ∧ MapsTo θ V (oneHandleCollar a) ∧
      MapsTo Θ (oneHandleCollar a) V ∧ (∀ m ∈ V, Θ (θ m) = m) ∧
      (∀ p ∈ oneHandleCollar a, θ (Θ p) = p) ∧
      (∀ w, Θ (w, -1) = F 0 w) ∧ (∀ w, Θ (w, 1) = F 1 w) ∧
      ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ θ V ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 3) ∞ Θ (oneHandleCollar a) := by
  classical
  obtain ⟨r, -, -, -, a₀, ha₀, c, hc, hcs, hc0, -, -, Y, -, dc, hdc⟩ :=
    DifferentialGeometry.Manifold.Boundary.exists_definingFunction_sublevel_collar
      (n := 2) (M := M)
  let _ : Fact ((0 : ℝ) < a₀) := ⟨ha₀⟩
  let B := BoundaryManifold (𝓡∂ 3) M
  obtain ⟨f₀, g₀, W₀, hf₀, hW₀, hg₀, hf₀s, hf₀o, hg₀s⟩ :=
    exists_diffeomorph_boundary_of_isSmoothEmbedding_plane (F 0) (hF 0) (hFbd 0)
  obtain ⟨f₁, g₁, W₁, hf₁, hW₁, hg₁, hf₁s, hf₁o, hg₁s⟩ :=
    exists_diffeomorph_boundary_of_isSmoothEmbedding_plane (F 1) (hF 1) (hFbd 1)
  have hf₀W : ∀ w, f₀ w ∈ W₀ := fun w => by
    rw [← SetLike.mem_coe, hW₀]
    exact ⟨w, rfl⟩
  have hf₁W : ∀ w, f₁ w ∈ W₁ := fun w => by
    rw [← SetLike.mem_coe, hW₁]
    exact ⟨w, rfl⟩
  have hf₁W₀ : ∀ w, f₁ w ∉ W₀ := by
    intro w hw
    rw [← SetLike.mem_coe, hW₀] at hw
    obtain ⟨v, hv⟩ := hw
    have h1 : (f₀ v : M) = (f₁ w : M) := congrArg Subtype.val hv
    rw [hf₀, hf₁] at h1
    exact hdisj.ne_of_mem ⟨v, rfl⟩ ⟨w, rfl⟩ h1
  let a : ℝ := min a₀ (1 / 2)
  have ha : 0 < a := lt_min ha₀ (by norm_num)
  have haa : a ≤ a₀ := min_le_left _ _
  have ha2 : a ≤ 1 / 2 := min_le_right _ _
  let G : B × Icc (0 : ℝ) a₀ → EuclideanSpace ℝ (Fin 2) × ℝ := fun q =>
    if q.1 ∈ W₀ then (g₀ q.1, -1 - (q.2 : ℝ)) else (g₁ q.1, 1 + (q.2 : ℝ))
  have hGs : ∀ q : B × Icc (0 : ℝ) a₀, q.1 ∈ W₀ ∨ q.1 ∈ W₁ →
      ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ G q := by
    intro q hq
    have ht : ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
        (fun q : B × Icc (0 : ℝ) a₀ => (q.2 : ℝ)) q :=
      (contMDiff_subtypeVal_Icc.comp contMDiff_snd).contMDiffAt
    rcases hq with hq | hq
    · have h1 : ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
          (fun q : B × Icc (0 : ℝ) a₀ => (g₀ q.1, -1 - (q.2 : ℝ))) q :=
        ((hg₀s q.1 hq).comp q contMDiffAt_fst).prodMk_space (contMDiffAt_const.sub ht)
      apply h1.congr_of_eventuallyEq
      have hn : {q : B × Icc (0 : ℝ) a₀ | q.1 ∈ W₀} ∈ 𝓝 q :=
        (W₀.isOpen.preimage continuous_fst).mem_nhds hq
      filter_upwards [hn] with q' hq'
      simp only [G, ite_eq_left (show q'.1 ∈ W₀ from hq')]
    · have hq0 : q.1 ∉ W₀ := by
        rw [← SetLike.mem_coe, hW₁] at hq
        obtain ⟨w, hw⟩ := hq
        rw [← hw]
        exact hf₁W₀ w
      have h1 : ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
          (fun q : B × Icc (0 : ℝ) a₀ => (g₁ q.1, 1 + (q.2 : ℝ))) q :=
        ((hg₁s q.1 hq).comp q contMDiffAt_fst).prodMk_space (contMDiffAt_const.add ht)
      apply h1.congr_of_eventuallyEq
      have hn : {q : B × Icc (0 : ℝ) a₀ | q.1 ∈ W₁} ∈ 𝓝 q :=
        (W₁.isOpen.preimage continuous_fst).mem_nhds hq
      filter_upwards [hn] with q' hq'
      have hq'0 : q'.1 ∉ W₀ := by
        have hq'' : q'.1 ∈ (W₁ : Set B) := hq'
        rw [hW₁] at hq''
        obtain ⟨w, hw⟩ := hq''
        rw [← hw]
        exact hf₁W₀ w
      simp only [G, ite_eq_right hq'0]
  let θ : M → EuclideanSpace ℝ (Fin 2) × ℝ :=
    fun m => if h : m ∈ Y then G (dc.symm ⟨m, h⟩).val else 0
  let Θ : EuclideanSpace ℝ (Fin 2) × ℝ → M := fun p =>
    if p.2 < 0 then c (f₀ p.1, projIcc 0 a₀ ha₀.le (-1 - p.2))
    else c (f₁ p.1, projIcc 0 a₀ ha₀.le (p.2 - 1))
  let D : Set B := f₀ '' Metric.ball 0 (3 / 2) ∪ f₁ '' Metric.ball 0 (3 / 2)
  let V : Set M := c '' {q | q.1 ∈ D ∧ (q.2 : ℝ) < a}
  have hcU : ∀ q : B × Icc (0 : ℝ) a₀, ∀ hq : (q.2 : ℝ) < a₀,
      ∃ hY : c q ∈ Y, dc.symm ⟨c q, hY⟩ = ⟨q, hq⟩ := by
    intro q hq
    have h := hdc ⟨q, hq⟩
    refine ⟨h ▸ (dc ⟨q, hq⟩).2, ?_⟩
    have he : (⟨c q, h ▸ (dc ⟨q, hq⟩).2⟩ : Y) = dc ⟨q, hq⟩ := Subtype.ext h.symm
    rw [he, Diffeomorph.symm_apply_apply]
  have hθc : ∀ q : B × Icc (0 : ℝ) a₀, (q.2 : ℝ) < a₀ → θ (c q) = G q := by
    intro q hq
    obtain ⟨hY, hsymm⟩ := hcU q hq
    simp only [θ, dite_eq_left hY, hsymm]
  have hG0 : ∀ w (t : Icc (0 : ℝ) a₀), G (f₀ w, t) = (w, -1 - (t : ℝ)) := by
    intro w t
    simp only [G, ite_eq_left (hf₀W w), hg₀]
  have hG1 : ∀ w (t : Icc (0 : ℝ) a₀), G (f₁ w, t) = (w, 1 + (t : ℝ)) := by
    intro w t
    simp only [G, ite_eq_right (hf₁W₀ w), hg₁]
  have hΘ0 : ∀ p : EuclideanSpace ℝ (Fin 2) × ℝ, p.2 < 0 →
      Θ p = c (f₀ p.1, projIcc 0 a₀ ha₀.le (-1 - p.2)) := fun p hp => ite_eq_left hp
  have hΘ1 : ∀ p : EuclideanSpace ℝ (Fin 2) × ℝ, ¬ p.2 < 0 →
      Θ p = c (f₁ p.1, projIcc 0 a₀ ha₀.le (p.2 - 1)) := fun p hp => ite_eq_right hp
  have hproj : ∀ x : ℝ, 0 ≤ x → x < a → (projIcc 0 a₀ ha₀.le x : ℝ) = x := by
    intro x h1 h2
    rw [projIcc_of_mem]
    exact ⟨h1, by linarith⟩
  refine ⟨a, V, θ, Θ, ha, ha2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hD : IsOpen D := (hf₀o _ Metric.isOpen_ball).union (hf₁o _ Metric.isOpen_ball)
    have hVeq : V = Subtype.val '' (dc '' {p | p.val.1 ∈ D ∧ (p.val.2 : ℝ) < a}) := by
      ext m
      constructor
      · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
        have hqa : (q.2 : ℝ) < a₀ := lt_of_lt_of_le hq2 haa
        exact ⟨dc ⟨q, hqa⟩, ⟨⟨q, hqa⟩, ⟨hq1, hq2⟩, rfl⟩, hdc _⟩
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p.val, hp, (hdc p).symm⟩
    rw [hVeq]
    exact Y.isOpen.isOpenMap_subtype_val _ (dc.toHomeomorph.isOpenMap _
      ((hD.preimage (continuous_fst.comp continuous_subtype_val)).inter
        (isOpen_lt (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
          continuous_const)))
  · rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    rw [hθc q (lt_of_lt_of_le hq2 haa)]
    have hq0 : (0 : ℝ) ≤ q.2 := q.2.2.1
    rcases hq1 with ⟨w, hw, hwq⟩ | ⟨w, hw, hwq⟩
    · have hq : q = (f₀ w, q.2) := Prod.ext hwq.symm rfl
      rw [hq, hG0]
      refine ⟨mem_ball_zero_iff.mp hw, Or.inl ⟨by linarith, by linarith⟩⟩
    · have hq : q = (f₁ w, q.2) := Prod.ext hwq.symm rfl
      rw [hq, hG1]
      refine ⟨mem_ball_zero_iff.mp hw, Or.inr ⟨by linarith, by linarith⟩⟩
  · rintro p ⟨h1, h2⟩
    rcases h2 with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · rw [hΘ0 p (by linarith)]
      refine ⟨(f₀ p.1, projIcc 0 a₀ ha₀.le (-1 - p.2)), ⟨Or.inl ⟨p.1, ?_, rfl⟩, ?_⟩, rfl⟩
      · exact mem_ball_zero_iff.mpr h1
      · rw [hproj _ (by linarith) (by linarith)]
        linarith
    · rw [hΘ1 p (by linarith)]
      refine ⟨(f₁ p.1, projIcc 0 a₀ ha₀.le (p.2 - 1)), ⟨Or.inr ⟨p.1, ?_, rfl⟩, ?_⟩, rfl⟩
      · exact mem_ball_zero_iff.mpr h1
      · rw [hproj _ (by linarith) (by linarith)]
        linarith
  · rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    rw [hθc q (lt_of_lt_of_le hq2 haa)]
    have hq0 : (0 : ℝ) ≤ q.2 := q.2.2.1
    rcases hq1 with ⟨w, -, hwq⟩ | ⟨w, -, hwq⟩
    · have hq : q = (f₀ w, q.2) := Prod.ext hwq.symm rfl
      rw [hq, hG0, hΘ0 _ (by change -1 - (q.2 : ℝ) < 0; linarith)]
      congr 2
      apply Subtype.ext
      rw [hproj _ (by linarith) (by linarith)]
      ring
    · have hq : q = (f₁ w, q.2) := Prod.ext hwq.symm rfl
      rw [hq, hG1, hΘ1 _ (by change ¬ (1 + (q.2 : ℝ) < 0); linarith)]
      congr 2
      apply Subtype.ext
      rw [hproj _ (by linarith) (by linarith)]
      ring
  · rintro p ⟨h1, h2⟩
    rcases h2 with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · rw [hΘ0 p (by linarith)]
      have hq : ((f₀ p.1, projIcc 0 a₀ ha₀.le (-1 - p.2)) : B × Icc (0 : ℝ) a₀).2.val < a₀ := by
        change (projIcc 0 a₀ ha₀.le (-1 - p.2) : ℝ) < a₀
        rw [hproj _ (by linarith) (by linarith)]
        linarith
      rw [hθc _ hq, hG0, hproj _ (by linarith) (by linarith)]
      ext
      · rfl
      · change -1 - (-1 - p.2) = p.2
        ring
    · rw [hΘ1 p (by linarith)]
      have hq : ((f₁ p.1, projIcc 0 a₀ ha₀.le (p.2 - 1)) : B × Icc (0 : ℝ) a₀).2.val < a₀ := by
        change (projIcc 0 a₀ ha₀.le (p.2 - 1) : ℝ) < a₀
        rw [hproj _ (by linarith) (by linarith)]
        linarith
      rw [hθc _ hq, hG1, hproj _ (by linarith) (by linarith)]
      ext
      · rfl
      · change 1 + (p.2 - 1) = p.2
        ring
  · intro w
    rw [hΘ0 _ (by norm_num)]
    change c (f₀ w, projIcc 0 a₀ ha₀.le (-1 - -1)) = F 0 w
    rw [sub_neg_eq_add, neg_add_cancel, projIcc_left, hc0, hf₀]
  · intro w
    rw [hΘ1 _ (by norm_num)]
    change c (f₁ w, projIcc 0 a₀ ha₀.le (1 - 1)) = F 1 w
    rw [sub_self, projIcc_left, hc0, hf₁]
  · intro m hm
    obtain ⟨q, ⟨hq1, hq2⟩, rfl⟩ := hm
    have hqa : (q.2 : ℝ) < a₀ := lt_of_lt_of_le hq2 haa
    obtain ⟨hY, hsymm⟩ := hcU q hqa
    have hqW : q.1 ∈ W₀ ∨ q.1 ∈ W₁ := by
      rcases hq1 with ⟨w, -, hwq⟩ | ⟨w, -, hwq⟩
      · rw [← hwq]
        exact Or.inl (hf₀W w)
      · rw [← hwq]
        exact Or.inr (hf₁W w)
    apply ContMDiffAt.contMDiffWithinAt
    have hres : (fun x : Y => θ x) = G ∘ Subtype.val ∘ dc.symm := by
      funext x
      simp only [θ, dite_eq_left x.2, Function.comp_apply]
    have h : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ (fun x : Y => θ x)
        ⟨c q, hY⟩ := by
      rw [hres]
      have hq : (dc.symm ⟨c q, hY⟩).val = q := by rw [hsymm]
      refine ContMDiffAt.comp (I' := (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1))
        _ ?_ (contMDiff_subtype_val.contMDiffAt.comp _ (dc.symm.contMDiff _))
      rw [Function.comp_apply, hq]
      exact hGs q hqW
    exact contMDiffAt_subtype_iff.mp h
  · intro p hp
    obtain ⟨h1, h2⟩ := hp
    have hfst : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => p.1) := contDiff_fst.contMDiff
    rcases h2 with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · have hN : {p : EuclideanSpace ℝ (Fin 2) × ℝ | p.2 < 0} ∈ 𝓝 p :=
        (isOpen_lt continuous_snd continuous_const).mem_nhds (by change p.2 < 0; linarith)
      have hsl' : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => -1 - p.2) :=
        contDiff_const.sub contDiff_snd
      have hpr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 1) ∞
          (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => projIcc 0 a₀ ha₀.le (-1 - p.2))
          (oneHandleCollar a ∩ {p | p.2 < 0}) := by
        refine contMDiffOn_projIcc.comp hsl'.contMDiff.contMDiffOn fun q hq => ?_
        obtain ⟨-, hq2⟩ := hq.1
        rcases hq2 with ⟨hq2, hq3⟩ | ⟨hq2, -⟩
        · exact ⟨by linarith, by linarith⟩
        · exfalso
          have := hq.2
          change q.2 < 0 at this
          linarith
      have hG : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 3) ∞
          (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => c (f₀ p.1, projIcc 0 a₀ ha₀.le (-1 - p.2)))
          (oneHandleCollar a ∩ {p | p.2 < 0}) :=
        hcs.comp_contMDiffOn ((hf₀s.comp hfst).contMDiffOn.prodMk hpr)
      have hW : ContMDiffWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 3) ∞ Θ
          (oneHandleCollar a ∩ {p | p.2 < 0}) p := by
        refine (hG p ⟨⟨h1, Or.inl ⟨h2, h3⟩⟩, by change p.2 < 0; linarith⟩).congr
          (fun q hq => hΘ0 q hq.2) (hΘ0 p (by linarith))
      exact (contMDiffWithinAt_inter hN).mp hW
    · have hN : {p : EuclideanSpace ℝ (Fin 2) × ℝ | ¬ p.2 < 0} ∈ 𝓝 p := by
        have ho : IsOpen {p : EuclideanSpace ℝ (Fin 2) × ℝ | 0 < p.2} :=
          isOpen_lt continuous_const continuous_snd
        exact Filter.mem_of_superset (ho.mem_nhds (by change 0 < p.2; linarith))
          fun q hq => not_lt.mpr (le_of_lt hq)
      have hsl' : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => p.2 - 1) :=
        contDiff_snd.sub contDiff_const
      have hpr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 1) ∞
          (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => projIcc 0 a₀ ha₀.le (p.2 - 1))
          (oneHandleCollar a ∩ {p | ¬ p.2 < 0}) := by
        refine contMDiffOn_projIcc.comp hsl'.contMDiff.contMDiffOn fun q hq => ?_
        obtain ⟨-, hq2⟩ := hq.1
        rcases hq2 with ⟨-, hq3⟩ | ⟨hq2, hq3⟩
        · exfalso
          have := hq.2
          change ¬ q.2 < 0 at this
          linarith
        · exact ⟨by linarith, by linarith⟩
      have hG : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 3) ∞
          (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => c (f₁ p.1, projIcc 0 a₀ ha₀.le (p.2 - 1)))
          (oneHandleCollar a ∩ {p | ¬ p.2 < 0}) :=
        hcs.comp_contMDiffOn ((hf₁s.comp hfst).contMDiffOn.prodMk hpr)
      have hW : ContMDiffWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 3) ∞ Θ
          (oneHandleCollar a ∩ {p | ¬ p.2 < 0}) p := by
        refine (hG p ⟨⟨h1, Or.inr ⟨h2, h3⟩⟩, by change ¬ p.2 < 0; linarith⟩).congr
          (fun q hq => hΘ1 q hq.2) (hΘ1 p (by linarith))
      exact (contMDiffWithinAt_inter hN).mp hW

end DifferentialGeometry.Topology.PiecewiseLinear
