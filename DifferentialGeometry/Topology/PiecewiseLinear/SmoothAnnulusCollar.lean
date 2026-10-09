/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Manifold.Boundary.DefiningCollar
import DifferentialGeometry.Topology.Manifold.Boundary.SmoothMap
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.SphereDirection
import DifferentialGeometry.Topology.PiecewiseLinear.TwoHandleModelAttachment
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.SmoothEmbedding

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Topology.Manifold (sphereDirection sphereDirection_pos_smul
  norm_smul_sphereDirection contMDiffOn_sphereDirection)

theorem exists_twoHandleCollar_of_isSmoothEmbedding
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × ℝ → M)
    (hf : IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞ f)
    (hfbd : range f ⊆ (𝓡∂ 3).boundary M) :
    ∃ (a : ℝ) (V : Set M) (θ : M → EuclideanSpace ℝ (Fin 2) × ℝ)
      (Θ : EuclideanSpace ℝ (Fin 2) × ℝ → M),
      0 < a ∧ a ≤ 1 / 2 ∧ IsOpen V ∧ MapsTo θ V (twoHandleCollar a) ∧
      MapsTo Θ (twoHandleCollar a) V ∧ (∀ m ∈ V, Θ (θ m) = m) ∧
      (∀ p ∈ twoHandleCollar a, θ (Θ p) = p) ∧
      (∀ (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (s : ℝ),
        Θ ((u : EuclideanSpace ℝ (Fin 2)), s) = f (u, (s + 1) / 2)) ∧
      ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ θ V ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 3) ∞ Θ (twoHandleCollar a) := by
  classical
  obtain ⟨r, -, -, -, a₀, ha₀, c, hc, hcs, hc0, -, -, Y, -, dc, hdc⟩ :=
    DifferentialGeometry.Manifold.Boundary.exists_definingFunction_sublevel_collar
      (n := 2) (M := M)
  let _ : Fact ((0 : ℝ) < a₀) := ⟨ha₀⟩
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩
  let B := BoundaryManifold (𝓡∂ 3) M
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let fB : S × ℝ → B := fun x => ⟨f x, hfbd ⟨x, rfl⟩⟩
  have hfBs : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ fB :=
    (DifferentialGeometry.Manifold.Boundary.contMDiff_boundary_iff le_rfl).mpr hf.contMDiff
  have hfBinj : Function.Injective fB := fun x y h =>
    hf.isEmbedding.injective (congrArg Subtype.val h)
  have hincl : ContMDiff (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡∂ 3) ∞
      (boundaryInclusion (𝓡∂ 3) M) := boundaryInclusion_contMDiff
  have hmf : ∀ x, Function.Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ))
      (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) fB x) := by
    intro x v w hvw
    have h1 := DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
      ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) f x (hf.isImmersion.isImmersionAt x)
    have hcomp : mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) (boundaryInclusion (𝓡∂ 3) M ∘ fB) x =
        (mfderiv (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡∂ 3)
          (boundaryInclusion (𝓡∂ 3) M) (fB x)).comp
          (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) fB x) :=
      mfderiv_comp x ((hincl (fB x)).mdifferentiableAt (by simp))
        ((hfBs x).mdifferentiableAt (by simp))
    change Function.Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3)
      (boundaryInclusion (𝓡∂ 3) M ∘ fB) x) at h1
    rw [hcomp, ContinuousLinearMap.coe_comp] at h1
    exact h1.of_comp hvw
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × ℝ) =
      Module.finrank ℝ (HasSmoothBoundary.boundaryE (I := 𝓡∂ 3)) := by
    have h := HasSmoothBoundary.finrank_boundaryE_succ (I := 𝓡∂ 3)
    simp only [finrank_euclideanSpace, Fintype.card_fin] at h
    rw [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin, Module.finrank_self]
    omega
  obtain ⟨Vb, Φ, hVb, hΦ, -⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_onto_range_of_injective_immersion
      fB hfBs hfBinj hmf hdim
  obtain ⟨u₀, hu₀⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let s₀ : S := ⟨u₀, hu₀⟩
  let g : B → S × ℝ := fun b => if h : b ∈ Vb then Φ.symm ⟨b, h⟩ else (s₀, 0)
  have hfBV : ∀ x, fB x ∈ Vb := fun x => by
    rw [← SetLike.mem_coe, hVb]
    exact ⟨x, rfl⟩
  have hg : ∀ x, g (fB x) = x := by
    intro x
    have hΦx : Φ x = ⟨fB x, hfBV x⟩ := Subtype.ext (hΦ x)
    simp only [g, dite_eq_left (hfBV x), ← hΦx, Diffeomorph.symm_apply_apply]
  have hgs : ∀ b ∈ Vb, ContMDiffAt (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3))
      ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ g b := by
    intro b hb
    have hres : (fun x : Vb => g x) = Φ.symm := by
      funext x
      simp only [g, dite_eq_left x.2]
    have h := Φ.symm.contMDiff ⟨b, hb⟩
    rw [← hres] at h
    exact contMDiffAt_subtype_iff.mp h
  let a : ℝ := min a₀ (1 / 2)
  have ha : 0 < a := lt_min ha₀ (by norm_num)
  have haa : a ≤ a₀ := min_le_left _ _
  have ha2 : a ≤ 1 / 2 := min_le_right _ _
  let F : B × Icc (0 : ℝ) a₀ → EuclideanSpace ℝ (Fin 2) × ℝ :=
    fun q => ((1 + (q.2 : ℝ)) • ((g q.1).1 : EuclideanSpace ℝ (Fin 2)), 2 * (g q.1).2 - 1)
  have hFs : ∀ q : B × Icc (0 : ℝ) a₀, q.1 ∈ Vb →
      ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ F q := by
    intro q hq
    have hgq : ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1))
        ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ (fun q : B × Icc (0 : ℝ) a₀ => g q.1) q :=
      (hgs q.1 hq).comp q contMDiffAt_fst
    have h1 : ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1)) 𝓘(ℝ)
        ∞ (fun q : B × Icc (0 : ℝ) a₀ => 1 + (q.2 : ℝ)) q :=
      contMDiffAt_const.add (contMDiff_subtypeVal_Icc.comp contMDiff_snd).contMDiffAt
    have h2 : ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun q : B × Icc (0 : ℝ) a₀ => ((g q.1).1 : EuclideanSpace ℝ (Fin 2))) q :=
      contMDiff_coe_sphere.contMDiffAt.comp q (contMDiffAt_fst.comp q hgq)
    have h3 : ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1)) 𝓘(ℝ)
        ∞ (fun q : B × Icc (0 : ℝ) a₀ => 2 * (g q.1).2 - 1) q :=
      (contMDiffAt_const.mul (contMDiffAt_snd.comp q hgq)).sub contMDiffAt_const
    exact (h1.smul h2).prodMk_space h3
  let θ : M → EuclideanSpace ℝ (Fin 2) × ℝ :=
    fun m => if h : m ∈ Y then F (dc.symm ⟨m, h⟩).val else 0
  let Θ : EuclideanSpace ℝ (Fin 2) × ℝ → M :=
    fun p => c (fB (sphereDirection s₀ p.1, (p.2 + 1) / 2), projIcc 0 a₀ ha₀.le (‖p.1‖ - 1))
  let Vb' : Set B := fB '' (univ ×ˢ Ioo (-(1 / 4)) (5 / 4))
  let V : Set M := c '' {q | q.1 ∈ Vb' ∧ (q.2 : ℝ) < a}
  have hcU : ∀ q : B × Icc (0 : ℝ) a₀, ∀ hq : (q.2 : ℝ) < a₀,
      ∃ hY : c q ∈ Y, dc.symm ⟨c q, hY⟩ = ⟨q, hq⟩ := by
    intro q hq
    have h := hdc ⟨q, hq⟩
    refine ⟨h ▸ (dc ⟨q, hq⟩).2, ?_⟩
    have he : (⟨c q, h ▸ (dc ⟨q, hq⟩).2⟩ : Y) = dc ⟨q, hq⟩ := Subtype.ext h.symm
    rw [he, Diffeomorph.symm_apply_apply]
  have hθc : ∀ q : B × Icc (0 : ℝ) a₀, (q.2 : ℝ) < a₀ → θ (c q) = F q := by
    intro q hq
    obtain ⟨hY, hsymm⟩ := hcU q hq
    simp only [θ, dite_eq_left hY, hsymm]
  have hproj : ∀ p : EuclideanSpace ℝ (Fin 2) × ℝ, 1 ≤ ‖p.1‖ → ‖p.1‖ < 1 + a →
      (projIcc 0 a₀ ha₀.le (‖p.1‖ - 1) : ℝ) = ‖p.1‖ - 1 := by
    intro p h1 h2
    rw [projIcc_of_mem]
    exact ⟨by linarith, by linarith⟩
  have hp0 : ∀ p : EuclideanSpace ℝ (Fin 2) × ℝ, 1 ≤ ‖p.1‖ → p.1 ≠ 0 := by
    intro p h1 h0
    rw [h0, norm_zero] at h1
    linarith
  refine ⟨a, V, θ, Θ, ha, ha2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hVb' : IsOpen Vb' := by
      have heq : Vb' = Subtype.val '' (Φ '' (univ ×ˢ Ioo (-(1 / 4)) (5 / 4))) := by
        ext b
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨Φ x, ⟨x, hx, rfl⟩, hΦ x⟩
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, (hΦ x).symm⟩
      rw [heq]
      exact Vb.isOpen.isOpenMap_subtype_val _ (Φ.toHomeomorph.isOpenMap _
        (isOpen_univ.prod isOpen_Ioo))
    have hVeq : V = Subtype.val '' (dc '' {p | p.val.1 ∈ Vb' ∧ (p.val.2 : ℝ) < a}) := by
      ext m
      constructor
      · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
        have hqa : (q.2 : ℝ) < a₀ := lt_of_lt_of_le hq2 haa
        exact ⟨dc ⟨q, hqa⟩, ⟨⟨q, hqa⟩, ⟨hq1, hq2⟩, rfl⟩, hdc _⟩
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p.val, hp, (hdc p).symm⟩
    rw [hVeq]
    exact Y.isOpen.isOpenMap_subtype_val _ (dc.toHomeomorph.isOpenMap _
      ((hVb'.preimage (continuous_fst.comp continuous_subtype_val)).inter
        (isOpen_lt (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
          continuous_const)))
  · rintro _ ⟨q, ⟨⟨x, ⟨-, hx⟩, hxq⟩, hq2⟩, rfl⟩
    rw [hθc q (lt_of_lt_of_le hq2 haa)]
    have hgq : g q.1 = x := by rw [← hxq, hg]
    have hq0 : (0 : ℝ) ≤ q.2 := q.2.2.1
    have hn : ‖(F q).1‖ = 1 + (q.2 : ℝ) := by
      simp only [F, hgq, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one]
      exact abs_of_nonneg (by linarith)
    refine ⟨by rw [hn]; linarith, by rw [hn]; linarith, ?_⟩
    simp only [F, hgq]
    obtain ⟨h1, h2⟩ := hx
    rw [abs_lt]
    constructor <;> linarith
  · rintro p ⟨h1, h2, h3⟩
    obtain ⟨h3a, h3b⟩ := abs_lt.mp h3
    refine ⟨(fB (sphereDirection s₀ p.1, (p.2 + 1) / 2), projIcc 0 a₀ ha₀.le (‖p.1‖ - 1)),
      ⟨⟨_, ⟨mem_univ _, ?_, ?_⟩, rfl⟩, ?_⟩, rfl⟩
    · linarith
    · linarith
    · rw [hproj p h1 h2]
      linarith
  · rintro _ ⟨q, ⟨⟨x, -, hxq⟩, hq2⟩, rfl⟩
    rw [hθc q (lt_of_lt_of_le hq2 haa)]
    have hgq : g q.1 = x := by rw [← hxq, hg]
    have hq0 : (0 : ℝ) ≤ q.2 := q.2.2.1
    have hpos : (0 : ℝ) < 1 + (q.2 : ℝ) := by linarith
    have hdir : sphereDirection s₀ (F q).1 = x.1 := by
      simp only [F, hgq]
      exact sphereDirection_pos_smul s₀ x.1 hpos
    have hnorm : ‖(F q).1‖ - 1 = (q.2 : ℝ) := by
      simp only [F, hgq, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one,
        abs_of_pos hpos]
      ring
    have hs : ((F q).2 + 1) / 2 = x.2 := by
      simp only [F, hgq]
      ring
    change c (fB (sphereDirection s₀ (F q).1, ((F q).2 + 1) / 2),
      projIcc 0 a₀ ha₀.le (‖(F q).1‖ - 1)) = c q
    rw [hdir, hs, hnorm, projIcc_val, Prod.mk.eta, hxq]
  · rintro p ⟨h1, h2, h3⟩
    have hq : ((fB (sphereDirection s₀ p.1, (p.2 + 1) / 2), projIcc 0 a₀ ha₀.le (‖p.1‖ - 1)) :
        B × Icc (0 : ℝ) a₀).2.val < a₀ := by
      rw [hproj p h1 h2]
      linarith
    change θ (c _) = p
    rw [hθc _ hq]
    simp only [F, hg, hproj p h1 h2]
    rw [show 1 + (‖p.1‖ - 1) = ‖p.1‖ by ring, norm_smul_sphereDirection s₀ (hp0 p h1)]
    ext
    · rfl
    · change 2 * ((p.2 + 1) / 2) - 1 = p.2
      ring
  · intro u s
    have hu : ‖(u : EuclideanSpace ℝ (Fin 2))‖ = 1 := norm_eq_of_mem_sphere u
    have hdir : sphereDirection s₀ (u : EuclideanSpace ℝ (Fin 2)) = u := by
      have h := sphereDirection_pos_smul s₀ u one_pos
      rwa [one_smul] at h
    change c (fB (sphereDirection s₀ (u : EuclideanSpace ℝ (Fin 2)), (s + 1) / 2),
      projIcc 0 a₀ ha₀.le (‖(u : EuclideanSpace ℝ (Fin 2))‖ - 1)) = f (u, (s + 1) / 2)
    rw [hdir, hu, sub_self, projIcc_left]
    exact hc0 (fB (u, (s + 1) / 2))
  · intro m hm
    obtain ⟨q, ⟨⟨x, -, hxq⟩, hq2⟩, rfl⟩ := hm
    have hqa : (q.2 : ℝ) < a₀ := lt_of_lt_of_le hq2 haa
    obtain ⟨hY, hsymm⟩ := hcU q hqa
    have hq1 : q.1 ∈ Vb := by
      rw [← hxq]
      exact hfBV x
    apply ContMDiffAt.contMDiffWithinAt
    have hres : (fun x : Y => θ x) = F ∘ Subtype.val ∘ dc.symm := by
      funext x
      simp only [θ, dite_eq_left x.2, Function.comp_apply]
    have h : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ (fun x : Y => θ x)
        ⟨c q, hY⟩ := by
      rw [hres]
      have hq : (dc.symm ⟨c q, hY⟩).val = q := by rw [hsymm]
      refine ContMDiffAt.comp (I' := (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1))
        _ ?_ (contMDiff_subtype_val.contMDiffAt.comp _ (dc.symm.contMDiff _))
      rw [Function.comp_apply, hq]
      exact hFs q hq1
    exact contMDiffAt_subtype_iff.mp h
  · have hd1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 1) ∞ (sphereDirection s₀)
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := contMDiffOn_sphereDirection s₀
    have hfst : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => p.1) := contDiff_fst.contMDiff
    have hdir : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡 1) ∞
        (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => sphereDirection s₀ p.1) (twoHandleCollar a) :=
      hd1.comp hfst.contMDiffOn fun p hp h0 => hp0 p hp.1 (mem_singleton_iff.mp h0)
    have hsl' : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => (p.2 + 1) / 2) :=
      (contDiff_snd.add contDiff_const).div_const 2
    have hsl : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ) ∞
        (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => (p.2 + 1) / 2) (twoHandleCollar a) :=
      hsl'.contMDiff.contMDiffOn
    have hnorm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) 𝓘(ℝ) ∞
        (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => ‖p.1‖ - 1) (twoHandleCollar a) := by
      intro p hp
      exact (((contDiffAt_norm ℝ (hp0 p hp.1)).comp p contDiffAt_fst).sub
        contDiffAt_const).contMDiffAt.contMDiffWithinAt
    have hpr : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 1) ∞
        (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => projIcc 0 a₀ ha₀.le (‖p.1‖ - 1))
        (twoHandleCollar a) :=
      contMDiffOn_projIcc.comp hnorm fun p hp => ⟨by linarith [hp.1], by linarith [hp.2.1]⟩
    exact hcs.comp_contMDiffOn ((hfBs.comp_contMDiffOn (hdir.prodMk hsl)).prodMk hpr)

end DifferentialGeometry.Topology.PiecewiseLinear
