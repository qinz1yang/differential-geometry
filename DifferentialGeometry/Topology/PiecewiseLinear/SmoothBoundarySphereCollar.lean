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
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.SmoothEmbedding

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Topology.Manifold (sphereDirection sphereDirection_pos_smul
  norm_smul_sphereDirection contMDiffOn_sphereDirection)

theorem exists_radialCollar_of_isSmoothEmbedding_sphere
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    (d : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M)
    (hd : IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ d) (hdbd : range d ⊆ (𝓡∂ 3).boundary M) :
    ∃ (a : ℝ) (V : Set M) (θ : M → EuclideanSpace ℝ (Fin 3))
      (Θ : EuclideanSpace ℝ (Fin 3) → M),
      0 < a ∧ IsOpen V ∧ range d ⊆ V ∧
      (∀ m ∈ V, 1 ≤ ‖θ m‖ ∧ ‖θ m‖ < 1 + a) ∧
      (∀ v, 1 ≤ ‖v‖ → ‖v‖ < 1 + a → Θ v ∈ V) ∧
      (∀ m ∈ V, Θ (θ m) = m) ∧ (∀ v, 1 ≤ ‖v‖ → ‖v‖ < 1 + a → θ (Θ v) = v) ∧
      (∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, Θ u = d u) ∧
      ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ θ V ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞ Θ
        {v | 1 ≤ ‖v‖ ∧ ‖v‖ < 1 + a} := by
  classical
  obtain ⟨r, -, -, -, a, ha, c, hc, hcs, hc0, -, -, Y, -, dc, hdc⟩ :=
    DifferentialGeometry.Manifold.Boundary.exists_definingFunction_sublevel_collar
      (n := 2) (M := M)
  let _ : Fact ((0 : ℝ) < a) := ⟨ha⟩
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let B := BoundaryManifold (𝓡∂ 3) M
  let dB : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → B :=
    fun u => ⟨d u, hdbd ⟨u, rfl⟩⟩
  have hdBs : ContMDiff (𝓡 2) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ dB :=
    (DifferentialGeometry.Manifold.Boundary.contMDiff_boundary_iff le_rfl).mpr hd.contMDiff
  have hdBinj : Function.Injective dB := fun u w h =>
    hd.isEmbedding.injective (congrArg Subtype.val h)
  have hincl : ContMDiff (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡∂ 3) ∞
      (boundaryInclusion (𝓡∂ 3) M) := boundaryInclusion_contMDiff
  have hmf : ∀ u, Function.Injective (mfderiv (𝓡 2) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3))
      dB u) := by
    intro u v w hvw
    have h1 := DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
      (𝓡 2) (𝓡∂ 3) d u (hd.isImmersion.isImmersionAt u)
    have hcomp : mfderiv (𝓡 2) (𝓡∂ 3) (boundaryInclusion (𝓡∂ 3) M ∘ dB) u =
        (mfderiv (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡∂ 3)
          (boundaryInclusion (𝓡∂ 3) M) (dB u)).comp
          (mfderiv (𝓡 2) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) dB u) :=
      mfderiv_comp u ((hincl (dB u)).mdifferentiableAt (by simp))
        ((hdBs u).mdifferentiableAt (by simp))
    change Function.Injective (mfderiv (𝓡 2) (𝓡∂ 3) (boundaryInclusion (𝓡∂ 3) M ∘ dB) u) at h1
    rw [hcomp, ContinuousLinearMap.coe_comp] at h1
    exact h1.of_comp hvw
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) =
      Module.finrank ℝ (HasSmoothBoundary.boundaryE (I := 𝓡∂ 3)) := by
    have h := HasSmoothBoundary.finrank_boundaryE_succ (I := 𝓡∂ 3)
    simp only [finrank_euclideanSpace, Fintype.card_fin] at h ⊢
    omega
  obtain ⟨Vb, Φ, hVb, hΦ, -⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_onto_range_of_injective_immersion
      dB hdBs hdBinj hmf hdim
  obtain ⟨u₀, hu₀⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let s₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨u₀, hu₀⟩
  let g : B → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun b => if h : b ∈ Vb then Φ.symm ⟨b, h⟩ else s₀
  have hdBV : ∀ u, dB u ∈ Vb := fun u => by
    rw [← SetLike.mem_coe, hVb]
    exact ⟨u, rfl⟩
  have hg : ∀ u, g (dB u) = u := by
    intro u
    have hΦu : Φ u = ⟨dB u, hdBV u⟩ := Subtype.ext (hΦ u)
    simp only [g, dite_eq_left (hdBV u), ← hΦu, Diffeomorph.symm_apply_apply]
  have hgs : ∀ b ∈ Vb, ContMDiffAt (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) (𝓡 2) ∞ g b := by
    intro b hb
    have hres : (fun x : Vb => g x) = Φ.symm := by
      funext x
      simp only [g, dite_eq_left x.2]
    have h := Φ.symm.contMDiff ⟨b, hb⟩
    rw [← hres] at h
    exact contMDiffAt_subtype_iff.mp h
  let F : B × Icc (0 : ℝ) a → EuclideanSpace ℝ (Fin 3) :=
    fun q => (1 + (q.2 : ℝ)) • (g q.1 : EuclideanSpace ℝ (Fin 3))
  have hFs : ∀ q : B × Icc (0 : ℝ) a, q.1 ∈ Vb →
      ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ F q := by
    intro q hq
    have h1 : ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1)) 𝓘(ℝ)
        ∞ (fun q : B × Icc (0 : ℝ) a => 1 + (q.2 : ℝ)) q :=
      contMDiffAt_const.add (contMDiff_subtypeVal_Icc.comp contMDiff_snd).contMDiffAt
    have h2 : ContMDiffAt ((HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        (fun q : B × Icc (0 : ℝ) a => (g q.1 : EuclideanSpace ℝ (Fin 3))) q :=
      contMDiff_coe_sphere.contMDiffAt.comp q ((hgs q.1 hq).comp q contMDiffAt_fst)
    exact h1.smul h2
  let θ : M → EuclideanSpace ℝ (Fin 3) :=
    fun m => if h : m ∈ Y then F (dc.symm ⟨m, h⟩).val else 0
  let Θ : EuclideanSpace ℝ (Fin 3) → M :=
    fun v => c (dB (sphereDirection s₀ v), projIcc 0 a ha.le (‖v‖ - 1))
  let V : Set M := c '' {q | q.1 ∈ Vb ∧ (q.2 : ℝ) < a}
  have hcU : ∀ q : B × Icc (0 : ℝ) a, ∀ hq : (q.2 : ℝ) < a,
      ∃ hY : c q ∈ Y, dc.symm ⟨c q, hY⟩ = ⟨q, hq⟩ := by
    intro q hq
    have h := hdc ⟨q, hq⟩
    refine ⟨h ▸ (dc ⟨q, hq⟩).2, ?_⟩
    have he : (⟨c q, h ▸ (dc ⟨q, hq⟩).2⟩ : Y) = dc ⟨q, hq⟩ := Subtype.ext h.symm
    rw [he, Diffeomorph.symm_apply_apply]
  have hθc : ∀ q : B × Icc (0 : ℝ) a, (q.2 : ℝ) < a → θ (c q) = F q := by
    intro q hq
    obtain ⟨hY, hsymm⟩ := hcU q hq
    simp only [θ, dite_eq_left hY, hsymm]
  have hdc0 : ∀ u, c (dB u, projIcc 0 a ha.le 0) = d u := by
    intro u
    rw [projIcc_left]
    exact hc0 (dB u)
  have hΘV : ∀ v : EuclideanSpace ℝ (Fin 3), 1 ≤ ‖v‖ → ‖v‖ < 1 + a →
      (projIcc 0 a ha.le (‖v‖ - 1) : ℝ) = ‖v‖ - 1 := by
    intro v h1 h2
    rw [projIcc_of_mem]
    exact ⟨by linarith, by linarith⟩
  refine ⟨a, V, θ, Θ, ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hVeq : V = Subtype.val '' (dc '' {p | p.val.1 ∈ Vb}) := by
      ext m
      constructor
      · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
        exact ⟨dc ⟨q, hq2⟩, ⟨⟨q, hq2⟩, hq1, rfl⟩, hdc _⟩
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p.val, ⟨hp, p.2⟩, (hdc p).symm⟩
    rw [hVeq]
    exact Y.isOpen.isOpenMap_subtype_val _ (dc.toHomeomorph.isOpenMap _
      (Vb.isOpen.preimage (continuous_fst.comp continuous_subtype_val)))
  · rintro _ ⟨u, rfl⟩
    refine ⟨(dB u, ⟨0, le_rfl, ha.le⟩), ⟨hdBV u, ha⟩, ?_⟩
    exact hc0 (dB u)
  · rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    rw [hθc q hq2]
    have hn : ‖F q‖ = 1 + (q.2 : ℝ) := by
      simp only [F, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one]
      exact abs_of_nonneg (by linarith [q.2.2.1])
    rw [hn]
    exact ⟨by linarith [q.2.2.1], by linarith⟩
  · intro v h1 h2
    refine ⟨(dB (sphereDirection s₀ v), projIcc 0 a ha.le (‖v‖ - 1)), ⟨hdBV _, ?_⟩, rfl⟩
    rw [hΘV v h1 h2]
    linarith
  · rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    rw [hθc q hq2]
    obtain ⟨u, hu⟩ : ∃ u, dB u = q.1 := by
      rw [← SetLike.mem_coe, hVb] at hq1
      exact hq1
    have hpos : (0 : ℝ) < 1 + (q.2 : ℝ) := by linarith [q.2.2.1]
    have hdir : sphereDirection s₀ (F q) = u := by
      simp only [F, ← hu, hg]
      exact sphereDirection_pos_smul s₀ u hpos
    have hnorm : ‖F q‖ - 1 = (q.2 : ℝ) := by
      simp only [F, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one,
        abs_of_pos hpos]
      ring
    simp only [Θ, hdir, hnorm, hu, projIcc_val]
  · intro v h1 h2
    have hv : v ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      linarith
    have hq : ((dB (sphereDirection s₀ v), projIcc 0 a ha.le (‖v‖ - 1)) :
        B × Icc (0 : ℝ) a).2.val < a := by
      rw [hΘV v h1 h2]
      linarith
    change θ (c _) = v
    rw [hθc _ hq]
    simp only [F, hg, hΘV v h1 h2]
    rw [show 1 + (‖v‖ - 1) = ‖v‖ by ring]
    exact norm_smul_sphereDirection s₀ hv
  · intro u
    have hu : ‖(u : EuclideanSpace ℝ (Fin 3))‖ = 1 := norm_eq_of_mem_sphere u
    have hdir : sphereDirection s₀ (u : EuclideanSpace ℝ (Fin 3)) = u := by
      have h := sphereDirection_pos_smul s₀ u one_pos
      rwa [one_smul] at h
    simp only [Θ, hdir, hu, sub_self]
    exact hdc0 u
  · intro m hm
    obtain ⟨q, ⟨hq1, hq2⟩, rfl⟩ := hm
    obtain ⟨hY, hsymm⟩ := hcU q hq2
    apply ContMDiffAt.contMDiffWithinAt
    have hres : (fun x : Y => θ x) = F ∘ Subtype.val ∘ dc.symm := by
      funext x
      simp only [θ, dite_eq_left x.2, Function.comp_apply]
    have h : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (fun x : Y => θ x)
        ⟨c q, hY⟩ := by
      rw [hres]
      have hq : (dc.symm ⟨c q, hY⟩).val = q := by rw [hsymm]
      refine ContMDiffAt.comp (I' := (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)).prod (𝓡∂ 1))
        _ ?_ (contMDiff_subtype_val.contMDiffAt.comp _ (dc.symm.contMDiff _))
      rw [Function.comp_apply, hq]
      exact hFs q hq1
    exact contMDiffAt_subtype_iff.mp h
  · have hdir : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 2) ∞ (sphereDirection s₀)
        {v : EuclideanSpace ℝ (Fin 3) | 1 ≤ ‖v‖ ∧ ‖v‖ < 1 + a} :=
      (contMDiffOn_sphereDirection s₀).mono fun v hv h0 => by
        have h1 : (1 : ℝ) ≤ ‖v‖ := hv.1
        rw [mem_singleton_iff.mp h0, norm_zero] at h1
        linarith
    have hnorm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ) ∞ (fun v => ‖v‖ - 1)
        {v : EuclideanSpace ℝ (Fin 3) | 1 ≤ ‖v‖ ∧ ‖v‖ < 1 + a} := by
      intro v hv
      have hv0 : v ≠ 0 := by
        intro h
        have h1 : (1 : ℝ) ≤ ‖v‖ := hv.1
        rw [h, norm_zero] at h1
        linarith
      exact ((contDiffAt_norm ℝ hv0).sub contDiffAt_const).contMDiffAt.contMDiffWithinAt
    have hproj : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 1) ∞
        (fun v => projIcc 0 a ha.le (‖v‖ - 1))
        {v : EuclideanSpace ℝ (Fin 3) | 1 ≤ ‖v‖ ∧ ‖v‖ < 1 + a} :=
      contMDiffOn_projIcc.comp hnorm fun v hv => ⟨by linarith [hv.1], by linarith [hv.2]⟩
    exact hcs.comp_contMDiffOn ((hdBs.comp_contMDiffOn hdir).prodMk hproj)

end DifferentialGeometry.Topology.PiecewiseLinear
