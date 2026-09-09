import DifferentialGeometry.Geometry.Metric.ChartLipschitz
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology NNReal

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle F (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]

theorem ContMDiffWithinAt.exists_lipschitzOnWith {f : E → M} {s : Set E} {x : E}
    (hf : ContMDiffWithinAt 𝓘(ℝ, E) I 1 f s x) (hs : Convex ℝ s) :
    ∃ K : ℝ≥0, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  obtain ⟨C, _, R, hR, hchart⟩ :=
    DifferentialGeometry.Geometry.Riemannian.chart_symm_edist_le (I := I) (f x)
  let g := extChartAt I (f x) ∘ f
  have hg : ContDiffWithinAt ℝ 1 g s x := by
    apply ContMDiffWithinAt.contDiffWithinAt
    exact (contMDiffAt_extChartAt (I := I) (x := f x) (n := 1)).comp_contMDiffWithinAt x hf
  obtain ⟨K, v, hv, hKv⟩ := hg.exists_lipschitzOnWith hs
  have hsrc : f ⁻¹' (extChartAt I (f x)).source ∈ 𝓝[s] x :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (f x))
  have hball : g ⁻¹' Metric.ball (extChartAt I (f x) (f x)) R ∈ 𝓝[s] x :=
    hg.continuousWithinAt.preimage_mem_nhdsWithin (Metric.ball_mem_nhds _ hR)
  let t := v ∩ f ⁻¹' (extChartAt I (f x)).source ∩
    g ⁻¹' Metric.ball (extChartAt I (f x) (f x)) R
  have ht : t ∈ 𝓝[s] x := inter_mem (inter_mem hv hsrc) hball
  refine ⟨C * K, t, ht, ?_⟩
  intro y hy z hz
  rcases hy with ⟨⟨hyv, hysrc⟩, hyball⟩
  rcases hz with ⟨⟨hzv, hzsrc⟩, hzball⟩
  have hyRange : g y ∈ range I :=
    extChartAt_target_subset_range (f x) ((extChartAt I (f x)).map_source hysrc)
  have hzRange : g z ∈ range I :=
    extChartAt_target_subset_range (f x) ((extChartAt I (f x)).map_source hzsrc)
  have hyInv : (extChartAt I (f x)).symm (g y) = f y :=
    (extChartAt I (f x)).left_inv hysrc
  have hzInv : (extChartAt I (f x)).symm (g z) = f z :=
    (extChartAt I (f x)).left_inv hzsrc
  rw [IsRiemannianManifold.out (I := I), ← hyInv, ← hzInv]
  refine (hchart (g y) ⟨hyball, hyRange⟩ (g z) ⟨hzball, hzRange⟩).trans ?_
  calc
    (C : ENNReal) * edist (g y) (g z) ≤ C * (K * edist y z) :=
      mul_right_mono (hKv hyv hzv)
    _ = (C * K) * edist y z := by simp only [mul_assoc]

theorem ContMDiffOn.locallyLipschitzOn {f : E → M} {s : Set E}
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f s) (hs : Convex ℝ s) :
    LocallyLipschitzOn s f := fun x hx => (hf x hx).exists_lipschitzOnWith hs

end

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M N : Type*} [PseudoEMetricSpace M] [PseudoEMetricSpace N]
  [ChartedSpace H M] [ChartedSpace H' N] [IsManifold I 1 M] [IsManifold J 1 N]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : N => TangentSpace J x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle F (fun x : N => TangentSpace J x)]
  [IsRiemannianManifold I M] [IsRiemannianManifold J N]

theorem ContMDiffAt.exists_lipschitzOnWith {f : M → N} {x : M}
    (hf : ContMDiffAt I J 1 f x) :
    ∃ K : ℝ≥0, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s := by
  obtain ⟨K, s, hs, hKs⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_lipschitzOnWith_extChartAt (I := I) x
  have hcomp : ContMDiffWithinAt 𝓘(ℝ, E) J 1 (f ∘ (extChartAt I x).symm)
      (range I) (extChartAt I x x) :=
    hf.comp_contMDiffWithinAt_of_eq (contMDiffWithinAt_extChartAt_symm_range_self x)
      ((extChartAt I x).left_inv (mem_extChartAt_source x))
  obtain ⟨L, t, ht, hLt⟩ := hcomp.exists_lipschitzOnWith I.convex_range
  have htpre : (extChartAt I x) ⁻¹' t ∈ 𝓝 x :=
    extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (mem_extChartAt_source x) ht
  let u := s ∩ (extChartAt I x) ⁻¹' t ∩ (extChartAt I x).source
  have hu : u ∈ 𝓝 x := inter_mem (inter_mem hs htpre) (extChartAt_source_mem_nhds x)
  refine ⟨L * K, u, hu, ?_⟩
  intro y hy z hz
  rcases hy with ⟨⟨hys, hyt⟩, hysrc⟩
  rcases hz with ⟨⟨hzs, hzt⟩, hzsrc⟩
  have hcoord : edist (f y) (f z) ≤ L * edist (extChartAt I x y) (extChartAt I x z) := by
    simpa only [Function.comp_apply, (extChartAt I x).left_inv hysrc,
      (extChartAt I x).left_inv hzsrc] using hLt hyt hzt
  refine hcoord.trans ?_
  calc
    (L : ENNReal) * edist (extChartAt I x y) (extChartAt I x z) ≤
        L * (K * edist y z) := mul_right_mono (hKs hys hzs)
    _ = (L * K) * edist y z := by simp only [mul_assoc]

theorem ContMDiff.locallyLipschitz {f : M → N} (hf : ContMDiff I J 1 f) :
    LocallyLipschitz f := fun _ => hf.contMDiffAt.exists_lipschitzOnWith

end

namespace DifferentialGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

open MeasureTheory in
theorem riemannianEDist_le_of_mfderivWithin_le
    {ψ : F → M} {s U : Set F} {L : ℝ}
    (hψ : ContMDiffOn 𝓘(ℝ, F) I 1 ψ s)
    (hU : U ⊆ s)
    (hspd : ∀ w ∈ U, ∀ v : F,
      ‖mfderivWithin 𝓘(ℝ, F) I ψ s w v‖ₑ ≤ ENNReal.ofReal (L * ‖v‖))
    {u v : F} (hseg : segment ℝ u v ⊆ U) :
    riemannianEDist I (ψ u) (ψ v) ≤ ENNReal.ofReal (L * dist u v) := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  let γ : ℝ → M := ψ ∘ η
  have hηU : MapsTo η (Icc (0 : ℝ) 1) U := by
    intro t ht
    apply hseg
    rw [segment_eq_image_lineMap]
    exact ⟨t, ht, rfl⟩
  have hηs : MapsTo η (Icc (0 : ℝ) 1) s := fun _ ht => hU (hηU ht)
  have hηsmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 η (Icc (0 : ℝ) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact η.contDiff.contDiffOn
  have hγsmooth := hψ.comp hηsmooth hηs
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc 0 1) t 1‖ₑ ≤
        ENNReal.ofReal (L * dist u v) := by
    intro t ht
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) 1) t := by
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
    have hηdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) η t := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact η.differentiableAt
    have hchain := mfderivWithin_comp t (hψ.mdifferentiableOn one_ne_zero _ (hηs ht))
      hηdiff.mdifferentiableWithinAt hηs hu
    have hηderiv : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, F) η (Icc 0 1) t 1 = v - u := by
      rw [mfderivWithin_eq_mfderiv hu hηdiff, mfderiv_eq_fderiv, η.fderiv]
      change ((AffineMap.lineMap u v).linear : ℝ →ₗ[ℝ] F) 1 = v - u
      rw [AffineMap.lineMap_linear]
      simp
    change ‖(mfderivWithin 𝓘(ℝ, ℝ) I (ψ ∘ η) (Icc 0 1) t) 1‖ₑ ≤ _
    rw [hchain, ContinuousLinearMap.comp_apply, hηderiv]
    simpa only [dist_eq_norm, norm_sub_rev] using hspd (η t) (hηU ht) (v - u)
  calc
    riemannianEDist I (ψ u) (ψ v) ≤ pathELength I γ 0 1 :=
      riemannianEDist_le_pathELength hγsmooth
        (by simp [γ, η, ContinuousAffineMap.coe_lineMap_eq])
        (by simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]) zero_le_one
    _ = ∫⁻ t in Icc (0 : ℝ) 1, ‖mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc 0 1) t 1‖ₑ :=
      pathELength_eq_lintegral_mfderivWithin_Icc
    _ ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (L * dist u v) :=
      setLIntegral_mono' measurableSet_Icc hpoint
    _ = ENNReal.ofReal (L * dist u v) := by
      rw [setLIntegral_const, Real.volume_Icc]
      norm_num

end DifferentialGeometry
