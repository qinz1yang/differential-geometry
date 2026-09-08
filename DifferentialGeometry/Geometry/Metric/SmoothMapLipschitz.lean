import DifferentialGeometry.Geometry.Metric.ChartLipschitz
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology NNReal

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
  obtain ⟨L, t, ht, hLt⟩ :=
    (contMDiffAt_iff.mp hf).2.exists_lipschitzOnWith I.convex_range
  obtain ⟨C, _, R, hR, hC⟩ :=
    DifferentialGeometry.Geometry.Riemannian.chart_symm_edist_le (I := J) (f x)
  let g := extChartAt J (f x) ∘ f
  have hg : ContinuousAt g x :=
    (contMDiffAt_extChartAt (I := J) (x := f x) (n := 1)).continuousAt.comp hf.continuousAt
  have htpre : (extChartAt I x) ⁻¹' t ∈ 𝓝 x :=
    extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (mem_extChartAt_source x) ht
  have hfpre : f ⁻¹' (extChartAt J (f x)).source ∈ 𝓝 x :=
    hf.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (f x))
  have hball : g ⁻¹' Metric.ball (extChartAt J (f x) (f x)) R ∈ 𝓝 x :=
    hg.preimage_mem_nhds (Metric.ball_mem_nhds _ hR)
  let u := s ∩ (extChartAt I x) ⁻¹' t ∩ (extChartAt I x).source ∩
    f ⁻¹' (extChartAt J (f x)).source ∩ g ⁻¹' Metric.ball (extChartAt J (f x) (f x)) R
  have hu : u ∈ 𝓝 x :=
    inter_mem (inter_mem (inter_mem (inter_mem hs htpre)
      (extChartAt_source_mem_nhds x)) hfpre) hball
  refine ⟨C * (L * K), u, hu, ?_⟩
  intro y hy z hz
  rcases hy with ⟨⟨⟨⟨hys, hyt⟩, hysrc⟩, hyfsrc⟩, hyball⟩
  rcases hz with ⟨⟨⟨⟨hzs, hzt⟩, hzsrc⟩, hzfsrc⟩, hzball⟩
  have hyRange : g y ∈ range J :=
    extChartAt_target_subset_range (f x) ((extChartAt J (f x)).map_source hyfsrc)
  have hzRange : g z ∈ range J :=
    extChartAt_target_subset_range (f x) ((extChartAt J (f x)).map_source hzfsrc)
  have hyInv : (extChartAt J (f x)).symm (g y) = f y :=
    (extChartAt J (f x)).left_inv hyfsrc
  have hzInv : (extChartAt J (f x)).symm (g z) = f z :=
    (extChartAt J (f x)).left_inv hzfsrc
  have hcoord : edist (g y) (g z) ≤ L * edist (extChartAt I x y) (extChartAt I x z) := by
    simpa only [g, Function.comp_apply, (extChartAt I x).left_inv hysrc,
      (extChartAt I x).left_inv hzsrc] using hLt hyt hzt
  rw [IsRiemannianManifold.out (I := J), ← hyInv, ← hzInv]
  refine (hC (g y) ⟨hyball, hyRange⟩ (g z) ⟨hzball, hzRange⟩).trans ?_
  calc
    (C : ENNReal) * edist (g y) (g z) ≤
        C * (L * edist (extChartAt I x y) (extChartAt I x z)) := mul_right_mono hcoord
    _ ≤ C * (L * (K * edist y z)) := mul_right_mono (mul_right_mono (hKs hys hzs))
    _ = (C * (L * K)) * edist y z := by simp only [mul_assoc]

theorem ContMDiff.locallyLipschitz {f : M → N} (hf : ContMDiff I J 1 f) :
    LocallyLipschitz f := fun _ => hf.contMDiffAt.exists_lipschitzOnWith
