import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Metric

section CompleteGeodesics

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private def lineEval
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (u : MetricUnitTangent g) (t : ℝ) : M :=
  intrinsicGeodesic g hEnorm (MetricUnitTangent.base u) (MetricUnitTangent.vec u) t

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
private theorem line_scale_initial_continuous :
    Continuous (fun z : TangentBundle I M × ℝ ↦
      (⟨z.1.proj, z.2 • z.1.snd⟩ : TangentBundle I M)) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hdata := (FiberBundle.continuousAt_totalSpace E
    (fun w : TangentBundle I M × ℝ ↦ w.1)).mp
      (continuous_fst.continuousAt : ContinuousAt
        (fun w : TangentBundle I M × ℝ ↦ w.1) z)
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hdata.1, ?_⟩
  let e := trivializationAt E (TangentSpace I) z.1.proj
  have hbase : ∀ᶠ w : TangentBundle I M × ℝ in 𝓝 z, w.1.proj ∈ e.baseSet :=
    hdata.1.preimage_mem_nhds (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) z.1.proj))
  have hscaled : ContinuousAt
      (fun w : TangentBundle I M × ℝ ↦ w.2 • (e w.1).2) z :=
    continuous_snd.continuousAt.smul hdata.2
  apply hscaled.congr_of_eventuallyEq
  filter_upwards [hbase] with w hw
  exact (e.linear ℝ hw).map_smul w.2 w.1.snd

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private theorem line_eval_continuous
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) :
    Continuous (fun z : MetricUnitTangent g × ℝ ↦ lineEval g hEnorm z.1 z.2) := by
  have hlaunch : Continuous (fun z : MetricUnitTangent g × ℝ ↦
      ((z.1.val, z.2) : TangentBundle I M × ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hexp := (intrinsicExp_smooth g hEnorm).continuous.comp
    (line_scale_initial_continuous (I := I) (M := M) |>.comp hlaunch)
  apply hexp.congr
  intro z
  change expMapIntrinsic g hEnorm z.1.val.proj (z.2 • z.1.val.snd) = _
  rw [expMapIntrinsic_def]
  exact intrinsicGeodesic_smul g hEnorm
    (MetricUnitTangent.base z.1) (MetricUnitTangent.vec z.1) z.2

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private theorem line_eval_zero
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (u : MetricUnitTangent g) :
    lineEval g hEnorm u 0 = MetricUnitTangent.base u :=
  intrinsicGeodesic_zero g hEnorm _ _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private theorem line_eval_dist_le
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (u : MetricUnitTangent g)
    {s t : ℝ} (hst : s ≤ t) :
    dist (lineEval g hEnorm u s) (lineEval g hEnorm u t) ≤ t - s := by
  have h := intrinsicGeodesic_riemannianEDist_le g hEnorm
    (MetricUnitTangent.base u) (MetricUnitTangent.vec u) hst
  rw [MetricUnitTangent.unit, Real.sqrt_one, one_mul] at h
  apply (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hst)).mp
  rw [← edist_dist, IsRiemannianManifold.out (I := I)]
  exact h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private theorem line_subsegment_minimizing
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (u : MetricUnitTangent g)
    (L : ℝ)
    (hend : dist (lineEval g hEnorm u 0) (lineEval g hEnorm u L) = L)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) :
    dist (lineEval g hEnorm u s) (lineEval g hEnorm u t) = t - s := by
  apply le_antisymm (line_eval_dist_le g hEnorm u hst)
  have hleft := line_eval_dist_le g hEnorm u hs
  have hright := line_eval_dist_le g hEnorm u ht
  have htri₁ := dist_triangle (lineEval g hEnorm u 0)
    (lineEval g hEnorm u s) (lineEval g hEnorm u L)
  have htri₂ := dist_triangle (lineEval g hEnorm u s)
    (lineEval g hEnorm u t) (lineEval g hEnorm u L)
  rw [hend] at htri₁
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem line_unit_initial_between
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (p q : M) (hpq : p ≠ q) :
    ∃ u : MetricUnitTangent g,
      MetricUnitTangent.base u = p ∧ lineEval g hEnorm u (dist p q) = q := by
  have hfinite : riemannianEDist I p q ≠ (⊤ : ENNReal) := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top p q
  obtain ⟨v, hv, hlength⟩ := minExp_of_ne_top g hEnorm p q hfinite
  have hlength' : Real.sqrt (g.inner p v v) = dist p q := by
    rw [← IsRiemannianManifold.out (I := I), edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] at hlength
    exact hlength
  have hpositive : 0 < dist p q := dist_pos.mpr hpq
  have hvv : g.inner p v v = dist p q ^ 2 := by
    rw [← hlength', Real.sq_sqrt (gInner_self_nonneg g p v)]
  let w : TangentSpace I p := (dist p q)⁻¹ • v
  have hw : g.inner p w w = 1 := by
    dsimp only [w]
    rw [gInner_smul_self, hvv, ← mul_pow,
      inv_mul_cancel₀ hpositive.ne', one_pow]
  let u : MetricUnitTangent g := ⟨(⟨p, w⟩ : TangentBundle I M), hw⟩
  refine ⟨u, rfl, ?_⟩
  have hrescale : dist p q • w = v := by
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ hpositive.ne', one_smul]
  change intrinsicGeodesic g hEnorm p w (dist p q) = q
  rw [← intrinsicGeodesic_smul g hEnorm p w (dist p q), hrescale]
  exact hv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
private theorem line_height_bound
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (f : M → ℝ) (hf : Continuous f)
    {K : Set M} (hK : IsCompact K) (N : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : MetricUnitTangent g,
      MetricUnitTangent.base u ∈ K → ∀ t ∈ Icc (-N) N,
        |f (lineEval g hEnorm u t)| ≤ B := by
  let U : Set (MetricUnitTangent g) := {u | MetricUnitTangent.base u ∈ K}
  have hU : IsCompact U := metricUnitOn_compact g hK
  have hcompact : IsCompact (U ×ˢ Icc (-N) N) := hU.prod isCompact_Icc
  have hcontinuous : Continuous
      (fun z : MetricUnitTangent g × ℝ ↦ |f (lineEval g hEnorm z.1 z.2)|) :=
    (hf.comp (line_eval_continuous g hEnorm)).abs
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hcontinuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun u hu t ht ↦ ?_⟩
  exact (hB ⟨(u, t), ⟨hu, ht⟩, rfl⟩).trans (le_max_left _ _)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem line_centered_segment
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (f : M → ℝ) (hf : Continuous f)
    (hfSurj : Surjective f) (hzero : IsCompact {x : M | f x = 0})
    (N : ℝ) (hN : 0 ≤ N) :
    ∃ u : MetricUnitTangent g, f (MetricUnitTangent.base u) = 0 ∧
      ∀ s ∈ Icc (-N) N, ∀ t ∈ Icc (-N) N,
        dist (lineEval g hEnorm u s) (lineEval g hEnorm u t) = |s - t| := by
  obtain ⟨B, hBpos, hB⟩ := line_height_bound g hEnorm f hf hzero N
  let R : ℝ := B + N + 1
  have hR : 0 < R := by dsimp only [R]; linarith
  obtain ⟨p, hp⟩ := hfSurj (-R)
  obtain ⟨q, hq⟩ := hfSurj R
  have hpq : p ≠ q := by
    intro heq
    have hh : -R = R := hp.symm.trans ((congrArg f heq).trans hq)
    linarith
  obtain ⟨v, hvbase, hvend⟩ := line_unit_initial_between g hEnorm p q hpq
  let L : ℝ := dist p q
  have hL : 0 < L := dist_pos.mpr hpq
  have hvzero : lineEval g hEnorm v 0 = p :=
    (line_eval_zero g hEnorm v).trans hvbase
  have hminimal : dist (lineEval g hEnorm v 0) (lineEval g hEnorm v L) = L := by
    rw [hvzero, hvend]
  have hpath : Continuous (fun t : ℝ ↦ f (lineEval g hEnorm v t)) :=
    hf.comp (intrinsicGeodesic_continuous g hEnorm
      (MetricUnitTangent.base v) (MetricUnitTangent.vec v))
  have hbetween : (0 : ℝ) ∈ Icc (f (lineEval g hEnorm v 0))
      (f (lineEval g hEnorm v L)) := by
    rw [hvzero, hvend, hp, hq]
    exact ⟨by linarith, hR.le⟩
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hL.le hpath.continuousOn hbetween
  let w : MetricUnitTangent g :=
    ⟨(⟨lineEval g hEnorm v c,
       mfderiv 𝓘(ℝ, ℝ) I (lineEval g hEnorm v) c 1⟩ : TangentBundle I M),
     (intrinsicGeodesic_speedSq_eq g hEnorm
       (MetricUnitTangent.base v) (MetricUnitTangent.vec v) c).trans
         (MetricUnitTangent.unit v)⟩
  have hwzero : f (MetricUnitTangent.base w) = 0 := hfc
  have hshift (s : ℝ) : lineEval g hEnorm w s = lineEval g hEnorm v (s + c) := by
    exact congrFun (intrinsicGeodesic_continuation g hEnorm
      (MetricUnitTangent.base v) (MetricUnitTangent.vec v) c).symm s
  have hleft : N < c := by
    by_contra hnot
    have hcle : c ≤ N := le_of_not_gt hnot
    have hm : -c ∈ Icc (-N) N := ⟨by linarith, by linarith [hc.1]⟩
    have hh := hB w hwzero (-c) hm
    rw [hshift, neg_add_cancel, hvzero, hp, abs_neg, abs_of_pos hR] at hh
    dsimp only [R] at hh
    linarith
  have hright : N < L - c := by
    by_contra hnot
    have hle : L - c ≤ N := le_of_not_gt hnot
    have hm : L - c ∈ Icc (-N) N := ⟨by linarith [hc.2], hle⟩
    have hh := hB w hwzero (L - c) hm
    rw [hshift, sub_add_cancel, hvend, hq, abs_of_pos hR] at hh
    dsimp only [R] at hh
    linarith
  have hordered {s t : ℝ} (hs : s ∈ Icc (-N) N) (ht : t ∈ Icc (-N) N)
      (hst : s ≤ t) :
      dist (lineEval g hEnorm w s) (lineEval g hEnorm w t) = t - s := by
    rw [hshift, hshift]
    have hh := line_subsegment_minimizing g hEnorm v L hminimal
      (s := s + c) (t := t + c) (by linarith [hs.1])
        (by linarith) (by linarith [ht.2])
    simpa only [add_sub_add_right_eq_sub] using hh
  refine ⟨w, hwzero, fun s hs t ht ↦ ?_⟩
  rcases le_total s t with hst | hts
  · rw [hordered hs ht hst, abs_of_nonpos (sub_nonpos.mpr hst)]
    ring
  · rw [dist_comm, hordered ht hs hts, abs_of_nonneg (sub_nonneg.mpr hts)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem line_initial_of_compact_level
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (f : M → ℝ) (hf : Continuous f)
    (hfSurj : Surjective f) (hzero : IsCompact {x : M | f x = 0}) :
    ∃ u : MetricUnitTangent g, f (MetricUnitTangent.base u) = 0 ∧
      ∀ s t : ℝ, dist (lineEval g hEnorm u s) (lineEval g hEnorm u t) = |s - t| := by
  let F : ℕ → Set (MetricUnitTangent g) := fun N ↦
    {u | f (MetricUnitTangent.base u) = 0 ∧
      ∀ s ∈ Icc (-(N : ℝ)) (N : ℝ), ∀ t ∈ Icc (-(N : ℝ)) (N : ℝ),
        dist (lineEval g hEnorm u s) (lineEval g hEnorm u t) = |s - t|}
  have hbase : Continuous (fun u : MetricUnitTangent g ↦ MetricUnitTangent.base u) :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  have heval (t : ℝ) : Continuous (fun u : MetricUnitTangent g ↦ lineEval g hEnorm u t) :=
    (line_eval_continuous g hEnorm).comp (continuous_id.prodMk continuous_const)
  have hclosed (N : ℕ) : IsClosed (F N) := by
    have hlevel : IsClosed {u : MetricUnitTangent g | f (MetricUnitTangent.base u) = 0} :=
      isClosed_eq (hf.comp hbase) continuous_const
    have hdist : IsClosed {u : MetricUnitTangent g |
        ∀ s ∈ Icc (-(N : ℝ)) (N : ℝ), ∀ t ∈ Icc (-(N : ℝ)) (N : ℝ),
          dist (lineEval g hEnorm u s) (lineEval g hEnorm u t) = |s - t|} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter (fun s ↦ isClosed_iInter (fun _hs ↦
        isClosed_iInter (fun t ↦ isClosed_iInter (fun _ht ↦
          isClosed_eq ((heval s).dist (heval t)) continuous_const))))
    exact hlevel.inter hdist
  have hnonempty (N : ℕ) : (F N).Nonempty :=
    line_centered_segment g hEnorm f hf hfSurj hzero (N : ℝ) (Nat.cast_nonneg N)
  have hdecreasing (N : ℕ) : F (N + 1) ⊆ F N := by
    intro u hu
    refine ⟨hu.1, fun s hs t ht ↦ ?_⟩
    have hs' : s ∈ Icc (-((N + 1 : ℕ) : ℝ)) ((N + 1 : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      constructor <;> linarith [hs.1, hs.2]
    have ht' : t ∈ Icc (-((N + 1 : ℕ) : ℝ)) ((N + 1 : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      constructor <;> linarith [ht.1, ht.2]
    exact hu.2 s hs' t ht'
  have hcompact : IsCompact (F 0) :=
    (metricUnitOn_compact g hzero).of_isClosed_subset (hclosed 0)
      (fun _ hu ↦ hu.1)
  obtain ⟨u, hu⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      F hdecreasing hnonempty hcompact hclosed
  have hmem (N : ℕ) : u ∈ F N := Set.mem_iInter.mp hu N
  refine ⟨u, (hmem 0).1, fun s t ↦ ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max |s| |t|)
  have hs : s ∈ Icc (-(N : ℝ)) (N : ℝ) :=
    abs_le.mp ((le_max_left |s| |t|).trans hN.le)
  have ht : t ∈ Icc (-(N : ℝ)) (N : ℝ) :=
    abs_le.mp ((le_max_right |s| |t|).trans hN.le)
  exact (hmem N).2 s hs t ht

end CompleteGeodesics

private abbrev Sphere3 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev Cyl3 := (Sphere3 × ℝ)
private abbrev ICyl3 := ((𝓡 2).prod 𝓘(ℝ))

private local instance : NeZero
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_minimizing_line_on_cylinder
    (g : SmoothRiemannianMetric ICyl3 Cyl3)
    (hcomplete : RiemannianMetricComplete g) :
    ∃ gamma : ℝ → Cyl3,
      ContMDiff 𝓘(ℝ, ℝ) ICyl3 ∞ gamma ∧
      IsGeodesic g gamma ∧ (gamma 0).2 = 0 ∧
      ∀ s t : ℝ,
        riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t| := by
  have hsphereConnected : IsConnected (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    apply isConnected_sphere _ _ (by norm_num)
    rw [← Module.finrank_eq_rank]
    norm_num
  let : ConnectedSpace Sphere3 := Subtype.connectedSpace hsphereConnected
  let : ConnectedSpace Cyl3 := inferInstance
  let : IsManifold ICyl3 1 Cyl3 :=
    IsManifold.of_le (I := ICyl3) (M := Cyl3) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace Cyl3 := Manifold.metrizableSpace ICyl3 Cyl3
  let : T3Space Cyl3 := inferInstance
  let : RiemannianBundle (fun x : Cyl3 ↦ TangentSpace ICyl3 x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2) × ℝ)
      (fun x : Cyl3 ↦ TangentSpace ICyl3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace Cyl3 := EMetricSpace.ofRiemannianMetric ICyl3 Cyl3
  let m : MetricSpace Cyl3 := HopfRinow.riemMetricSpace (I := ICyl3) (M := Cyl3)
  let : MetricSpace Cyl3 := m
  let : PseudoMetricSpace Cyl3 := m.toPseudoMetricSpace
  let : PseudoEMetricSpace Cyl3 := m.toPseudoEMetricSpace
  let : UniformSpace Cyl3 := m.toUniformSpace
  let : IsRiemannianManifold ICyl3 Cyl3 := ⟨by intro x y; rfl⟩
  let : @CompleteSpace Cyl3 m.toUniformSpace := hcomplete.complete
  have hEnorm : IsMetricNorm (I := ICyl3) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hzero : IsCompact {x : Cyl3 | x.2 = 0} := by
    have hc : IsCompact (Set.range (fun y : Sphere3 ↦ (y, (0 : ℝ)))) :=
      isCompact_range (continuous_id.prodMk continuous_const)
    have heq : Set.range (fun y : Sphere3 ↦ (y, (0 : ℝ))) = {x : Cyl3 | x.2 = 0} := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        rfl
      · intro hx
        exact ⟨x.1, Prod.ext rfl hx.symm⟩
    rwa [heq] at hc
  have hsurj : Surjective (Prod.snd : Cyl3 → ℝ) := by
    intro t
    exact ⟨(Classical.choice (inferInstance : Nonempty Sphere3), t), rfl⟩
  obtain ⟨u, hu0, hline⟩ := line_initial_of_compact_level g hEnorm
    (Prod.snd : Cyl3 → ℝ) continuous_snd hsurj hzero
  let gamma : ℝ → Cyl3 := lineEval g hEnorm u
  refine ⟨gamma, intrinsicGeodesic_contMDiff g hEnorm _ _,
    intrinsicGeodesic_isGeodesic g hEnorm _ _, ?_, fun s t ↦ ?_⟩
  · change (lineEval g hEnorm u 0).2 = 0
    rw [line_eval_zero]
    exact hu0
  · rw [riemannianEDistOf_eq_riemannianEDist g hEnorm,
      ← IsRiemannianManifold.out (I := ICyl3), edist_dist, hline]

end DifferentialGeometry.Geometry.Metric

end
