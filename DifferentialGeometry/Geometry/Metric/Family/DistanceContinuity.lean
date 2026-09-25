import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Parameter
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.DistanceUpper
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Analysis.FunctionalAnalysis.SeminormBounds
import DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.TimeSlab
import DifferentialGeometry.Geometry.Metric.Distance.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology Bundle

namespace DifferentialGeometry

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private def pullbackSeminormWithin (g : SmoothRiemannianMetric I M) (ψ : F → M) (s : Set F) (x : F) :
    Seminorm ℝ F :=
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  (normSeminorm ℝ (TangentSpace I (ψ x))).comp
    (mfderivWithin 𝓘(ℝ, F) I ψ s x).toLinearMap

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem pullbackSeminormWithin_apply (g : SmoothRiemannianMetric I M) (ψ : F → M) (s : Set F)
    (x v : F) :
    pullbackSeminormWithin g ψ s x v = Real.sqrt (g.inner (ψ x)
      (mfderivWithin 𝓘(ℝ, F) I ψ s x v) (mfderivWithin 𝓘(ℝ, F) I ψ s x v)) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  change ‖mfderivWithin 𝓘(ℝ, F) I ψ s x v‖ = _
  rw [norm_eq_sqrt_real_inner]
  rfl

private theorem continuous_pullbackSeminormWithin
    (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ}
    (hquad : Continuous (metricTimeBundleQuad g K))
    {ψ : F → M} {s : Set F} (hψ : ContMDiffOn 𝓘(ℝ, F) I 1 ψ s)
    (hs : UniqueDiffOn ℝ s) :
    Continuous (fun q : ({t : ℝ // t ∈ K} × s) × F =>
      pullbackSeminormWithin (g q.1.1.1) ψ s q.1.2.1 q.2) := by
  let Q := ({t : ℝ // t ∈ K} × s) × F
  let lift : Q → TangentBundle 𝓘(ℝ, F) F := fun q => ⟨q.1.2.1, q.2⟩
  have hlift : Continuous lift :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).symm.continuous.comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  have hunique : UniqueMDiffOn 𝓘(ℝ, F) s := by
    intro x hx
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact hs x hx
  have htan := hψ.continuousOn_tangentMapWithin (le_refl 1) hunique
  have hc : Continuous (fun q : Q => tangentMapWithin 𝓘(ℝ, F) I ψ s (lift q)) :=
    htan.comp_continuous hlift (fun q => q.1.2.2)
  have hpull : Continuous (fun q : Q =>
      (q.1.1, tangentMapWithin 𝓘(ℝ, F) I ψ s (lift q))) :=
    (continuous_fst.comp continuous_fst).prodMk hc
  have hspeed := Real.continuous_sqrt.comp (hquad.comp hpull)
  refine hspeed.congr fun q => ?_
  exact (pullbackSeminormWithin_apply (g q.1.1.1) ψ s q.1.2.1 q.2).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_sqrt_inner_mfderivWithin_le_of_isCompact
    (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ}
    (hK : IsCompact K) (hquad : Continuous (metricTimeBundleQuad g K))
    {ψ : F → M} {s B : Set F} (hψ : ContMDiffOn 𝓘(ℝ, F) I 1 ψ s)
    (hs : UniqueDiffOn ℝ s) (hB : B ⊆ s) (hBcompact : IsCompact B) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ t ∈ K, ∀ w ∈ B, ∀ v : F,
      Real.sqrt ((g t).inner (ψ w)
        (mfderivWithin 𝓘(ℝ, F) I ψ s w v) (mfderivWithin 𝓘(ℝ, F) I ψ s w v)) ≤ L * ‖v‖ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompactSpace B := isCompact_iff_compactSpace.mp hBcompact
  let q : K × B → Seminorm ℝ F := fun p =>
    pullbackSeminormWithin (g p.1.1) ψ s p.2.1
  have hm : Continuous (fun w : B => (⟨w.1, hB w.2⟩ : s)) :=
    continuous_subtype_val.subtype_mk _
  let j : (K × B) × F → (K × s) × F := fun p =>
    ((p.1.1, ⟨p.1.2.1, hB p.1.2.2⟩), p.2)
  have hj : Continuous j :=
    ((continuous_fst.comp continuous_fst).prodMk
      (hm.comp (continuous_snd.comp continuous_fst))).prodMk continuous_snd
  have hall : Continuous (fun p : (K × s) × F =>
      pullbackSeminormWithin (g p.1.1.1) ψ s p.1.2.1 p.2) :=
    continuous_pullbackSeminormWithin g hquad hψ hs
  have hcomp := hall.comp hj
  have hc : Continuous (fun p : (K × B) × F => q p.1 p.2) := by
    simpa only [q, j, Function.comp_def] using hcomp
  obtain ⟨L, hL, hb⟩ := SeminormFamily.exists_le_mul_norm_of_compact q hc
  refine ⟨L, hL, fun t ht w hw v => ?_⟩
  simpa only [q, pullbackSeminormWithin_apply] using
    hb (⟨⟨t, ht⟩, ⟨w, hw⟩⟩ : K × B) v

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem continuousAt_riemannianEDistOf_center
    (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ} {t : ℝ}
    (ht : K ∈ 𝓝 t) (hquad : Continuous (metricTimeBundleQuad g K)) (O : M) :
    ContinuousAt (fun p : ℝ × M => riemannianEDistOf (g p.1) O p.2) (t, O) := by
  let e := extChartAt I O
  let s : Set E := e.target
  let y : E := e O
  have hy : y ∈ s := mem_extChartAt_target O
  have htK : t ∈ K := mem_of_mem_nhds ht
  let P := {t : ℝ // t ∈ K} × s
  let qnorm : P → Seminorm ℝ E := fun p =>
    pullbackSeminormWithin (g p.1.1) e.symm s p.2.1
  have hψ : ContMDiffOn 𝓘(ℝ, E) I 1 e.symm s := contMDiffOn_extChartAt_symm O
  have hqcont : Continuous (fun q : P × E => qnorm q.1 q.2) :=
    continuous_pullbackSeminormWithin g hquad hψ (uniqueDiffOn_extChartAt_target O)
  obtain ⟨L, hL, hbound⟩ := SeminormFamily.exists_eventually_le_mul_norm qnorm
    (p₀ := (⟨t, htK⟩, ⟨y, hy⟩)) hqcont.continuousAt
  rw [nhds_prod_eq, Filter.Eventually, Filter.mem_prod_iff] at hbound
  obtain ⟨U, hU, V, hV, hUV⟩ := hbound
  obtain ⟨T, hT, hTU⟩ := (mem_nhds_subtype K ⟨t, htK⟩ U).mp hU
  obtain ⟨W, hW, hWV⟩ := (mem_nhds_subtype s ⟨y, hy⟩ V).mp hV
  have htime : K ∩ T ∈ 𝓝 t := inter_mem ht hT
  have hcontrol (τ : ℝ) (hτ : τ ∈ K ∩ T) (w : E) (hw : w ∈ s ∩ W) (v : E) :
      Real.sqrt ((g τ).inner (e.symm w)
        (mfderivWithin 𝓘(ℝ, E) I e.symm s w v)
        (mfderivWithin 𝓘(ℝ, E) I e.symm s w v)) ≤ L * ‖v‖ := by
    have hp : (⟨τ, hτ.1⟩, ⟨w, hw.1⟩) ∈ U ×ˢ V :=
      ⟨hTU hτ.2, hWV hw.2⟩
    have hb := hUV hp v
    simpa only [qnorm, pullbackSeminormWithin_apply] using hb
  have hlocal : s ∩ W ∈ 𝓝[range I] y :=
    inter_mem (extChartAt_target_mem_nhdsWithin O) (nhdsWithin_le_nhds hW)
  obtain ⟨r, hr, hrcontrol⟩ := Metric.mem_nhdsWithin_iff.mp hlocal
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  change Tendsto (fun p : ℝ × M => riemannianEDistOf (g p.1) O p.2)
    (𝓝 (t, O)) (𝓝 (riemannianEDistOf (g t) O O))
  rw [riemannianEDistOf_self]
  apply ENNReal.tendsto_nhds_zero.2
  intro eps heps
  by_cases hepstop : eps = ⊤
  · exact Eventually.of_forall fun _ => by simp [hepstop]
  have hepsreal : 0 < eps.toReal := ENNReal.toReal_pos heps.ne' hepstop
  let delta : ℝ := min (r / 2) (eps.toReal / (2 * L))
  have hdelta : 0 < delta := lt_min (half_pos hr)
    (div_pos hepsreal (mul_pos (by norm_num) hLpos))
  have hdelta_r : delta < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hball : Metric.ball y delta ∩ range I ∈ 𝓝[range I] y :=
    inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds y hdelta)) self_mem_nhdsWithin
  have hspace : e ⁻¹' (Metric.ball y delta ∩ range I) ∈ 𝓝 O :=
    extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (I := I)
      (x := O) (mem_extChartAt_source (I := I) O) hball
  filter_upwards [prod_mem_nhds htime
    (inter_mem hspace (extChartAt_source_mem_nhds (I := I) O))] with p hp
  let z : E := e p.2
  have hz : z ∈ Metric.ball y delta ∩ range I := hp.2.1
  let A : Set E := Metric.ball y r ∩ range I
  have hzA : z ∈ A := ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp hz.1).trans hdelta_r), hz.2⟩
  have hyA : y ∈ A := ⟨Metric.mem_ball_self hr, extChartAt_target_subset_range O hy⟩
  have hseg : segment ℝ y z ⊆ A := ((convex_ball y r).inter I.convex_range).segment_subset hyA hzA
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g p.1).toRiemannianMetric⟩
  have hspeed : ∀ w ∈ A, ∀ v : E,
      ‖mfderivWithin 𝓘(ℝ, E) I e.symm s w v‖ₑ ≤ ENNReal.ofReal (L * ‖v‖) := by
    intro w hw v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    exact ENNReal.ofReal_le_ofReal (hcontrol p.1 hp.1 w (hrcontrol hw) v)
  have hdist := riemannianEDist_le_of_mfderivWithin_le
    hψ (fun _ hw => (hrcontrol hw).1) hspeed hseg
  have hcenter : e.symm y = O := e.left_inv (mem_extChartAt_source O)
  have hend : e.symm z = p.2 := e.left_inv hp.2.2
  change Manifold.riemannianEDist I O p.2 ≤ eps
  rw [← hcenter, ← hend]
  apply hdist.trans
  have hzdist : dist y z < delta := by simpa only [Metric.mem_ball, dist_comm] using hz.1
  have hmul : L * dist y z < eps.toReal := by
    calc
      L * dist y z < L * delta := mul_lt_mul_of_pos_left hzdist hLpos
      _ ≤ L * (eps.toReal / (2 * L)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hLpos.le
      _ = eps.toReal / 2 := by field_simp
      _ < eps.toReal := by linarith
  exact ((ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg hLpos.le dist_nonneg) hepstop).2 hmul).le

end DifferentialGeometry

end

noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}
  {g : ℝ → SmoothRiemannianMetric I M}

private theorem metric_deriv_sup_continuousAt
    (hg : MetricFamilySmoothOn D g) {t : ℝ} (ht : t ∈ D.regular)
    {K : Set M} (hK : IsCompact K) (n : ℕ) :
    ContinuousAt (fun s => metricDerivNormSupOn K n (g s)
      (g t) (g t)) t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hc : ContinuousOn (fun s => metricDerivNormSupOn K n (g s)
      (g t) (g t)) D.regular := by
    apply metricDerivNormSupOn_continuousOn g (fun _ => g t)
      (fun _ => g t) (U := univ) _ hK (subset_univ _) n
    intro x _
    refine ⟨(extChartAt I x).target, isOpen_extChartAt_target x, mem_extChartAt_target x, Subset.rfl, ?_⟩
    intro i j
    have hmain := chartGramOnE_joint_contDiffOn g D.regular
      (hg.metricCLMSection_contMDiffOn Subset.rfl) x i j
    have hfixed : ContDiffOn ℝ ∞ (fun z : ℝ × E => chartGramOnE (g t) x i j z.2)
        (D.regular ×ˢ (extChartAt I x).target) :=
      (chartGramOnE_contDiffOn (g t) x i j).comp contDiffOn_snd (fun _ hz => hz.2)
    exact ⟨hmain,hfixed,hfixed⟩
  exact hc.continuousAt (D.regular_isOpen.mem_nhds ht)

private theorem eventually_metric_upper_on_compact
    (hg : MetricFamilySmoothOn D g) {t : ℝ} (ht : t ∈ D.regular)
    (K : Set M) (hK : IsCompact K) {B : ℝ} (hB : 1 < B) :
    ∀ᶠ s in 𝓝 t, ∀ z ∈ K, ∀ v : TangentSpace I z,
      (g s).inner z v v ≤ B^2 * (g t).inner z v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hsmall : 0 < B^2-1 := by nlinarith
  have hc := metric_deriv_sup_continuousAt hg ht hK 0
  have hev : ∀ᶠ s in 𝓝 t,
      metricDerivNormSupOn K 0 (g s) (g t) (g t) < B^2-1 := by
    have hzero : metricDerivNormSupOn K 0 (g t) (g t) (g t) < B^2-1 := by
      simpa only [metricDerivNormSupOn_self] using hsmall
    exact hc.eventually (Iio_mem_nhds hzero)
  filter_upwards [hev] with s hs
  intro z hz v
  have hnorm := derivNorm_le_sup hK (show (0:ℕ) ≤ 0 by rfl)
    (g s) (g t) (g t) hz
  have hbound := (Geometry.Metric.inner_bounds_of_metricDerivNorm_le
    (g t) (g s) z (hnorm.trans hs.le) v).2
  simpa only [add_sub_cancel] using hbound


private theorem eventually_edist_lt_of_lt
    (hg : MetricFamilySmoothOn D g) {t : ℝ} (ht : t ∈ D.regular) (x z : M)
    {R : ℝ} (hR : riemannianEDistOf (g t) x z < ENNReal.ofReal R) :
    ∀ᶠ q : (ℝ × M) × M in 𝓝 ((t,x),z),
      riemannianEDistOf (g q.1.1) q.1.2 q.2 < ENNReal.ofReal R := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let d := (riemannianEDistOf (g t) x z).toReal
  have hd : d < R := ENNReal.toReal_lt_of_lt_ofReal hR
  let e := (R-d)/4
  have he : 0 < e := div_pos (sub_pos.mpr hd) (by norm_num)
  have hinner : riemannianEDistOf (g t) x z < ENNReal.ofReal (R-2*e) := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt (ne_top_of_lt hR)).mpr
    change d < R-2*e
    dsimp only [e]
    linarith
  have hmiddle := Geometry.Riemannian.eventually_riemannianEDistOf_lt_of_compact_metric_upper
    (g t) g (fun K hK B hB => eventually_metric_upper_on_compact hg ht K hK hB)
    x z hinner
  have hquad := metricTimeBundleQuad_cont_of_metricFamilySmoothOn g hg (subset_refl D.carrier)
  have hcenterX := continuousAt_riemannianEDistOf_center g
    (D.regular_mem_nhds ht) hquad x
  have hcenterZ := continuousAt_riemannianEDistOf_center g
    (D.regular_mem_nhds ht) hquad z
  have hX : ∀ᶠ p : ℝ × M in 𝓝 (t,x),
      riemannianEDistOf (g p.1) x p.2 < ENNReal.ofReal e := by
    have hzero : riemannianEDistOf (g t) x x < ENNReal.ofReal e := by
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr he
    exact hcenterX.eventually (Iio_mem_nhds hzero)
  have hZ : ∀ᶠ p : ℝ × M in 𝓝 (t,z),
      riemannianEDistOf (g p.1) z p.2 < ENNReal.ofReal e := by
    have hzero : riemannianEDistOf (g t) z z < ENNReal.ofReal e := by
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr he
    exact hcenterZ.eventually (Iio_mem_nhds hzero)
  have hparam : Continuous (fun q : (ℝ × M) × M => (q.1.1,q.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hmiddlet : ∀ᶠ q : (ℝ × M) × M in 𝓝 ((t,x),z),
      riemannianEDistOf (g q.1.1) x z < ENNReal.ofReal (R-2*e) :=
    ((continuous_fst.comp continuous_fst).tendsto ((t,x),z)).eventually hmiddle
  filter_upwards [(continuous_fst.tendsto ((t,x),z)).eventually hX,
    hparam.continuousAt.eventually hZ, hmiddlet] with q hx hz hm
  have heq : ENNReal.ofReal e + ENNReal.ofReal (R-2*e) + ENNReal.ofReal e = ENNReal.ofReal R := by
    have hmid : 0 ≤ R-2*e := by dsimp only [e,d]; linarith [ENNReal.toReal_nonneg (a := riemannianEDistOf (g t) x z)]
    rw [← ENNReal.ofReal_add he.le hmid, ← ENNReal.ofReal_add (by positivity) he.le]
    congr 1
    ring
  have hb := (riemannianEDistOf_triangle (g q.1.1) q.1.2 x q.2).trans
    (add_le_add le_rfl (riemannianEDistOf_triangle (g q.1.1) x z q.2))
  rw [riemannianEDistOf_comm (g q.1.1) q.1.2 x] at hb
  exact hb.trans_lt ((ENNReal.add_lt_add hx (ENNReal.add_lt_add hm hz)).trans_eq (by rw [← add_assoc, heq]))

theorem MetricFamilySmoothOn.eventually_compact_subset_ball
    (hg : MetricFamilySmoothOn D g) {t : ℝ} (ht : t ∈ D.regular) (x : M)
    {K : Set M} (hK : IsCompact K) {R : ℝ}
    (hball : K ⊆ riemannianBallOf (g t) x R) :
    ∀ᶠ p : ℝ × M in 𝓝 (t,x), K ⊆ riemannianBallOf (g p.1) p.2 R := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply hK.eventually_forall_of_forall_eventually
  intro z hz
  exact eventually_edist_lt_of_lt hg ht x z (hball hz)

end DifferentialGeometry.Geometry.Curvature

end
