import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRescaling
import DifferentialGeometry.Geometry.Metric.ConeDistance

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {W : Type*} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
  {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
  {ray : EndRay H.endpoint} {d : ℕ → ℝ}

attribute [local instance] EndAngles.metric

def AnnularConvergence.compSubseq (C : AnnularConvergence H angles ray d)
    (s : ℕ → ℕ) (hs : StrictMono s) : AnnularConvergence H angles ray (d ∘ s) where
  relation a b i := C.relation a b (s i)
  error a b i := C.error a b (s i)
  error_pos a b i := C.error_pos a b (s i)
  error_zero a b ha hab := (C.error_zero a b ha hab).comp hs.tendsto_atTop
  annuli a b ha hab := hs.tendsto_atTop.eventually (C.annuli a b ha hab)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] EndAngles.metric

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem AnnularConvergence.exists_annular_selection
    {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g}
    {angles : EndAngles H} {ray : EndRay H.endpoint} {d : ℕ → ℝ}
    (C : AnnularConvergence H angles ray d) {Q : Type*}
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (w : ℕ → Q → W)
    (hw : ∀ᶠ i in atTop, ∀ p : Q,
      dist (w i p : UniformSpace.Completion W) H.endpoint / d i ∈ Icc a b) :
    ∃ (f : ℕ → Q → Icc a b × UniformSpace.Completion angles.quotient)
      (z : ℕ → Q → W),
      ∀ᶠ i in atTop, ∀ p : Q,
        (((f i p).1.1, (f i p).2), z i p) ∈ C.relation a b i ∧
          dist (w i p) (z i p) / d i < C.error a b i := by
  classical
  have hchoose : ∀ᶠ i in atTop, ∀ p : Q,
      ∃ q : Icc a b × UniformSpace.Completion angles.quotient,
        ∃ y : W, (((q.1.1, q.2), y) ∈ C.relation a b i) ∧
          dist (w i p) y / d i < C.error a b i := by
    filter_upwards [C.annuli a b ha hab, hw] with i hi hwi
    intro p
    obtain ⟨q, y, hqy, hclose⟩ := hi.2.2.2.1 (w i p) (hwi p)
    have hqrad : q.1 ∈ Icc a b := (hi.2.1 q y hqy).1
    exact ⟨(⟨q.1, hqrad⟩, q.2), y, hqy, hclose⟩
  let default : (Icc a b × UniformSpace.Completion angles.quotient) × W :=
    ((⟨a, le_rfl, hab.le⟩, (angles.classOf ray : UniformSpace.Completion angles.quotient)),
      ray.point 0)
  let selected : ℕ → Q → (Icc a b × UniformSpace.Completion angles.quotient) × W :=
    fun i p => if h : ∀ p : Q, ∃ q : Icc a b × UniformSpace.Completion angles.quotient,
        ∃ y : W, (((q.1.1, q.2), y) ∈ C.relation a b i) ∧
          dist (w i p) y / d i < C.error a b i then
      (Classical.choose (h p), Classical.choose (Classical.choose_spec (h p))) else default
  refine ⟨fun i p => (selected i p).1, fun i p => (selected i p).2, ?_⟩
  filter_upwards [hchoose] with i hi
  intro p
  simpa only [selected, dite_eq_left hi] using
    Classical.choose_spec (Classical.choose_spec (hi p))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]

attribute [local instance] EndAngles.metric

theorem AnnularConvergence.exists_curvature_rescaled_marked_representatives
    {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
    [CompactSpace (UniformSpace.Completion angles.quotient)]
    {ray : EndRay H.endpoint} {d : ℕ → ℝ} (C : AnnularConvergence H angles ray d)
    {a b lambda A : ℝ} (ha : 0 < a) (ha1 : a < 1) (h1b : 1 < b)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (hscale : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2)) atTop (𝓝 lambda))
    (x : ℝ × UniformSpace.Completion angles.quotient) (hx : x.1 ∈ Icc a b)
    (hA : lambda * Metric.coneDistance
      (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) x < A) :
    ∃ (y : ℕ → ℝ × UniformSpace.Completion angles.quotient) (w : ℕ → W),
      Tendsto y atTop (𝓝 x) ∧
      (∀ᶠ i in atTop, (y i, w i) ∈ C.relation a b i ∧
        Metric.coneDistance x (y i) < C.error a b i) ∧
      Tendsto (fun i => metricDistance
        (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
          (ray.point (d i)) (w i)) atTop
        (𝓝 (lambda * Metric.coneDistance
          (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) x)) ∧
      ∀ᶠ i in atTop, metricDistance
        (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
          (ray.point (d i)) (w i) < A := by
  classical
  have hab : a < b := ha1.trans h1b
  let B := Icc a b × UniformSpace.Completion angles.quotient
  let P : B → ℝ × UniformSpace.Completion angles.quotient := fun z => (z.1.1, z.2)
  let xB : B := (⟨x.1, hx⟩, x.2)
  have hP : Continuous P :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  let good (i : ℕ) : Prop := ∃ y : B, ∃ w : W,
    (P y, w) ∈ C.relation a b i ∧ Metric.coneDistance x (P y) < C.error a b i
  have hgood : ∀ᶠ i in atTop, good i := by
    filter_upwards [C.annuli a b ha hab] with i hi
    obtain ⟨y, w, hyw, hnear⟩ := hi.2.2.1 x hx
    exact ⟨(⟨y.1, (hi.2.1 y w hyw).1⟩, y.2), w, hyw, hnear⟩
  have hchoose : ∀ i, ∃ y : B, ∃ w : W, good i →
        (P y, w) ∈ C.relation a b i ∧ Metric.coneDistance x (P y) < C.error a b i := by
    intro i
    by_cases hi : good i
    · obtain ⟨y, w, hyw, hnear⟩ := hi
      exact ⟨y, w, fun _ => ⟨hyw, hnear⟩⟩
    · exact ⟨xB, ray.point (d i), fun h => (hi h).elim⟩
  choose y w hy using hchoose
  have hrel : ∀ᶠ i in atTop,
      (P (y i), w i) ∈ C.relation a b i ∧ Metric.coneDistance x (P (y i)) < C.error a b i := by
    filter_upwards [hgood] with i hi
    exact hy i hi
  have hnear : Tendsto (fun i => Metric.coneDistance x (P (y i))) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i => Real.sqrt_nonneg _) ?_
      (C.error_zero a b ha hab)
    exact hrel.mono fun _ hi => hi.2.le
  have hyB : Tendsto y atTop (𝓝 xB) := by
    apply (isCompact_univ : IsCompact (univ : Set B)).tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall fun _ => mem_univ _)
    intro z _ hz
    have hc : Continuous (fun z : B => Metric.coneDistance x (P z)) :=
      Metric.continuous_coneDistance.comp (continuous_const.prodMk hP)
    have hcluster := hz.continuousAt_comp hc.continuousAt
    have heq : Metric.coneDistance x (P z) = 0 :=
      eq_of_nhds_neBot (hcluster.clusterPt.mono hnear)
    have hzpos : 0 < (P z).1 := ha.trans_le z.1.2.1
    have hp := (Metric.coneDistance_eq_zero_iff (ha.trans_le hx.1) hzpos).mp heq
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hp).symm)
      (congrArg Prod.snd hp).symm
  have hyx : Tendsto (fun i => P (y i)) atTop (𝓝 x) := hP.continuousAt.tendsto.comp hyB
  let o : ℝ × UniformSpace.Completion angles.quotient :=
    (1, (angles.classOf ray : UniformSpace.Completion angles.quotient))
  have hcone : Tendsto (fun i => Metric.coneDistance o (P (y i))) atTop
      (𝓝 (Metric.coneDistance o x)) :=
    Metric.continuous_coneDistance.continuousAt.tendsto.comp
      (tendsto_const_nhds.prodMk_nhds hyx)
  have hdist : Tendsto (fun i => dist (ray.point (d i)) (w i) / d i) atTop
      (𝓝 (Metric.coneDistance o x)) := by
    have hdiff : Tendsto (fun i => Metric.coneDistance o (P (y i)) -
        dist (ray.point (d i)) (w i) / d i) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        (C.error_zero a b ha hab)
      filter_upwards [C.annuli a b ha hab, hrel] with i hi hri
      exact (hi.2.2.2.2.1 o (ray.point (d i)) (P (y i)) (w i)
        (hi.2.2.2.2.2.2 ha1 h1b) hri.1).le
    simpa only [sub_sub_cancel, sub_zero] using hcone.sub hdiff
  have hscaled := hscale.mul hdist
  have hscaled' : Tendsto (fun i => metricDistance
      (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
        (ray.point (d i)) (w i)) atTop (𝓝 (lambda * Metric.coneDistance o x)) := by
    have hfun : (fun i => metricDistance
        (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
          (ray.point (d i)) (w i)) = fun i =>
        Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) *
          (dist (ray.point (d i)) (w i) / d i) := by
      funext i
      exact rescaled_distance_eq_radial_scale_mul H (hQ i) (hd i).1 _ _
    rw [hfun]
    exact hscaled
  exact ⟨fun i => P (y i), w, hyx, hrel, hscaled',
    hscaled'.eventually (eventually_lt_nhds hA)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {W : Type*} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
  {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
  {ray : EndRay H.endpoint} {d : ℕ → ℝ}

attribute [local instance] EndAngles.metric

theorem AnnularConvergence.tendsto_curvature_scaled_distance_of_representatives
    (C : AnnularConvergence H angles ray d) {a b lambda : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (hscale : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2)) atTop (𝓝 lambda))
    (x y : ℕ → ℝ × UniformSpace.Completion angles.quotient) (w z : ℕ → W)
    {x₀ y₀ : ℝ × UniformSpace.Completion angles.quotient}
    (hx : Tendsto x atTop (𝓝 x₀)) (hy : Tendsto y atTop (𝓝 y₀))
    (hw : ∀ᶠ i in atTop, (x i, w i) ∈ C.relation a b i)
    (hz : ∀ᶠ i in atTop, (y i, z i) ∈ C.relation a b i) :
    Tendsto (fun i => metricDistance
      (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g) (w i) (z i)) atTop
      (𝓝 (lambda * Metric.coneDistance x₀ y₀)) := by
  have hcone := Metric.continuous_coneDistance.continuousAt.tendsto.comp (hx.prodMk_nhds hy)
  have herr : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2) * C.error a b i) atTop (𝓝 0) := by
    simpa only [mul_zero] using hscale.mul (C.error_zero a b ha hab)
  have hdiff : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2) * Metric.coneDistance (x i) (y i) -
        metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
          (w i) (z i)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ herr
    filter_upwards [C.annuli a b ha hab, hw, hz] with i hi hwi hzi
    rw [Real.norm_eq_abs, rescaled_distance_eq_radial_scale_mul H (hQ i) (hd i).1,
      ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hi.2.2.2.2.1 _ _ _ _ hwi hzi).le
      (Real.sqrt_nonneg _)
  simpa only [Function.comp_apply, sub_sub_cancel, sub_zero] using (hscale.mul hcone).sub hdiff

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {W : Type*} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
  {g : SmoothRiemannianMetric I3 W} {H : FiniteHorn g} {angles : EndAngles H}
  {ray : EndRay H.endpoint} {d : ℕ → ℝ}

attribute [local instance] EndAngles.metric

theorem AnnularConvergence.tendsto_rescaled_distance_of_approximated_representatives
    (C : AnnularConvergence H angles ray d) {a b lambda : ℝ} (ha : 0 < a) (hab : a < b)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (hscale : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2)) atTop (𝓝 lambda))
    {l : Filter ℕ} (hl : l ≤ atTop)
    (x y : ℕ → ℝ × UniformSpace.Completion angles.quotient) (w z v : ℕ → W)
    {x₀ y₀ : ℝ × UniformSpace.Completion angles.quotient}
    (hx : Tendsto x l (𝓝 x₀)) (hy : Tendsto y l (𝓝 y₀))
    (hw : ∀ᶠ i in l, (x i, w i) ∈ C.relation a b i)
    (hz : ∀ᶠ i in l, (y i, z i) ∈ C.relation a b i)
    (hnear : Tendsto (fun i => dist (v i) (z i) / d i) l (𝓝 0)) :
    Tendsto (fun i => metricDistance
      (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g) (w i) (v i)) l
      (𝓝 (lambda * Metric.coneDistance x₀ y₀)) := by
  have hcone := Metric.continuous_coneDistance.continuousAt.tendsto.comp (hx.prodMk_nhds hy)
  have hdiff : Tendsto (fun i => Metric.coneDistance (x i) (y i) -
      dist (w i) (z i) / d i) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      ((C.error_zero a b ha hab).mono_left hl)
    filter_upwards [hl (C.annuli a b ha hab), hw, hz] with i hi hwi hzi
    simpa only [Real.norm_eq_abs] using (hi.2.2.2.2.1 _ _ _ _ hwi hzi).le
  have hrel : Tendsto (fun i => dist (w i) (z i) / d i) l
      (𝓝 (Metric.coneDistance x₀ y₀)) := by
    simpa only [Function.comp_apply, sub_sub_cancel, sub_zero] using hcone.sub hdiff
  have hperturb : Tendsto (fun i => dist (w i) (v i) / d i -
      dist (w i) (z i) / d i) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hnear
    exact Eventually.of_forall fun i => by
      rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos (hd i).1]
      simpa only [dist_comm (v i) (w i), dist_comm (z i) (w i)] using
        div_le_div_of_nonneg_right (abs_dist_sub_le (v i) (z i) (w i)) (hd i).1.le
  have hdist : Tendsto (fun i => dist (w i) (v i) / d i) l
      (𝓝 (Metric.coneDistance x₀ y₀)) := by
    simpa only [sub_add_cancel, zero_add] using hperturb.add hrel
  have hscaled := (hscale.mono_left hl).mul hdist
  apply hscaled.congr'
  exact Eventually.of_forall fun i =>
    (rescaled_distance_eq_radial_scale_mul H (hQ i) (hd i).1 (w i) (v i)).symm


theorem eventually_radial_mem_of_rescaled_distance_le
    {a b lambda delta : ℝ} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (ha1 : a < 1) (h1b : 1 < b) (hlambda : 0 < lambda)
    (hda : delta < lambda / 2 * (1 - a)) (hdb : delta < lambda / 2 * (b - 1))
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (hscale : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2)) atTop (𝓝 lambda)) :
    ∀ᶠ i in atTop, ∀ w : W,
      metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
        (ray.point (d i)) w ≤ delta →
      dist (w : UniformSpace.Completion W) H.endpoint / d i ∈ Ioo a b := by
  filter_upwards [hscale.eventually (eventually_gt_nhds (by linarith : lambda / 2 < lambda))]
    with i hi
  intro w hw
  have hs : 0 < Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) :=
    lt_trans (by positivity : 0 < lambda / 2) hi
  have hr := radial_ratio_sub_one_le_rescaled_distance H ray (hQ i) (hd i) w
  have hb := ((le_div_iff₀ hs).mp hr).trans hw
  have hlo := neg_abs_le (dist (w : UniformSpace.Completion W) H.endpoint / d i - 1)
  have hhi := le_abs_self (dist (w : UniformSpace.Completion W) H.endpoint / d i - 1)
  have hda' : delta < Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) * (1 - a) :=
    hda.trans (mul_lt_mul_of_pos_right hi (by linarith))
  have hdb' : delta < Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) * (b - 1) :=
    hdb.trans (mul_lt_mul_of_pos_right hi (by linarith))
  constructor <;> nlinarith

theorem AnnularConvergence.rescaled_cone_distance_le_of_captured_limit
    (C : AnnularConvergence H angles ray d) {a b lambda delta : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (h1b : 1 < b)
    (hd : ∀ i, d i ∈ Ioc 0 ray.length)
    (hQ : ∀ i, 0 < metricScalarAt g (ray.point (d i)))
    (hscale : Tendsto (fun i => Real.sqrt
      (metricScalarAt g (ray.point (d i)) * d i ^ 2)) atTop (𝓝 lambda))
    {l : Filter ℕ} [NeBot l] (hl : l ≤ atTop)
    (y : ℕ → ℝ × UniformSpace.Completion angles.quotient) (z v : ℕ → W)
    {x : ℝ × UniformSpace.Completion angles.quotient}
    (hy : Tendsto y l (𝓝 x))
    (hz : ∀ᶠ i in l, (y i, z i) ∈ C.relation a b i)
    (hnear : Tendsto (fun i => dist (v i) (z i) / d i) l (𝓝 0))
    (hbound : ∀ᶠ i in l,
      metricDistance (scaleMetric (metricScalarAt g (ray.point (d i))) (hQ i) g)
        (ray.point (d i)) (v i) ≤ delta) :
    lambda * Metric.coneDistance
      (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)) x ≤ delta := by
  have hbase : ∀ᶠ i in l,
      ((1, (angles.classOf ray : UniformSpace.Completion angles.quotient)), ray.point (d i)) ∈
        C.relation a b i := by
    filter_upwards [hl (C.annuli a b ha (ha1.trans h1b))] with i hi
    exact hi.2.2.2.2.2.2 ha1 h1b
  have ht := C.tendsto_rescaled_distance_of_approximated_representatives ha (ha1.trans h1b)
    hd hQ hscale hl (fun _ => (1, (angles.classOf ray : UniformSpace.Completion angles.quotient)))
    y (fun i => ray.point (d i)) z v tendsto_const_nhds hy hbase hz hnear
  exact le_of_tendsto ht hbound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
