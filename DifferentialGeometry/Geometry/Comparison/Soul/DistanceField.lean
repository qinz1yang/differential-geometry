import DifferentialGeometry.Geometry.Comparison.Soul.SoulAngles
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem continuous_scaled_vector
    {P : Type*} [TopologicalSpace P] {b : P → M}
    {v : (x : P) → TangentSpace I (b x)} {f : P → ℝ}
    (hv : Continuous (fun x => (⟨b x, v x⟩ : TangentBundle I M)))
    (hf : Continuous f) :
    Continuous (fun x => (⟨b x, f x • v x⟩ : TangentBundle I M)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hvc := (FiberBundle.continuousAt_totalSpace E _).mp (hv.continuousAt (x := x))
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hvc.1, ?_⟩
  let e := trivializationAt E (TangentSpace I) (b x)
  have he : ∀ᶠ y in 𝓝 x, b y ∈ e.baseSet :=
    hvc.1.preimage_mem_nhds (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ _))
  apply (hf.continuousAt.smul hvc.2).congr_of_eventuallyEq
  filter_upwards [he] with y hy
  exact (e.linear ℝ hy).map_smul (f y) (v y)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem continuous_metric_inner
    (g : SmoothRiemannianMetric I M)
    {P : Type*} [TopologicalSpace P] {b : P → M}
    {v w : (x : P) → TangentSpace I (b x)}
    (hv : Continuous (fun x => (⟨b x, v x⟩ : TangentBundle I M)))
    (hw : Continuous (fun x => (⟨b x, w x⟩ : TangentBundle I M))) :
    Continuous (fun x => g.inner (b x) (v x) (w x)) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact hv.inner_bundle hw

theorem eventually_infDist_minimizing_inner_lt
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsClosed S) (q : M) (W : (y : M) → TangentSpace I y)
    (hW : Continuous (fun y => (⟨y, W y⟩ : TangentBundle I M))) (c : ℝ)
    (hneg : ∀ u : TangentSpace I q, g.inner q u u = 1 →
      intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S →
      g.inner q (W q) u < c) :
    ∀ᶠ y in 𝓝 q, ∀ u : TangentSpace I y, g.inner y u u = 1 →
      intrinsicGeodesic g hEnorm y u (Metric.infDist y S) ∈ S →
      g.inner y (W y) u < c := by
  let b : MetricUnitTangent (I := I) g → M := MetricUnitTangent.base
  let v : (z : MetricUnitTangent (I := I) g) → TangentSpace I (b z) :=
    MetricUnitTangent.vec
  have hb : Continuous b :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  have hv : Continuous (fun z => (⟨b z, v z⟩ : TangentBundle I M)) := continuous_subtype_val
  have hscale := continuous_scaled_vector (I := I)
    (f := fun z => Metric.infDist (b z) S) hv ((Metric.continuous_infDist_pt S).comp hb)
  have hend : Continuous (fun z => expMapIntrinsic g hEnorm (b z)
      (Metric.infDist (b z) S • v z)) :=
    (intrinsicExp_smooth g hEnorm).continuous.comp hscale
  have hinner : Continuous (fun z => g.inner (b z) (W (b z)) (v z)) :=
    continuous_metric_inner g (hW.comp hb) hv
  let bad : Set (MetricUnitTangent (I := I) g) :=
    {z | expMapIntrinsic g hEnorm (b z) (Metric.infDist (b z) S • v z) ∈ S ∧
      c ≤ g.inner (b z) (W (b z)) (v z)}
  have hbad : IsClosed bad :=
    (hS.preimage hend).inter (isClosed_le continuous_const hinner)
  have hproper : IsProperMap b := isProperMap_iff_isCompact_preimage.mpr
    ⟨hb, fun _ hK => metricUnitOn_compact g hK⟩
  have hq : q ∈ (b '' bad)ᶜ := by
    rintro ⟨⟨⟨y, u⟩, hu⟩, hbad, hy⟩
    change y = q at hy
    subst y
    change expMapIntrinsic g hEnorm q (Metric.infDist q S • u) ∈ S ∧
      c ≤ g.inner q (W q) u at hbad
    have hup : intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S := by
      simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hbad.1
    exact (not_lt_of_ge hbad.2) (hneg u hu hup)
  filter_upwards [(hproper.isClosedMap bad hbad).isOpen_compl.mem_nhds hq] with y hy
  intro u hu hup
  by_contra h
  apply hy
  refine ⟨⟨⟨y, u⟩, hu⟩, ?_, rfl⟩
  change expMapIntrinsic g hEnorm y (Metric.infDist y S • u) ∈ S ∧
    c ≤ g.inner y (W y) u
  exact ⟨by simpa only [expMapIntrinsic_def, intrinsicGeodesic_smul] using hup, le_of_not_gt h⟩

theorem exists_smooth_outward_field_infDist
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {S : Set M} (hS : IsClosed S) {a b : ℝ} (hab : a < b)
    (hout : ∀ q : M, b ≤ Metric.infDist q S →
      ∃ v : TangentSpace I q, g.inner q v v = 1 ∧
        ∀ u : TangentSpace I q, g.inner q u u = 1 →
          intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S →
          g.inner q v u < 0) :
    ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ q, g.inner q (X q) (X q) < 4) ∧
      (∀ q, Metric.infDist q S ≤ a → X q = 0) ∧
      ∀ q, b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
        intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S →
        g.inner q (X q) u < 0 := by
  classical
  let t : (q : M) → Set (TangentSpace I q) := fun q =>
    {w | g.inner q w w < 4 ∧ (Metric.infDist q S ≤ a → w = 0) ∧
      (b ≤ Metric.infDist q S → ∀ u : TangentSpace I q, g.inner q u u = 1 →
        intrinsicGeodesic g hEnorm q u (Metric.infDist q S) ∈ S → g.inner q w u < 0)}
  have ht (q : M) : Convex ℝ (t q) := by
    intro x hx y hy α β hα hβ hαβ
    have hid : g.inner q (α • x + β • y) (α • x + β • y) =
        (α + β) * (α * g.inner q x x + β * g.inner q y y) -
          α * β * g.inner q (x - y) (x - y) := by
      simp only [map_add, map_smul, add_apply, _root_.smul_apply, smul_eq_mul,
        map_sub, sub_apply, g.symm q y x]
      ring
    have hpos := mul_nonneg (mul_nonneg hα hβ) (gInner_self_nonneg g q (x - y))
    have hbound : α * g.inner q x x + β * g.inner q y y < 4 := by
      by_cases hα0 : α = 0
      · have hβ1 : β = 1 := by linarith
        simpa [hα0, hβ1] using hy.1
      · have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        have hαx := mul_lt_mul_of_pos_left hx.1 hαp
        have hβy := mul_le_mul_of_nonneg_left hy.1.le hβ
        nlinarith only [hαx, hβy, hαβ]
    refine ⟨?_, ?_, ?_⟩
    · rw [hid, hαβ, one_mul]
      linarith
    · intro hq
      rw [hx.2.1 hq, hy.2.1 hq, smul_zero, smul_zero, add_zero]
    · intro hq u hu hup
      have hxu := hx.2.2 hq u hu hup
      have hyu := hy.2.2 hq u hu hup
      simp only [map_add, map_smul, add_apply, _root_.smul_apply, smul_eq_mul]
      by_cases hα0 : α = 0
      · have hβ1 : β = 1 := by linarith
        simpa only [hα0, hβ1, zero_mul, one_mul, zero_add] using hyu
      · have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hαp hxu)
          (mul_nonpos_of_nonneg_of_nonpos hβ hyu.le)
  have hloc (q : M) : ∃ U ∈ 𝓝 q, ∃ W : (y : M) → TangentSpace I y,
      ContMDiffOn I I.tangent ∞ (fun y => (⟨y, W y⟩ : TangentBundle I M)) U ∧
      ∀ y ∈ U, W y ∈ t y := by
    by_cases hq : Metric.infDist q S < b
    · refine ⟨{y | Metric.infDist y S < b},
        (isOpen_lt (Metric.continuous_infDist_pt S) continuous_const).mem_nhds hq,
        fun _ => 0, (0 : Cₛ^∞⟮I; E, TangentSpace I⟯).contMDiff.contMDiffOn, ?_⟩
      intro y hy
      refine ⟨by simp, fun _ => rfl, ?_⟩
      intro hfar
      exact ((not_le_of_gt hy) hfar).elim
    · have hfar : a < Metric.infDist q S := hab.trans_le (le_of_not_gt hq)
      obtain ⟨v, hv, hvu⟩ := hout q (le_of_not_gt hq)
      obtain ⟨W, hWq⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (n := ⊤) q v
      have hneg := eventually_infDist_minimizing_inner_lt g hEnorm hS q W
        W.contMDiff.continuous 0 (by
          intro u hu hup
          rw [hWq]
          exact hvu u hu hup)
      have hnorm : ∀ᶠ y in 𝓝 q, g.inner y (W y) (W y) < 4 :=
        (continuous_metric_inner g W.contMDiff.continuous W.contMDiff.continuous).continuousAt
          (gt_mem_nhds (by rw [hWq, hv]; norm_num))
      have houter : ∀ᶠ y in 𝓝 q, a < Metric.infDist y S :=
        (Metric.continuous_infDist_pt S).continuousAt (lt_mem_nhds hfar)
      refine ⟨_, hneg.and (hnorm.and houter), W, W.contMDiff.contMDiffOn, ?_⟩
      intro y hy
      exact ⟨hy.2.1, fun hle => ((not_lt_of_ge hle) hy.2.2).elim,
        fun _ u hu hup => hy.1 u hu hup⟩
  obtain ⟨X, hX⟩ := exists_contMDiffSection_forall_mem_convex_of_local I
    (TangentSpace I) t ht hloc
  exact ⟨X, fun q => (hX q).1, fun q => (hX q).2.1, fun q => (hX q).2.2⟩

end DifferentialGeometry.Geometry.Topology
