import DifferentialGeometry.Geometry.Metric.Comparison.DerivativeDistance
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Approximation.MarkedPointEvaluation















set_option autoImplicit false

noncomputable section
open Set Filter Manifold Bundle TopologicalSpace
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry.Metric

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private abbrev distanceLimitBilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private abbrev distanceLimitBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
attribute [local instance] distanceLimitBilinearGroup distanceLimitBilinearSpace

private theorem relative_forms_of_norm_sub_le
    {B b : E →L[ℝ] E →L[ℝ] ℝ} {c η : ℝ}
    (hc : 0 < c) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hlower : ∀ v : E, c * ‖v‖ ^ 2 ≤ b v v)
    (hclose : ‖B - b‖ ≤ η * c) (v : E) :
    (1 - η) ^ 2 * b v v ≤ B v v ∧ B v v ≤ (1 + η) ^ 2 * b v v := by
  have hpos : 0 ≤ b v v := (mul_nonneg hc.le (sq_nonneg _)).trans (hlower v)
  have habs : |B v v - b v v| ≤ η * b v v := by
    calc
      |B v v - b v v| = ‖(B - b) v v‖ := by simp only [sub_apply, Real.norm_eq_abs]
      _ ≤ ‖B - b‖ * ‖v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm₂ (B - b) v v
      _ ≤ (η * c) * ‖v‖ * ‖v‖ := by gcongr
      _ = η * (c * ‖v‖ ^ 2) := by ring
      _ ≤ η * b v v := mul_le_mul_of_nonneg_left (hlower v) hη
  have hlo := (abs_le.mp habs).1
  have hhi := (abs_le.mp habs).2
  have hm : 0 ≤ η * (1 - η) * b v v := mul_nonneg (mul_nonneg hη (sub_nonneg.mpr hη1)) hpos
  have hp : 0 ≤ η * (1 + η) * b v v := mul_nonneg (mul_nonneg hη (by linarith)) hpos
  constructor <;> nlinarith

private theorem eventually_relative_forms_of_uniform_convergence
    {ι : Type*} {l : Filter ι} {S : Set E}
    {B : ι → E → E →L[ℝ] E →L[ℝ] ℝ} {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    {c η : ℝ} (hc : 0 < c) (hη : 0 < η) (hη1 : η ≤ 1)
    (hlower : ∀ x ∈ S, ∀ v : E, c * ‖v‖ ^ 2 ≤ b x v v)
    (hconv : TendstoUniformlyOn B b l S) :
    ∀ᶠ i in l, ∀ x ∈ S, ∀ v : E,
      (1 - η) ^ 2 * b x v v ≤ B i x v v ∧
      B i x v v ≤ (1 + η) ^ 2 * b x v v := by
  have he := (Metric.tendstoUniformlyOn_iff.mp hconv) (η * c) (mul_pos hη hc)
  filter_upwards [he] with i hi x hx v
  apply relative_forms_of_norm_sub_le hc hη.le hη1 (hlower x hx)
  simpa only [dist_eq_norm, norm_sub_rev] using (hi x hx).le

end

section
variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

private theorem contMDiffAt_to_open_subtype
    {U : Opens N} {f : M → U} {x : M}
    (hf : ContMDiffAt I J n (fun y => (f y : N)) x) :
    ContMDiffAt I J n f x := by
  rw [contMDiffAt_iff] at hf ⊢
  obtain ⟨hc, hd⟩ := hf
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hc, ?_⟩
  exact hd

private theorem restricted_chart_injective
    (Φ : OpenPartialHomeomorph M N) (U : Opens M) (hU : (U : Set M) ⊆ Φ.source) :
    Function.Injective (fun x : U => Φ (x : M)) := by
  intro x y hxy
  apply Subtype.ext
  exact Φ.toPartialEquiv.injOn (hU x.property) (hU y.property) hxy

private theorem restricted_chart_inverse_eq
    (Φ : OpenPartialHomeomorph M N) (U : Opens M) [Nonempty U]
    (hU : (U : Set M) ⊆ Φ.source) :
    EqOn (fun y => ((Function.invFun (fun x : U => Φ (x : M)) y : U) : M))
      Φ.symm ((Φ : M → N) '' (U : Set M)) := by
  rintro y ⟨x, hx, rfl⟩
  let u : U := ⟨x, hx⟩
  have hi := Function.leftInverse_invFun (restricted_chart_injective Φ U hU) u
  change ((Function.invFun (fun x : U => Φ (x : M)) (Φ (u : M)) : U) : M) = _
  rw [hi]
  exact (Φ.left_inv' (hU hx)).symm

private theorem restricted_chart_inverse_contMDiffOn
    (Φ : OpenPartialHomeomorph M N)
    (hΦinv : ContMDiffOn J I n Φ.symm Φ.target) (U : Opens M) [Nonempty U]
    (hU : (U : Set M) ⊆ Φ.source) :
    ContMDiffOn J I n (Function.invFun (fun x : U => Φ (x : M)))
      ((Φ : M → N) '' (U : Set M)) := by
  have hopen : IsOpen ((Φ : M → N) '' (U : Set M)) :=
    Φ.isOpen_image_of_subset_source U.isOpen hU
  intro y hy
  have hyt : y ∈ Φ.target := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact Φ.map_source (hU hx)
  have heq := (restricted_chart_inverse_eq Φ U hU).eventuallyEq_of_mem (hopen.mem_nhds hy)
  have hs : ContMDiffAt J I n (fun y =>
      ((Function.invFun (fun x : U => Φ (x : M)) y : U) : M)) y :=
    (hΦinv.contMDiffAt (Φ.open_target.mem_nhds hyt)).congr_of_eventuallyEq heq
  exact (contMDiffAt_to_open_subtype hs).contMDiffWithinAt

end

section
variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [MetricSpace M] [ChartedSpace H M]
  [MetricSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : N => TangentSpace J x)]
  [IsRiemannianManifold I M] [IsRiemannianManifold J N]

private theorem dist_map_le_of_speed_on_buffer
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I J 1 f U) {x y : M} {R : ℝ} {C : ℝ≥0}
    (hsub : Metric.closedBall x R ⊆ U)
    (hspeed : ∀ z ∈ Metric.closedBall x R,
      ∀ v : TangentSpace I z, ‖mfderiv I J f z v‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ)
    (hxy : dist x y < R) :
    dist (f x) (f y) ≤ (C : ℝ) * dist x y := by
  have hR : 0 < R := dist_nonneg.trans_lt hxy
  have hb := Manifold.edist_map_le_mul_of_enorm_mfderiv_le_on_closedEBall hU hf
    (x := x) (y := y) (R := R) (C := C)
    (by simpa only [Metric.closedEBall_ofReal hR.le] using hsub)
    (by simpa only [Metric.closedEBall_ofReal hR.le] using hspeed)
    (by simpa only [edist_dist, ENNReal.ofReal_lt_ofReal_iff hR] using hxy)
  have hb' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top x y)) hb
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg] using hb'

private theorem dist_map_le_of_speed
    {f : M → N} (hf : ContMDiff I J 1 f) {C : ℝ≥0}
    (hspeed : ∀ z, ∀ v : TangentSpace I z,
      ‖mfderiv I J f z v‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ) (x y : M) :
    dist (f x) (f y) ≤ (C : ℝ) * dist x y := by
  exact dist_map_le_of_speed_on_buffer isOpen_univ hf.contMDiffOn
    (R := dist x y + 1) (subset_univ _) (fun z _ => hspeed z) (by linarith)

omit [IsRiemannianManifold I M] [IsRiemannianManifold J N] in
private theorem inverse_speed_bound [Nonempty M]
    {f : M → N} (hf : ContMDiff I J 1 f)
    (hopen : IsOpen (range f))
    (hinv : ContMDiffOn J I 1 (Function.invFun f) (range f))
    {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x, ∀ v : TangentSpace I x,
      a * ‖v‖ ≤ ‖mfderiv I J f x v‖)
    {y : N} (hy : y ∈ range f) (w : TangentSpace J y) :
    ‖mfderiv J I (Function.invFun f) y w‖ ≤ a⁻¹ * ‖w‖ := by
  have hi := (hinv.contMDiffAt (hopen.mem_nhds hy)).mdifferentiableAt one_ne_zero
  have heq : f ∘ Function.invFun f =ᶠ[𝓝 y] id := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact Function.invFun_eq hz
  have hD := mfderiv_comp_apply y (hf.mdifferentiable one_ne_zero _) hi w
  have hmaps : mfderiv J J (f ∘ Function.invFun f) y = mfderiv J J (id : N → N) y :=
    heq.mfderiv_eq
  have hid := DFunLike.congr_fun hmaps w
  rw [mfderiv_id] at hid
  have hder : mfderiv I J f (Function.invFun f y)
      (mfderiv J I (Function.invFun f) y w) = w := hD.symm.trans hid
  have hp := Function.invFun_eq hy
  have hb := hlower (Function.invFun f y) (mfderiv J I (Function.invFun f) y w)
  rw [hder, hp] at hb
  exact (le_inv_mul_iff₀ ha).mpr hb

private theorem dist_le_inverse_mul_dist [Nonempty M]
    {f : M → N} (hf : ContMDiff I J 1 f) (hinj : Function.Injective f)
    (hopen : IsOpen (range f))
    (hinv : ContMDiffOn J I 1 (Function.invFun f) (range f))
    {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x, ∀ v : TangentSpace I x,
      a * ‖v‖ ≤ ‖mfderiv I J f x v‖)
    {x y : M} {R : ℝ} (hsub : Metric.closedBall (f x) R ⊆ range f)
    (hxy : dist (f x) (f y) < R) :
    dist x y ≤ a⁻¹ * dist (f x) (f y) := by
  let C : ℝ≥0 := ⟨a⁻¹, (inv_pos.mpr ha).le⟩
  have hb := dist_map_le_of_speed_on_buffer hopen hinv hsub
    (C := C) (fun z hz w => ?_) hxy
  · rw [Function.leftInverse_invFun hinj x, Function.leftInverse_invFun hinj y] at hb
    exact hb
  · have hr := ENNReal.ofReal_le_ofReal
      (inverse_speed_bound hf hopen hinv ha hlower (hsub hz) w)
    have hC : ENNReal.ofReal a⁻¹ = (C : ℝ≥0∞) := by
      change ENNReal.ofReal (C : ℝ) = (C : ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    simpa only [ENNReal.ofReal_mul (inv_pos.mpr ha).le, ofReal_norm, hC] using hr

end

section
open DifferentialGeometry
variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem restricted_map_norm_sq (g : SmoothRiemannianMetric I M)
    (Φ : E → M) (U : Opens E) (x : U) (v : E) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, E) I (fun w : U => Φ (w : E)) x v‖ ^ 2 =
      Geometry.pullbackMetricCoefficients g Φ (x : E) v v := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [← real_inner_self_eq_norm_sq]
  change g.inner (Φ (x : E)) _ _ = _
  rw [DifferentialGeometry.mfderiv_restrict_open]
  rfl

private theorem finite_metric_norm_sq (U : Opens E) (k : ℕ∞ω)
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, E) k E (TangentSpace 𝓘(ℝ, E) : U → Type _))
    (x : U) (v : TangentSpace 𝓘(ℝ, E) x) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) := ⟨h.toRiemannianMetric⟩
    ‖v‖ ^ 2 = h.inner x v v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : U → Type _) := ⟨h.toRiemannianMetric⟩
  rw [← real_inner_self_eq_norm_sq]
  rfl

end

section
variable {E M : Type*} [NormedAddCommGroup E] [MetricSpace M]

private theorem radial_chart_buffer {R : ℝ} (hR : 0 < R) (Φ : E → M)
    (himage : Φ '' Metric.ball 0 R = Metric.ball (Φ 0) R)
    (hrad : ∀ x ∈ Metric.ball 0 R, dist (Φ x) (Φ 0) = ‖x‖)
    (x y : (⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩ : Opens E))
    (hx : ‖(x : E)‖ ≤ R / 8) (hy : ‖(y : E)‖ ≤ R / 8) :
    Metric.closedBall (Φ (x : E)) (R / 3) ⊆
        range (fun w : (⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩ : Opens E) => Φ w) ∧
      dist (Φ (x : E)) (Φ (y : E)) < R / 3 := by
  constructor
  · intro z hz
    have hz' : z ∈ Metric.ball (Φ 0) R := by
      rw [Metric.mem_ball]
      calc
        dist z (Φ 0) ≤ dist z (Φ (x : E)) + dist (Φ (x : E)) (Φ 0) := dist_triangle _ _ _
        _ ≤ R / 3 + R / 8 := add_le_add hz (by rw [hrad x x.property]; exact hx)
        _ < R := by linarith
    rw [← himage] at hz'
    obtain ⟨w, hw, rfl⟩ := hz'
    exact ⟨⟨w, hw⟩, rfl⟩
  · calc
      dist (Φ (x : E)) (Φ (y : E)) ≤
          dist (Φ (x : E)) (Φ 0) + dist (Φ 0) (Φ (y : E)) := dist_triangle _ _ _
      _ = ‖(x : E)‖ + ‖(y : E)‖ := by rw [dist_comm (Φ 0), hrad x x.property, hrad y y.property]
      _ ≤ R / 8 + R / 8 := add_le_add hx hy
      _ < R / 3 := by linarith
end

section
open DifferentialGeometry Geometry
variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (R : ℝ)
local notation "Ω" => (Opens.mk (Metric.ball (0 : E) R) Metric.isOpen_ball)

private theorem finite_chart_distance_bounds
    (hR : 0 < R) (g : SmoothRiemannianMetric I M)
    (hg : letI : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩; IsRiemannianManifold I M)
    (Φ : OpenPartialHomeomorph E M)
    (hΦ : ContMDiffOn 𝓘(ℝ, E) I 1 Φ Φ.source)
    (hΦinv : ContMDiffOn I 𝓘(ℝ, E) 1 Φ.symm Φ.target)
    (hsource : (Ω : Set E) ⊆ Φ.source)
    (himage : (Φ : E → M) '' Metric.ball 0 R = Metric.ball (Φ 0) R)
    (hrad : ∀ x ∈ Metric.ball 0 R, dist (Φ x) (Φ 0) = ‖x‖)
    (k : ℕ∞ω) (h : ContMDiffRiemannianMetric 𝓘(ℝ, E) k E
      (TangentSpace 𝓘(ℝ, E) : Ω → Type _))
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hforms : ∀ (x : Ω) (v : E),
      a ^ 2 * h.inner x v v ≤ pullbackMetricCoefficients g Φ (x : E) v v ∧
      pullbackMetricCoefficients g Φ (x : E) v v ≤ b ^ 2 * h.inner x v v) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Ω → Type _) := ⟨h.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : Ω → Type _) :=
      ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : PreconnectedSpace Ω :=
      isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : E) R).isPreconnected
    letI : PseudoEMetricSpace Ω := PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) Ω
    letI : EMetricSpace Ω := EMetricSpace.ofT0PseudoEMetricSpace Ω
    let D : MetricSpace Ω := EMetricSpace.toMetricSpace
      (fun x y => (Manifold.riemannianEDist_lt_top (I := 𝓘(ℝ, E)) x y).ne)
    ∀ x y : Ω, ‖(x : E)‖ ≤ R / 8 → ‖(y : E)‖ ≤ R / 8 →
      a * @dist Ω D.toDist x y ≤ dist (Φ (x : E)) (Φ (y : E)) ∧
      dist (Φ (x : E)) (Φ (y : E)) ≤ b * @dist Ω D.toDist x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Ω → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : Ω → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PreconnectedSpace Ω :=
    isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : E) R).isPreconnected
  let : PseudoEMetricSpace Ω := PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) Ω
  let : EMetricSpace Ω := EMetricSpace.ofT0PseudoEMetricSpace Ω
  let D : MetricSpace Ω := EMetricSpace.toMetricSpace
    (fun x y => (Manifold.riemannianEDist_lt_top (I := 𝓘(ℝ, E)) x y).ne)
  let : MetricSpace Ω := D
  let : PseudoMetricSpace Ω := D.toPseudoMetricSpace
  let : PseudoEMetricSpace Ω := D.toPseudoEMetricSpace
  let : Dist Ω := D.toDist
  let : EDist Ω := D.toEDist
  let : IsRiemannianManifold 𝓘(ℝ, E) Ω := ⟨fun _ _ => rfl⟩
  let : Nonempty Ω := ⟨⟨0, Metric.mem_ball_self hR⟩⟩
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsRiemannianManifold I M := hg
  dsimp only
  intro x y hx hy
  let f : Ω → M := fun w => Φ (w : E)
  have hf : ContMDiff 𝓘(ℝ, E) I 1 f := by
    intro w
    rw [contMDiffAt_subtype_iff]
    exact hΦ.contMDiffAt
      (Φ.open_source.mem_nhds (hsource w.property))
  have hfnorm (w : Ω) (v : TangentSpace 𝓘(ℝ, E) w) :
      a * ‖v‖ ≤ ‖mfderiv 𝓘(ℝ, E) I f w v‖ ∧
      ‖mfderiv 𝓘(ℝ, E) I f w v‖ ≤ b * ‖v‖ := by
    have hq := hforms w v
    rw [← restricted_map_norm_sq g (Φ : E → M) Ω w v,
      ← finite_metric_norm_sq Ω k h w v] at hq
    constructor
    · apply (sq_le_sq₀ (mul_nonneg ha.le (norm_nonneg _)) (norm_nonneg _)).mp
      simpa only [mul_pow] using hq.1
    · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (norm_nonneg _))).mp
      simpa only [mul_pow] using hq.2
  have hrange : range f = (Φ : E → M) '' (Ω : Set E) := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨w, w.property, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩
  have hopen : IsOpen (range f) := by
    rw [hrange]
    exact Φ.isOpen_image_of_subset_source (Ω).isOpen hsource
  have hinv : ContMDiffOn I 𝓘(ℝ, E) 1 (Function.invFun f) (range f) := by
    rw [hrange]
    exact restricted_chart_inverse_contMDiffOn Φ hΦinv Ω hsource
  have hbuf := radial_chart_buffer hR (Φ : E → M) himage hrad x y hx hy
  have hlo := dist_le_inverse_mul_dist hf (restricted_chart_injective Φ Ω hsource)
    hopen hinv ha (fun w v => (hfnorm w v).1) hbuf.1 hbuf.2
  refine ⟨?_, ?_⟩
  · exact (le_inv_mul_iff₀ ha).mp hlo
  · let C : ℝ≥0 := ⟨b, hb⟩
    have hs (w : Ω) (v : TangentSpace 𝓘(ℝ, E) w) :
        ‖mfderiv 𝓘(ℝ, E) I f w v‖ₑ ≤ (C : ℝ≥0∞) * ‖v‖ₑ := by
      have hh := ENNReal.ofReal_le_ofReal (hfnorm w v).2
      have hC : ENNReal.ofReal b = (C : ℝ≥0∞) := by
        exact show ENNReal.ofReal (C : ℝ) = (C : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal
      simpa only [ENNReal.ofReal_mul hb, ofReal_norm, hC] using hh
    exact dist_map_le_of_speed hf hs x y
end

private theorem tendsto_of_relative_bounds {ι : Type*} {l : Filter ι}
    {f : ι → ℝ} {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      ∀ᶠ i in l, (1 - η) * d ≤ f i ∧ f i ≤ (1 + η) * d) :
    Tendsto f l (𝓝 d) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := min (1 / 2 : ℝ) (ε / (d + 1))
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε (by linarith))
  have hηhalf : η ≤ 1 / 2 := min_le_left _ _
  have hsmall : η * (d + 1) ≤ ε := (le_div_iff₀ (by linarith)).mp (min_le_right _ _)
  filter_upwards [h η hη hηhalf] with i hi
  have habs : |f i - d| ≤ η * d := abs_le.mpr ⟨by nlinarith [hi.1], by nlinarith [hi.2]⟩
  rw [Real.dist_eq]
  exact habs.trans_lt (by nlinarith)

section
open DifferentialGeometry Geometry
variable {ι E F H : Type*} {l : Filter ι} [l.NeBot]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : ι → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]
attribute [local instance] distanceLimitBilinearGroup distanceLimitBilinearSpace

variable (R : ℝ)
local notation "Ω" => (Opens.mk (Metric.ball (0 : E) R) Metric.isOpen_ball)

theorem tendsto_edist_of_uniform_pullbackMetricCoefficients
    (hR : 0 < R)
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hg : ∀ i, letI : RiemannianBundle (TangentSpace I : M i → Type _) :=
      ⟨(g i).toRiemannianMetric⟩; IsRiemannianManifold I (M i))
    (Φ : ∀ i, OpenPartialHomeomorph E (M i))
    (hΦ : ∀ᶠ i in l, ContMDiffOn 𝓘(ℝ, E) I 1 (Φ i) (Φ i).source)
    (hΦinv : ∀ᶠ i in l, ContMDiffOn I 𝓘(ℝ, E) 1 (Φ i).symm (Φ i).target)
    (hsource : ∀ᶠ i in l, Metric.ball (0 : E) R ⊆ (Φ i).source)
    (himage : ∀ᶠ i in l, (Φ i : E → M i) '' Metric.ball 0 R = Metric.ball (Φ i 0) R)
    (hrad : ∀ᶠ i in l, ∀ x ∈ Metric.ball 0 R, dist (Φ i x) (Φ i 0) = ‖x‖)
    (k : ℕ∞ω) (b : E → E →L[ℝ] E →L[ℝ] ℝ)
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, E) k E (TangentSpace 𝓘(ℝ, E) : Ω → Type _))
    (hh : ∀ x : Ω, ∀ v w : E, h.inner x v w = b x v w)
    (hconv : TendstoUniformlyOn (fun i => pullbackMetricCoefficients (g i) (Φ i)) b l
      (Metric.ball 0 R))
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ᶠ i in l, ∀ x ∈ Metric.ball 0 R, ∀ v : E,
      c * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients (g i) (Φ i) x v v) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Ω → Type _) := ⟨h.toRiemannianMetric⟩
    ∀ x y : Ω, ‖(x : E)‖ ≤ R / 8 → ‖(y : E)‖ ≤ R / 8 →
      Tendsto (fun i => edist (Φ i (x : E)) (Φ i (y : E))) l
        (𝓝 (riemannianEDist 𝓘(ℝ, E) x y)) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Ω → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : Ω → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PreconnectedSpace Ω :=
    isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : E) R).isPreconnected
  let : PseudoEMetricSpace Ω := PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) Ω
  let : EMetricSpace Ω := EMetricSpace.ofT0PseudoEMetricSpace Ω
  let D : MetricSpace Ω := EMetricSpace.toMetricSpace
    (fun x y => (Manifold.riemannianEDist_lt_top (I := 𝓘(ℝ, E)) x y).ne)
  let : MetricSpace Ω := D
  let : PseudoMetricSpace Ω := D.toPseudoMetricSpace
  let : PseudoEMetricSpace Ω := D.toPseudoEMetricSpace
  let : Dist Ω := D.toDist
  let : EDist Ω := D.toEDist
  intro x y hx hy
  have hd : Tendsto (fun i => dist (Φ i (x : E)) (Φ i (y : E))) l
      (𝓝 (@dist Ω D.toDist x y)) := by
    apply tendsto_of_relative_bounds (dist_nonneg (x := x) (y := y))
    intro η hη hηhalf
    have hl : ∀ w ∈ Metric.ball 0 R, ∀ v : E, c * ‖v‖ ^ 2 ≤ b w v v := by
      intro w hw v
      have he : Continuous (fun a : E →L[ℝ] E →L[ℝ] ℝ => a v v) := by fun_prop
      exact ge_of_tendsto ((he.tendsto (b w)).comp (hconv.tendsto_at hw))
        (hlower.mono (fun i hi => hi w hw v))
    filter_upwards [eventually_relative_forms_of_uniform_convergence hc hη
      (by linarith : η ≤ 1) hl hconv, hΦ, hΦinv, hsource, himage, hrad]
      with i hi hiΦ hiΦinv hisource hiimage hirad
    exact finite_chart_distance_bounds R hR (g i) (hg i) (Φ i) hiΦ hiΦinv
      hisource hiimage hirad k h (by linarith : 0 < 1 - η)
      (by linarith : 0 ≤ 1 + η) (fun w v => by simpa only [hh] using hi w w.property v)
      x y hx hy
  have hDE : ENNReal.ofReal (@dist Ω D.toDist x y) = riemannianEDist 𝓘(ℝ, E) x y :=
    (@edist_dist Ω D.toPseudoMetricSpace x y).symm
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hd
  simpa only [Function.comp_def, edist_dist, hDE] using ht

theorem edist_eq_of_uniform_pullbackMetricCoefficients
    (hR : 0 < R)
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hg : ∀ i, letI : RiemannianBundle (TangentSpace I : M i → Type _) :=
      ⟨(g i).toRiemannianMetric⟩; IsRiemannianManifold I (M i))
    (Φ : ∀ i, OpenPartialHomeomorph E (M i))
    (hΦ : ∀ᶠ i in l, ContMDiffOn 𝓘(ℝ, E) I 1 (Φ i) (Φ i).source)
    (hΦinv : ∀ᶠ i in l, ContMDiffOn I 𝓘(ℝ, E) 1 (Φ i).symm (Φ i).target)
    (hsource : ∀ᶠ i in l, Metric.ball (0 : E) R ⊆ (Φ i).source)
    (himage : ∀ᶠ i in l, (Φ i : E → M i) '' Metric.ball 0 R = Metric.ball (Φ i 0) R)
    (hrad : ∀ᶠ i in l, ∀ x ∈ Metric.ball 0 R, dist (Φ i x) (Φ i 0) = ‖x‖)
    (k : ℕ∞ω) (b : E → E →L[ℝ] E →L[ℝ] ℝ)
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, E) k E (TangentSpace 𝓘(ℝ, E) : Ω → Type _))
    (hh : ∀ x : Ω, ∀ v w : E, h.inner x v w = b x v w)
    (hconv : TendstoUniformlyOn (fun i => pullbackMetricCoefficients (g i) (Φ i)) b l
      (Metric.ball 0 R))
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ᶠ i in l, ∀ x ∈ Metric.ball 0 R, ∀ v : E,
      c * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients (g i) (Φ i) x v v)
    {X : Type*} [MetricSpace X] (o : ∀ i, M i) (p : X) {r ε : ι → ℝ}
    (A : ∀ i, GC.MetricGeometry.PointedBallApprox (o i) p (r i) (ε i))
    (hε : Tendsto ε l (𝓝 0)) (G : E → X)
    (hdom : ∀ᶠ i in l, ∀ w ∈ Metric.closedBall (0 : E) (R / 4),
      Φ i w ∈ Metric.closedBall (o i) (r i))
    (hmap : TendstoUniformlyOn (fun i w => (A i).extendToWholeSpace (Φ i w)) G l
      (Metric.closedBall 0 (R / 4))) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Ω → Type _) := ⟨h.toRiemannianMetric⟩
    ∀ x y : Ω, ‖(x : E)‖ ≤ R / 8 → ‖(y : E)‖ ≤ R / 8 →
      edist (G (x : E)) (G (y : E)) = riemannianEDist 𝓘(ℝ, E) x y := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Ω → Type _) := ⟨h.toRiemannianMetric⟩
  have hd := tendsto_edist_of_uniform_pullbackMetricCoefficients R hR g hg Φ hΦ hΦinv
    hsource himage hrad k b h hh hconv c hc hlower
  intro x y hx hy
  have hx' : (x : E) ∈ Metric.closedBall 0 (R / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hy' : (y : E) ∈ Metric.closedBall 0 (R / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hxy := (hmap.tendsto_at hx').dist (hmap.tendsto_at hy')
  have he : Tendsto (fun i => dist
      (dist ((A i).extendToWholeSpace (Φ i (x : E))) ((A i).extendToWholeSpace (Φ i (y : E))))
      (dist (Φ i (x : E)) (Φ i (y : E)))) l (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) _ hε
    filter_upwards [hdom] with i hi
    rw [(A i).extendToWholeSpace_apply _ (hi x hx'),
      (A i).extendToWholeSpace_apply _ (hi y hy'), Real.dist_eq]
    exact ((A i).distortion ⟨Φ i (x : E), hi x hx'⟩ ⟨Φ i (y : E), hi y hy'⟩).le
  have hp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hxy.congr_dist he)
  have hp' : Tendsto (fun i => edist (Φ i (x : E)) (Φ i (y : E))) l
      (𝓝 (edist (G (x : E)) (G (y : E)))) := by
    simpa only [Function.comp_def, edist_dist] using hp
  exact tendsto_nhds_unique hp' (hd x y hx hy)

end
end DifferentialGeometry.Geometry.Metric
