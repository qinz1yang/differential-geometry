import DifferentialGeometry.Geometry.Collapse.CirclePacketFamily
import DifferentialGeometry.Geometry.Collapse.CirclePacketSupport
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.KL618Tail
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.ModifiedScaleSmooth
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume

/-!
# CF3: the circle packet family on the late tail of the standing sequence

Blueprint `master207A.tex`, LPA03 (A:30435–30444) and the circle part of LPA06 (A:30601–30612),
for the closed standing sequence with the KL standing scale bound `R_p ≥ α r_p(1/α)` (LC01).
CF2's hypotheses are bound on the late tail:

* the scale `ρ` is LC02's smooth `Λ`-Lipschitz modified volume scale
  (`eventually_exists_smooth_modifiedScale`);
* the model map at EVERY point is LC09's (`exists_kl618_metric_model_tail`): a complete proper
  geodesic nonnegatively curved model of dimension at most two with an actual KL `σ`-map, its
  Icc-segments giving CF2's length clause (`Metric.arbitrarily_short_curves_of_metric_segments`);
* the splitting at a point of the stratum `S = {p | (M, ρ(p)⁻¹ d) has a (2, β)-splitting at p}`
  is chosen from the definition of `HasEuclideanSplitting`;
* the sectional bounds on `B(p, β⁻¹ρ(p))` and on the enlarged multiplicity ball come from the
  curvature-scale convention and the standing bound
  (`sectionalBoundedBelowAt_of_lt_curvatureRadius`);
* the Riemannian instances are those of `g` (its distance is the metric by `hmetric`).

`eventually_circle_packet_family`: the constants `a₂` (before `γ`), `β₀` (from `γ`) and `w₀`
(from `σ = min (a₂/2) (1/2)` and `Λ`) precede the sequence; on one late tail, ONE finite
selection of stratum points covers the stratum by the balls `B(j, 2ρ_j)`, with disjoint
`ρ/3`-balls, the numerical multiplicity bound, and at every selected point the full circle
packet built from an actual splitting map, whose cutoff has closed support inside the packet
domain (`tsupport_subset_of_circle_packet`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **CF3: the circle packet family on the late tail.** -/
theorem eventually_circle_packet_family (hdim : Module.finrank ℝ E = 3) {Λ : ℝ} (hΛ : 0 < Λ)
    (hΛsmall : Λ * 2000000 ≤ 1 / 100) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ β : ℝ, 0 < β → β ≤ β₀ → ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧ LipschitzWith (Real.toNNReal Λ) ρ ∧
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        ∃ J : Set (X i), J.Finite ∧
          (∀ j ∈ J, @HasEuclideanSplitting.{u, 0} (X i)
            ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) j 2 β) ∧
          J.PairwiseDisjoint (fun p => ball p (ρ p / 3)) ∧
          {p | @HasEuclideanSplitting.{u, 0} (X i)
            ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p 2 β} ⊆
            ⋃ j ∈ J, ball j (2 * ρ j) ∧
          (∀ x : X i, ((J ∩ {j | x ∈ ball j (2000000 * ρ j)}).ncard : ℝ) ≤
            modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
              modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) ∧
          ∀ j ∈ J, ∃ (Y : Type) (mY : MetricSpace Y) (a : Y), letI := mY
            ∃ F : @KleinerLottApprox (X i) _ ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _
              j (WithLp.toLp 2 ((0 : ℝ²), a)) β,
            let hmet := hmetric i
            let hMc : CompleteSpace (X i) := complete_of_compact
            letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI := ((mX i).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
            letI := radialScaledBundle (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI := radialScaledContinuous (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI := radialScaledManifold (m := mX i) (g i) hmet (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            ∃ η : X i → ℝ², ∃ hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball j 200),
            ∃ hrank : ∀ x ∈ ball j 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x),
              η j = 0 ∧ LipschitzOnWith 2 η (ball j 200) ∧
              (∀ x ∈ ball j 200, ‖η x - (F.toFun x).fst‖ < γ) ∧
              (∀ x ∈ ball j 200, ‖η x‖ < 100 → x ∈ ball j 102) ∧
              (∀ x ∈ ball j 200, η x = 0 → x ∈ ball j 2) ∧
              (∀ x ∈ ball j 2, ‖η x‖ ≤ 8) ∧
              (let f := diskPreimageMap (ball j 200) isOpen_ball η hη.continuousOn 100
              ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧
                (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧ Surjective f ∧
                (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
                ∀ R (hR : 0 < R) (hRr : R < 100),
                  let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
                  letI := regularFiberChartedSpace f y₀
                    (contMDiff_diskPreimageMap isOpen_ball hη 100)
                    (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
                  let U : TopologicalSpace.Opens
                      (diskPreimageOpens (ball j 200) isOpen_ball η hη.continuousOn 100) :=
                    ⟨f ⁻¹' planeBallInner 100 R,
                      (planeBallInner 100 R).isOpen.preimage
                        (continuous_diskPreimageMap isOpen_ball hη.continuousOn 100)⟩
                  ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
                      (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
                      ({x // f x = y₀} × planeBallInner 100 R) U ∞),
                    (∀ z, f (Θ z).1 = z.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
              (Module.finrank ℝ E = 3 → ∀ z : planeBallOpens 100,
                let f := diskPreimageMap (ball j 200) isOpen_ball η hη.continuousOn 100
                letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball hη 100)
                  (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
                Nonempty (Circle ≃ₘ⟮𝓡 1,
                  𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯ {x // f x = z})) ∧
              ∃ ζ : X i → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
                (∀ x, ζ x ∈ Icc 0 1) ∧ (∀ x ∈ ball j 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧
                (∀ x, ζ x ≠ 0 → x ∈ ball j 200 ∧ ‖η x‖ < 9) ∧
                tsupport ζ ⊆ {x | x ∈ ball j 200 ∧ ‖η x‖ ≤ 9} := by
  obtain ⟨a₂, ha₂, hCF2⟩ := exists_circle_packet_family.{uE, uH, u, 0, 0}
  refine ⟨a₂, ha₂, fun γ hγ hγone => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hfam⟩ := hCF2 γ hγ hγone
  refine ⟨β₀, hβ₀, hβ₀a, fun β hβ hββ₀ => ?_⟩
  have hσ : 0 < min (a₂ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  have hσ1 : min (a₂ / 2) (1 / 2) < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hσa : min (a₂ / 2) (1 / 2) ≤ a₂ := (min_le_left _ _).trans (by linarith)
  obtain ⟨w₀, hw₀, hLC09⟩ :=
    exists_kl618_metric_model_tail.{u} (E := E) (H := H) (I := I) hdim hσ hσ1 hΛ
  refine ⟨w₀, hw₀, fun w hw hww₀ hwc X mX _ _ _ g hmetric α hα hstand => ?_⟩
  have hden : 1 < 2 * (1 + 2 * Λ⁻¹) ^ 3 := by
    have h := one_le_pow₀ (show 1 ≤ 1 + 2 * Λ⁻¹ by linarith [inv_pos.mpr hΛ]) (n := 3)
    linarith
  have hv : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := div_pos hw (by linarith)
  have hvc : w / (2 * (1 + 2 * Λ⁻¹) ^ 3) < 4 * Real.pi / 3 := (div_lt_self hw hden).trans hwc
  filter_upwards [eventually_exists_smooth_modifiedScale hdim g hmetric hα hstand hΛ hw hwc,
    hLC09 w hw hww₀ hwc X g hmetric α hα hstand,
    hα.eventually (eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹),
    hα.eventually (eventually_gt_atTop (2 * (β⁻¹ + 6000001)))] with i hscale hmodel hiv hiβ
  obtain ⟨ρ, hρsm, hρlip, hρb⟩ := hscale
  have hρpos : ∀ p, 0 < ρ p := fun p => (hρb p).1
  refine ⟨ρ, hρpos, hρsm, hρlip, fun p => (hρb p).2, ?_⟩
  have hαpos : 0 < α i := (inv_pos.mpr hv).trans_le hiv
  have hαinv : (α i)⁻¹ ≤ w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := by
    rw [inv_le_comm₀ hαpos hv]
    exact hiv
  have hcurv : ∀ (p : X i) (L : ℝ), 0 < L → 2 * L < α i →
      ENNReal.ofReal (L * ρ p) < curvatureRadius (g i) p := by
    intro p L hL hLα
    have hu' := (firstVolumeScale_spec (g i) hdim p (inv_pos.mpr hαpos) (hαinv.trans_lt hvc)).1
    have hule : firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) ≤
        firstVolumeScale (g i) p (α i)⁻¹ :=
      (firstVolumeScale_strictAntiOn (g i) hdim p).antitoneOn
        ⟨inv_pos.mpr hαpos, hαinv.trans_lt hvc⟩ ⟨hv, hvc⟩ hαinv
    have hlt : L * ρ p < α i * firstVolumeScale (g i) p (α i)⁻¹ := by
      calc L * ρ p < L * (2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) :=
            mul_lt_mul_of_pos_left (hρb p).2.2 hL
        _ ≤ L * (2 * firstVolumeScale (g i) p (α i)⁻¹) := by gcongr
        _ < α i * firstVolumeScale (g i) p (α i)⁻¹ := by nlinarith
    exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt).trans_le (hstand i p)
  let : RiemannianBundle (fun x : X i => TangentSpace I x) := ⟨(g i).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (fun x : X i => TangentSpace I x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric (g i)
  have : IsRiemannianManifold I (X i) := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf (g i) a b
    rw [edist_dist, hmetric]
  have hEnorm : IsMetricNorm (I := I) (g i) := isMetricNorm_of_riemannianBundle (g i)
  have : IsManifold I 1 (X i) := IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have : T2Space (TangentBundle I (X i)) := inferInstance
  rcases isEmpty_or_nonempty (X i) with hX | ⟨⟨p₀⟩⟩
  · exact ⟨∅, finite_empty, fun j _ => (hX.false j).elim, pairwiseDisjoint_empty,
      fun p _ => (hX.false p).elim, fun x => (hX.false x).elim, fun j _ => (hX.false j).elim⟩
  have : ConnectedSpace (X i) := connectedSpace_of_aligned_metric (g i) (hmetric i) p₀
  let S : Set (X i) := {p | @HasEuclideanSplitting.{u, 0} (X i)
    ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p 2 β}
  have hsplit : ∀ p : S, @HasEuclideanSplitting.{u, 0} (X i)
      ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p 2 β := fun p => p.2
  choose Y mY a hF using hsplit
  have hmod := fun p : S => hmodel p (ρ p) (hρpos p) (hρb p).2.1.le (hρb p).2.2.le
  choose C mC c hC using hmod
  have hCc : ∀ p, CompleteSpace (C p) := fun p => (hC p).1
  have hΛ' : ((Real.toNNReal Λ : NNReal) : ℝ) * 2000000 ≤ 1 / 100 := by
    rw [Real.coe_toNNReal _ hΛ.le]
    exact hΛsmall
  have hsec1 : ∀ p : S, ∀ y ∈ ball (p : X i) (β⁻¹ * ρ p),
      SectionalBoundedBelowAt (g i) y (-(β ^ 2 * (ρ p)⁻¹ ^ 2)) := by
    intro p y hy
    rw [← DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm (g i)
      hEnorm] at hy
    have h := sectionalBoundedBelowAt_of_lt_curvatureRadius (g i)
      (hcurv p β⁻¹ (inv_pos.mpr hβ) (by linarith)) hy
    have he : -((β⁻¹ * ρ p) ^ 2)⁻¹ = -(β ^ 2 * (ρ p)⁻¹ ^ 2) := by
      rw [mul_pow, mul_inv, inv_pow, inv_inv, ← inv_pow]
    rwa [he] at h
  have hsec2 : ∀ p : S, ∀ y ∈ ball (p : X i) ((3 * 2000000 + 2 / 3) * ρ p),
      SectionalBoundedBelowAt (g i) y (-((2000000 * ρ p) ^ 2)⁻¹) := by
    intro p y hy
    rw [← DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm (g i)
      hEnorm] at hy
    have h := sectionalBoundedBelowAt_of_lt_curvatureRadius (g i)
      (hcurv p (3 * 2000000 + 2 / 3) (by norm_num) (by linarith [inv_pos.mpr hβ])) hy
    refine h.mono ?_
    have hρp := hρpos p
    rw [neg_le_neg_iff]
    apply inv_anti₀ (by positivity)
    gcongr
    norm_num
  obtain ⟨J, hJS, hfin, hdisj, hcov, hmult, hpack⟩ :=
    hfam E hdim H I (X i) (g i) hEnorm ρ hρlip hρpos hΛ' S Y a C c
      (fun _ => min (a₂ / 2) (1 / 2)) (fun _ => β) (fun p => (hC p).2.2.2.2.2.some)
      (fun p => (hF p).some)
      (fun p => ⟨Metric.arbitrarily_short_curves_of_metric_segments (hC p).2.2.2.2.1,
        (hC p).2.2.1, (hC p).2.2.2.1, hσa, hββ₀, hsec1 p, hsec2 p⟩)
  refine ⟨J, hfin, fun j hj => hJS hj, hdisj, hcov, hmult, fun j hj => ?_⟩
  obtain ⟨η, hη, hrank, hq, hlip, hclose, h102, h2, h8, hbundle, hcircle, ζ, hζ, hsupp, hζ01, hζ1,
      hζnz⟩ := hpack j hj
  exact ⟨Y ⟨j, hJS hj⟩, mY ⟨j, hJS hj⟩, a ⟨j, hJS hj⟩, (hF ⟨j, hJS hj⟩).some, η, hη, hrank, hq,
    hlip, hclose, h102, h2, h8, hbundle, hcircle, ζ, hζ, hsupp, hζ01, hζ1, hζnz,
    @tsupport_subset_of_circle_packet (X i) ℝ² ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j)))
      _ j η ζ hη.continuousOn h102 hζnz⟩

end DifferentialGeometry.Geometry.Collapse
