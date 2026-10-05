import DifferentialGeometry.Geometry.Collapse.CirclePacketTwoStratum

/-!
# The circle kind of LPA03 / LPA06 in the blueprint parameter order

`eventually_circle_packets_two_stratum_reordered` is `eventually_circle_packets_two_stratum`
(`CirclePacketTwoStratum.lean`) with the splitting tolerances `β` quantified AFTER LC09's `w₀` and
`w` (blueprint LPA04, A:30493–30507: `σ_col, Λ → w → b → β₁`). This is possible because `w₀` is
LC09's (`exists_kl618_metric_model_tail` at `σ, Λ`) and does not depend on `β`.

The old theorem is monolithic (its proof body is inline), so the body is copied with the
re-chained head; the S1 lemmas are cited from `CirclePacketTwoStratum.lean`.
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
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The circle kind of LPA03 / LPA06, blueprint parameter order** (`w₀` before `β`). -/
theorem eventually_circle_packets_two_stratum_reordered (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ σ : ℝ, 0 < σ → σ < 1 → σ ≤ a₂ →
      ∀ Λ : ℝ, 0 < Λ → Λ * 2000000 ≤ 1 / 100 → ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ β : ℕ → ℝ, 0 < β 2 → β 2 ≤ β₀ →
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
        (∀ L : ℝ, 0 < L → 2 * L < α i → ∀ (p : X i), ∀ y ∈ ball p (L * ρ p),
          SectionalBoundedBelowAt (g i) y (-((L * ρ p) ^ 2)⁻¹)) ∧
        (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 2,
          ∃ (C : Type) (mC : MetricSpace C) (c : C), letI := mC
          CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
          fourPointComparison 0 (univ : Set C) ∧
          Nonempty (@KleinerLottApprox (X i) C
            ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ) ∧
          ∃ (Y : Type) (mY : MetricSpace Y) (a : Y), letI := mY
            ∃ F : @KleinerLottApprox (X i) _ ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _
              p (WithLp.toLp 2 ((0 : ℝ²), a)) (β 2),
            let hmet := hmetric i
            let hMc : CompleteSpace (X i) := complete_of_compact
            letI := (mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI := ((mX i).rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hMc
            letI := radialScaledBundle (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI := radialScaledContinuous (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI := radialScaledManifold (m := mX i) (g i) hmet (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            ∃ η : X i → ℝ², ∃ hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball p 200),
            ∃ hrank : ∀ x ∈ ball p 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x),
              η p = 0 ∧ LipschitzOnWith 2 η (ball p 200) ∧
              (∀ x ∈ ball p 200, ‖η x - (F.toFun x).fst‖ < γ) ∧
              (∀ x ∈ ball p 200, ‖η x‖ < 100 → x ∈ ball p 102) ∧
              (∀ x ∈ ball p 200, η x = 0 → x ∈ ball p 2) ∧
              (∀ x ∈ ball p 2, ‖η x‖ ≤ 8) ∧
              (let f := diskPreimageMap (ball p 200) isOpen_ball η hη.continuousOn 100
              ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧
                (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧ Surjective f ∧
                (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
                ∀ R (hR : 0 < R) (hRr : R < 100),
                  let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
                  letI := regularFiberChartedSpace f y₀
                    (contMDiff_diskPreimageMap isOpen_ball hη 100)
                    (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
                  let U : TopologicalSpace.Opens
                      (diskPreimageOpens (ball p 200) isOpen_ball η hη.continuousOn 100) :=
                    ⟨f ⁻¹' planeBallInner 100 R,
                      (planeBallInner 100 R).isOpen.preimage
                        (continuous_diskPreimageMap isOpen_ball hη.continuousOn 100)⟩
                  ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
                      (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
                      ({x // f x = y₀} × planeBallInner 100 R) U ∞),
                    (∀ z, f (Θ z).1 = z.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
              (Module.finrank ℝ E = 3 → ∀ z : planeBallOpens 100,
                let f := diskPreimageMap (ball p 200) isOpen_ball η hη.continuousOn 100
                letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball hη 100)
                  (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
                Nonempty (Circle ≃ₘ⟮𝓡 1,
                  𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯ {x // f x = z})) ∧
              ∃ ζ : X i → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
                (∀ x, ζ x ∈ Icc 0 1) ∧ (∀ x ∈ ball p 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧
                (∀ x, ζ x ≠ 0 → x ∈ ball p 200 ∧ ‖η x‖ < 9) ∧
                tsupport ζ ⊆ {x | x ∈ ball p 200 ∧ ‖η x‖ ≤ 9} ∧
                tsupport ζ ⊆
                  (diskPreimageOpens (ball p 200) isOpen_ball η hη.continuousOn 100 : Set (X i)) ∧
                @ball (X i) (mX i).toPseudoMetricSpace p (2 * ρ p) ⊆
                  (diskPreimageOpens (ball p 200) isOpen_ball η hη.continuousOn 100 : Set (X i)) ∩
                    {x | ζ x = 1} ∧
                tsupport ζ ⊆ @ball (X i) (mX i).toPseudoMetricSpace p (200 * ρ p)) ∧
        ∃ J : Set (X i), J.Finite ∧ J ⊆ scaledSplittingStratum.{u, 0} ρ hρpos β 2 ∧
          J.PairwiseDisjoint (fun p => ball p (ρ p / 3)) ∧
          (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 2, ∃ j ∈ J,
            ball p (ρ p) ⊆ ball j (2 * ρ j)) ∧
          ∀ x : X i, ((J ∩ {j | x ∈ ball j (2000000 * ρ j)}).ncard : ℝ) ≤
            modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
              modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) := by
  obtain ⟨a₂, ha₂, hCF1⟩ := exists_circle_packet_at_scale.{uE, uH, u, 0, 0}
  refine ⟨a₂, ha₂, fun γ hγ hγone => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hpack⟩ := hCF1 γ hγ hγone
  refine ⟨β₀, hβ₀, hβ₀a, fun σ hσ hσ1 hσa Λ hΛ hΛsmall => ?_⟩
  obtain ⟨w₀, hw₀, hLC09⟩ :=
    exists_kl618_metric_model_tail.{u} (E := E) (H := H) (I := I) hdim hσ hσ1 hΛ
  refine ⟨w₀, hw₀, fun w hw hww₀ hwc β hβ hββ₀ X mX _ _ _ g hmetric α hα hstand => ?_⟩
  have hden : 1 < 2 * (1 + 2 * Λ⁻¹) ^ 3 := by
    have h := one_le_pow₀ (show 1 ≤ 1 + 2 * Λ⁻¹ by linarith [inv_pos.mpr hΛ]) (n := 3)
    linarith
  have hv : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := div_pos hw (by linarith)
  have hvc : w / (2 * (1 + 2 * Λ⁻¹) ^ 3) < 4 * Real.pi / 3 := (div_lt_self hw hden).trans hwc
  filter_upwards [eventually_exists_smooth_modifiedScale hdim g hmetric hα hstand hΛ hw hwc,
    hLC09 w hw hww₀ hwc X g hmetric α hα hstand,
    hα.eventually (eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹),
    hα.eventually (eventually_gt_atTop (2 * ((β 2)⁻¹ + 6000001)))] with i hscale hmodel hiv hiβ
  obtain ⟨ρ, hρsm, hρlip, hρb⟩ := hscale
  have hρpos : ∀ p, 0 < ρ p := fun p => (hρb p).1
  have hαpos : 0 < α i := (inv_pos.mpr hv).trans_le hiv
  have hαinv : (α i)⁻¹ ≤ w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := by
    rw [inv_le_comm₀ hαpos hv]
    exact hiv
  have hcurv : ∀ (p : X i) (L : ℝ), 0 < L → 2 * L < α i →
      ENNReal.ofReal (L * ρ p) < curvatureRadius (g i) p := by
    intro p L hL hLα
    have hu := (firstVolumeScale_spec (g i) hdim p (inv_pos.mpr hαpos)
      (hαinv.trans_lt hvc)).1
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
  have hsec : ∀ L : ℝ, 0 < L → 2 * L < α i → ∀ (p : X i), ∀ y ∈ ball p (L * ρ p),
      SectionalBoundedBelowAt (g i) y (-((L * ρ p) ^ 2)⁻¹) := by
    intro L hL hLα p y hy
    rw [← DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm (g i)
      hEnorm] at hy
    exact sectionalBoundedBelowAt_of_lt_curvatureRadius (g i) (hcurv p L hL hLα) hy
  have hβinv : 0 < (β 2)⁻¹ := inv_pos.mpr hβ
  have hsec1 : ∀ (p : X i), ∀ y ∈ ball p ((β 2)⁻¹ * ρ p),
      SectionalBoundedBelowAt (g i) y (-(β 2 ^ 2 * (ρ p)⁻¹ ^ 2)) := by
    intro p y hy
    have h := hsec (β 2)⁻¹ hβinv (by linarith) p y hy
    have he : -(((β 2)⁻¹ * ρ p) ^ 2)⁻¹ = -(β 2 ^ 2 * (ρ p)⁻¹ ^ 2) := by
      rw [mul_pow, mul_inv, inv_pow, inv_inv, ← inv_pow]
    rwa [he] at h
  have hsec2 : ∀ (p : X i), ∀ y ∈ ball p ((3 * 2000000 + 2 / 3) * ρ p),
      SectionalBoundedBelowAt (g i) y (-((2000000 * ρ p) ^ 2)⁻¹) := by
    intro p y hy
    refine (hsec (3 * 2000000 + 2 / 3) (by norm_num) (by linarith) p y hy).mono ?_
    have hρp := hρpos p
    rw [neg_le_neg_iff]
    apply inv_anti₀ (by positivity)
    gcongr
    norm_num
  refine ⟨ρ, hρpos, hρsm, hρlip, fun p => (hρb p).2, hsec, fun p hp => ?_, ?_⟩
  · obtain ⟨Y, mY, a, ⟨F⟩⟩ := hasEuclideanSplitting_of_mem_scaledSplittingStratum_two hp
    obtain ⟨C, mC, c, hCc, hCp, hCdim, hCcomp, hCseg, ⟨f⟩⟩ :=
      hmodel p (ρ p) (hρpos p) (hρb p).2.1.le (hρb p).2.2.le
    obtain ⟨η, hη, hrank, hq, hlip, hclose, h102, h2, h8, hbundle, hcircle, ζ, hζ, hsupp, hζ01,
        hζ1, hζnz⟩ :=
      hpack E H I (X i) (g i) (hmetric i) Y p a (ρ p) (hρpos p) C c
        (Metric.arbitrarily_short_curves_of_metric_segments hCseg) hCdim hCcomp hσa hββ₀ f F
        (hsec1 p)
    have htsupp := @tsupport_subset_of_circle_packet (X i) ℝ²
      ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p η ζ hη.continuousOn h102 hζnz
    have hρinv : 0 < (ρ p)⁻¹ := inv_pos.mpr (hρpos p)
    refine ⟨C, mC, c, hCc, hCp, hCdim, hCcomp, ⟨f⟩, Y, mY, a, F, η, hη, hrank, hq, hlip, hclose,
      h102, h2, h8, hbundle, hcircle, ζ, hζ, hsupp, hζ01, hζ1, hζnz, htsupp, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨h200, h9⟩ := htsupp hx
      refine ⟨h200, ?_⟩
      rw [mem_preimage, mem_ball, dist_zero_right]
      linarith
    · intro x hx
      have hx' : dist x p < 2 * ρ p := hx
      have hx2 : (ρ p)⁻¹ * dist x p < 2 := by
        rw [inv_mul_lt_iff₀ (hρpos p)]
        linarith
      have hx200 : (ρ p)⁻¹ * dist x p < 200 := by linarith
      have h8x := h8 x hx2
      refine ⟨⟨hx200, ?_⟩, hζ1 x hx200 h8x⟩
      rw [mem_preimage, mem_ball, dist_zero_right]
      linarith
    · intro x hx
      have h200 : (ρ p)⁻¹ * dist x p < 200 := (htsupp hx).1
      change dist x p < 200 * ρ p
      rw [inv_mul_lt_iff₀ (hρpos p)] at h200
      linarith
  · rcases isEmpty_or_nonempty (X i) with hX | ⟨⟨p₀⟩⟩
    · exact ⟨∅, finite_empty, empty_subset _, pairwiseDisjoint_empty,
        fun p _ => (hX.false p).elim, fun x => (hX.false x).elim⟩
    have : ConnectedSpace (X i) := connectedSpace_of_aligned_metric (g i) (hmetric i) p₀
    have hΛ' : ((Real.toNNReal Λ : NNReal) : ℝ) * 2000000 ≤ 1 / 100 := by
      rw [Real.coe_toNNReal _ hΛ.le]
      exact hΛsmall
    obtain ⟨J, hJS, hfin, hdisj, hcov, hmult⟩ :=
      exists_simultaneous_support_cover (g i) hEnorm hdim
        (scaledSplittingStratum.{u, 0} ρ hρpos β 2) hρlip hρpos hΛ' (fun p _ => hsec2 p)
    exact ⟨J, hfin, hJS, hdisj, hcov, hmult⟩

end DifferentialGeometry.Geometry.Collapse
