import DifferentialGeometry.Geometry.Collapse.SharedInteriorAssignment
import DifferentialGeometry.Geometry.Collapse.CirclePacketTwoStratumReordered

/-!
# S2 (LPA04's single assignment, existing-rows part) in the blueprint parameter order

`eventually_shared_interior_assignment_reordered` is `eventually_shared_interior_assignment`
(`SharedInteriorAssignment.lean`) with `β` quantified AFTER `w₀` and `w` (blueprint LPA04,
A:30493–30507). Its `w₀ = min w₁ w₂` comes from LC09 (`exists_kl618_metric_model_tail`) and from
`eventually_circle_packets_two_stratum_reordered`, neither of which depends on `β`.

The old theorem's tail (rank bound, zero-scale curvature clause, strata trichotomy) is inline, so
it is copied with the re-chained head.
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

/-- **S2 in the blueprint parameter order** (`w₀` before `β`). -/
theorem eventually_shared_interior_assignment_reordered (hdim : Module.finrank ℝ E = 3) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ Λ : ℝ, 0 < Λ → Λ * 2000000 ≤ 1 / 100 → ∃ w₀ : ℝ, 0 < w₀ ∧
      ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ β : ℕ → ℝ, 0 < β 2 → β 2 ≤ β₀ → β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
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
        (∀ s : ℝ, 0 < s → 800 * s < α i → ∀ (p : X i), ∀ y ∈ ball p (400 * (s * ρ p)),
          SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (s * ρ p)⁻¹ ^ 2))) ∧
        (∀ p : X i, ∃ (C : Type) (mC : MetricSpace C), letI := mC
          ∃ c : C, CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
            fourPointComparison 0 (univ : Set C) ∧
            (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
              f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
            Nonempty (@KleinerLottApprox (X i) C
              ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ)) ∧
        (∀ p : X i, scaledSplittingRank.{u, 0} ρ hρpos β p ≤ 2) ∧
        (∀ p : X i, p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 0 ∨
          p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1 ∨
          p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 2) ∧
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
  obtain ⟨a₂, ha₂, h1⟩ := eventually_circle_packets_two_stratum_reordered.{uE, uH, u} (E := E)
    (H := H) (I := I) hdim
  have hη := threeSplittingExclusionThreshold_pos.{u, 0}
  have hηsmall := threeSplittingExclusionThreshold_lt.{u, 0}
  refine ⟨a₂, ha₂, fun γ hγ hγone => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h1⟩ := h1 γ hγ hγone
  refine ⟨β₀, hβ₀, hβ₀a, fun σ hσ hσa hση Λ hΛ hΛsmall => ?_⟩
  have hσ1 : σ < 1 := by linarith
  obtain ⟨w₁, hw₁, h1⟩ := h1 σ hσ hσ1 hσa Λ hΛ hΛsmall
  obtain ⟨w₂, hw₂, hLC09⟩ :=
    exists_kl618_metric_model_tail.{u} (E := E) (H := H) (I := I) hdim hσ hσ1 hΛ
  refine ⟨min w₁ w₂, lt_min hw₁ hw₂, fun w hw hww hwc β hβ hββ₀ hβ3 X mX _ _ _ g hmetric α hα
    hstand => ?_⟩
  filter_upwards [h1 w hw (hww.trans_le (min_le_left _ _)) hwc β hβ hββ₀ X g hmetric α hα hstand,
    hLC09 w hw (hww.trans_le (min_le_right _ _)) hwc X g hmetric α hα hstand] with i hi hmodel
  obtain ⟨ρ, hρpos, hρsm, hρlip, hρb, hsec, hpt, hfam⟩ := hi
  have hmod := fun p : X i => hmodel p (ρ p) (hρpos p) (hρb p).1.le (hρb p).2.le
  have hrank : ∀ p : X i, scaledSplittingRank.{u, 0} ρ hρpos β p ≤ 2 := by
    intro p
    obtain ⟨C, mC, c, hCc, -, hCdim, hCcomp, hCseg, ⟨f⟩⟩ := hmod p
    exact @splittingRank_le_two_of_no_three.{u, 0} (X i)
      ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p β
      (@threeSplittingExclusionThreshold_excludes.{u, 0} (X i)
        ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) p C mC hCc c hCseg hCdim hCcomp σ
        (β 3) hση hβ3 f)
  have hzero : ∀ s : ℝ, 0 < s → 800 * s < α i → ∀ (p : X i), ∀ y ∈ ball p (400 * (s * ρ p)),
      SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (s * ρ p)⁻¹ ^ 2)) := by
    intro s hs hsα p y hy
    have ht : 0 < s * ρ p := mul_pos hs (hρpos p)
    have h := hsec (400 * s) (by positivity) (by linarith) p y (by rwa [mul_assoc])
    refine h.mono ?_
    have he : ((400 * s * ρ p) ^ 2)⁻¹ = (1 / 160000) * (s * ρ p)⁻¹ ^ 2 := by
      field_simp
      ring
    have hnn : 0 ≤ (s * ρ p)⁻¹ ^ 2 := sq_nonneg _
    rw [he]
    nlinarith
  refine ⟨ρ, hρpos, hρsm, hρlip, hρb, hsec, hzero, hmod, hrank, fun p => ?_, hpt, hfam⟩
  have hp := hrank p
  rcases Nat.lt_or_ge (scaledSplittingRank.{u, 0} ρ hρpos β p) 1 with h0 | h1
  · left
    change scaledSplittingRank.{u, 0} ρ hρpos β p = 0
    omega
  rcases Nat.lt_or_ge (scaledSplittingRank.{u, 0} ρ hρpos β p) 2 with h1' | h2
  · right
    left
    change scaledSplittingRank.{u, 0} ρ hρpos β p = 1
    omega
  · right
    right
    change scaledSplittingRank.{u, 0} ρ hρpos β p = 2
    omega

end DifferentialGeometry.Geometry.Collapse
