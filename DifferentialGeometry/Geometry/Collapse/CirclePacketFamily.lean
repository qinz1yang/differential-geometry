import DifferentialGeometry.Geometry.Collapse.SimultaneousCircleProduction
import DifferentialGeometry.Geometry.Collapse.SimultaneousProductionApplications
import DifferentialGeometry.Geometry.Collapse.SimultaneousAnnularProduction
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls

/-!
# The circle packet family at the physical scale (LPA06, circle kind)

Blueprint `master207A.tex`, LPA03 (A:30408) and the circle part of LPA06 (A:30586–30610).
Consumers of Codex X77's public theorems `exists_early_simultaneous_circle_packet_parameters`
(`SimultaneousCircleProduction.lean`) and `exists_simultaneous_support_cover`
(`SimultaneousProductionApplications.lean`); nothing of X77 is edited or copied.

* `exists_circle_packet_at_scale` (CF1): X77's normalized circle packet at an ARBITRARY physical
  scale `r`, i.e. for the metric space `(M, r⁻¹ d)` with tensor `r⁻² g`, from the sectional bound
  `sec_g ≥ -β² r⁻²` on `B(q, β⁻¹ r)`; moreover the covering ball `B_{r⁻¹d}(q, 2)` lies in the
  plateau `‖η‖ ≤ 8` of the cutoff (A:30610: "On the circle covering ball |η| < 2 < 8").
* `exists_circle_packet_family` (CF2): on a closed connected Riemannian three-manifold with a
  Lipschitz scale `ρ`, data at every point of a set `S` (an actual KL map to a nonnegative model
  of dimension at most two and an actual `(2, β)`-splitting at scale `ρ(p)`, with the sectional
  bounds) give ONE finite selection `J ⊆ S` with disjoint `ρ/3`-balls, the balls `B(i, 2ρ_i)`
  covering `S`, the support-ball multiplicity bound with a numerical constant, and at every
  selected center the full X77 packet at scale `ρ_i` built from the SAME splitting map, whose
  cutoff equals one on `B(i, 2ρ_i)` and is supported in `B(i, 200ρ_i)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **CF1: X77's circle packet at a physical scale `r`.** The constants `a₂` (before `γ`) and
`β₀` (depending on `γ` only) precede every manifold, model, map and scale. The conclusion is
X77's for the metric space `(M, r⁻¹ d)` with tensor `r⁻² g`, plus the plateau clause on the
normalized ball of radius `2`. -/
theorem exists_circle_packet_at_scale :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ (γ : ℝ), 0 < γ → γ < 1 / 10 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [hM : CompleteSpace M]
        (g : SmoothRiemannianMetric I M)
        (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (Y : Type w) [MetricSpace Y] (q : M) (a : Y) (r : ℝ) (hr : 0 < r),
      ∀ (C : Type v) [MetricSpace C] [CompleteSpace C] (c : C),
      (∀ x y : C, ∀ e : ℝ, 0 < e →
        ∃ ξ : unitInterval → C, Continuous ξ ∧ ξ 0 = x ∧ ξ 1 = y ∧
          eVariationOn ξ univ < ENNReal.ofReal (dist x y + e)) →
      dimH (univ : Set C) ≤ 2 → fourPointComparison 0 (univ : Set C) →
      ∀ {σ β : ℝ}, σ ≤ a₂ → β ≤ β₀ →
      @KleinerLottApprox M C (m.rescale r⁻¹ (inv_pos.mpr hr)) _ q c σ →
      ∀ F : @KleinerLottApprox M _ (m.rescale r⁻¹ (inv_pos.mpr hr)) _ q
        (WithLp.toLp 2 ((0 : ℝ²), a)) β,
      (∀ y ∈ ball q (β⁻¹ * r), SectionalBoundedBelowAt g y (-(β ^ 2 * r⁻¹ ^ 2))) →
      letI := m.rescale r⁻¹ (inv_pos.mpr hr)
      letI := (m.rescale_completeSpace_iff r⁻¹ (inv_pos.mpr hr)).mpr hM
      letI := radialScaledBundle g r⁻¹ (inv_pos.mpr hr)
      letI := radialScaledContinuous g r⁻¹ (inv_pos.mpr hr)
      letI := radialScaledManifold (m := m) g hmetric r⁻¹ (inv_pos.mpr hr)
      ∃ η : M → ℝ², ∃ hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball q 200),
      ∃ hrank : ∀ x ∈ ball q 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x),
        η q = 0 ∧ LipschitzOnWith 2 η (ball q 200) ∧
        (∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < γ) ∧
        (∀ x ∈ ball q 200, ‖η x‖ < 100 → x ∈ ball q 102) ∧
        (∀ x ∈ ball q 200, η x = 0 → x ∈ ball q 2) ∧
        (∀ x ∈ ball q 2, ‖η x‖ ≤ 8) ∧
        (let f := diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100
        ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧
          (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧ Surjective f ∧
          (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
          ∀ R (hR : 0 < R) (hRr : R < 100),
            let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
            letI := regularFiberChartedSpace f y₀ (contMDiff_diskPreimageMap isOpen_ball hη 100)
              (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
            let U : TopologicalSpace.Opens
                (diskPreimageOpens (ball q 200) isOpen_ball η hη.continuousOn 100) :=
              ⟨f ⁻¹' planeBallInner 100 R,
                (planeBallInner 100 R).isOpen.preimage
                  (continuous_diskPreimageMap isOpen_ball hη.continuousOn 100)⟩
            ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
                (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
                ({x // f x = y₀} × planeBallInner 100 R) U ∞),
              (∀ z, f (Θ z).1 = z.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
        (Module.finrank ℝ E = 3 → ∀ z : planeBallOpens 100,
          let f := diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100
          letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball hη 100)
            (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
          Nonempty (Circle ≃ₘ⟮𝓡 1,
            𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯ {x // f x = z})) ∧
        ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
          (∀ x, ζ x ∈ Icc 0 1) ∧ (∀ x ∈ ball q 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧
          ∀ x, ζ x ≠ 0 → x ∈ ball q 200 ∧ ‖η x‖ < 9 := by
  obtain ⟨a₂, ha₂, hX⟩ := exists_early_simultaneous_circle_packet_parameters.{uE, uH, u, v, w}
  refine ⟨a₂, ha₂, fun γ hγ hγone => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hprod⟩ := hX γ hγ hγone
  refine ⟨min β₀ (1 / 4), lt_min hβ₀ (by norm_num), (min_le_left _ _).trans hβ₀a, ?_⟩
  intro E _ _ _ _ H _ I _ M m _ _ _ hM g hmetric Y _ q a r hr C _ _ c hlen hdim hcomp σ β hσ hβ
    f F hsec
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hβq : β ≤ 1 / 4 := hβ.trans (min_le_right _ _)
  have hsec' : ∀ y ∈ @ball M (m.rescale r⁻¹ hrinv).toPseudoMetricSpace q β⁻¹,
      SectionalBoundedBelowAt (scaleMetric (r⁻¹ ^ 2) (pow_pos hrinv 2) g) y (-β ^ 2) := by
    intro y hy
    have hy' : r⁻¹ * dist y q < β⁻¹ := hy
    have hyr : y ∈ ball q (β⁻¹ * r) := by
      rw [mem_ball]
      have := (inv_mul_lt_iff₀ hr).mp hy'
      linarith
    rw [sectionalBoundedBelowAt_scaleMetric_iff]
    simpa only [neg_mul] using hsec y hyr
  let mr : MetricSpace M := m.rescale r⁻¹ hrinv
  let : CompleteSpace M := (m.rescale_completeSpace_iff r⁻¹ hrinv).mpr hM
  let := radialScaledBundle g r⁻¹ hrinv
  let := radialScaledContinuous g r⁻¹ hrinv
  let := radialScaledManifold (m := m) g hmetric r⁻¹ hrinv
  have hβpos : 0 < β := F.error_pos
  have hEnorm : IsMetricNorm (scaleMetric (r⁻¹ ^ 2) (pow_pos hrinv 2) g) :=
    isMetricNorm_of_riemannianBundle _
  obtain ⟨η, hη, hrank, hq, hlip, hclose, h102, h2, hbundle, hcircle, ζ, hζ, hsupp, hζ01, hζ1,
      hζnz⟩ :=
    hprod E H I M (scaleMetric (r⁻¹ ^ 2) (pow_pos hrinv 2) g) hEnorm Y q a C c hlen hdim hcomp
      hσ ((hβ.trans (min_le_left _ _))) f F hsec'
  refine ⟨η, hη, hrank, hq, hlip, hclose, h102, h2, ?_, hbundle, hcircle, ζ, hζ, hsupp, hζ01,
    hζ1, hζnz⟩
  intro x hx
  have hx2 : dist x q < 2 := hx
  have hxβ : x ∈ ball q β⁻¹ := by
    rw [mem_ball]
    have : (4 : ℝ) ≤ β⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hβpos]
      linarith
    linarith
  have hdist := F.distortion x hxβ q (mem_ball_self (inv_pos.mpr hβpos))
  rw [F.basepoint] at hdist
  have hfst : ‖(F.toFun x).fst‖ ≤ dist (F.toFun x) (WithLp.toLp 2 ((0 : ℝ²), a)) := by
    have h := WithLp.dist_fst_le (F.toFun x) (WithLp.toLp 2 ((0 : ℝ²), a))
    simpa [dist_zero_right] using h
  have hxq : x ∈ ball q 200 := mem_ball.mpr (by linarith)
  have hc := hclose x hxq
  have habs := (abs_le.mp hdist).2
  have htri : ‖η x‖ ≤ ‖(F.toFun x).fst‖ + ‖η x - (F.toFun x).fst‖ :=
    norm_le_insert' (η x) (F.toFun x).fst
  linarith

/-- **CF2: the finite circle packet family on a closed manifold (LPA06, circle kind).** Data at
every point `p` of a set `S`, indexed by `S` (an actual KL `σ_p`-map from `(M, ρ(p)⁻¹ d, p)` to a
complete length space of dimension at most two with nonnegative four-point comparison, an actual
`(2, β_p)`-splitting `F p` at the same scale, `sec_g ≥ -β_p² ρ(p)⁻²` on `B(p, β_p⁻¹ ρ(p))` and the
enlarged-ball bound for the multiplicity) give ONE finite selection `J ⊆ S`: disjoint
`ρ/3`-balls, the balls `B(i, 2ρ_i)` cover `S`, at most a numerical number of the balls
`B(i, 2·10⁶ ρ_i)` contain any point, and at every selected center the full CF1 packet at scale
`ρ_i` built from the SAME splitting map `F i`. The constants precede every manifold and datum. -/
theorem exists_circle_packet_family :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ (γ : ℝ), 0 < γ → γ < 1 / 10 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)], Module.finrank ℝ E = 3 →
      ∀ (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        [ConnectedSpace M] [CompactSpace M]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (ρ : M → ℝ) {Λ : NNReal}, LipschitzWith Λ ρ → ∀ (hρpos : ∀ p, 0 < ρ p),
        (Λ : ℝ) * 2000000 ≤ 1 / 100 →
      ∀ (S : Set M) (Y : S → Type w) [∀ p, MetricSpace (Y p)] (a : ∀ p, Y p)
        (C : S → Type v) [∀ p, MetricSpace (C p)] [∀ p, CompleteSpace (C p)] (c : ∀ p, C p)
        (σ β : S → ℝ),
      (∀ p : S, @KleinerLottApprox M (C p)
          (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p (c p) (σ p)) →
      ∀ (F : ∀ p : S, @KleinerLottApprox M _ (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
          (WithLp.toLp 2 ((0 : ℝ²), a p)) (β p)),
      (∀ p : S,
        (∀ x y : C p, ∀ e : ℝ, 0 < e →
          ∃ ξ : unitInterval → C p, Continuous ξ ∧ ξ 0 = x ∧ ξ 1 = y ∧
            eVariationOn ξ univ < ENNReal.ofReal (dist x y + e)) ∧
        dimH (univ : Set (C p)) ≤ 2 ∧ fourPointComparison 0 (univ : Set (C p)) ∧
        σ p ≤ a₂ ∧ β p ≤ β₀ ∧
        (∀ y ∈ ball (p : M) ((β p)⁻¹ * ρ p),
          SectionalBoundedBelowAt g y (-(β p ^ 2 * (ρ p)⁻¹ ^ 2))) ∧
        ∀ y ∈ ball (p : M) ((3 * 2000000 + 2 / 3) * ρ p),
          SectionalBoundedBelowAt g y (-((2000000 * ρ p) ^ 2)⁻¹)) →
      ∃ J : Set M, ∃ hJS : J ⊆ S, J.Finite ∧ J.PairwiseDisjoint (fun p => ball p (ρ p / 3)) ∧
        S ⊆ ⋃ i ∈ J, ball i (2 * ρ i) ∧
        (∀ x : M, ((J ∩ {i | x ∈ ball i (2000000 * ρ i)}).ncard : ℝ) ≤
          modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
            modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) ∧
        ∀ i (hi : i ∈ J),
        let hmet := simultaneousMetricAlignment g hEnorm
        let hMc : CompleteSpace M := complete_of_compact
        letI := m.rescale (ρ i)⁻¹ (inv_pos.mpr (hρpos i))
        letI := (m.rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr (hρpos i))).mpr hMc
        letI := radialScaledBundle g (ρ i)⁻¹ (inv_pos.mpr (hρpos i))
        letI := radialScaledContinuous g (ρ i)⁻¹ (inv_pos.mpr (hρpos i))
        letI := radialScaledManifold (m := m) g hmet (ρ i)⁻¹ (inv_pos.mpr (hρpos i))
        ∃ η : M → ℝ², ∃ hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball i 200),
        ∃ hrank : ∀ x ∈ ball i 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x),
          η i = 0 ∧ LipschitzOnWith 2 η (ball i 200) ∧
          (∀ x ∈ ball i 200, ‖η x - ((F ⟨i, hJS hi⟩).toFun x).fst‖ < γ) ∧
          (∀ x ∈ ball i 200, ‖η x‖ < 100 → x ∈ ball i 102) ∧
          (∀ x ∈ ball i 200, η x = 0 → x ∈ ball i 2) ∧
          (∀ x ∈ ball i 2, ‖η x‖ ≤ 8) ∧
          (let f := diskPreimageMap (ball i 200) isOpen_ball η hη.continuousOn 100
          ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧
            (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧ Surjective f ∧
            (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
            ∀ R (hR : 0 < R) (hRr : R < 100),
              let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
              letI := regularFiberChartedSpace f y₀ (contMDiff_diskPreimageMap isOpen_ball hη 100)
                (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
              let U : TopologicalSpace.Opens
                  (diskPreimageOpens (ball i 200) isOpen_ball η hη.continuousOn 100) :=
                ⟨f ⁻¹' planeBallInner 100 R,
                  (planeBallInner 100 R).isOpen.preimage
                    (continuous_diskPreimageMap isOpen_ball hη.continuousOn 100)⟩
              ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
                  (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
                  ({x // f x = y₀} × planeBallInner 100 R) U ∞),
                (∀ z, f (Θ z).1 = z.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
          (Module.finrank ℝ E = 3 → ∀ z : planeBallOpens 100,
            let f := diskPreimageMap (ball i 200) isOpen_ball η hη.continuousOn 100
            letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball hη 100)
              (fun x _ => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
            Nonempty (Circle ≃ₘ⟮𝓡 1,
              𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯ {x // f x = z})) ∧
          ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
            (∀ x, ζ x ∈ Icc 0 1) ∧ (∀ x ∈ ball i 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧
            ∀ x, ζ x ≠ 0 → x ∈ ball i 200 ∧ ‖η x‖ < 9 := by
  obtain ⟨a₂, ha₂, hCF1⟩ := exists_circle_packet_at_scale.{uE, uH, u, v, w}
  refine ⟨a₂, ha₂, fun γ hγ hγone => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hpack⟩ := hCF1 γ hγ hγone
  refine ⟨β₀, hβ₀, hβ₀a, ?_⟩
  intro E _ _ _ _ hdim H _ I _ M m _ _ _ _ _ _ _ _ _ g hEnorm ρ Λ hρ hρpos hΛ S Y _ a C _ _ c
    σ β f F hdata
  obtain ⟨J, hJS, hfin, hdisj, hcov, hmult⟩ :=
    exists_simultaneous_support_cover g hEnorm hdim S hρ hρpos hΛ
      (fun p hp => (hdata ⟨p, hp⟩).2.2.2.2.2.2)
  refine ⟨J, hJS, hfin, hdisj, ?_, hmult, ?_⟩
  · intro p hp
    obtain ⟨i, hi, hsub⟩ := hcov p hp
    exact mem_iUnion₂.mpr ⟨i, hi, hsub (mem_ball_self (hρpos p))⟩
  · intro i hi
    obtain ⟨hlen, hdimC, hcomp, hσ, hβ, hsec, -⟩ := hdata ⟨i, hJS hi⟩
    exact hpack E H I M g (simultaneousMetricAlignment g hEnorm) (Y ⟨i, hJS hi⟩) i
      (a ⟨i, hJS hi⟩) (ρ i) (hρpos i) (C ⟨i, hJS hi⟩) (c ⟨i, hJS hi⟩) hlen hdimC hcomp hσ hβ
      (f ⟨i, hJS hi⟩) (F ⟨i, hJS hi⟩) hsec

end DifferentialGeometry.Geometry.Collapse
