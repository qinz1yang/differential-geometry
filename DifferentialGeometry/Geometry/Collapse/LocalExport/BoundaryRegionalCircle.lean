import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalPacketsOn
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySelections

/-!
# LC88 / BCP04, packets P4c / P5: the regional circle family with adapted packets (BDRY-4)

Review 45 §3.3–3.4: the shared regionalised kernel on ONE complete σ-compact carrier. The closed
producer `eventually_nonempty_localChartFamilyEA` builds the circle family from (i) the eligible
maximal selection among the two-stratum points, (ii) at every centre the LC87 at-scale kernel
`exists_circleChart_with_tests_at_scale_LC87` (chart, formula cutoff, adapted packet against the
SAME `(2, β₂)`-splitting). Both steps use compactness of the carrier only for completeness and for
the finiteness of the selection; here:

* `exists_circleChart_with_tests_at_scale_complete_BDRY4`: the at-scale kernel on a COMPLETE
  σ-compact carrier (the instance blocks take the carrier's own `CompleteSpace`);
* `exists_regional_circleFamily_BDRY4`: on a complete, proper, σ-compact, connected carrier with a
  Lipschitz scale `ρ`, regions `U₁ ⊆ Kc` (`Kc` compact), the collapsed model at every point of `U₁`
  and the two sectional buffers at every point of `U₁`: a `CircleFamilyOn … U₁ U₂` (candidates
  `U₁ ∩ Z₂`, G14's proper selection) with the formula cutoffs and a `CircleAdaptedCentreOn` at
  every centre;
* consumer `exists_regional_circleFamily_centres_BDRY4`: the centres lie in `U₁ ∩ Z₂` and cover
  every eligible ball.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The LC87 at-scale circle kernel on a complete carrier.**
`exists_circleChart_with_tests_at_scale_LC87` with `[CompleteSpace X] [SigmaCompactSpace X]` instead
of `[CompactSpace X]` (compactness was used only for completeness). -/
theorem exists_circleChart_with_tests_at_scale_complete_BDRY4 :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ (X : Type u) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompleteSpace X] [SigmaCompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (j : X) (r : ℝ) (hr : 0 < r) {σ β : ℝ}, σ ≤ a₂ → β ≤ β₀ →
      (∃ (C : Type) (mC : MetricSpace C) (c : C), letI := mC
        CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
        fourPointComparison 0 (univ : Set C) ∧
        (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        Nonempty (@KleinerLottApprox X C (mX.rescale r⁻¹ (inv_pos.mpr hr)) mC j c σ)) →
      ∀ (Y : Type) [mY : MetricSpace Y] (a : Y)
        (F : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin 2) × Y))
          (mX.rescale r⁻¹ (inv_pos.mpr hr)) _ j
          (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), a)) β),
      (∀ y ∈ ball j (β⁻¹ * r), SectionalBoundedBelowAt g y (-(β ^ 2 * r⁻¹ ^ 2))) →
      ∃ c : (letI := mX.rescale r⁻¹ (inv_pos.mpr hr); CircleChart 𝓘(ℝ, E3) X), ∃ ζc : X → ℝ,
        (letI := mX.rescale r⁻¹ (inv_pos.mpr hr);
          c.center = j ∧ (∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → ζc x = 1) ∧
          (∀ x, ζc x ≠ 0 → x ∈ ball j 200 ∧ ‖c.coord x‖ < 9) ∧
          tsupport ζc ⊆ (diskPreimageOpens (ball c.center 200) isOpen_ball c.coord
            c.contMDiffOn_coord.continuousOn 100 : Set X) ∧ ζc = c.formulaCutoff) ∧
        ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ζc ∧ (∀ x, ζc x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x ∈ ball j (2 * r), ζc x = 1) ∧ tsupport ζc ⊆ ball j (200 * r) ∧
        (letI := mX.rescale r⁻¹ (inv_pos.mpr hr)
          ∀ x ∈ ball j 200, ‖c.coord x - (F.toFun x).fst‖ < γ) ∧
        (letI := mX.rescale r⁻¹ (inv_pos.mpr hr);
          LipschitzOnWith (Real.toNNReal (1 + γ)) c.coord (ball j 200)) ∧
        (let hMc : CompleteSpace X := ‹CompleteSpace X›
        letI := mX.rescale r⁻¹ (inv_pos.mpr hr)
        letI := radialScaledBundle g r⁻¹ (inv_pos.mpr hr)
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g r⁻¹ (inv_pos.mpr hr)
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric r⁻¹ (inv_pos.mpr hr)
        letI : CompleteSpace X := (mX.rescale_completeSpace_iff r⁻¹ (inv_pos.mpr hr)).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
        ∀ x ∈ ball j 200, ∀ z ∈ ball j (201 * 10000), 201 < dist x z →
          ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
          intrinsicGeodesic gR hnR x w (dist x z) = z →
          ‖mvfderiv (I := 𝓘(ℝ, E3)) c.coord x w -
            (dist x z)⁻¹ • ((F.toFun z).fst - (F.toFun x).fst)‖ < γ) := by
  obtain ⟨a₂, ha₂, hK2⟩ := exists_circleChart_with_tests.{0, 0, u, 0, 0}
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hK2⟩ := hK2 γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun X mX _ _ _ _ g hmetric j r hr σ β hσ hβ hmodel Y mY a F hsec1 => ?_⟩
  obtain ⟨C, mC, c, hCc, -, hCdim, hCcomp, hCseg, ⟨f⟩⟩ := hmodel
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR : MetricSpace X := mX.rescale r⁻¹ (inv_pos.mpr hr)
  let bR := radialScaledBundle g r⁻¹ (inv_pos.mpr hr)
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g r⁻¹ (inv_pos.mpr hr)
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric r⁻¹ (inv_pos.mpr hr)
  let kR : CompleteSpace X := (mX.rescale_completeSpace_iff r⁻¹ (inv_pos.mpr hr)).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X := scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hsecR : ∀ y ∈ ball j β⁻¹, SectionalBoundedBelowAt gR y (-β ^ 2) := by
    intro y hy
    have hy' : r⁻¹ * @dist X mX.toDist y j < β⁻¹ := hy
    have hyr : y ∈ @ball X mX.toPseudoMetricSpace j (β⁻¹ * r) := by
      change @dist X mX.toDist y j < β⁻¹ * r
      rw [inv_mul_lt_iff₀ hr] at hy'
      linarith
    rw [sectionalBoundedBelowAt_scaleMetric_iff]
    simpa only [neg_mul] using hsec1 y hyr
  obtain ⟨ch, hcen, h8, hlipγ, hadapt, htests⟩ := hK2 E3 E3 𝓘(ℝ, E3) X gR hnR Y j a C c
    (Metric.arbitrarily_short_curves_of_metric_segments hCseg) hCdim hCcomp hσ hβ f F hsecR
  obtain ⟨hsm, h01, heq1, hne, hts102, htsdom⟩ := ch.formulaCutoff_spec
  have hcen' : ch.center = j := hcen
  refine ⟨ch, ch.formulaCutoff, ⟨hcen', fun x hx h8x => heq1 x (by rw [hcen']; exact hx) h8x,
    fun x hx => ⟨by have h := (hne x hx).1; rw [hcen'] at h; exact h, (hne x hx).2⟩, htsdom,
    rfl⟩, hsm, h01, ?_, ?_, hadapt, hlipγ, htests⟩
  · intro x hx
    have hx2 : r⁻¹ * @dist X mX.toDist x j < 2 := by
      have hx' : @dist X mX.toDist x j < 2 * r := hx
      rw [inv_mul_lt_iff₀ hr]
      linarith
    have hxc : x ∈ ball ch.center 200 := by
      rw [hcen']
      change r⁻¹ * @dist X mX.toDist x j < 200
      linarith
    exact heq1 x hxc (h8 x hx2)
  · intro x hx
    have h102 := (hts102 hx).1
    rw [hcen'] at h102
    have h102' : r⁻¹ * @dist X mX.toDist x j ≤ 102 := h102
    rw [inv_mul_le_iff₀ hr] at h102'
    change @dist X mX.toDist x j < 200 * r
    linarith

/-- **The regional circle family with formula cutoffs and adapted packets.** On a complete,
proper, σ-compact, connected carrier with a `Λ`-Lipschitz scale (`2·10⁶ Λ ≤ 1/100`), regions
`U₁ ⊆ Kc` with `Kc` compact, at every `p ∈ U₁` the collapsed model of quality `σ ≤ a₂` and the
sectional buffers on `B(p, β₂⁻¹ρ(p))` and `B(p, (3·2·10⁶ + 2/3) ρ(p))`: a `CircleFamilyOn … U₁ U₂`
whose cutoffs are the formula cutoffs, with a `CircleAdaptedCentreOn` at every centre. -/
theorem exists_regional_circleFamily_BDRY4 :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompleteSpace X] [SigmaCompactSpace X] [ProperSpace X] [ConnectedSpace X]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p) {Λ : ℝ}, 0 ≤ Λ → LipschitzWith (Real.toNNReal Λ) ρ →
        Λ * 2000000 ≤ 1 / 100 →
      ∀ (β : ℕ → ℝ) {σ : ℝ}, σ ≤ a₂ → β 2 ≤ β₀ →
      ∀ (U₁ U₂ Kc : Set X), IsCompact Kc → U₁ ⊆ Kc →
      (∀ p ∈ U₁, ∃ (C : Type) (mC : MetricSpace C) (c : C), letI := mC
        CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
        fourPointComparison 0 (univ : Set C) ∧
        (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        Nonempty (@KleinerLottApprox X C (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ)) →
      (∀ p ∈ U₁, ∀ y ∈ ball p ((β 2)⁻¹ * ρ p),
        SectionalBoundedBelowAt g y (-(β 2 ^ 2 * (ρ p)⁻¹ ^ 2))) →
      (∀ p ∈ U₁, ∀ y ∈ ball p ((3 * 2000000 + 2 / 3) * ρ p),
        SectionalBoundedBelowAt g y (-((2000000 * ρ p) ^ 2)⁻¹)) →
      ∃ C : CircleFamilyOn 𝓘(ℝ, E3) X ρ hρpos β U₁ U₂,
        (∀ j (hj : j ∈ C.centres),
          let c := C.chart j hj
          let ζ := C.cutoff j
          letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          ζ = c.formulaCutoff) ∧
        Nonempty (∀ j (hj : j ∈ C.centres),
          CircleAdaptedCentreOn X g hmetric ρ hρpos β γ U₁ U₂ C j hj) := by
  classical
  obtain ⟨a₂, ha₂, hK2⟩ := exists_circleChart_with_tests_at_scale_complete_BDRY4.{0}
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hK2⟩ := hK2 γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun X mX _ _ _ _ _ _ g hmetric ρ hρpos Λ hΛ hρlip hΛs β σ hσ hβ U₁ U₂
    Kc hKc hU₁ hmodel hsec1 hsec2 => ?_⟩
  -- the Riemannian instances of the aligned metric
  let instRB : RiemannianBundle (fun x : X => TangentSpace 𝓘(ℝ, E3) x) := ⟨g.toRiemannianMetric⟩
  have instCRB : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric g
  have instRM : IsRiemannianManifold 𝓘(ℝ, E3) X := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]
  have hEnorm : IsMetricNorm (I := 𝓘(ℝ, E3)) g := isMetricNorm_of_riemannianBundle g
  have instM1 : IsManifold 𝓘(ℝ, E3) 1 X := IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have instT2 : T2Space (TangentBundle 𝓘(ℝ, E3) X) := inferInstance
  -- the eligible selection among the candidates `U₁ ∩ Z₂`
  have hΛ' : ((Real.toNNReal Λ : NNReal) : ℝ) * 2000000 ≤ 1 / 100 := by
    rw [Real.coe_toNNReal _ hΛ]
    exact hΛs
  obtain ⟨J, hJS, hJfin, hJdisj, hJcov, hJmult⟩ :=
    exists_simultaneous_support_cover_proper_BDRY3 g hEnorm finrank_euclideanSpace_fin hKc
      (U₁ ∩ scaledSplittingStratum.{0, 0} ρ hρpos β 2)
      (fun x hx => hU₁ hx.1) hρlip hρpos hΛ' (fun p hp => hsec2 p hp.1)
  -- the chart, formula cutoff and adapted packet at every centre
  have hcdata : ∀ j ∈ J, ∃ c : (letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
      CircleChart 𝓘(ℝ, E3) X), ∃ ζc : X → ℝ,
      (letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
        c.center = j ∧ (∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → ζc x = 1) ∧
        (∀ x, ζc x ≠ 0 → x ∈ ball j 200 ∧ ‖c.coord x‖ < 9) ∧
        tsupport ζc ⊆ (diskPreimageOpens (ball c.center 200) isOpen_ball c.coord
          c.contMDiffOn_coord.continuousOn 100 : Set X) ∧ ζc = c.formulaCutoff) ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ζc ∧ (∀ x, ζc x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ball j (2 * ρ j), ζc x = 1) ∧ tsupport ζc ⊆ ball j (200 * ρ j) ∧
      ∃ (Y : Type) (mY : MetricSpace Y), letI := mY
        ∃ (a : Y) (F : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin 2) × Y))
            (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j
            (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), a)) (β 2)),
        (letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          ∀ x ∈ ball j 200, ‖c.coord x - (F.toFun x).fst‖ < γ) ∧
        (letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
          LipschitzOnWith (Real.toNNReal (1 + γ)) c.coord (ball j 200)) ∧
        (let hMc : CompleteSpace X := ‹CompleteSpace X›
        letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI : CompleteSpace X :=
          (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) g
        have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
        ∀ x ∈ ball j 200, ∀ z ∈ ball j (201 * 10000), 201 < dist x z →
          ∀ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 →
          intrinsicGeodesic gR hnR x w (dist x z) = z →
          ‖mvfderiv (I := 𝓘(ℝ, E3)) c.coord x w -
            (dist x z)⁻¹ • ((F.toFun z).fst - (F.toFun x).fst)‖ < γ) := by
    intro j hj
    obtain ⟨Y, mY, a, ⟨F⟩⟩ := hasEuclideanSplitting_of_mem_scaledSplittingStratum_two (hJS hj).2
    obtain ⟨c, ζc, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hK2 X g hmetric j (ρ j) (hρpos j) hσ hβ
      (hmodel j (hJS hj).1) Y a F (hsec1 j (hJS hj).1)
    exact ⟨c, ζc, h1, h2, h3, h4, h5, Y, mY, a, F, h6, h7, h8⟩
  choose cc ζc hcc using hcdata
  let circle : CircleFamilyOn 𝓘(ℝ, E3) X ρ hρpos β U₁ U₂ :=
    { centres := J
      finite_centres := hJfin
      centres_subset := hJS
      disjoint_centres := hJdisj
      covers := hJcov
      chart := cc
      chart_center := fun j hj => (hcc j hj).1.1
      cutoff := fun j => if hj : j ∈ J then ζc j hj else 0
      contMDiff_cutoff := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).2.1
      cutoff_mem_Icc := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).2.2.1
      cutoff_eq_one := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).1.2.1
      coord_lt_of_cutoff_ne_zero := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).1.2.2.1
      tsupport_subset_domain := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).1.2.2.2.1
      plateau := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).2.2.2.1
      tsupport_subset_ball := fun j hj => by rw [dite_eq_left hj]; exact (hcc j hj).2.2.2.2.1
      multiplicity := fun x => by
        refine le_trans ?_ (hJmult x)
        have hsub : J ∩ {j | x ∈ tsupport (if hj : j ∈ J then ζc j hj else 0)} ⊆
            J ∩ {j | x ∈ ball j (2000000 * ρ j)} := by
          rintro j ⟨hj, hx⟩
          rw [mem_ofPred_eq, dite_eq_left hj] at hx
          refine ⟨hj, ball_subset_ball ?_ ((hcc j hj).2.2.2.2.1 hx)⟩
          linarith [hρpos j]
        exact_mod_cast Set.ncard_le_ncard hsub (hJfin.subset inter_subset_left) }
  choose Yc mYc ac Fc hFc using fun j (hj : j ∈ J) => (hcc j hj).2.2.2.2.2
  refine ⟨circle, fun j hj => ?_, ⟨fun j hj =>
    { Y := Yc j hj
      instY := mYc j hj
      a := ac j hj
      split := Fc j hj
      adapted := (hFc j hj).1
      lipschitz := (hFc j hj).2.1
      test := (hFc j hj).2.2 }⟩⟩
  change (if hj' : j ∈ J then ζc j hj' else 0) = _
  rw [dite_eq_left hj]
  exact (hcc j hj).1.2.2.2.2

/-- **Consumer: the regional circle centres.** Every centre of the regional circle family lies in
`U₁ ∩ Z₂` and every eligible `ρ`-ball of `U₁ ∩ Z₂` lies in a doubled centre ball. -/
theorem exists_regional_circleFamily_centres_BDRY4 :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompleteSpace X] [SigmaCompactSpace X] [ProperSpace X] [ConnectedSpace X]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X),
        (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) →
        ∀ (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p) {Λ : ℝ}, 0 ≤ Λ →
        LipschitzWith (Real.toNNReal Λ) ρ → Λ * 2000000 ≤ 1 / 100 →
      ∀ (β : ℕ → ℝ) {σ : ℝ}, σ ≤ a₂ → β 2 ≤ β₀ →
      ∀ (U₁ U₂ Kc : Set X), IsCompact Kc → U₁ ⊆ Kc →
      (∀ p ∈ U₁, ∃ (C : Type) (mC : MetricSpace C) (c : C), letI := mC
        CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
        fourPointComparison 0 (univ : Set C) ∧
        (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        Nonempty (@KleinerLottApprox X C (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ)) →
      (∀ p ∈ U₁, ∀ y ∈ ball p ((β 2)⁻¹ * ρ p),
        SectionalBoundedBelowAt g y (-(β 2 ^ 2 * (ρ p)⁻¹ ^ 2))) →
      (∀ p ∈ U₁, ∀ y ∈ ball p ((3 * 2000000 + 2 / 3) * ρ p),
        SectionalBoundedBelowAt g y (-((2000000 * ρ p) ^ 2)⁻¹)) →
      ∃ J : Set X, J.Finite ∧ J ⊆ U₁ ∩ scaledSplittingStratum.{0, 0} ρ hρpos β 2 ∧
        ∀ p ∈ U₁ ∩ scaledSplittingStratum.{0, 0} ρ hρpos β 2, ∃ j ∈ J,
          ball p (ρ p) ⊆ ball j (2 * ρ j) := by
  obtain ⟨a₂, ha₂, h⟩ := exists_regional_circleFamily_BDRY4
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun X mX _ _ _ _ _ _ g hmetric ρ hρpos Λ hΛ hρlip hΛs β σ hσ hβ U₁ U₂
    Kc hKc hU₁ hmodel hsec1 hsec2 => ?_⟩
  obtain ⟨C, -, -⟩ := h X g hmetric ρ hρpos hΛ hρlip hΛs β hσ hβ U₁ U₂ Kc hKc hU₁ hmodel hsec1
    hsec2
  exact ⟨C.centres, C.finite_centres, C.centres_subset, C.covers⟩

end DifferentialGeometry.Geometry.Collapse
