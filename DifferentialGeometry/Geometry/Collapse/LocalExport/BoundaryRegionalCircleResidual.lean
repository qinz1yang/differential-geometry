import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalCircle
import DifferentialGeometry.Geometry.Collapse.LocalExport.CircleResidualEnclosure

/-!
# Review 51, A2: the regional circle family keeping LFR07's residual certificate (lane BE-1)

Blueprint 207A, LFR07 (`cor:collapse-rank-two-circle-packet`, A:25322: the actual residual
coordinate has distance `< 1` from `y₀`) and 207B, TCP01 (`lem:fibration-first-comparison-list`,
B:5250: every point `|η_j| ≤ 8` lies in `D_j = B(j, 10ρ(j))`). External review 51 (P0-B, A2): the
boundary base family must carry the closed route's `circle_residual`
(`LocalChartPacketsR.circle_residual`, LocalChartPacketsResidual.lean) for the SAME circle chart,
on the complete carrier, without the closed wrapper's `[CompactSpace X]`.

* `exists_circleChart_with_tests_residual_at_scale_complete_BE1`: the at-scale circle kernel on a
  COMPLETE σ-compact carrier (`exists_circleChart_with_tests_at_scale_complete_BDRY4`) with the
  residual enclosure `|η| ≤ 8 ⇒ B(j, 10)` of the produced chart on its normalized domain
  `B(j, 200)` (thresholds folded with `exists_simultaneous_circle_residual_threshold` of the SAME
  two-dimensional model data, and `β ≤ 1/200`; mirror of
  `exists_circleChart_with_tests_residual_at_scale_LC87`).
* `exists_regional_circleFamily_residual_BE1`: the statement of `exists_regional_circleFamily_BDRY4`
  (same binders, same order) whose family carries, in addition, the residual enclosure of EVERY
  circle chart of that family (the chart, the formula cutoff and the adapted packet are the same
  objects as before).
* consumer `exists_regional_circleFamily_residual_dist_BE1`: on the family returned by the
  producer, every point of the physical chart domain `B(j, 200ρ(j))` with `|η_j| ≤ 8` lies in
  `D_j = B(j, 10ρ(j))` (TCP01's circle clause, regional form).
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

/-- **The at-scale circle kernel on a complete carrier with LFR07's residual enclosure.** The
statement of `exists_circleChart_with_tests_at_scale_complete_BDRY4` with, in addition, the residual
enclosure of the produced chart at normalized scale: `|η| ≤ 8` on `B(j, 200)` forces `B(j, 10)`. -/
theorem exists_circleChart_with_tests_residual_at_scale_complete_BE1 :
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
            c.contMDiffOn_coord.continuousOn 100 : Set X) ∧ ζc = c.formulaCutoff ∧
          ∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → x ∈ ball j 10) ∧
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
  obtain ⟨a₀, ha₀, -, hres⟩ := exists_simultaneous_circle_residual_threshold.{u, 0, 0}
  obtain ⟨a₂, ha₂, hK⟩ := exists_circleChart_with_tests_at_scale_complete_BDRY4.{u}
  refine ⟨min a₂ a₀, lt_min ha₂ ha₀, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hK⟩ := hK γ hγ hγ1
  refine ⟨min β₀ (min a₀ (1 / 200)), lt_min hβ₀ (lt_min ha₀ (by norm_num)),
    le_min ((min_le_left _ _).trans hβ₀a) ((min_le_right _ _).trans (min_le_left _ _)),
    fun X mX _ _ _ _ g hmetric j r hr σ β hσ hβ hmodel Y mY a F hsec1 => ?_⟩
  obtain ⟨c, ζc, ⟨hcen, h8, hne, hts, hform⟩, hsm, h01, hpl, htsb, hadapt, hlip, htest⟩ :=
    hK X g hmetric j r hr (hσ.trans (min_le_left _ _)) (hβ.trans (min_le_left _ _)) hmodel Y a F
      hsec1
  refine ⟨c, ζc, ⟨hcen, h8, hne, hts, hform, ?_⟩, hsm, h01, hpl, htsb, hadapt, hlip, htest⟩
  obtain ⟨C, mC, cC, hCc, -, hCdim, hCcomp, hCseg, ⟨f⟩⟩ := hmodel
  let mR : MetricSpace X := mX.rescale r⁻¹ (inv_pos.mpr hr)
  have hres' : ∀ x ∈ ball j 200, dist (F.toFun x).snd a < 1 := fun x hx =>
    hres X j C cC (Metric.arbitrarily_short_curves_of_metric_segments hCseg) hCdim hCcomp Y a σ β
      (hσ.trans (min_le_right _ _)) (hβ.trans ((min_le_right _ _).trans (min_le_left _ _))) f F x
      ((mem_ball.mp hx).le.trans (by norm_num))
  exact circlePacket_residual_enclosure F
    (hβ.trans ((min_le_right _ _).trans (min_le_right _ _))) hres'
    (fun x hx => (hadapt x hx).trans hγ1)

/-- **The regional circle family keeping LFR07's residual certificate.** The statement of
`exists_regional_circleFamily_BDRY4` whose family carries, in addition, at every circle centre `j`
the residual enclosure of ITS chart on the normalized domain: `|η_j| ≤ 8` on `B(j, 200)` (at scale
`ρ(j)`) forces `B(j, 10)`. -/
theorem exists_regional_circleFamily_residual_BE1 :
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
          CircleAdaptedCentreOn X g hmetric ρ hρpos β γ U₁ U₂ C j hj) ∧
        ∀ j (hj : j ∈ C.centres),
          let c := C.chart j hj
          letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          ∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → x ∈ ball j 10 := by
  classical
  obtain ⟨a₂, ha₂, hK2⟩ := exists_circleChart_with_tests_residual_at_scale_complete_BE1.{0}
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
  -- the chart, formula cutoff, residual enclosure and adapted packet at every centre
  have hcdata : ∀ j ∈ J, ∃ c : (letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
      CircleChart 𝓘(ℝ, E3) X), ∃ ζc : X → ℝ,
      (letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
        c.center = j ∧ (∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → ζc x = 1) ∧
        (∀ x, ζc x ≠ 0 → x ∈ ball j 200 ∧ ‖c.coord x‖ < 9) ∧
        tsupport ζc ⊆ (diskPreimageOpens (ball c.center 200) isOpen_ball c.coord
          c.contMDiffOn_coord.continuousOn 100 : Set X) ∧ ζc = c.formulaCutoff ∧
        ∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → x ∈ ball j 10) ∧
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
      test := (hFc j hj).2.2 }⟩, fun j hj => (hcc j hj).1.2.2.2.2.2⟩
  change (if hj' : j ∈ J then ζc j hj' else 0) = _
  rw [dite_eq_left hj]
  exact (hcc j hj).1.2.2.2.2.1

/-- **Consumer: TCP01's circle clause on the regional family.** On the family returned by
`exists_regional_circleFamily_residual_BE1`, at every circle centre `j`, every point `x` of the
physical chart domain `B(j, 200ρ(j))` with `|η_j(x)| ≤ 8` lies in `D_j = B(j, 10ρ(j))`. -/
theorem exists_regional_circleFamily_residual_dist_BE1 :
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
      ∃ C : CircleFamilyOn 𝓘(ℝ, E3) X ρ hρpos β U₁ U₂,
        ∀ j (hj : j ∈ C.centres), ∀ x, dist x j < 200 * ρ j →
          (let c := C.chart j hj; letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j));
            ‖c.coord x‖ ≤ 8) →
          dist x j < 10 * ρ j := by
  obtain ⟨a₂, ha₂, h⟩ := exists_regional_circleFamily_residual_BE1
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun X mX _ _ _ _ _ _ g hmetric ρ hρpos Λ hΛ hρlip hΛs β σ hσ hβ U₁ U₂
    Kc hKc hU₁ hmodel hsec1 hsec2 => ?_⟩
  obtain ⟨C, -, -, hres⟩ := h X g hmetric ρ hρpos hΛ hρlip hΛs β hσ hβ U₁ U₂ Kc hKc hU₁ hmodel
    hsec1 hsec2
  refine ⟨C, fun j hj x hx h8 => ?_⟩
  have hx' : (ρ j)⁻¹ * dist x j < 200 := by
    rw [inv_mul_lt_iff₀ (hρpos j)]
    linarith
  have h10 : (ρ j)⁻¹ * dist x j < 10 := hres j hj x hx' h8
  have h := (inv_mul_lt_iff₀ (hρpos j)).mp h10
  linarith

end DifferentialGeometry.Geometry.Collapse
