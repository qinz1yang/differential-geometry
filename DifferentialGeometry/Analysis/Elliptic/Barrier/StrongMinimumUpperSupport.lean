import DifferentialGeometry.Analysis.Elliptic.Barrier.ChartAnnulusComparison
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Closure
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Manifold.BumpFunction

set_option autoImplicit false
noncomputable section

open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem norm_distance_le_transported_distance (z w : E) :
    dist z w ≤ ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ *
      Euclidean.dist z w := by
  have he : Euclidean.dist z w = ‖toEuclidean (z - w)‖ := by
    rw [Euclidean.dist, dist_eq_norm, map_sub]
  rw [dist_eq_norm, he]
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
    (toEuclidean (E := E)).symm.toContinuousLinearMap.le_opNorm (toEuclidean (z - w))

omit [IsManifold I ∞ M] [T2Space M] in
private theorem coordinate_target_of_fit (a : M) (b : SmoothBumpFunction I a)
    (z : E) (R : ℝ)
    (hfit : ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ * R +
      dist z (extChartAt I a a) < b.rIn)
    {w : E} (hw : w ∈ Euclidean.closedBall z R) :
    w ∈ (extChartAt I a).target := by
  have hnorm := norm_distance_le_transported_distance w z
  have hbound := mul_le_mul_of_nonneg_left hw
    (norm_nonneg (toEuclidean (E := E)).symm.toContinuousLinearMap)
  have hcore : dist w (extChartAt I a a) < b.rIn :=
    (dist_triangle w z (extChartAt I a a)).trans_lt
      ((add_le_add (hnorm.trans hbound) (le_refl (dist z (extChartAt I a a)))).trans_lt hfit)
  apply b.closedBall_subset
  refine ⟨hcore.le.trans b.rIn_lt_rOut.le, ?_⟩
  rw [I.range_eq_univ]
  exact mem_univ w

private theorem annulus_fit_arithmetic (A d D B : ℝ) (hA : 0 ≤ A) (hd : 0 < d)
    (hsmall : d * (8 * (A + 1)) < B) (hD : D ≤ A * d) : A * (2 * d) + D < B := by
  have hAd : 0 ≤ A * d := mul_nonneg hA hd.le
  nlinarith only [hsmall, hD, hd, hAd]

private theorem exists_positive_near_map {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    (u : X → ℝ) (q : X) (hq : q ∈ closure {x : X | 0 < u x}) (huq : u q = 0)
    (χ : X → Y) (U : Set X) (hU : IsOpen U) (hqU : q ∈ U)
    (hχ : ContinuousOn χ U) (hinj : Set.InjOn χ U) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : X, 0 < u c ∧ c ∈ U ∧ 0 < dist (χ c) (χ q) ∧ dist (χ c) (χ q) < δ := by
  let W := U ∩ χ ⁻¹' Metric.ball (χ q) δ
  have hW : IsOpen W := hχ.isOpen_inter_preimage hU Metric.isOpen_ball
  have hqW : q ∈ W := ⟨hqU, Metric.mem_ball_self hδ⟩
  obtain ⟨c, hcW, hcpos⟩ := mem_closure_iff.mp hq W hW hqW
  have hcq : c ≠ q := by
    intro heq
    have h : 0 < u q := heq ▸ hcpos
    rw [huq] at h
    exact (lt_irrefl 0) h
  exact ⟨c, hcpos, hcW.1,
    dist_pos.mpr (fun heq => hcq (hinj hcW.1 hqU heq)), hcW.2⟩

omit [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
private theorem exists_positive_chart_point
    (u : M → ℝ) (q : M) (hq : q ∈ closure {x : M | 0 < u x})
    (huq : u q = 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : M, 0 < u c ∧ c ∈ (extChartAt I q).source ∧
      0 < Euclidean.dist (extChartAt I q c) (extChartAt I q q) ∧
        Euclidean.dist (extChartAt I q c) (extChartAt I q q) < δ := by
  let χ : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun x => toEuclidean (extChartAt I q x)
  have hU : IsOpen (extChartAt I q).source := by
    rw [extChartAt_source]
    exact (chartAt H q).open_source
  have hχ : ContinuousOn χ (extChartAt I q).source :=
    toEuclidean.continuous.comp_continuousOn (continuousOn_extChartAt (I := I) q)
  exact exists_positive_near_map u q hq huq χ _ hU (mem_extChartAt_source q) hχ
    (fun c hc d hd heq => (extChartAt I q).injOn hc hd (toEuclidean.injective heq)) δ hδ

omit [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] in
private theorem exists_fitted_positive_center
    (u : M → ℝ) (q : M) (hq : q ∈ closure {x : M | 0 < u x})
    (huq : u q = 0) (b : SmoothBumpFunction I q) :
    ∃ c : M, 0 < u c ∧ c ∈ (extChartAt I q).source ∧
      let z := extChartAt I q c
      let d := Euclidean.dist z (extChartAt I q q)
      0 < d ∧ ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ * (2 * d) +
        dist z (extChartAt I q q) < b.rIn := by
  let A : ℝ := ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖
  have hA : 0 ≤ A := norm_nonneg _
  let δ : ℝ := b.rIn / (8 * (A + 1))
  have hdenom : 0 < 8 * (A + 1) := by positivity
  have hδ : 0 < δ := div_pos b.rIn_pos hdenom
  have hδeq : δ * (8 * (A + 1)) = b.rIn := div_mul_cancel₀ _ hdenom.ne'
  obtain ⟨c, hcpos, hcs, hd, hdδ⟩ := exists_positive_chart_point (I := I) u q hq huq δ hδ
  let z : E := extChartAt I q c
  let d : ℝ := Euclidean.dist z (extChartAt I q q)
  have hsmall : d * (8 * (A + 1)) < b.rIn :=
    (mul_lt_mul_of_pos_right hdδ hdenom).trans_eq hδeq
  have hfit : ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ * (2 * d) +
      dist z (extChartAt I q q) < b.rIn := by
    have hnorm := norm_distance_le_transported_distance z (extChartAt I q q)
    change dist z (extChartAt I q q) ≤ A * d at hnorm
    change A * (2 * d) + dist z (extChartAt I q q) < b.rIn
    exact annulus_fit_arithmetic A d (dist z (extChartAt I q q)) b.rIn hA hd hsmall hnorm
  exact ⟨c, hcpos, hcs, hd, hfit⟩

omit [IsManifold I ∞ M] [T2Space M] in
private theorem exists_fitted_positive_annulus
    (u : M → ℝ) (hu : Continuous u) (q : M)
    (hq : q ∈ closure {x : M | 0 < u x}) (huq : u q = 0)
    (b : SmoothBumpFunction I q) :
    ∃ (z : E) (r R η : ℝ), 0 < r ∧
      (‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖ * R +
        dist z (extChartAt I q q) < b.rIn) ∧ 0 < η ∧
      let K := (extChartAt I q).symm '' (Euclidean.closedBall z R \ Euclidean.ball z r)
      q ∈ K ∧ Euclidean.dist (extChartAt I q q) z < R ∧
        (∀ y ∈ K, Euclidean.dist (extChartAt I q y) z = r → η ≤ u y) := by
  obtain ⟨c, hcpos, hcs, hd, hfit⟩ := exists_fitted_positive_center u q hq huq b
  let z : E := extChartAt I q c
  let d : ℝ := Euclidean.dist z (extChartAt I q q)
  have hqs : q ∈ (extChartAt I q).source := mem_extChartAt_source q
  let η : ℝ := u c / 2
  have hη : 0 < η := half_pos hcpos
  have hηc : η < u ((extChartAt I q).symm z) := by
    rw [show (extChartAt I q).symm z = c from (extChartAt I q).left_inv hcs]
    exact half_lt_self hcpos
  have hcomp : ContinuousAt (fun w : E => u ((extChartAt I q).symm w)) z :=
    hu.continuousAt.comp (continuousAt_extChartAt_symm' hcs)
  have hnear : {w : E | η < u ((extChartAt I q).symm w)} ∈ 𝓝 z :=
    hcomp.preimage_mem_nhds (Ioi_mem_nhds hηc)
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Euclidean.nhds_basis_closedBall.mem_iff.mp hnear
  let r : ℝ := min (r₀ / 2) (d / 2)
  have hr : 0 < r := lt_min (half_pos hr₀) (half_pos hd)
  have hrr₀ : r ≤ r₀ := (min_le_left _ _).trans (half_le_self hr₀.le)
  have hrd : r < d := (min_le_right _ _).trans_lt (half_lt_self hd)
  let K : Set M := (extChartAt I q).symm ''
    (Euclidean.closedBall z (2 * d) \ Euclidean.ball z r)
  have hKsource : ∀ y ∈ K, y ∈ (extChartAt I q).source := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact (extChartAt I q).map_target (coordinate_target_of_fit q b z (2 * d) hfit hw.1)
  have hinner : ∀ y ∈ K, Euclidean.dist (extChartAt I q y) z = r → η ≤ u y := by
    intro y hy heq
    have hball : extChartAt I q y ∈ Euclidean.closedBall z r₀ := by
      change Euclidean.dist (extChartAt I q y) z ≤ r₀
      rw [heq]
      exact hrr₀
    have hpos := hr₀sub hball
    change η < u ((extChartAt I q).symm (extChartAt I q y)) at hpos
    rw [(extChartAt I q).left_inv (hKsource y hy)] at hpos
    exact hpos.le
  have hqd : Euclidean.dist (extChartAt I q q) z = d := by
    change dist (toEuclidean (extChartAt I q q)) (toEuclidean z) =
      dist (toEuclidean z) (toEuclidean (extChartAt I q q))
    exact dist_comm _ _
  have hqK : q ∈ K := by
    refine ⟨extChartAt I q q, ⟨?_, ?_⟩, (extChartAt I q).left_inv hqs⟩
    · change Euclidean.dist (extChartAt I q q) z ≤ 2 * d
      rw [hqd]
      linarith only [hd]
    · change ¬ Euclidean.dist (extChartAt I q q) z < r
      rw [hqd]
      exact not_lt.mpr hrd.le
  exact ⟨z, r, 2 * d, η, hr, hfit, hη, hqK,
    (by rw [hqd]; linarith only [hd]), hinner⟩

private theorem no_zero_in_closure_positive_of_upper_supports
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (hu : Continuous u)
    (hnonneg : ∀ x, 0 ≤ u x)
    (hsupport : ∀ x : M, ∀ ε : ℝ, 0 < ε →
      ∃ U : Set M, ∃ φ : M → ℝ,
        IsOpen U ∧ x ∈ U ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ U ∧
          φ x = u x ∧ (∀ y ∈ U, u y ≤ φ y) ∧
            laplacian (LeviCivita g) g φ x ≤ ε)
    (q : M) (hq : q ∈ closure {x : M | 0 < u x}) (huq : u q = 0) : False := by
  let b : SmoothBumpFunction I q := Classical.choice inferInstance
  obtain ⟨z, r, R, η, hr, hfit, hη, hqK, hqR, hinner⟩ :=
    exists_fitted_positive_annulus u hu q hq huq b
  have hpositive := positive_on_chart_annulus_of_laplacian_upper_supports
    g q b z r R hr hfit u η hη hu.continuousOn
    (fun y _ => hnonneg y) hinner (fun y _ ε hε => hsupport y ε hε)
  have hqpositive : 0 < u q := hpositive q hqK hqR
  rw [huq] at hqpositive
  exact (lt_irrefl 0) hqpositive

theorem eq_zero_of_laplacian_upper_supports [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ) (hu : Continuous u)
    (hnonneg : ∀ x, 0 ≤ u x)
    (hsupport : ∀ x : M, ∀ ε : ℝ, 0 < ε →
      ∃ U : Set M, ∃ φ : M → ℝ,
        IsOpen U ∧ x ∈ U ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ U ∧
          φ x = u x ∧ (∀ y ∈ U, u y ≤ φ y) ∧
            laplacian (LeviCivita g) g φ x ≤ ε)
    (x₀ : M) (hzero : u x₀ = 0) : ∀ x, u x = 0 := by
  have hopen : IsOpen {x : M | 0 < u x} := isOpen_lt continuous_const hu
  have hclosed : IsClosed {x : M | 0 < u x} := by
    apply isClosed_of_closure_subset
    intro q hq
    by_contra hnot
    have huq : u q = 0 := le_antisymm (le_of_not_gt hnot) (hnonneg q)
    exact no_zero_in_closure_positive_of_upper_supports g u hu hnonneg hsupport q hq huq
  intro x
  apply le_antisymm ?_ (hnonneg x)
  by_contra hnot
  have hxpos : 0 < u x := lt_of_not_ge hnot
  have huniv := (show IsClopen {y : M | 0 < u y} from ⟨hclosed, hopen⟩).eq_univ ⟨x, hxpos⟩
  have hx₀pos : 0 < u x₀ := by
    change x₀ ∈ {y : M | 0 < u y}
    rw [huniv]
    exact mem_univ x₀
  rw [hzero] at hx₀pos
  exact (lt_irrefl 0) hx₀pos

theorem eq_zero_of_nonneg_laplacian_nonpos [PreconnectedSpace M]
    (g : SmoothRiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (hnonneg : ∀ x, 0 ≤ u x)
    (hlap : ∀ x, laplacian (LeviCivita g) g u x ≤ 0)
    (x₀ : M) (hzero : u x₀ = 0) : ∀ x, u x = 0 := by
  apply eq_zero_of_laplacian_upper_supports g u hu.continuous hnonneg ?_ x₀ hzero
  intro x ε hε
  exact ⟨univ, u, isOpen_univ, mem_univ x, hu.contMDiffOn, rfl,
    fun _ _ => le_rfl, (hlap x).trans hε.le⟩

end DifferentialGeometry.Analysis

end
