import DifferentialGeometry.Geometry.Comparison.OneDimensionalRank
import DifferentialGeometry.Geometry.Comparison.RankExclusionChart
import DifferentialGeometry.Topology.MetricSpace.SegmentNeighborhood

set_option autoImplicit false

open Set Metric Real
open scoped Topology ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem exists_injOn_dist_ball_at_segment_interior_of_dimH_le_one
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hcomplete : ∀ z : X, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    (hdim : dimH (univ : Set X) ≤ 1)
    {l u : ℝ} (hlu : l ≤ u) {σ : Icc l u → X} (hσ : Isometry σ)
    (p : Icc l u) (hlp : l < (p : ℝ)) (hpu : (p : ℝ) < u) :
    ∃ r : ℝ, 0 < r ∧ InjOn (fun x : X => dist (σ ⟨l, le_rfl, hlu⟩) x) (ball (σ p) r) := by
  let a : Fin 1 → X := fun _ => σ ⟨l, le_rfl, hlu⟩
  let b : Fin 1 → X := fun _ => σ ⟨u, hlu, le_rfl⟩
  let δ : ℝ := 1/100000
  let β : ℝ := 1/1000
  have hδ : 0 < δ := by norm_num [δ]
  have hpa : dist (σ p) (a 0) = (p : ℝ) - l := by
    rw [hσ.dist_eq]
    exact abs_of_pos (sub_pos.mpr hlp)
  have hpb : dist (σ p) (b 0) = u - (p : ℝ) := by
    rw [hσ.dist_eq]
    change |(p : ℝ) - u| = _
    rw [abs_of_neg (sub_neg.mpr hpu)]
    ring
  have hab : dist (a 0) (b 0) = dist (σ p) (a 0) + dist (σ p) (b 0) := by
    rw [hpa, hpb, hσ.dist_eq]
    change |l - u| = _
    rw [abs_of_nonpos (sub_nonpos.mpr hlu)]
    ring
  have hang : comparisonAngleNegCurvature 1 (dist (σ p) (a 0))
      (dist (σ p) (b 0)) (dist (a 0) (b 0)) = Real.pi := by
    rw [hab]
    exact comparisonAngleNegCurvature_add (by norm_num)
      (by rw [hpa]; linarith) (by rw [hpb]; linarith)
  have hp : PairedComparisonPacket (δ/2) {σ p} a b := by
    constructor
    · intro z hz i
      have hz' : z = σ p := mem_singleton_iff.mp hz
      subst z
      change Real.pi - δ/2 < comparisonAngleNegCurvature 1 (dist (σ p) (a 0))
        (dist (σ p) (b 0)) (dist (a 0) (b 0))
      rw [hang]
      linarith
    · intro z hz i j hij
      exact False.elim (hij (Subsingleton.elim _ _))
  have hne := hp.not_mem_anchors (mem_singleton _) (show δ/2 < Real.pi/2 by
    dsimp [δ]; linarith [two_le_pi])
  obtain ⟨V, hVo, hpV, _, hpacket, a₀, A, ha₀, _, hbounds⟩ :=
    hp.exists_uniform_nhds hδ hne (Filter.univ_mem : (univ : Set X) ∈ 𝓝 (σ p))
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.mp hVo (σ p) hpV
  let ε : ℝ := (β / (100 * Real.pi)) ^ 2
  let K : ℝ := 4 * cosh (A + 1) / sinh a₀
  let r : ℝ := min (R/4) (min (1/4) (min (a₀/8) (ε/(4*K))))
  have hK : 0 < K := div_pos (by positivity) (sinh_pos_iff.mpr ha₀)
  have hε : 0 < ε := by dsimp [ε, β]; positivity
  have hr : 0 < r := lt_min (by positivity) (lt_min (by norm_num)
    (lt_min (by positivity) (div_pos hε (by positivity))))
  have hrR : r ≤ R/4 := min_le_left _ _
  have hr1 : r ≤ 1/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hra : r ≤ a₀/8 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrε : r ≤ ε/(4*K) := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hrK : 2*r ≤ ε/K := by
    have h := (le_div_iff₀ (show 0 < 4*K by positivity)).mp hrε
    apply (le_div_iff₀ hK).mpr
    nlinarith [mul_pos hK hr]
  obtain ⟨U, _, e, he, _, _, _⟩ := hpacket.exists_chart_of_rank_exclusion
    hcurves (hcomp.of_zero (by norm_num)) (subset_univ _) (subset_univ _)
    ha₀ (β := β) (q := σ p) (r := r) (by norm_num [β]) (by norm_num [β])
    hδ (by norm_num [δ, β]) hbounds (fun z _ => hcomplete z)
    (fun z _ c d _ => not_pairedComparisonPacket_of_dimH_le_one hcurves hcomp hcomplete
      hdim (by norm_num) z c d)
    hr ((ball_subset_ball (show 3*r ≤ R by linarith)).trans hRV)
    (by linarith) (by linarith) hrK
  refine ⟨r, hr, ?_⟩
  intro x hx y hy hxy
  have hF : distanceCoordinates 2 a x = distanceCoordinates 2 a y := by
    apply WithLp.ofLp_injective 2
    funext i
    change dist x (σ ⟨l, le_rfl, hlu⟩) = dist y (σ ⟨l, le_rfl, hlu⟩)
    simpa only [dist_comm] using hxy
  have heq : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
    apply Subtype.ext
    rw [he, he]
    exact hF
  exact congrArg Subtype.val (e.injective heq)

theorem isOpen_segment_image_of_dimH_le_one
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hcomplete : ∀ z : X, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    (hdim : dimH (univ : Set X) ≤ 1)
    (l u : ℝ) (σ : Icc l u → X) (hσ : Isometry σ) :
    IsOpen (σ '' {t | l < (t : ℝ) ∧ (t : ℝ) < u}) := by
  by_cases hlu : l ≤ u
  · exact isOpen_segment_image_of_locally_injOn_dist hlu hσ
      (fun p hlp hpu => exists_injOn_dist_ball_at_segment_interior_of_dimH_le_one
        hcurves hcomp hcomplete hdim hlu hσ p hlp hpu)
  · have hempty : {t : Icc l u | l < (t : ℝ) ∧ (t : ℝ) < u} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t _
      exact hlu (t.property.1.trans t.property.2)
    rw [hempty, image_empty]
    exact isOpen_empty

end DifferentialGeometry.Geometry.Comparison.Toponogov
