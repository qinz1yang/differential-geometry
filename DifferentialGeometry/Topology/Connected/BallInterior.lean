import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.LocallyConvex.WithSeminorms

section

noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joinedIn_ball_inter_of_isPreconnected_closedBall_inter
    {R : ℝ} (hR : 0 < R) {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected (closedBall (0 : E) R ∩ U))
    {x y : E} (hx : x ∈ ball (0 : E) R ∩ U) (hy : y ∈ ball (0 : E) R ∩ U) :
    JoinedIn (ball (0 : E) R ∩ U) x y := by
  let D := closedBall (0 : E) R
  let : LocallyPathConnectedSpace D := (convex_closedBall (0 : E) R).locallyPathConnectedSpace
  let S : Set D := Subtype.val ⁻¹' U
  have hS : IsOpen S := hU.preimage continuous_subtype_val
  have himage : Subtype.val '' S = closedBall (0 : E) R ∩ U := by
    ext z
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hzD, hzU⟩
      exact ⟨⟨z, hzD⟩, hzU, rfl⟩
  have hSc : IsPreconnected S :=
    Topology.IsInducing.subtypeVal.isPreconnected_image.mp (himage.symm ▸ hconn)
  let xD : D := ⟨x, ball_subset_closedBall hx.1⟩
  let yD : D := ⟨y, ball_subset_closedBall hy.1⟩
  have hpath := hS.isConnected_iff_isPathConnected.mp ⟨⟨xD, hx.2⟩, hSc⟩
  obtain ⟨γ, hγ⟩ := hpath.joinedIn xD hx.2 yD hy.2
  let γE : Path x y := γ.map continuous_subtype_val
  have hγD (t : unitInterval) : γE t ∈ closedBall (0 : E) R := (γ t).property
  have hγU (t : unitInterval) : γE t ∈ U := hγ t
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_range γE.continuous).exists_thickening_subset_open
    hU (range_subset_iff.mpr hγU)
  let θ := min (1 / 2 : ℝ) (δ / (2 * R))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hθhalf : θ ≤ 1 / 2 := min_le_left _ _
  have hθδ : θ * R < δ := by
    have hle : θ ≤ δ / (2 * R) := min_le_right _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * R)).mp hle
    nlinarith
  let kappa := 1 - θ
  have hkappa : 0 < kappa := by dsimp only [kappa]; linarith
  have hkappa1 : kappa < 1 := by dsimp only [kappa]; linarith
  have hdist (z : E) (hz : z ∈ closedBall (0 : E) R) : dist (kappa • z) z < δ := by
    rw [dist_eq_norm, show kappa • z - z = (kappa - 1) • z by
      simp only [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
    have habs : |kappa - 1| = θ := by rw [abs_of_neg (by linarith)]; dsimp only [kappa]; ring
    rw [habs]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hθ.le).trans_lt hθδ
  have hshrink (z : E) (hz : z ∈ closedBall (0 : E) R) : kappa • z ∈ ball (0 : E) R := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hkappa]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hkappa.le).trans_lt
      (by nlinarith)
  have hkappaU (t : unitInterval) : kappa • γE t ∈ U :=
    hthick ((ball_subset_thickening (show γE t ∈ range γE from ⟨t, rfl⟩) δ) (hdist _ (hγD t)))
  have hkappapath : JoinedIn (ball (0 : E) R ∩ U) (kappa • x) (kappa • y) := by
    refine ⟨γE.map (continuous_const.smul continuous_id), ?_⟩
    intro t
    exact ⟨hshrink _ (hγD t), hkappaU t⟩
  have hjoin (z : E) (hz : z ∈ ball (0 : E) R ∩ U) (hzrange : z ∈ range γE) :
      JoinedIn (ball (0 : E) R ∩ U) z (kappa • z) := by
    apply JoinedIn.of_segment_subset
    exact subset_inter
      ((convex_ball (0 : E) R).segment_subset hz.1 (hshrink z (ball_subset_closedBall hz.1)))
      (((convex_ball z δ).segment_subset (mem_ball_self hδ)
        (hdist z (ball_subset_closedBall hz.1))).trans
          ((ball_subset_thickening hzrange δ).trans hthick))
  exact (hjoin x hx ⟨0, γE.source⟩).trans
    (hkappapath.trans (hjoin y hy ⟨1, γE.target⟩).symm)

theorem isPreconnected_ball_inter_of_isPreconnected_closedBall_inter
    {R : ℝ} (hR : 0 < R) {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected (closedBall (0 : E) R ∩ U)) :
    IsPreconnected (ball (0 : E) R ∩ U) := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  obtain ⟨γ, hγ⟩ := joinedIn_ball_inter_of_isPreconnected_closedBall_inter hR hU hconn hx hy
  exact ⟨range γ, range_subset_iff.mpr hγ, ⟨0, γ.source⟩, ⟨1, γ.target⟩,
    (isConnected_range γ.continuous).isPreconnected⟩


end DifferentialGeometry.Topology

open DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ContinuousOn.isPreconnected_ball_gt_of_closedBall
    {R : ℝ} (hR : 0 < R) {f : E → ℝ}
    (hf : ContinuousOn f (closedBall (0 : E) R)) {a : ℝ}
    (hconn : IsPreconnected (closedBall (0 : E) R ∩ {x | a < f x})) :
    IsPreconnected (ball (0 : E) R ∩ {x | a < f x}) := by
  let D := closedBall (0 : E) R
  have hopen : IsOpen {x : D | a < f x} :=
    isOpen_lt continuous_const (hf.domRestrict)
  obtain ⟨U, hU, hUS⟩ := _root_.Topology.IsInducing.subtypeVal.isOpen_iff.mp hopen
  have heq (x : E) (hx : x ∈ closedBall (0 : E) R) : x ∈ U ↔ a < f x := by
    exact Set.ext_iff.mp hUS ⟨x, hx⟩
  have hc : closedBall (0 : E) R ∩ U = closedBall (0 : E) R ∩ {x | a < f x} := by
    ext x
    exact and_congr_right (heq x)
  have ho : ball (0 : E) R ∩ U = ball (0 : E) R ∩ {x | a < f x} := by
    ext x
    exact and_congr_right (fun hx => heq x (ball_subset_closedBall hx))
  rw [← ho]
  exact isPreconnected_ball_inter_of_isPreconnected_closedBall_inter hR hU (hc.symm ▸ hconn)

theorem ContinuousOn.isPreconnected_ball_lt_of_closedBall
    {R : ℝ} (hR : 0 < R) {f : E → ℝ}
    (hf : ContinuousOn f (closedBall (0 : E) R)) {a : ℝ}
    (hconn : IsPreconnected (closedBall (0 : E) R ∩ {x | f x < a})) :
    IsPreconnected (ball (0 : E) R ∩ {x | f x < a}) := by
  have h := hf.neg.isPreconnected_ball_gt_of_closedBall hR (a := -a)
  simpa only [Pi.neg_apply, neg_lt_neg_iff] using
    h (by simpa only [Pi.neg_apply, neg_lt_neg_iff] using hconn)

end

end
