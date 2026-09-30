import DifferentialGeometry.Geometry.Metric.FiniteGeodesicDirections
import DifferentialGeometry.Geometry.Metric.TangentCone
import DifferentialGeometry.Geometry.Metric.Approximation.PairedNets
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale

set_option autoImplicit false

open Set Metric Filter Topology
open scoped NNReal

namespace Metric

open GC.MetricGeometry

theorem eventually_pointedBallApprox_tangent_of_local_radial_control
    {X : Type*} [m : MetricSpace X] (q : X) [HasAnglesAt q]
    [CompactSpace (SpaceOfDirections q)] {A C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hreach : ∀ x : X, dist x q < A → x ≠ q →
      ∃ σ : GeodesicRepresentative q, dist q x ≤ σ.length ∧ σ.path (dist q x) = x)
    (hradial : ∀ σ τ : GeodesicRepresentative q, ∀ r : ℝ, 0 < r →
      r ≤ σ.length → r ≤ τ.length → r ≤ A →
      dist (σ.path r) (τ.path r) ≤ C * r * dist σ.direction τ.direction)
    {B ε : ℝ} (hε : 0 < ε) (hεB : ε < B) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∃ ht : 0 < t,
      Nonempty (@PointedBallApprox X (TangentCone q)
        (m.rescale t⁻¹ (inv_pos.mpr ht)) inferInstance q EuclideanCone.tip B ε) := by
  classical
  let Y := TangentCone q
  let coneMetric : MetricSpace Y := inferInstance
  have hB : 0 < B := hε.trans hεB
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  let δ := η / (4 * (C + 1) * (B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨F, S, hS, hlength, hnet⟩ := exists_finite_representative_net_with_common_length q hδ
  obtain ⟨T, hT, hTnet⟩ := exists_finset_net_of_isCompact
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) B)) (show 0 < η / 4 by positivity)
  let L := Option (F × T)
  let x : ℝ → L → X := fun t l => match l with
    | none => q
    | some v => v.1.val.path (v.2.val * t)
  let y : L → TangentCone q := fun l => match l with
    | none => EuclideanCone.tip
    | some v => v.1.val.tangentVector (NNReal.mk v.2.val (hT v.2.val v.2.property).1)
  have hscalar1 : C * B * δ ≤ η / 4 := by
    have hden : 0 < 4 * (C + 1) * (B + 1) := by positivity
    have hid : δ * (4 * (C + 1) * (B + 1)) = η := div_mul_cancel₀ _ hden.ne'
    have hp : C * B ≤ (C + 1) * (B + 1) := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hp hδ.le
    nlinarith
  have hscalar2 : B * δ ≤ η / 4 := by
    have hden : 0 < 4 * (C + 1) * (B + 1) := by positivity
    have hid : δ * (4 * (C + 1) * (B + 1)) = η := div_mul_cancel₀ _ hden.ne'
    have hp : B ≤ (C + 1) * (B + 1) := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hp hδ.le
    nlinarith
  have htarget (v : TangentCone q) (hv : dist v EuclideanCone.tip ≤ B) :
      ∃ l : L, dist v (y l) ≤ η := by
    rcases EuclideanCone.eq_tip_or_eq_mk v with rfl | ⟨r, u, hr, rfl⟩
    · exact ⟨none, by simpa [y] using hη.le⟩
    have hrB : (r : ℝ) ≤ B := by simpa only [EuclideanCone.dist_tip, EuclideanCone.radius_mk] using hv
    obtain ⟨σ, hσ, hu⟩ := hnet u
    obtain ⟨s, hs, hrs⟩ := hTnet (r : ℝ) ⟨r.property, hrB⟩
    refine ⟨some (⟨σ, hσ⟩, ⟨s, hs⟩), ?_⟩
    change dist (EuclideanCone.mk r u) (σ.tangentVector (NNReal.mk s (hT s hs).1)) ≤ η
    rw [GeodesicRepresentative.tangentVector, EuclideanCone.dist_mk]
    have hc := coneDistance_le_abs_sub_add_mul_dist (Y := SpaceOfDirections q)
      (x := ((r : ℝ), u)) (y := (s, σ.direction)) ⟨r.property, hrB⟩ (hT s hs)
    have hu' := mul_le_mul_of_nonneg_left hu.le hB.le
    have hrs' : |(r : ℝ) - s| ≤ η / 4 := hrs
    change coneDistance ((r : ℝ), u) (s, σ.direction) ≤ η
    linarith
  have hsource {t : ℝ} (ht : 0 < t) (htA : t * B < A) (htS : t * B ≤ S)
      (u : X) (hu : dist u q ≤ t * B) : ∃ l : L, dist u (x t l) / t ≤ η := by
    by_cases huq : u = q
    · subst u
      exact ⟨none, by simpa [x] using hη.le⟩
    obtain ⟨σ, hσlength, hσend⟩ := hreach u (hu.trans_lt htA) huq
    have ha : 0 < dist q u := dist_pos.mpr (Ne.symm huq)
    obtain ⟨τ, hτ, hang⟩ := hnet σ.direction
    have hrad := hradial σ τ (dist q u) ha hσlength
      (by rw [dist_comm]; exact hu.trans (htS.trans (hlength τ hτ)))
      (by rw [dist_comm]; exact hu.trans htA.le)
    rw [hσend] at hrad
    have hru : dist q u / t ∈ Icc (0 : ℝ) B := by
      refine ⟨div_nonneg dist_nonneg ht.le, (div_le_iff₀ ht).mpr ?_⟩
      simpa only [dist_comm q u, mul_comm B t] using hu
    obtain ⟨s, hs, hrs⟩ := hTnet (dist q u / t) hru
    have haτ : dist q u ≤ τ.length := by
      rw [dist_comm]; exact hu.trans (htS.trans (hlength τ hτ))
    have hsτ : s * t ≤ τ.length :=
      (mul_le_mul_of_nonneg_right (hT s hs).2 ht.le).trans (by nlinarith [hlength τ hτ])
    have hseg := τ.dist_path ⟨dist_nonneg, haτ⟩ ⟨mul_nonneg (hT s hs).1 ht.le, hsτ⟩
    have hdiff : |dist q u - s * t| = t * |dist q u / t - s| := by
      have heq : dist q u - s * t = t * (dist q u / t - s) := by
        field_simp
      rw [heq, abs_mul, abs_of_pos ht]
    rw [hdiff] at hseg
    have htri := dist_triangle u (τ.path (dist q u)) (τ.path (s * t))
    rw [hseg] at htri
    have hangle := mul_le_mul_of_nonneg_left hang.le (show 0 ≤ C * dist q u by positivity)
    have hsmall : C * dist q u * δ ≤ C * (t * B) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [dist_comm q u] using hu
    have hcoef := mul_le_mul_of_nonneg_left hscalar1 ht.le
    have hmesh := mul_le_mul_of_nonneg_left hrs ht.le
    refine ⟨some (⟨τ, hτ⟩, ⟨s, hs⟩), (div_le_iff₀ ht).mpr ?_⟩
    change dist u (τ.path (s * t)) ≤ η * t
    change t * |dist q u / t - s| ≤ t * (η / 4) at hmesh
    nlinarith
  have hpair (a b : L) :
      Tendsto (fun t : ℝ => dist (x t a) (x t b) / t) (𝓝[>] (0 : ℝ)) (𝓝 (dist (y a) (y b))) := by
    cases a with
    | none =>
      cases b with
      | none => simp [x, y]
      | some b =>
        have h := b.1.val.dist_div_tendsto_tangentVector b.1.val 0 (NNReal.mk b.2.val (hT b.2.val b.2.property).1)
        simpa only [x, y, NNReal.coe_mk, NNReal.coe_zero, zero_mul, GeodesicRepresentative.path_zero,
          GeodesicRepresentative.tangentVector, EuclideanCone.mk_zero] using h
    | some a =>
      cases b with
      | none =>
        have h := a.1.val.dist_div_tendsto_tangentVector a.1.val (NNReal.mk a.2.val (hT a.2.val a.2.property).1) 0
        simpa only [x, y, NNReal.coe_mk, NNReal.coe_zero, zero_mul, GeodesicRepresentative.path_zero,
          GeodesicRepresentative.tangentVector, EuclideanCone.mk_zero] using h
      | some b =>
        exact a.1.val.dist_div_tendsto_tangentVector b.1.val
          (NNReal.mk a.2.val (hT a.2.val a.2.property).1)
          (NNReal.mk b.2.val (hT b.2.val b.2.property).1)
  have hpairs : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ a b : L,
      |dist (y a) (y b) - dist (x t a) (x t b) / t| < η := by
    apply eventually_all.mpr
    intro a
    apply eventually_all.mpr
    intro b
    simpa only [Real.dist_eq, abs_sub_comm] using (Metric.tendsto_nhds.mp (hpair a b)) η hη
  have hdom : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t ∧ t * B < A ∧ t * B ≤ S := by
    have hb : Tendsto (fun t : ℝ => t * B) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using hid.mul_const B
    filter_upwards [self_mem_nhdsWithin, hb.eventually (gt_mem_nhds hA), hb.eventually (gt_mem_nhds hS)] with t ht ha hs
    exact ⟨ht, ha, hs.le⟩
  filter_upwards [hdom, hpairs] with t ht hmatrix
  refine ⟨ht.1, ?_⟩
  let mt := m.rescale t⁻¹ (inv_pos.mpr ht.1)
  have hd (u v : X) : @dist X mt.toDist u v = @dist X m.toDist u v / t := by
    change t⁻¹ * @dist X m.toDist u v = @dist X m.toDist u v / t
    rw [div_eq_mul_inv, mul_comm]
  refine ⟨@PointedBallApprox.ofPairedNets X Y L mt coneMetric q (y none) B ε η
    (x t) y none rfl rfl hη hεB (by dsimp [η]; linarith) ?_ ?_ ?_⟩
  · intro u
    have hu : @dist X m.toDist u.val q ≤ t * B := by
      have hh := u.property
      rw [hd, div_le_iff₀ ht.1] at hh
      nlinarith
    obtain ⟨a, ha⟩ := hsource ht.1 ht.2.1 ht.2.2 u.val hu
    exact ⟨a, by rwa [hd]⟩
  · intro v hv
    exact htarget v (by linarith)
  · intro a b
    rw [hd]
    exact hmatrix a b

end Metric
