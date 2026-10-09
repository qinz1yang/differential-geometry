/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.Topology

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.HyperbolicGeometry

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.Hyperbolic.HUpper
open DifferentialGeometry.HyperbolicAction
open DifferentialGeometry.HyperbolicFaithful
open DifferentialGeometry.HyperbolicBoundary
open DifferentialGeometry.BoundaryTopology

variable {n : ℕ}

section GeodesicRays

theorem lorB_spatialEmbed_spatial (ξ : BoundaryH n) :
    lorB (spatialEmbed (spatial ξ)) (spatialEmbed (spatial ξ)) = 1 := by
  have hsd : sdot (spatialEmbed (spatial ξ)) (spatialEmbed (spatial ξ)) = 1 := by
    rw [sdot_spatialEmbed]
    have h2 : ∀ i : Fin n, (spatial ξ : EuclideanSpace ℝ (Fin n)) i * (spatial ξ) i
        = ξ.val (Sum.inl i) * ξ.val (Sum.inl i) := fun i => by rw [spatial_apply]
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    exact sdot_self_of_boundary ξ
  change sdot (spatialEmbed (spatial ξ)) (spatialEmbed (spatial ξ))
      - tc (spatialEmbed (spatial ξ)) * tc (spatialEmbed (spatial ξ)) = 1
  rw [hsd, tc_spatialEmbed]
  norm_num

theorem lorB_geodesicRay_geodesicRay (ξ : BoundaryH n) (t s : ℝ) :
    lorB ((geodesicRay ξ t).val) ((geodesicRay ξ s).val) = - Real.cosh (t - s) := by
  change lorB (Real.cosh t • (eTime : LorVec n) + Real.sinh t • spatialEmbed (spatial ξ))
      (Real.cosh s • (eTime : LorVec n) + Real.sinh s • spatialEmbed (spatial ξ)) = _
  set u : LorVec n := spatialEmbed (spatial ξ) with hudef
  have heu : lorB (eTime : LorVec n) u = 0 := by
    rw [hudef]
    change sdot (eTime : LorVec n) (spatialEmbed (spatial ξ))
        - tc (eTime : LorVec n) * tc (spatialEmbed (spatial ξ)) = 0
    rw [sdot_eTime_spatialEmbed, tc_eTime, tc_spatialEmbed]
    norm_num
  have hue : lorB u (eTime : LorVec n) = 0 := by rw [lorB_comm]; exact heu
  have huu : lorB u u = 1 := by rw [hudef]; exact lorB_spatialEmbed_spatial ξ
  rw [lorB_add_left, lorB_add_right, lorB_add_right,
    lorB_smul_left, lorB_smul_right, lorB_eTime,
    lorB_smul_left, lorB_smul_right, heu,
    lorB_smul_left, lorB_smul_right, hue,
    lorB_smul_left, lorB_smul_right, huu, Real.cosh_sub]
  ring

theorem dist_geodesicRay (ξ : BoundaryH n) (t s : ℝ) :
    dist (geodesicRay ξ t) (geodesicRay ξ s) = |t - s| := by
  change HUpper.hdist (geodesicRay ξ t) (geodesicRay ξ s) = |t - s|
  unfold HUpper.hdist
  rw [lorB_geodesicRay_geodesicRay, neg_neg]
  rcases le_or_gt 0 (t - s) with hts | hts
  · rw [abs_of_nonneg hts]
    exact Real.arcosh_cosh hts
  · have h2 : (0 : ℝ) ≤ s - t := by linarith
    rw [abs_of_neg hts, ← Real.cosh_neg (t - s), neg_sub]
    exact Real.arcosh_cosh h2

theorem isometry_geodesicRay (ξ : BoundaryH n) : Isometry (geodesicRay ξ) := by
  intro t s
  rw [edist_dist, edist_dist, dist_geodesicRay, Real.dist_eq]

theorem lipschitzWith_geodesicRay (ξ : BoundaryH n) :
    LipschitzWith 1 (geodesicRay ξ) := by
  intro t s
  rw [edist_dist, edist_dist, dist_geodesicRay, Real.dist_eq, ENNReal.coe_one, one_mul]

theorem continuous_geodesicRay (ξ : BoundaryH n) : Continuous (geodesicRay ξ) :=
  (lipschitzWith_geodesicRay ξ).continuous

theorem geodesicRay_zero (ξ : BoundaryH n) : geodesicRay ξ 0 = basepointH := by
  apply HUpper.ext
  change Real.cosh 0 • eTime + Real.sinh 0 • spatialEmbed (spatial ξ) = eTime
  rw [Real.cosh_zero, Real.sinh_zero, zero_smul, add_zero, one_smul]

theorem dist_basepoint_geodesicRay (ξ : BoundaryH n) (t : ℝ) :
    dist basepointH (geodesicRay ξ t) = |t| := by
  rw [← geodesicRay_zero, dist_geodesicRay, zero_sub, abs_neg]

end GeodesicRays

section Properness

theorem tc_le_neg_lorB_mul (x y : HUpper n) :
    tc y.val ≤ (- lorB x.val y.val) * (tc x.val + Real.sqrt (sdot x.val x.val)) := by
  set sx := sdot x.val x.val with hsxd
  have hsx : 0 ≤ sx := sdot_self_nonneg _
  have htx : 0 < tc x.val := x.future
  have hty : 0 < tc y.val := y.future
  have hx2 : tc x.val ^ 2 = 1 + sx := tc_sq x
  have hy2 : tc y.val ^ 2 = 1 + sdot y.val y.val := tc_sq y
  have hsy_le : Real.sqrt (sdot y.val y.val) ≤ tc y.val := by
    have h1 : sdot y.val y.val ≤ tc y.val ^ 2 := by linarith
    calc Real.sqrt (sdot y.val y.val) ≤ Real.sqrt (tc y.val ^ 2) := Real.sqrt_le_sqrt h1
      _ = tc y.val := Real.sqrt_sq (le_of_lt hty)
  have hdiff_pos : (0 : ℝ) < tc x.val - Real.sqrt sx := by
    have h1 : Real.sqrt sx < tc x.val := by
      have hsx2 : sx < tc x.val ^ 2 := by linarith
      calc Real.sqrt sx < Real.sqrt (tc x.val ^ 2) := Real.sqrt_lt_sqrt hsx hsx2
        _ = tc x.val := Real.sqrt_sq (le_of_lt htx)
    linarith
  have hconj : (tc x.val - Real.sqrt sx) * (tc x.val + Real.sqrt sx) = 1 := by
    have hsq : (Real.sqrt sx) ^ 2 = sx := Real.sq_sqrt hsx
    nlinarith [hx2, hsq]
  have hlow : tc y.val * (tc x.val - Real.sqrt sx) ≤ - lorB x.val y.val := by
    have hsd : sdot x.val y.val ≤ Real.sqrt sx * tc y.val :=
      (le_abs_self _).trans <|
        (abs_sdot_le _ _).trans <|
          mul_le_mul_of_nonneg_left hsy_le (Real.sqrt_nonneg _)
    have heq : - lorB x.val y.val = tc x.val * tc y.val - sdot x.val y.val := by
      simp only [lorB]; ring
    rw [heq]
    nlinarith [hsd, Real.sqrt_nonneg sx, hty]
  have key := mul_le_mul_of_nonneg_right hlow
    (le_of_lt (add_pos_of_pos_of_nonneg htx (Real.sqrt_nonneg sx)))
  have e : tc y.val * (tc x.val - Real.sqrt sx) * (tc x.val + Real.sqrt sx) = tc y.val := by
    rw [mul_assoc, hconj, mul_one]
  rwa [e] at key

theorem tc_le_of_lorB (x : HUpper n) {v : LorVec n} (hv1 : lorB v v = -1)
    (hv2 : 0 < tc v) :
    tc v ≤ (- lorB x.val v) * (tc x.val + Real.sqrt (sdot x.val x.val)) :=
  tc_le_neg_lorB_mul x ⟨v, hv1, hv2⟩

theorem abs_inl_le_tc (y : HUpper n) (i : Fin n) : |y.val (Sum.inl i)| ≤ tc y.val := by
  have hty : 0 < tc y.val := y.future
  have hs : (y.val (Sum.inl i)) ^ 2 ≤ tc y.val ^ 2 := by
    have hsum : (y.val (Sum.inl i)) ^ 2 ≤ ∑ j : Fin n, (y.val (Sum.inl j)) ^ 2 :=
      Finset.single_le_sum (f := fun j => (y.val (Sum.inl j)) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have heq : (∑ j : Fin n, (y.val (Sum.inl j)) ^ 2) = sdot y.val y.val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_two]
    have hy2 : tc y.val ^ 2 = 1 + sdot y.val y.val := tc_sq y
    linarith
  exact abs_le_of_sq_le_sq hs (le_of_lt hty)

theorem abs_inl_le_of_lorB {v : LorVec n} (hv1 : lorB v v = -1) (hv2 : 0 < tc v)
    (i : Fin n) : |v (Sum.inl i)| ≤ tc v :=
  abs_inl_le_tc ⟨v, hv1, hv2⟩ i

theorem one_le_neg_lorB_of_lorB (x : HUpper n) {v : LorVec n} (hv1 : lorB v v = -1)
    (hv2 : 0 < tc v) : 1 ≤ - lorB x.val v :=
  one_le_neg_lorB x ⟨v, hv1, hv2⟩

theorem dist_le_iff {x y : HUpper n} {r : ℝ} (hr : 0 ≤ r) :
    dist x y ≤ r ↔ - lorB x.val y.val ≤ Real.cosh r := by
  have h1 : 1 ≤ - lorB x.val y.val := one_le_neg_lorB x y
  change HUpper.hdist x y ≤ r ↔ _
  unfold HUpper.hdist
  constructor
  · intro h
    have hmono : Real.cosh (Real.arcosh (- lorB x.val y.val)) ≤ Real.cosh r := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (Real.arcosh_nonneg h1), abs_of_nonneg hr]
      exact h
    rwa [Real.cosh_arcosh h1] at hmono
  · intro h
    have h2 : Real.arcosh (- lorB x.val y.val) ≤ Real.arcosh (Real.cosh r) :=
      (Real.arcosh_le_arcosh (by linarith)
        (by linarith [Real.one_le_cosh r])).mpr h
    rwa [Real.arcosh_cosh hr] at h2

noncomputable def ofLorVec (v : LorVec n) : HUpper n :=
  if h : lorB v v = -1 ∧ 1 ≤ tc v then ⟨v, h.1, lt_of_lt_of_le one_pos h.2⟩ else basepointH

theorem ofLorVec_val (x : HUpper n) : ofLorVec x.val = x := by
  unfold ofLorVec
  rw [dite_eq_left ⟨x.is_unit, one_le_tc x⟩]

theorem val_ofLorVec {v : LorVec n} (h : lorB v v = -1 ∧ 1 ≤ tc v) :
    (ofLorVec v).val = v := by
  unfold ofLorVec
  rw [dite_eq_left h]

def boundingSet (x : HUpper n) (r : ℝ) : Set (LorVec n) :=
  {v | lorB v v = -1 ∧ 1 ≤ tc v ∧ - lorB x.val v ≤ Real.cosh r}

theorem continuous_lorB_self : Continuous fun v : LorVec n => lorB v v := by
  change Continuous fun v : LorVec n =>
    (∑ i : Fin n, v (Sum.inl i) * v (Sum.inl i)) - v (Sum.inr 0) * v (Sum.inr 0)
  fun_prop

theorem continuous_neg_lorB_left (x : HUpper n) :
    Continuous fun v : LorVec n => - lorB x.val v := by
  change Continuous fun v : LorVec n =>
    - ((∑ i : Fin n, x.val (Sum.inl i) * v (Sum.inl i)) - tc x.val * v (Sum.inr 0))
  fun_prop

theorem continuous_neg_lorB_right (v₀ : LorVec n) :
    Continuous fun w : LorVec n => - lorB w v₀ := by
  change Continuous fun w : LorVec n =>
    - ((∑ i : Fin n, w (Sum.inl i) * v₀ (Sum.inl i)) - w (Sum.inr 0) * v₀ (Sum.inr 0))
  fun_prop

theorem isClosed_boundingSet (x : HUpper n) (r : ℝ) : IsClosed (boundingSet x r) := by
  have h1 : IsClosed {v : LorVec n | lorB v v = -1} :=
    isClosed_singleton.preimage continuous_lorB_self
  have h2 : IsClosed {v : LorVec n | 1 ≤ tc v} :=
    isClosed_Ici.preimage (continuous_apply (Sum.inr 0))
  have h3 : IsClosed {v : LorVec n | - lorB x.val v ≤ Real.cosh r} :=
    isClosed_Iic.preimage (continuous_neg_lorB_left x)
  have heq : {v : LorVec n | lorB v v = -1 ∧ 1 ≤ tc v ∧ - lorB x.val v ≤ Real.cosh r}
      = ({v | lorB v v = -1} ∩ {v | 1 ≤ tc v}) ∩ {v | - lorB x.val v ≤ Real.cosh r} := by
    ext v
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
  change IsClosed {v : LorVec n | lorB v v = -1 ∧ 1 ≤ tc v ∧ - lorB x.val v ≤ Real.cosh r}
  rw [heq]
  exact (h1.inter h2).inter h3

theorem isBounded_boundingSet (x : HUpper n) (r : ℝ) :
    Bornology.IsBounded (boundingSet x r) := by
  set B : ℝ := Real.cosh r * (tc x.val + Real.sqrt (sdot x.val x.val)) with hBd
  have hBnn : 0 ≤ B := by
    rw [hBd]
    exact mul_nonneg (by linarith [Real.one_le_cosh r])
      (add_nonneg (le_of_lt x.future) (Real.sqrt_nonneg _))
  refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : LorVec n)) (r := B))
    ?_
  intro v hv
  have htv : 0 < tc v := lt_of_lt_of_le one_pos hv.2.1
  have htcB : tc v ≤ B := by
    have h1 : tc v ≤ (- lorB x.val v) * (tc x.val + Real.sqrt (sdot x.val x.val)) :=
      tc_le_of_lorB x hv.1 htv
    have h2 : (- lorB x.val v) * (tc x.val + Real.sqrt (sdot x.val x.val)) ≤ B := by
      rw [hBd]
      exact mul_le_mul_of_nonneg_right hv.2.2
        (add_nonneg (le_of_lt x.future) (Real.sqrt_nonneg _))
    exact h1.trans h2
  rw [Metric.mem_closedBall, dist_pi_le_iff hBnn]
  intro a
  rcases a with i | k
  · rw [Pi.zero_apply, dist_zero_right, Real.norm_eq_abs]
    exact (abs_inl_le_of_lorB hv.1 htv i).trans htcB
  · rw [Pi.zero_apply, dist_zero_right, Real.norm_eq_abs, Fin.eq_zero k]
    change |tc v| ≤ B
    rw [abs_of_pos htv]
    exact htcB

theorem isCompact_boundingSet (x : HUpper n) (r : ℝ) : IsCompact (boundingSet x r) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_boundingSet x r) (isBounded_boundingSet x r)

theorem continuousOn_ofLorVec (x : HUpper n) (r : ℝ) :
    ContinuousOn ofLorVec (boundingSet x r) := by
  intro v₀ hv₀
  have hv₀val : (ofLorVec v₀).val = v₀ := val_ofLorVec ⟨hv₀.1, hv₀.2.1⟩
  change Filter.Tendsto ofLorVec (nhdsWithin v₀ (boundingSet x r)) (nhds (ofLorVec v₀))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hg : Filter.Tendsto (fun w : LorVec n => - lorB w v₀)
      (nhdsWithin v₀ (boundingSet x r)) (nhdsWithin (- lorB v₀ v₀) (Set.Ici 1)) :=
    (continuous_neg_lorB_right v₀).continuousWithinAt.tendsto_nhdsWithin
      (fun w hw => Set.mem_Ici.mpr
        (one_le_neg_lorB_of_lorB ⟨w, hw.1, lt_of_lt_of_le one_pos hw.2.1⟩ hv₀.1
          (lt_of_lt_of_le one_pos hv₀.2.1)))
  have hac : Filter.Tendsto Real.arcosh (nhdsWithin (- lorB v₀ v₀) (Set.Ici 1))
      (nhds (Real.arcosh (- lorB v₀ v₀))) :=
    Real.continuousOn_arcosh _ (Set.mem_Ici.mpr (by rw [hv₀.1]; norm_num))
  have hcomp : Filter.Tendsto (fun w : LorVec n => Real.arcosh (- lorB w v₀))
      (nhdsWithin v₀ (boundingSet x r)) (nhds (Real.arcosh (- lorB v₀ v₀))) :=
    hac.comp hg
  have h0 : Real.arcosh (- lorB v₀ v₀) = 0 := by rw [hv₀.1, neg_neg, Real.arcosh_zero]
  have hIio : Set.Iio ε ∈ nhds (Real.arcosh (- lorB v₀ v₀)) := by
    rw [h0]
    exact Iio_mem_nhds hε
  have hev := hcomp.eventually hIio
  filter_upwards [hev, self_mem_nhdsWithin] with w hwlt hwS
  have hwval : (ofLorVec w).val = w := val_ofLorVec ⟨hwS.1, hwS.2.1⟩
  change dist (ofLorVec w) (ofLorVec v₀) < ε
  change HUpper.hdist (ofLorVec w) (ofLorVec v₀) < ε
  unfold HUpper.hdist
  rw [hwval, hv₀val]
  exact hwlt

theorem closedBall_eq_image_ofLorVec (x : HUpper n) {r : ℝ} (hr : 0 ≤ r) :
    Metric.closedBall x r = ofLorVec '' boundingSet x r := by
  ext y
  constructor
  · intro hy
    rw [Metric.mem_closedBall, dist_comm y x, dist_le_iff hr] at hy
    exact ⟨y.val, ⟨y.is_unit, one_le_tc y, hy⟩, ofLorVec_val y⟩
  · rintro ⟨v, hv, rfl⟩
    rw [Metric.mem_closedBall, dist_comm (ofLorVec v) x, dist_le_iff hr,
      val_ofLorVec ⟨hv.1, hv.2.1⟩]
    exact hv.2.2

instance properSpaceHUpper : ProperSpace (HUpper n) where
  isCompact_closedBall x r := by
    rcases le_or_gt 0 r with hr | hr
    · rw [closedBall_eq_image_ofLorVec x hr]
      exact (isCompact_boundingSet x r).image_of_continuousOn (continuousOn_ofLorVec x r)
    · rw [Metric.closedBall_eq_empty.mpr hr]
      exact isCompact_empty

end Properness

end DifferentialGeometry.HyperbolicGeometry
