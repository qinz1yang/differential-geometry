import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Defs
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Collar

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

namespace BallChart

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] (c d : BallChart n I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))

def firstRadialMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (r : ℝ) (hr : r ∈ Icc 1 2) : c.DoublePunctured d :=
  ⟨(c.radialMap z r hr).val, by
    rintro (hc | hd)
    · exact (c.radialMap z r hr).property hc
    · exact Set.disjoint_left.mp hdisj
        ⟨r • z.val, by
          rw [Metric.mem_closedBall, dist_zero_right, norm_radial z (by linarith [hr.1])]
          exact hr.2, rfl⟩
        (Set.image_mono (Metric.ball_subset_closedBall.trans
          (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))) hd)⟩

def secondRadialMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (r : ℝ) (hr : r ∈ Icc 1 2) : c.DoublePunctured d :=
  ⟨(d.firstRadialMap c hdisj.symm z r hr).val, by
    intro h
    exact (d.firstRadialMap c hdisj.symm z r hr).property h.symm⟩

@[simp] theorem firstRadialMap_val (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (r : ℝ) (hr : r ∈ Icc 1 2) :
    (c.firstRadialMap d hdisj z r hr).val = c.chart (r • z.val) := rfl

@[simp] theorem secondRadialMap_val (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (r : ℝ) (hr : r ∈ Icc 1 2) :
    (c.secondRadialMap d hdisj z r hr).val = d.chart (r • z.val) := rfl

@[simp] theorem firstRadialMap_one (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hr : (1 : ℝ) ∈ Icc 1 2) :
    c.firstRadialMap d hdisj z 1 hr = c.firstBoundaryMap d hdisj z := by
  apply Subtype.ext
  simp

@[simp] theorem secondRadialMap_one (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hr : (1 : ℝ) ∈ Icc 1 2) :
    c.secondRadialMap d hdisj z 1 hr = c.secondBoundaryMap d hdisj z := by
  apply Subtype.ext
  simp

theorem continuous_firstRadialMap {A : Type*} [TopologicalSpace A]
    (z : A → Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (r : A → ℝ)
    (hz : Continuous z) (hr : Continuous r) (hrange : ∀ q, r q ∈ Icc 1 2) :
    Continuous (fun q => c.firstRadialMap d hdisj (z q) (r q) (hrange q)) := by
  have hs : Continuous (fun q => r q • (z q).val) := hr.smul (continuous_subtype_val.comp hz)
  refine (c.chart.contMDiffOn_toFun.continuousOn.comp_continuous hs ?_).subtype_mk _
  intro q
  apply c.closedBall_subset_source
  rw [Metric.mem_closedBall, dist_zero_right, norm_radial (z q) (by linarith [(hrange q).1])]
  exact (hrange q).2

theorem continuous_secondRadialMap {A : Type*} [TopologicalSpace A]
    (z : A → Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (r : A → ℝ)
    (hz : Continuous z) (hr : Continuous r) (hrange : ∀ q, r q ∈ Icc 1 2) :
    Continuous (fun q => c.secondRadialMap d hdisj (z q) (r q) (hrange q)) :=
  (continuous_subtype_val.comp (d.continuous_firstRadialMap c hdisj.symm z r hz hr hrange)).subtype_mk _

theorem firstRadialMap_eq_iff
    (z w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (r s : ℝ) (hr : r ∈ Icc 1 2) (hs : s ∈ Icc 1 2) :
    c.firstRadialMap d hdisj z r hr = c.firstRadialMap d hdisj w s hs ↔ z = w ∧ r = s := by
  constructor
  · intro h
    have hr0 : 0 < r := by linarith [hr.1]
    have hs0 : 0 < s := by linarith [hs.1]
    have heq := c.chart.toPartialEquiv.injOn
      (c.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right, norm_radial z hr0.le]
        exact hr.2))
      (c.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right, norm_radial w hs0.le]
        exact hs.2)) (congrArg Subtype.val h)
    have hrs := congrArg norm heq
    rw [norm_radial z hr0.le, norm_radial w hs0.le] at hrs
    refine ⟨?_, hrs⟩
    rw [← hrs] at heq
    exact Subtype.ext (smul_right_injective _ hr0.ne' heq)
  · rintro ⟨rfl, rfl⟩
    rfl

end BallChart

namespace SelfAttachment

abbrev CollarDomain := ConnectedSumQuotient.CollarDomain

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] (c d : BallChart 3 I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

private def lowerCore (p : CollarDomain) : c.DoublePunctured d :=
  c.firstRadialMap d hdisj p.1 (max 1 (1 - p.2.val))
    ⟨le_max_left _ _, max_le (by norm_num) (by linarith [p.2.2.1])⟩

private def upperCore (p : CollarDomain) : c.DoublePunctured d :=
  c.secondRadialMap d hdisj (a p.1) (max 1 (1 + p.2.val))
    ⟨le_max_left _ _, max_le (by norm_num) (by linarith [p.2.2.2])⟩

private def lowerBand (p : CollarDomain) : Band (n := 3) :=
  (p.1, ⟨max 0 p.2.val, le_max_left _ _, max_le (by norm_num) (by linarith [p.2.2.2])⟩)

private def upperBand (p : CollarDomain) : Band (n := 3) :=
  (p.1, ⟨min 1 (1 + p.2.val), le_min (by norm_num) (by linarith [p.2.2.1]), min_le_left _ _⟩)

def lowerCollar (p : CollarDomain) : Quotient c d hdisj a :=
  if p.2.val ≤ 0 then coreInclusion c d hdisj a (lowerCore c d hdisj p)
  else bandInclusion c d hdisj a (lowerBand p)

def upperCollar (p : CollarDomain) : Quotient c d hdisj a :=
  if 0 ≤ p.2.val then coreInclusion c d hdisj a (upperCore c d hdisj a p)
  else bandInclusion c d hdisj a (upperBand p)

theorem lowerCollar_of_nonpos (p : CollarDomain) (ht : p.2.val ≤ 0) :
    lowerCollar c d hdisj a p =
      coreInclusion c d hdisj a
        (c.firstRadialMap d hdisj p.1 (1 - p.2.val) ⟨by linarith, by linarith [p.2.2.1]⟩) := by
  simp only [lowerCollar, ite_eq_left ht, lowerCore, max_eq_right (by linarith : 1 ≤ 1 - p.2.val)]

theorem lowerCollar_of_pos (p : CollarDomain) (ht : 0 < p.2.val) :
    lowerCollar c d hdisj a p =
      bandInclusion c d hdisj a (p.1, ⟨p.2.val, ht.le, by linarith [p.2.2.2]⟩) := by
  simp only [lowerCollar, ite_eq_right (not_le.mpr ht), lowerBand, max_eq_right ht.le]

theorem upperCollar_of_nonneg (p : CollarDomain) (ht : 0 ≤ p.2.val) :
    upperCollar c d hdisj a p =
      coreInclusion c d hdisj a
        (c.secondRadialMap d hdisj (a p.1) (1 + p.2.val)
          ⟨by linarith, by linarith [p.2.2.2]⟩) := by
  simp only [upperCollar, ite_eq_left ht, upperCore, max_eq_right (by linarith : 1 ≤ 1 + p.2.val)]

theorem upperCollar_of_neg (p : CollarDomain) (ht : p.2.val < 0) :
    upperCollar c d hdisj a p =
      bandInclusion c d hdisj a (p.1, ⟨1 + p.2.val, by linarith [p.2.2.1], by linarith⟩) := by
  simp only [upperCollar, ite_eq_right (not_le.mpr ht), upperBand,
    min_eq_right (by linarith : 1 + p.2.val ≤ 1)]

theorem lowerCollar_zero (z : Sphere (n := 3)) :
    lowerCollar c d hdisj a (z, ⟨0, by constructor <;> norm_num [ConnectedSumQuotient.collarInterval]⟩) =
      coreInclusion c d hdisj a (c.firstBoundaryMap d hdisj z) := by
  rw [lowerCollar_of_nonpos c d hdisj a _ le_rfl]
  simp

theorem upperCollar_zero (z : Sphere (n := 3)) :
    upperCollar c d hdisj a (z, ⟨0, by constructor <;> norm_num [ConnectedSumQuotient.collarInterval]⟩) =
      coreInclusion c d hdisj a (c.secondBoundaryMap d hdisj (a z)) := by
  rw [upperCollar_of_nonneg c d hdisj a _ le_rfl]
  simp

theorem continuous_lowerCollar : Continuous (lowerCollar c d hdisj a) := by
  have ht : Continuous (fun p : CollarDomain => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hcore : Continuous (lowerCore c d hdisj) :=
    c.continuous_firstRadialMap d hdisj Prod.fst _ continuous_fst
      (continuous_const.max (continuous_const.sub ht)) _
  have hband : Continuous lowerBand :=
    continuous_fst.prodMk ((continuous_const.max ht).subtype_mk _)
  apply continuous_if_le ht continuous_const
    ((continuous_coreInclusion c d hdisj a).comp hcore).continuousOn
    ((continuous_bandInclusion c d hdisj a).comp hband).continuousOn
  intro p hp
  have hc : lowerCore c d hdisj p = c.firstBoundaryMap d hdisj p.1 := by
    apply Subtype.ext
    change c.chart ((max 1 (1 - p.2.val)) • p.1.val) = c.chart p.1.val
    rw [hp]
    norm_num
  have hb : lowerBand p = boundaryInclusion (false, p.1) := by
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    change max 0 p.2.val = 0
    rw [hp, max_self]
  dsimp only [Function.comp_apply]
  rw [hc, hb]
  exact (seam_eq c d hdisj a (false, p.1)).symm

theorem continuous_upperCollar : Continuous (upperCollar c d hdisj a) := by
  have ht : Continuous (fun p : CollarDomain => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hcore : Continuous (upperCore c d hdisj a) :=
    c.continuous_secondRadialMap d hdisj (a ∘ Prod.fst) _
      (a.continuous.comp continuous_fst) (continuous_const.max (continuous_const.add ht)) _
  have hband : Continuous upperBand :=
    continuous_fst.prodMk ((continuous_const.min (continuous_const.add ht)).subtype_mk _)
  apply continuous_if_le continuous_const ht
    ((continuous_coreInclusion c d hdisj a).comp hcore).continuousOn
    ((continuous_bandInclusion c d hdisj a).comp hband).continuousOn
  intro p hp
  have hc : upperCore c d hdisj a p = c.secondBoundaryMap d hdisj (a p.1) := by
    apply Subtype.ext
    change d.chart ((max 1 (1 + p.2.val)) • (a p.1).val) = d.chart (a p.1).val
    rw [← hp]
    norm_num
  have hb : upperBand p = boundaryInclusion (true, p.1) := by
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    change min 1 (1 + p.2.val) = 1
    rw [← hp]
    norm_num
  dsimp only [Function.comp_apply]
  rw [hc, hb]
  exact (seam_eq c d hdisj a (true, p.1)).symm

end SelfAttachment
end DifferentialGeometry.Topology
