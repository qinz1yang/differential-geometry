import DifferentialGeometry.Geometry.Comparison.ConsistentEndpointDirections
import DifferentialGeometry.Geometry.Comparison.IntrinsicEightHingeComparison
import DifferentialGeometry.Geometry.Comparison.IntrinsicGeodesicDirections
import DifferentialGeometry.Geometry.Comparison.PairedPacketLocalization

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_endpoint_representatives_of_intrinsic_eight_comparison
    {X ι : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ x y : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + ε))
    (p : X) {R : ℝ} (hR : 0 < R) [LocallyCompactSpace (ball p (8 * R))]
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ ball p (R / 2)) [HasAnglesAt q]
    (a : ι → X) (ha : ∀ i, a i ∈ ball p R) (hne : ∀ i, q ≠ a i) :
    ∃ σ : ι → GeodesicRepresentative q,
      (∀ i, (σ i).length = dist q (a i) ∧ (σ i).path (dist q (a i)) = a i ∧
        ∀ t ∈ Icc (0 : ℝ) (dist q (a i)), (σ i).path t ∈ ball p (2 * R)) ∧
      ∀ i j, comparisonAngleNegCurvature 1 (dist q (a i)) (dist q (a j))
        (dist (a i) (a j)) ≤ dist (σ i).direction (σ j).direction := by
  have hqR : q ∈ ball p R := (ball_subset_ball (by linarith : R / 2 ≤ R)) hq
  let x : ball p R := ⟨q, hqR⟩
  let y : ι → ball p R := fun i => ⟨a i, ha i⟩
  obtain ⟨γ, hγ, hhinge⟩ := exists_consistent_endpoint_representatives_of_eight_buffer hcurves p hR
  let σ : ι → GeodesicRepresentative q := fun i => γ x (y i) (hne i)
  refine ⟨σ, fun i => hγ x (y i) (hne i), ?_⟩
  intro i j
  obtain ⟨H, hc, _, _, hang⟩ := hhinge x (y i) (y j) (hne i) (hne j) inferInstance
  have hcenter : H.center = q := hc
  have hbound := H.comparisonAngle_le_of_intrinsic_8_buffer hcurves p zero_lt_one hR hlocal
    (by simpa only [hcenter] using hq)
    (ball_subset_closedBall (ha i)) (ball_subset_closedBall (ha j))
    (by simpa only [hcenter] using dist_pos.mpr (hne i))
    (by simpa only [hcenter] using dist_pos.mpr (hne j))
  rw [hang 1 (by norm_num)] at hbound
  simpa only [hcenter, dist_comm] using hbound

theorem PairedComparisonPacket.exists_directions_of_intrinsic_eight_comparison
    {X ι : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ x y : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + ε))
    (p : X) {R : ℝ} (hR : 0 < R) [LocallyCompactSpace (ball p (8 * R))]
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)
    {q : X} (hq : q ∈ ball p (R / 2)) {a b : ι → X}
    (ha : ∀ i, a i ∈ ball p R) (hb : ∀ i, b i ∈ ball p R)
    {δ : ℝ} (hpacket : PairedComparisonPacket δ {q} a b)
    (hδ : δ < Real.pi / 2) :
    letI : HasAnglesAt q := by
      apply hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
        (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
      change dist q p < 8 * R
      have hh : dist q p < R / 2 := hq
      linarith
    ∃ σ : (ι × Bool) → GeodesicRepresentative q,
      (∀ v, (σ v).length = dist q (if v.2 then a v.1 else b v.1) ∧
        (σ v).path (dist q (if v.2 then a v.1 else b v.1)) =
          (if v.2 then a v.1 else b v.1) ∧
        ∀ t ∈ Icc (0 : ℝ) (dist q (if v.2 then a v.1 else b v.1)),
          (σ v).path t ∈ ball p (2 * R)) ∧
      (∀ v w, comparisonAngleNegCurvature 1
        (dist q (if v.2 then a v.1 else b v.1))
        (dist q (if w.2 then a w.1 else b w.1))
        (dist (if v.2 then a v.1 else b v.1) (if w.2 then a w.1 else b w.1)) ≤
          dist (σ v).direction (σ w).direction) ∧
      (∀ j, Real.pi - δ < dist (σ (j, true)).direction (σ (j, false)).direction) ∧
      ∀ j l, j ≠ l → ∀ s t : Bool,
        Real.pi / 2 - δ < dist (σ (j, s)).direction (σ (l, t)).direction := by
  let : HasAnglesAt q := by
    apply hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    change dist q p < 8 * R
    have hh : dist q p < R / 2 := hq
    linarith
  let c : (ι × Bool) → X := fun v => if v.2 then a v.1 else b v.1
  have hne : q ∉ range a ∪ range b := hpacket.not_mem_anchors (mem_singleton q) hδ
  have hc : ∀ v, q ≠ c v := by
    rintro ⟨j, s⟩ he
    cases s with
    | false => exact hne (Or.inr ⟨j, he.symm⟩)
    | true => exact hne (Or.inl ⟨j, he.symm⟩)
  have hcr : ∀ v, c v ∈ ball p R := by
    rintro ⟨i, s⟩
    cases s with
    | false => exact hb i
    | true => exact ha i
  obtain ⟨σ, hσ, hbound⟩ := exists_endpoint_representatives_of_intrinsic_eight_comparison
    hcurves p hR hlocal hq c hcr hc
  refine ⟨σ, hσ, hbound, ?_, ?_⟩
  · intro j
    exact (hpacket.opposite q (mem_singleton q) j).trans_le (hbound (j, true) (j, false))
  · intro j l hjl s t
    have hs : c (j, s) ∈ ({a j, b j} : Set X) := by cases s <;> simp [c]
    have ht : c (l, t) ∈ ({a l, b l} : Set X) := by cases t <;> simp [c]
    exact (hpacket.cross q (mem_singleton q) j l hjl _ hs _ ht).trans_le
      (hbound (j, s) (l, t))

end DifferentialGeometry.Geometry.Comparison.Toponogov
