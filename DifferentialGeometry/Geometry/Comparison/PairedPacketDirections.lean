import DifferentialGeometry.Geometry.Comparison.CompleteHingeComparison
import DifferentialGeometry.Geometry.Comparison.HingeDirections
import DifferentialGeometry.Geometry.Comparison.PairedPacketLocalization
import DifferentialGeometry.Geometry.Comparison.LocalGeodesicDirections

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_endpoint_representatives_of_complete_local_comparison
    {X ι : Type*} [MetricSpace X] [CompleteSpace X] {κ : ℝ} (hκ : 0 ≤ κ)
    (hsegments : ∀ x y : X, ∃ σ : Icc (0 : ℝ) (dist x y) → X,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hlocal : ∀ z : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    (q : X) [HasAnglesAt q] (a : ι → X) (ha : ∀ i, q ≠ a i) :
    ∃ σ : ι → GeodesicRepresentative q,
      (∀ i, (σ i).length = dist q (a i) ∧ (σ i).path (dist q (a i)) = a i) ∧
      ∀ i j, comparisonAngleNegCurvature κ (dist q (a i)) (dist q (a j))
        (dist (a i) (a j)) ≤ dist (σ i).direction (σ j).direction := by
  classical
  choose γ hγ hγ0 hγend using fun i => hsegments q (a i)
  let σ : ι → GeodesicRepresentative q := fun i =>
    ⟨dist q (a i), dist_pos.mpr (ha i), γ i, hγ i, hγ0 i⟩
  refine ⟨σ, ?_, ?_⟩
  · intro i
    refine ⟨rfl, ?_⟩
    change IccExtend _ (γ i) (dist q (a i)) = a i
    rw [IccExtend_right, hγend]
  · intro i j
    let H : MinimizingHinge (a i) (a j) :=
      ⟨q, γ i, γ j, hγ i, hγ j, hγ0 i, hγ0 j, hγend i, hγend j⟩
    have h := H.comparisonAngle_le_of_complete_local_comparison hκ hsegments hlocal
      (dist_pos.mpr (ha i)) (dist_pos.mpr (ha j))
    rw [H.germAngle_eq_dist_directions hκ (dist_pos.mpr (ha i))
      (dist_pos.mpr (ha j))] at h
    exact h

theorem PairedComparisonPacket.exists_directions_of_complete_local_comparison
    {X ι : Type*} [MetricSpace X] [CompleteSpace X]
    (hsegments : ∀ x y : X, ∃ σ : Icc (0 : ℝ) (dist x y) → X,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hlocal : ∀ z : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ z ∈ Ω)
    {q : X} {a b : ι → X} {δ : ℝ} (hpacket : PairedComparisonPacket δ {q} a b)
    (hδ : δ < Real.pi / 2) :
    letI : HasAnglesAt q := by
      obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
      exact hasAnglesAt_of_local_fourPointComparison
        (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
    ∃ σ : (ι × Bool) → GeodesicRepresentative q,
      (∀ v, (σ v).length = dist q (if v.2 then a v.1 else b v.1) ∧
        (σ v).path (dist q (if v.2 then a v.1 else b v.1)) =
          (if v.2 then a v.1 else b v.1)) ∧
      (∀ v w, comparisonAngleNegCurvature 1
        (dist q (if v.2 then a v.1 else b v.1))
        (dist q (if w.2 then a w.1 else b w.1))
        (dist (if v.2 then a v.1 else b v.1) (if w.2 then a w.1 else b w.1)) ≤
          dist (σ v).direction (σ w).direction) ∧
      (∀ j, Real.pi - δ < dist (σ (j, true)).direction (σ (j, false)).direction) ∧
      ∀ j l, j ≠ l → ∀ s t : Bool,
        Real.pi / 2 - δ < dist (σ (j, s)).direction (σ (l, t)).direction := by
  let : HasAnglesAt q := by
    obtain ⟨Ω, hΩ, hcomp, hqΩ⟩ := hlocal q
    exact hasAnglesAt_of_local_fourPointComparison
      (by norm_num : (0 : ℝ) ≤ 1) hΩ hcomp hqΩ
  let c : (ι × Bool) → X := fun v => if v.2 then a v.1 else b v.1
  have hne : q ∉ range a ∪ range b := hpacket.not_mem_anchors (mem_singleton q) hδ
  have hc : ∀ v, q ≠ c v := by
    rintro ⟨j, s⟩ he
    cases s with
    | false => exact hne (Or.inr ⟨j, he.symm⟩)
    | true => exact hne (Or.inl ⟨j, he.symm⟩)
  obtain ⟨σ, hσ, hbound⟩ := exists_endpoint_representatives_of_complete_local_comparison
    (by norm_num : (0 : ℝ) ≤ 1) hsegments hlocal q c hc
  refine ⟨σ, hσ, hbound, ?_, ?_⟩
  · intro j
    exact (hpacket.opposite q (mem_singleton q) j).trans_le (hbound (j, true) (j, false))
  · intro j l hjl s t
    have hs : c (j, s) ∈ ({a j, b j} : Set X) := by cases s <;> simp [c]
    have ht : c (l, t) ∈ ({a l, b l} : Set X) := by cases t <;> simp [c]
    exact (hpacket.cross q (mem_singleton q) j l hjl _ hs _ ht).trans_le
      (hbound (j, s) (l, t))

end DifferentialGeometry.Geometry.Comparison.Toponogov
