import DifferentialGeometry.Geometry.Comparison.VaryingLocalGeometry
import DifferentialGeometry.Geometry.Comparison.GermAngle
import DifferentialGeometry.Topology.MetricSpace.SegmentExtension

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem comparisonAngleNegCurvature_le_of_radial_isometries_in_local_buffer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {κ L r A B : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r) (hbuffer : 256 * r < L)
    {n : ℕ} (hdim : dimH (ball p L) ≤ n)
    (hlocal : ∀ z ∈ ball p L,
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    (hrA : r ≤ A) (hrB : r ≤ B)
    (γ : Icc (0 : ℝ) A → X) (β : Icc (0 : ℝ) B → X)
    (hγ : Isometry γ) (hβ : Isometry β)
    (hγ0 : γ ⟨0, ⟨le_rfl, hr.le.trans hrA⟩⟩ = p)
    (hβ0 : β ⟨0, ⟨le_rfl, hr.le.trans hrB⟩⟩ = p)
    {s t : ℝ} (hs : s ∈ Ioc (0 : ℝ) r) (ht : t ∈ Ioc (0 : ℝ) r) :
    comparisonAngleNegCurvature κ r r
        (dist (γ ⟨r, ⟨hr.le, hrA⟩⟩) (β ⟨r, ⟨hr.le, hrB⟩⟩)) ≤
      comparisonAngleNegCurvature κ s t
        (dist (γ ⟨s, ⟨hs.1.le, hs.2.trans hrA⟩⟩)
          (β ⟨t, ⟨ht.1.le, ht.2.trans hrB⟩⟩)) := by
  have hsub : ball p (256 * r) ⊆ ball p L := ball_subset_ball hbuffer.le
  have hcomp := fourPointComparison_two_ball_of_local_comparison_and_dimH
    hcurves p hκ hr ((dimH_mono hsub).trans hdim) (fun z hz => hlocal z (hsub hz))
  let γ' := IccExtend (hr.le.trans hrA) γ
  let β' := IccExtend (hr.le.trans hrB) β
  have hγrad (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) r) : dist p (γ' u) = u := by
    simpa only [γ', zero_add, sub_zero, hγ0] using
      hγ.IccExtend_forward_radial (h := 0) ⟨le_rfl, hr.le.trans hrA⟩
        (show u ∈ Icc (0 : ℝ) (A - 0) from ⟨hu.1.le, by simpa using hu.2.trans hrA⟩)
  have hβrad (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) r) : dist p (β' u) = u := by
    simpa only [β', zero_add, sub_zero, hβ0] using
      hβ.IccExtend_forward_radial (h := 0) ⟨le_rfl, hr.le.trans hrB⟩
        (show u ∈ Icc (0 : ℝ) (B - 0) from ⟨hu.1.le, by simpa using hu.2.trans hrB⟩)
  have hγmin (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) r)
      (v : ℝ) (hv : v ∈ Ioc (0 : ℝ) r) : dist (γ' u) (γ' v) = |u - v| :=
    hγ.dist_IccExtend _ ⟨hu.1.le, hu.2.trans hrA⟩ ⟨hv.1.le, hv.2.trans hrA⟩
  have hβmin (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) r)
      (v : ℝ) (hv : v ∈ Ioc (0 : ℝ) r) : dist (β' u) (β' v) = |u - v| :=
    hβ.dist_IccExtend _ ⟨hu.1.le, hu.2.trans hrB⟩ ⟨hv.1.le, hv.2.trans hrB⟩
  have hγmem (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) r) : γ' u ∈ ball p (2 * r) := by
    rw [mem_ball, dist_comm, hγrad u hu]
    linarith [hu.2]
  have hβmem (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) r) : β' u ∈ ball p (2 * r) := by
    rw [mem_ball, dist_comm, hβrad u hu]
    linarith [hu.2]
  have hmono := comparisonAngleNegCurvature_antitone_on_segments hκ hcomp
    (mem_ball_self (by linarith : 0 < 2 * r)) hγrad hβrad hγmin hβmin hγmem hβmem
  have hrr : r ∈ Ioc (0 : ℝ) r := ⟨hr, le_rfl⟩
  have hangle := (hmono.1 hs hrr hrr hs.2).trans (hmono.2 hs ht hrr ht.2)
  simpa only [γ', β', IccExtend_of_mem (hr.le.trans hrA) γ ⟨hr.le, hrA⟩,
    IccExtend_of_mem (hr.le.trans hrB) β ⟨hr.le, hrB⟩,
    IccExtend_of_mem (hr.le.trans hrA) γ ⟨hs.1.le, hs.2.trans hrA⟩,
    IccExtend_of_mem (hr.le.trans hrB) β ⟨ht.1.le, ht.2.trans hrB⟩] using hangle

end DifferentialGeometry.Geometry.Comparison.Toponogov
