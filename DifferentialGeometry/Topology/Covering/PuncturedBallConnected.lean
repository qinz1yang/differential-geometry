import DifferentialGeometry.Topology.PuncturedConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Separation.Hausdorff

noncomputable section

open Set Metric Filter
open scoped Topology

namespace DifferentialGeometry.Topology.Covering

/-- A covering near a unique central fiber has path connected total source.
The source and target radii are the original fixed radii. -/
theorem pathConnectedSpace_preimage_puncturedBall_of_isCoveringMap
    {F : ℂ → ℂ} {a : ℂ} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ)
    (hF : ContinuousOn F (Metric.closedBall a r))
    (hcenter : ∀ z ∈ Metric.closedBall a r, F z = F a ↔ z = a)
    (hcover : IsCoveringMap
      ((Metric.ball (F a) δ \ {F a}).restrictPreimage
        (fun z : Metric.closedBall a r => F z.val))) :
    PathConnectedSpace
      ((fun z : Metric.closedBall a r => F z.val) ⁻¹'
        (Metric.ball (F a) δ \ {F a})) := by
  let K : Set ℂ := closedBall a r
  let f : K → ℂ := fun z => F z.val
  let S : Set ℂ := ball (F a) δ \ {F a}
  let D : Set K := f ⁻¹' S
  let p : D → S := S.restrictPreimage f
  change PathConnectedSpace D
  have hp : IsCoveringMap p := hcover
  have hf : Continuous f := hF.domRestrict
  have hfclosed : IsClosedMap f := hf.isClosedMap
  have hdim : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hS : IsPathConnected S :=
    Metric.isPathConnected_ball_sdiff_singleton hdim (F a) hδ
  let : PathConnectedSpace S := isPathConnected_iff_pathConnectedSpace.mp hS
  have hpre : F ⁻¹' ball (F a) δ ∈ 𝓝 a :=
    (hF.continuousAt (closedBall_mem_nhds a hr)).preimage_mem_nhds
      (ball_mem_nhds (F a) hδ)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let ρ := min r ε
  have hρ : 0 < ρ := lt_min hr hε
  let W : Set ℂ := ball a ρ \ {a}
  have hW : IsPathConnected W :=
    Metric.isPathConnected_ball_sdiff_singleton hdim a hρ
  have hWK : W ⊆ K := by
    intro z hz
    exact ball_subset_closedBall (ball_subset_ball (min_le_left r ε) hz.1)
  let WK : Set K := (Subtype.val : K → ℂ) ⁻¹' W
  have hWKconn : IsPathConnected WK := hW.preimage_coe hWK
  have hWKD : WK ⊆ D := by
    intro z hz
    refine ⟨hεsub (ball_subset_ball (min_le_right r ε) hz.1), ?_⟩
    intro heq
    exact hz.2 ((hcenter z.val z.property).mp heq)
  let WD : Set D := (Subtype.val : D → K) ⁻¹' WK
  have hWD : IsPathConnected WD := hWKconn.preimage_coe hWKD
  obtain ⟨w, hw⟩ := hWD.nonempty
  have hlocal : ∀ᶠ y in 𝓝 (F a), ∀ z ∈ f ⁻¹' {y}, z.val ∈ ball a ρ := by
    apply hfclosed.eventually_nhds_fiber (F a)
    intro z hz
    have hza : z.val = a := (hcenter z.val z.property).mp hz
    have hzball : z.val ∈ ball a ρ := by
      rw [hza]
      exact mem_ball_self hρ
    exact (isOpen_ball.preimage
      (continuous_subtype_val : Continuous (Subtype.val : K → ℂ))).mem_nhds hzball
  obtain ⟨η, hη, hηlocal⟩ := Metric.eventually_nhds_iff_ball.mp hlocal
  obtain ⟨y, hy⟩ :=
    (Metric.isPathConnected_ball_sdiff_singleton hdim (F a) (lt_min hδ hη)).nonempty
  have hyS : y ∈ S := ⟨ball_subset_ball (min_le_left δ η) hy.1, hy.2⟩
  have hyη : y ∈ ball (F a) η := ball_subset_ball (min_le_right δ η) hy.1
  have hjoined (x : D) : Joined x w := by
    obtain ⟨v, hv⟩ := hp.comp_subtypeVal_pathComponent_surjective x ⟨y, hyS⟩
    have hvy : f v.val.val = y := congrArg Subtype.val hv
    have hvρ : v.val.val.val ∈ ball a ρ := hηlocal y hyη v.val.val hvy
    have hvWD : v.val ∈ WD := by
      refine ⟨hvρ, ?_⟩
      intro heq
      exact hy.2 (hvy.symm.trans (congrArg F heq))
    exact (mem_pathComponent_iff.mp v.property).trans
      (hWD.joinedIn v.val hvWD w hw).joined
  exact ⟨⟨w⟩, fun x z => (hjoined x).trans (hjoined z).symm⟩

end DifferentialGeometry.Topology.Covering
