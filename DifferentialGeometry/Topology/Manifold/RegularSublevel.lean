import DifferentialGeometry.Topology.Morse.RegularLevel.Sublevel

set_option autoImplicit false
noncomputable section

open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.Manifold

variable {m : ℕ} {H : Type} [TopologicalSpace H]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
  [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] in
private theorem smooth_sublevel_inclusion_of_chart
    (f : M → ℝ) (a : ℝ) [ChartedSpace (MorseHalfSpace m) (SublevelSpace f a)]
    (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target)
    (mc : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x.1 b) a)
      (MorseHalfSpace m))
    (hchart : chartAt (MorseHalfSpace m) x = (sublevelPullbackChart I f a x b hb).trans mc)
    (R : MorseModel (m + 1) → MorseModel (m + 1)) (D : Set (MorseModel (m + 1)))
    (hD : IsOpen D)
    (hDx : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈ D)
    (hR : ContDiffOn ℝ ∞ R D)
    (hvalue : ∀ z ∈ mc.target, (mc.symm z).1 = R (morseModelWithCornersHalfSpace m z)) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) I ∞
      (fun y : SublevelSpace f a ↦ y.1) x := by
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  let F := extChartAt I x.1 ∘ (fun y : SublevelSpace f a ↦ y.1) ∘
    (extChartAt (morseModelWithCornersHalfSpace m) x).symm
  have heq : F =ᶠ[𝓝[Set.range (morseModelWithCornersHalfSpace m)]
      (extChartAt (morseModelWithCornersHalfSpace m) x x)] R := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := morseModelWithCornersHalfSpace m) x]
      with z hz
    have hzrange : z ∈ Set.range (morseModelWithCornersHalfSpace m) := by
      simpa only [ModelWithCorners.target_eq] using hz.1
    have hzt : (morseModelWithCornersHalfSpace m).symm z ∈
        ((sublevelPullbackChart I f a x b hb).trans mc).target := by
      rw [← hchart]
      exact hz.2
    have hzmc := hzt.1
    have hze := hzt.2
    have hball : (mc.symm ((morseModelWithCornersHalfSpace m).symm z)).1 ∈
        Metric.ball ((extChartAt I x.1) x.1) b.rIn := hze
    have hambient := hb (Metric.ball_subset_closedBall
      (Metric.ball_subset_ball b.rIn_lt_rOut.le hball))
    change (extChartAt I x.1)
      (((extChartAt (morseModelWithCornersHalfSpace m) x).symm z : SublevelSpace f a).1) = R z
    change (extChartAt I x.1)
      (((chartAt (MorseHalfSpace m) x).symm ((morseModelWithCornersHalfSpace m).symm z)).1) = R z
    rw [hchart]
    change (extChartAt I x.1)
      (((sublevelPullbackChart I f a x b hb).symm
        (mc.symm ((morseModelWithCornersHalfSpace m).symm z))).1) = R z
    rw [sublevelPullbackChart_symm_value I f a x b hb hze,
      (extChartAt I x.1).right_inv hambient, hvalue _ hzmc,
      (morseModelWithCornersHalfSpace m).right_inv hzrange]
  exact ((hR.contDiffAt (hD.mem_nhds hDx)).contDiffWithinAt).congr_of_eventuallyEq
    heq (heq.eq_of_nhdsWithin (by exact Set.mem_range_self _))

theorem contMDiff_manifoldSublevelInclusion
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hreg : ∀ x, f x = a → ¬ IsCriticalPointAt I f x) :
    let _ := manifoldSublevelChartedSpace I f a hf hreg
    ContMDiff (morseModelWithCornersHalfSpace m) I ∞
      (fun x : SublevelSpace f a ↦ x.1) := by
  classical
  dsimp only
  let _ := manifoldSublevelChartedSpace I f a hf hreg
  intro x
  let b := sublevelPullbackBump I x.1
  have hb := sublevelPullbackBump_closedBall_target (I := I) x.1
  let g := sublevelPullbackCutoff I f x.1 b
  let p := sublevelPullbackCutoffPoint I f a x b
  have hg := contDiff_sublevelPullbackCutoff I f hf x.1 b hb
  by_cases hx : f x.1 = a
  · have hp := sublevelPullbackCutoffPoint_value I f a x b hx
    have hr := fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x b hx
    let mc := sublevelBoundaryChart g a p hp hg hr
    have hc : chartAt (MorseHalfSpace m) x =
        (sublevelPullbackChart I f a x b hb).trans mc := by
      change (if h : f x.1 = a then _ else _) = _
      rw [dif_pos hx]
      rfl
    apply smooth_sublevel_inclusion_of_chart f a x b hb mc hc
      (sublevelBoundaryChartInvValueRaw g a p hp hg hr)
      (sublevelBoundaryChartDomain g a p hp hg hr)
      (isOpen_sublevelBoundaryChartDomain g a p hp hg hr)
    · have ht := (chartAt (MorseHalfSpace m) x).map_source (mem_chart_source _ x)
      rw [hc] at ht
      change ((chartAt (MorseHalfSpace m) x x : MorseHalfSpace m) : MorseModel (m + 1)) ∈ _
      rw [hc]
      exact ht.1
    · exact contDiffOn_sublevelBoundaryChartInvValueRaw g a p hp hg hr
    · intro z hz
      rw [sublevelBoundaryChart_symm_value g a p hp hg hr hz]
      rfl
  · have hp := sublevelPullbackCutoffPoint_value_lt I f a x b
      (lt_of_le_of_ne (show f x.1 ≤ a from x.2) hx)
    let mc := sublevelInteriorChart g a p hp hg
    have hc : chartAt (MorseHalfSpace m) x =
        (sublevelPullbackChart I f a x b hb).trans mc := by
      change (if h : f x.1 = a then _ else _) = _
      rw [dif_neg hx]
      rfl
    apply smooth_sublevel_inclusion_of_chart f a x b hb mc hc
      (morseHalfSpaceShift (-(sublevelInteriorShift g a p hp hg))) Set.univ
      isOpen_univ (Set.mem_univ _)
      (contDiff_morseHalfSpaceShift _).contDiffOn
    intro z hz
    rw [sublevelInteriorChart_symm_value g a p hp hg hz]
    rfl

theorem mem_boundary_manifoldSublevel_iff
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hreg : ∀ x, f x = a → ¬ IsCriticalPointAt I f x) (x : SublevelSpace f a) :
    let _ := manifoldSublevelChartedSpace I f a hf hreg
    x ∈ (morseModelWithCornersHalfSpace m).boundary (SublevelSpace f a) ↔ f x.1 = a := by
  classical
  dsimp only
  let _ := manifoldSublevelChartedSpace I f a hf hreg
  change (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
    frontier (Set.range (morseModelWithCornersHalfSpace m)) ↔ _
  rw [frontier_morseHalfSpace_range]
  change ((chartAt (MorseHalfSpace m) x x : MorseHalfSpace m) :
    MorseModel (m + 1)) (Fin.last m) = 0 ↔ _
  by_cases hx : f x.1 = a
  · have hc : chartAt (MorseHalfSpace m) x =
        manifoldSublevelBoundaryChart I f a x hx hf hreg := by
      change (if h : f x.1 = a then _ else _) = _
      rw [dif_pos hx]
    rw [hc]
    exact iff_of_true (manifoldSublevelBoundaryChart_extend_last_zero I f a hf hreg x hx) hx
  · have hxlt := lt_of_le_of_ne (show f x.1 ≤ a from x.2) hx
    have hc : chartAt (MorseHalfSpace m) x =
        manifoldSublevelInteriorChart I f a x hxlt hf := by
      change (if h : f x.1 = a then _ else _) = _
      rw [dif_neg hx]
    rw [hc]
    exact iff_of_false
      (ne_of_gt (manifoldSublevelInteriorChart_extend_last_pos I f a hf x hxlt)) hx

end DifferentialGeometry.Topology.Manifold
