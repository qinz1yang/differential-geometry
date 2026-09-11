import DifferentialGeometry.Topology.Morse.RegularLevel.Sublevel
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

namespace DifferentialGeometry.Topology.Morse

open scoped Manifold

noncomputable section

theorem contDiffOn_sublevelBoundaryChart_symm_val {m : ℕ}
    (g : MorseModel (m + 1) → ℝ) (a : ℝ) (x : SublevelSpace g a) (hx : g x.1 = a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hreg : fderiv ℝ g x.1 ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ((sublevelBoundaryChart g a x hx hg hreg).symm
        ((morseModelWithCornersHalfSpace m).symm z)).1)
      (morseModelWithCornersHalfSpace m '' (sublevelBoundaryChart g a x hx hg hreg).target) := by
  have hraw := contDiffOn_sublevelBoundaryChartInvValueRaw g a x hx hg hreg
  apply hraw.congr_mono
  · rintro _ ⟨z, hz, rfl⟩
    rw [(morseModelWithCornersHalfSpace m).left_inv,
      sublevelBoundaryChart_symm_value g a x hx hg hreg hz]
    rfl
  · rintro _ ⟨z, hz, rfl⟩
    exact hz

theorem contDiffOn_sublevelInteriorChart_symm_val {m : ℕ}
    (g : MorseModel (m + 1) → ℝ) (a : ℝ) (x : SublevelSpace g a) (hx : g x.1 < a)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ((sublevelInteriorChart g a x hx hg).symm
        ((morseModelWithCornersHalfSpace m).symm z)).1)
      (morseModelWithCornersHalfSpace m '' (sublevelInteriorChart g a x hx hg).target) := by
  apply (contDiff_morseHalfSpaceShift (-sublevelInteriorShift g a x hx hg)).contDiffOn.congr
  rintro _ ⟨z, hz, rfl⟩
  rw [(morseModelWithCornersHalfSpace m).left_inv,
    sublevelInteriorChart_symm_value g a x hx hg hz]
  rfl

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)

private theorem contMDiffAt_sublevelInclusion_of_chart
    (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target)
    (mc : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x.1 b) a)
      (MorseHalfSpace m))
    (hcs : ChartedSpace (MorseHalfSpace m) (SublevelSpace f a))
    (hchart : hcs.chartAt x = sublevelPullbackChart I f a x b hb ≫ₕ mc)
    (hmc : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (mc.symm ((morseModelWithCornersHalfSpace m).symm z)).1)
      (morseModelWithCornersHalfSpace m '' mc.target)) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) I (⊤ : ℕ∞)
      (fun y : SublevelSpace f a => y.1) x := by
  let := hcs
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  let c := sublevelPullbackChart I f a x b hb ≫ₕ mc
  let F := extChartAt I x.1 ∘ (fun y : SublevelSpace f a => y.1) ∘
    (extChartAt (morseModelWithCornersHalfSpace m) x).symm
  have htarget : (extChartAt (morseModelWithCornersHalfSpace m) x).target =
      morseModelWithCornersHalfSpace m '' c.target := by
    change ((hcs.chartAt x).extend (morseModelWithCornersHalfSpace m)).target = _
    rw [hchart, OpenPartialHomeomorph.extend_target']
  have hval (z : MorseModel (m + 1))
      (hz : z ∈ (extChartAt (morseModelWithCornersHalfSpace m) x).target) :
      F z = (mc.symm ((morseModelWithCornersHalfSpace m).symm z)).1 := by
    rw [htarget] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [(morseModelWithCornersHalfSpace m).left_inv]
    have hze : mc.symm w ∈ (sublevelPullbackChart I f a x b hb).target := hw.2
    have hzball : (mc.symm w).1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
      change dist (mc.symm w).1 ((extChartAt I x.1) x.1) < b.rIn at hze
      exact hze
    have hzt : (mc.symm w).1 ∈ (extChartAt I x.1).target :=
      ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
        Metric.ball_subset_closedBall).trans hb hzball
    change extChartAt I x.1
      (((hcs.chartAt x).symm ((morseModelWithCornersHalfSpace m).symm
        (morseModelWithCornersHalfSpace m w))).1) = _
    rw [(morseModelWithCornersHalfSpace m).left_inv, hchart]
    change extChartAt I x.1 (((sublevelPullbackChart I f a x b hb).symm (mc.symm w)).1) = _
    rw [sublevelPullbackChart_symm_value I f a x b hb hze,
      (extChartAt I x.1).right_inv hzt]
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F
      (extChartAt (morseModelWithCornersHalfSpace m) x).target := by
    apply hmc.congr_mono hval
    rw [htarget]
    exact Set.image_mono Set.inter_subset_left
  exact (hF.contDiffWithinAt
    ((extChartAt (morseModelWithCornersHalfSpace m) x).map_source (mem_extChartAt_source x)))
      |>.mono_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin x)

theorem contMDiff_manifoldSublevelInclusion [I.Boundaryless] [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    ContMDiff (morseModelWithCornersHalfSpace m) I (⊤ : ℕ∞)
      (fun x : SublevelSpace f a => x.1) := by
  classical
  let hcs := manifoldSublevelChartedSpace I f a hf hreg
  intro x
  let b := sublevelPullbackBump I x.1
  have hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  let g := sublevelPullbackCutoff I f x.1 b
  let p := sublevelPullbackCutoffPoint I f a x b
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_sublevelPullbackCutoff I f hf x.1 b hb
  by_cases hx : f x.1 = a
  · have hp : g p.1 = a := sublevelPullbackCutoffPoint_value I f a x b hx
    have hr : fderiv ℝ g p.1 ≠ 0 :=
      fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x b hx
    apply contMDiffAt_sublevelInclusion_of_chart I f a x b hb
      (sublevelBoundaryChart g a p hp hg hr) hcs
    · change (if h : f x.1 = a then manifoldSublevelBoundaryChart I f a x h hf hreg
        else manifoldSublevelInteriorChart I f a x
          (lt_of_le_of_ne (show f x.1 ≤ a from x.2) h) hf) = _
      rw [dif_pos hx]
      rfl
    · exact contDiffOn_sublevelBoundaryChart_symm_val g a p hp hg hr
  · have hlt : f x.1 < a := lt_of_le_of_ne x.2 hx
    have hp : g p.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x b hlt
    apply contMDiffAt_sublevelInclusion_of_chart I f a x b hb
      (sublevelInteriorChart g a p hp hg) hcs
    · change (if h : f x.1 = a then manifoldSublevelBoundaryChart I f a x h hf hreg
        else manifoldSublevelInteriorChart I f a x
          (lt_of_le_of_ne (show f x.1 ≤ a from x.2) h) hf) = _
      rw [dif_neg hx]
      rfl
    · exact contDiffOn_sublevelInteriorChart_symm_val g a p hp hg

end

end DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.Morse

open scoped Manifold

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]

private theorem mfderiv_sublevelInclusion_injective_of_chart
    (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target)
    (mc : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x.1 b) a)
      (MorseHalfSpace m))
    (hcs : ChartedSpace (MorseHalfSpace m) (SublevelSpace f a))
    [IsManifold (morseModelWithCornersHalfSpace m) 1 (SublevelSpace f a)]
    (hchart : hcs.chartAt x = sublevelPullbackChart I f a x b hb ≫ₕ mc)
    (hi : MDifferentiableAt (morseModelWithCornersHalfSpace m) I
      (fun y : SublevelSpace f a => y.1) x)
    (V : MorseModel (m + 1) → MorseModel (m + 1)) (hV : ContDiff ℝ 1 V)
    (hvalue : ∀ y ∈ mc.source, (mc y : MorseModel (m + 1)) = V y.1) :
    Function.Injective (mfderiv (morseModelWithCornersHalfSpace m) I
      (fun y : SublevelSpace f a => y.1) x) := by
  let := hcs
  let G : M → MorseModel (m + 1) := V ∘ extChartAt I x.1
  have hG : MDifferentiableAt I 𝓘(ℝ, MorseModel (m + 1)) G x.1 :=
    hV.contMDiff.contMDiffAt.mdifferentiableAt (by simp) |>.comp x.1
      (mdifferentiableAt_extChartAt (mem_chart_source H x.1))
  have heq : (G ∘ (fun y : SublevelSpace f a => y.1)) =ᶠ[nhds x]
      extChartAt (morseModelWithCornersHalfSpace m) x := by
    filter_upwards [(chartAt (MorseHalfSpace m) x).open_source.mem_nhds
      (mem_chart_source (MorseHalfSpace m) x)] with y hy
    change y ∈ (hcs.chartAt x).source at hy
    rw [hchart] at hy
    change G y.1 = (hcs.chartAt x y : MorseModel (m + 1))
    rw [hchart]
    change V (extChartAt I x.1 y.1) =
      (mc (sublevelPullbackChart I f a x b hb y) : MorseModel (m + 1))
    have hy' : sublevelPullbackChart I f a x b hb y ∈ mc.source := hy.2
    rw [hvalue _ hy', sublevelPullbackChart_apply_of_mem I f a x b hb hy.1]
  have hd : (mfderiv I 𝓘(ℝ, MorseModel (m + 1)) G x.1).comp
      (mfderiv (morseModelWithCornersHalfSpace m) I
        (fun y : SublevelSpace f a => y.1) x) =
      ContinuousLinearMap.id ℝ (MorseModel (m + 1)) := by
    rw [← mfderiv_comp x hG hi, heq.mfderiv_eq, mfderiv_extChartAt_self]
    rfl
  intro u v huv
  have h := congrArg (mfderiv I 𝓘(ℝ, MorseModel (m + 1)) G x.1) huv
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, hd] at h
  exact h

theorem mfderiv_manifoldSublevelInclusion_injective [I.Boundaryless]
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    Function.Injective (mfderiv (morseModelWithCornersHalfSpace m) I
      (fun y : SublevelSpace f a => y.1) x) := by
  classical
  let hcs := manifoldSublevelChartedSpace I f a hf hreg
  let : IsManifold (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞) (SublevelSpace f a) :=
    manifoldSublevelIsManifold I f a hf hreg
  have hi := (contMDiff_manifoldSublevelInclusion I f a hf hreg x).mdifferentiableAt (by simp)
  let b := sublevelPullbackBump I x.1
  have hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  let g := sublevelPullbackCutoff I f x.1 b
  let p := sublevelPullbackCutoffPoint I f a x b
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_sublevelPullbackCutoff I f hf x.1 b hb
  by_cases hx : f x.1 = a
  · have hp : g p.1 = a := sublevelPullbackCutoffPoint_value I f a x b hx
    have hr : fderiv ℝ g p.1 ≠ 0 :=
      fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x b hx
    refine mfderiv_sublevelInclusion_injective_of_chart I f a x b hb
      (sublevelBoundaryChart g a p hp hg hr) hcs ?_ hi
      (sublevelBoundaryChartValue g a p hp hg hr)
      ((contDiff_sublevelBoundaryChartValue g a p hp hg hr).of_le (by simp)) ?_
    · change (if h : f x.1 = a then manifoldSublevelBoundaryChart I f a x h hf hreg
        else manifoldSublevelInteriorChart I f a x
          (lt_of_le_of_ne (show f x.1 ≤ a from x.2) h) hf) = _
      rw [dif_pos hx]
      rfl
    · intro y _
      exact sublevelBoundaryChart_apply_value g a p hp hg hr y
  · have hlt : f x.1 < a := lt_of_le_of_ne x.2 hx
    have hp : g p.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x b hlt
    refine mfderiv_sublevelInclusion_injective_of_chart I f a x b hb
      (sublevelInteriorChart g a p hp hg) hcs ?_ hi
      (morseHalfSpaceShift (sublevelInteriorShift g a p hp hg))
      ((contDiff_morseHalfSpaceShift _).of_le (by simp)) ?_
    · change (if h : f x.1 = a then manifoldSublevelBoundaryChart I f a x h hf hreg
        else manifoldSublevelInteriorChart I f a x
          (lt_of_le_of_ne (show f x.1 ≤ a from x.2) h) hf) = _
      rw [dif_neg hx]
      rfl
    · intro y hy
      exact sublevelInteriorChart_apply_value g a p hp hg y hy

theorem mfderiv_manifoldSublevelInclusion_bijective [I.Boundaryless]
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (⊤ : ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) :
    letI := manifoldSublevelChartedSpace I f a hf hreg
    Function.Bijective (mfderiv (morseModelWithCornersHalfSpace m) I
      (fun y : SublevelSpace f a => y.1) x) := by
  let := manifoldSublevelChartedSpace I f a hf hreg
  let : FiniteDimensional ℝ (TangentSpace (morseModelWithCornersHalfSpace m) x) := by
    change FiniteDimensional ℝ (MorseModel (m + 1))
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace I x.1) := by
    change FiniteDimensional ℝ (MorseModel (m + 1))
    infer_instance
  have hi := mfderiv_manifoldSublevelInclusion_injective I f a hf hreg x
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp hi⟩

end

end DifferentialGeometry.Topology.Morse
