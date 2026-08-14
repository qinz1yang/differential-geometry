import DifferentialGeometry.Topology.Morse.LevelSet
import DifferentialGeometry.Topology.Morse.Manifold
import DifferentialGeometry.Analysis.ODE.CompactSupportFlow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Icc

namespace DifferentialGeometry.Topology.Morse

open DifferentialGeometry.Analysis.ODE
open scoped Manifold Topology

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)

theorem fderiv_sublevelPullback_ne_zero [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    {p : M} {y : MorseModel (m + 1)}
    (hy : f ((extChartAt I p).symm y) = a) (hyt : y ∈ (extChartAt I p).target) :
    fderiv ℝ (fun y : MorseModel (m + 1) => f ((extChartAt I p).symm y)) y ≠ 0 := by
  classical
  let q : M := (extChartAt I p).symm y
  have hq : f q = a := hy
  have hregq : ¬ IsCriticalPointAt I f q := hreg q hq
  have hψq : (extChartAt I p) q = y := (extChartAt I p).right_inv hyt
  have hleft : ((extChartAt I p).symm ∘ (extChartAt I p)) =ᶠ[nhds q] id := by
    have hsrc : q ∈ (extChartAt I p).source := (extChartAt I p).map_target hyt
    have hopen : IsOpen (extChartAt I p).source := isOpen_extChartAt_source (I := I) p
    exact Filter.eventuallyEq_of_mem (by simpa [q] using hopen.mem_nhds hsrc)
      (fun x hx => (extChartAt I p).left_inv hx)
  have hright : ((extChartAt I p) ∘ (extChartAt I p).symm) =ᶠ[nhds y] id := by
    exact Filter.eventuallyEq_of_mem ((isOpen_extChartAt_target (I := I) p).mem_nhds hyt)
      (fun x hx => (extChartAt I p).right_inv hx)
  have hσmd : MDifferentiableAt I 𝓘(ℝ, MorseModel (m + 1)) (extChartAt I p) q := by
    have hsrc : q ∈ (chartAt H p).source := by
      simpa [q, extChartAt_source (I := I)] using (extChartAt I p).map_target hyt
    exact (contMDiffAt_extChartAt' (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := p)
      (by simpa [q] using hsrc)).mdifferentiableAt (by norm_num)
  have hτmd : MDifferentiableAt 𝓘(ℝ, MorseModel (m + 1)) I (extChartAt I p).symm y := by
    have hc : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (extChartAt I p).symm y := by
      have hon : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
          (extChartAt I p).symm (extChartAt I p).target :=
        contMDiffOn_extChartAt_symm (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) p
      exact hon.contMDiffAt ((isOpen_extChartAt_target (I := I) p).mem_nhds hyt)
    exact hc.mdifferentiableAt (by norm_num)
  have hh : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (f ∘ (extChartAt I p).symm) y := by
    have hc : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (extChartAt I p).symm y := by
      have hon : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
          (extChartAt I p).symm (extChartAt I p).target :=
        contMDiffOn_extChartAt_symm (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) p
      exact hon.contMDiffAt ((isOpen_extChartAt_target (I := I) p).mem_nhds hyt)
    have hfq : ContMDiffAt I 𝓘(ℝ, ℝ) ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) f q := hf q
    exact ContMDiffAt.comp (x := y) (g := f) (f := (extChartAt I p).symm)
      (hg := hfq) (hf := hc)
  have htrans : IsCriticalPointAt I ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q ↔
      fderiv ℝ (f ∘ (extChartAt I p).symm) y = 0 := by
    have htr := isCriticalPointAt_iff_fderiv_of_localInverse I (x := q) (σ := (extChartAt I p))
      (τ := (extChartAt I p).symm) (h := f ∘ (extChartAt I p).symm)
      (hleft := hleft) (hright := by
        rw [hψq]
        exact hright)
      (hσmd := hσmd) (hτmd := by
        rw [hψq]
        exact hτmd) (hh := by
          rw [hψq]
          exact hh)
    rw [hψq] at htr
    exact htr
  have hfuneq : (f ∘ (extChartAt I p).symm) ∘ (extChartAt I p) =ᶠ[nhds q] f := by
    have hsrc : q ∈ (extChartAt I p).source := (extChartAt I p).map_target hyt
    have hopen : IsOpen (extChartAt I p).source := isOpen_extChartAt_source (I := I) p
    exact Filter.eventuallyEq_of_mem (by simpa [q] using hopen.mem_nhds hsrc)
      (fun x hx => congrArg f ((extChartAt I p).left_inv hx))
  have hcrit_eq : IsCriticalPointAt I ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q ↔
      IsCriticalPointAt I f q := by
    change mfderiv I 𝓘(ℝ, ℝ) ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q = 0 ↔
      mfderiv I 𝓘(ℝ, ℝ) f q = 0
    exact Iff.of_eq (congrArg (fun L : TangentSpace I q →L[ℝ] ℝ => L = 0)
      (Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hfuneq))
  have hne : fderiv ℝ (f ∘ (extChartAt I p).symm) y ≠ 0 := by
    intro hzero
    have hcrit : IsCriticalPointAt I ((f ∘ (extChartAt I p).symm) ∘ (extChartAt I p)) q :=
      htrans.2 hzero
    exact hregq (hcrit_eq.mp hcrit)
  change fderiv ℝ (fun y : MorseModel (m + 1) => f ((extChartAt I p).symm y)) y ≠ 0
  simpa [q] using hne

noncomputable def sublevelPullback (f : M → ℝ) (p : M) : MorseModel (m + 1) → ℝ :=
  fun y => f ((extChartAt I p).symm y)

theorem contDiffOn_sublevelPullback [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (p : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sublevelPullback I f p) (extChartAt I p).target := by
  have hcomp : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : MorseModel (m + 1) => f ((extChartAt I p).symm y)) (extChartAt I p).target := by
    exact hf.contMDiffOn.comp (t := (Set.univ : Set M)) (contMDiffOn_extChartAt_symm (I := I)
      (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) p) (by intro y hy; exact Set.mem_preimage.mpr (Set.mem_univ _))
  have hcf : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : MorseModel (m + 1) => f ((extChartAt I p).symm y)) (extChartAt I p).target :=
    (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := MorseModel (m + 1)) (E' := ℝ)).mp hcomp
  simpa [sublevelPullback] using hcf

theorem sublevelPullbackBump_spec [I.Boundaryless] (x : M) :
    ∃ b : ContDiffBump ((extChartAt I x) x),
      Metric.closedBall ((extChartAt I x) x) b.rOut ⊆ (extChartAt I x).target := by
  classical
  let p : MorseModel (m + 1) := (extChartAt I x) x
  have hp : p ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source (I := I) x)
  rcases Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target (I := I) x).mem_nhds hp) with
    ⟨δ, hδ, hball⟩
  let rOut : ℝ := δ / 2
  let rIn : ℝ := rOut / 2
  have hrOut : 0 < rOut := by
    dsimp [rOut]
    positivity
  have hrIn : 0 < rIn := by
    dsimp [rIn]
    positivity
  refine ⟨⟨rIn, rOut, hrIn, half_lt_self hrOut⟩, ?_⟩
  intro y hy
  exact hball (by
    rw [Metric.mem_ball]
    have hy' : dist y p ≤ rOut := by simpa [Metric.mem_closedBall] using hy
    exact lt_of_le_of_lt hy' (by dsimp [rOut]; exact half_lt_self hδ))

noncomputable def sublevelPullbackBump [I.Boundaryless] (x : M) :
    ContDiffBump ((extChartAt I x) x) :=
  Classical.choose (sublevelPullbackBump_spec I x)

theorem sublevelPullbackBump_closedBall_target [I.Boundaryless] (x : M) :
    Metric.closedBall ((extChartAt I x) x) (sublevelPullbackBump I x).rOut ⊆
      (extChartAt I x).target :=
  Classical.choose_spec (sublevelPullbackBump_spec I x)

noncomputable def sublevelPullbackCutoff (f : M → ℝ) (x : M)
    (b : ContDiffBump ((extChartAt I x) x)) : MorseModel (m + 1) → ℝ :=
  fun y => b y * sublevelPullback I f x y

theorem sublevelPullbackCutoff_eqOn (f : M → ℝ) (x : M) (b : ContDiffBump ((extChartAt I x) x))
    {y : MorseModel (m + 1)} (hy : y ∈ Metric.ball ((extChartAt I x) x) b.rIn) :
    sublevelPullbackCutoff I f x b y = sublevelPullback I f x y := by
  have hb : b y = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  unfold sublevelPullbackCutoff
  rw [hb, one_mul]

theorem sublevelPullbackCutoff_eventuallyEq
    (f : M → ℝ) (x : M) (b : ContDiffBump ((extChartAt I x) x)) :
    sublevelPullbackCutoff I f x b =ᶠ[nhds ((extChartAt I x) x)] sublevelPullback I f x := by
  exact Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds ((extChartAt I x) x) b.rIn_pos)
    (fun z hz => sublevelPullbackCutoff_eqOn I f x b hz)

theorem contDiff_sublevelPullbackCutoff [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (x : M)
    (b : ContDiffBump ((extChartAt I x) x))
    (hb : Metric.closedBall ((extChartAt I x) x) b.rOut ⊆ (extChartAt I x).target) :
    ContDiff ℝ (⊤ : ℕ∞) (sublevelPullbackCutoff I f x b) := by
  classical
  let p : MorseModel (m + 1) := (extChartAt I x) x
  have hball : Metric.ball p b.rIn ⊆ (extChartAt I x).target := by
    exact ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
      Metric.ball_subset_closedBall).trans hb
  rw [← contDiffOn_univ]
  intro y hy
  rw [contDiffWithinAt_univ]
  by_cases hy : ‖y - p‖ ≤ b.rOut
  · have hyc : y ∈ Metric.closedBall p b.rOut := by
      rw [Metric.mem_closedBall]
      exact hy
    have hg : ContDiffAt ℝ (⊤ : ℕ∞) (sublevelPullback I f x) y := by
      exact (contDiffOn_sublevelPullback I f hf x).contDiffAt
        ((isOpen_extChartAt_target (I := I) x).mem_nhds (hb hyc))
    change ContDiffAt ℝ (⊤ : ℕ∞) (fun z : MorseModel (m + 1) =>
      (b : MorseModel (m + 1) → ℝ) z * sublevelPullback I f x z) y
    exact b.contDiffAt.mul hg
  · have hy' : b.rOut < ‖y - p‖ := lt_of_not_ge hy
    have hopen : IsOpen {z : MorseModel (m + 1) | b.rOut < ‖z - p‖} := by
      exact isOpen_lt continuous_const
        (continuous_norm.comp (continuous_id.sub continuous_const))
    have hzero : (fun z : MorseModel (m + 1) => sublevelPullbackCutoff I f x b z) =ᶠ[nhds y]
        (fun _ : MorseModel (m + 1) => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hy'] with z hz
      unfold sublevelPullbackCutoff
      have hb0 : b z = 0 := b.zero_of_le_dist (by
        change b.rOut ≤ dist z p
        rw [dist_eq_norm]
        exact le_of_lt hz)
      rw [hb0, zero_mul]
    exact (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun _ : MorseModel (m + 1) => (0 : ℝ)) y).congr_of_eventuallyEq hzero

theorem fderiv_sublevelPullbackCutoff_ne_zero
    (f : M → ℝ) (x : M) (b : ContDiffBump ((extChartAt I x) x))
    (hne : fderiv ℝ (sublevelPullback I f x) ((extChartAt I x) x) ≠ 0) :
    fderiv ℝ (sublevelPullbackCutoff I f x b) ((extChartAt I x) x) ≠ 0 := by
  intro h
  apply hne
  rw [← (sublevelPullbackCutoff_eventuallyEq I f x b).fderiv_eq]
  exact h

noncomputable def sublevelPullbackCutoffPoint (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) :
    SublevelSpace (sublevelPullbackCutoff I f x.1 b) a :=
  ⟨(extChartAt I x.1) x.1, by
    change (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) ≤ a
    have hpball : (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn :=
      Metric.mem_ball_self b.rIn_pos
    rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
    change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) ≤ a
    rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
    exact x.2⟩

theorem sublevelPullbackCutoffPoint_value (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) (hx : f x.1 = a) :
    (sublevelPullbackCutoff I f x.1 b) (sublevelPullbackCutoffPoint I f a x b).1 = a := by
  change (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) = a
  have hpball : (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn :=
    Metric.mem_ball_self b.rIn_pos
  rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
  change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a
  rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
  exact hx

theorem sublevelPullbackCutoffPoint_value_lt (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) (hx : f x.1 < a) :
    (sublevelPullbackCutoff I f x.1 b) (sublevelPullbackCutoffPoint I f a x b).1 < a := by
  change (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) < a
  have hpball : (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn :=
    Metric.mem_ball_self b.rIn_pos
  rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
  change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) < a
  rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
  exact hx

theorem fderiv_sublevelPullbackCutoffPoint_ne_zero [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) (hx : f x.1 = a) :
    fderiv ℝ (sublevelPullbackCutoff I f x.1 b) (sublevelPullbackCutoffPoint I f a x b).1 ≠ 0 := by
  change fderiv ℝ (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) ≠ 0
  apply fderiv_sublevelPullbackCutoff_ne_zero I f x.1 b
  have hx₀ : f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a := by
    rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
    exact hx
  have hyt : (extChartAt I x.1) x.1 ∈ (extChartAt I x.1).target :=
    (extChartAt I x.1).map_source (mem_extChartAt_source (I := I) x.1)
  exact fderiv_sublevelPullback_ne_zero I f hf a hreg hx₀ hyt

noncomputable def sublevelPullbackChart (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target) :
    OpenPartialHomeomorph (SublevelSpace f a)
      (SublevelSpace (sublevelPullbackCutoff I f x.1 b) a) := by
  classical
  let e : PartialEquiv M (MorseModel (m + 1)) := extChartAt I x.1
  let p : MorseModel (m + 1) := (extChartAt I x.1) x.1
  let toFun' : SublevelSpace f a → SublevelSpace (sublevelPullbackCutoff I f x.1 b) a :=
    fun x' =>
      if hx : x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn then
        ⟨e x'.1, by
          change (sublevelPullbackCutoff I f x.1 b) (e x'.1) ≤ a
          rw [sublevelPullbackCutoff_eqOn I f x.1 b hx.2]
          change f ((extChartAt I x.1).symm (e x'.1)) ≤ a
          rw [(extChartAt I x.1).left_inv hx.1]
          exact x'.2⟩
      else
        ⟨p, by
          change (sublevelPullbackCutoff I f x.1 b) p ≤ a
          have hpball : p ∈ Metric.ball p b.rIn := Metric.mem_ball_self b.rIn_pos
          rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
          change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) ≤ a
          rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
          exact x.2⟩
  let invFun' : SublevelSpace (sublevelPullbackCutoff I f x.1 b) a → SublevelSpace f a :=
    fun z =>
      if hz : z.1 ∈ Metric.ball p b.rIn then
        ⟨(extChartAt I x.1).symm z.1, by
          change f ((extChartAt I x.1).symm z.1) ≤ a
          change (sublevelPullback I f x.1 z.1) ≤ a
          rw [← sublevelPullbackCutoff_eqOn I f x.1 b hz]
          exact z.2⟩
      else ⟨x.1, x.2⟩
  exact
    { toPartialEquiv :=
        { toFun := toFun'
          invFun := invFun'
          source := {x' : SublevelSpace f a | x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn}
          target := {z : SublevelSpace (sublevelPullbackCutoff I f x.1 b) a |
            z.1 ∈ Metric.ball p b.rIn}
          map_source' := by
            intro x' hx'
            change x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn at hx'
            change (toFun' x').1 ∈ Metric.ball p b.rIn
            simp only [toFun']
            rw [dif_pos hx']
            exact hx'.2
          map_target' := by
            intro z hz
            change z.1 ∈ Metric.ball p b.rIn at hz
            change (invFun' z).1 ∈ e.source ∧ e ((invFun' z).1) ∈ Metric.ball p b.rIn
            simp only [invFun']
            rw [dif_pos hz]
            change (extChartAt I x.1).symm z.1 ∈ e.source ∧
              e ((extChartAt I x.1).symm z.1) ∈ Metric.ball p b.rIn
            have hzt : z.1 ∈ (extChartAt I x.1).target :=
              ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
                Metric.ball_subset_closedBall).trans hb hz
            constructor
            · exact (extChartAt I x.1).map_target hzt
            · rw [(extChartAt I x.1).right_inv hzt]
              exact hz
          left_inv' := by
            intro x' hx'
            change x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn at hx'
            apply Subtype.ext
            change (invFun' (toFun' x')).1 = x'.1
            simp only [toFun']
            rw [dif_pos hx']
            simp only [invFun']
            rw [dif_pos (by exact hx'.2)]
            change (extChartAt I x.1).symm (e x'.1) = x'.1
            exact (extChartAt I x.1).left_inv hx'.1
          right_inv' := by
            intro z hz
            change z.1 ∈ Metric.ball p b.rIn at hz
            apply Subtype.ext
            change (toFun' (invFun' z)).1 = z.1
            simp only [invFun']
            rw [dif_pos hz]
            have hzt : z.1 ∈ (extChartAt I x.1).target :=
              ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
                Metric.ball_subset_closedBall).trans hb hz
            have hsrc : (extChartAt I x.1).symm z.1 ∈ e.source :=
              (extChartAt I x.1).map_target hzt
            have hcond : (extChartAt I x.1).symm z.1 ∈ e.source ∧
                e ((extChartAt I x.1).symm z.1) ∈ Metric.ball p b.rIn := by
              constructor
              · exact hsrc
              · rw [(extChartAt I x.1).right_inv hzt]
                exact hz
            simp only [toFun']
            rw [dif_pos hcond]
            change (extChartAt I x.1) ((extChartAt I x.1).symm z.1) = z.1
            exact (extChartAt I x.1).right_inv hzt }
      open_source := by
        have hcont : Continuous (fun x' : SublevelSpace f a => (x' : M)) := continuous_subtype_val
        have h₁ : IsOpen {x' : SublevelSpace f a | x'.1 ∈ e.source} :=
          (isOpen_extChartAt_source (I := I) x.1).preimage hcont
        have hf : ContinuousOn (fun x' : SublevelSpace f a => e x'.1)
            {x' : SublevelSpace f a | x'.1 ∈ e.source} := by
          exact (continuousOn_extChartAt x.1).comp hcont.continuousOn (by intro x' hx'; exact hx')
        simpa using (hf.isOpen_inter_preimage h₁ (Metric.isOpen_ball))
      open_target := by
        have hcont : Continuous (fun z : SublevelSpace (sublevelPullbackCutoff I f x.1 b) a =>
            (z : MorseModel (m + 1))) := continuous_subtype_val
        exact (Metric.isOpen_ball).preimage hcont
      continuousOn_toFun := by
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hcont : Continuous (fun x' : {x' : SublevelSpace f a |
            x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn} => e x'.1.1) := by
          exact continuousOn_univ.mp ((continuousOn_extChartAt x.1).comp
            (Continuous.continuousOn (continuous_subtype_val.comp continuous_subtype_val))
            (by intro x' hx'; exact x'.2.1))
        refine (Continuous.subtype_mk hcont (by
          intro x'
          change (sublevelPullbackCutoff I f x.1 b) (e x'.1.1) ≤ a
          rw [sublevelPullbackCutoff_eqOn I f x.1 b x'.2.2]
          change f ((extChartAt I x.1).symm (e x'.1.1)) ≤ a
          rw [(extChartAt I x.1).left_inv x'.2.1]
          exact x'.1.2)).congr ?_
        intro x'
        simp only [Set.restrict]
        apply Subtype.ext
        change e x'.1.1 = (toFun' x'.1).1
        simp only [toFun']
        rw [dif_pos (show x'.1.1 ∈ e.source ∧ e x'.1.1 ∈ Metric.ball p b.rIn from x'.2)]
      continuousOn_invFun := by
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hcont : Continuous (fun z : {z : SublevelSpace (sublevelPullbackCutoff I f x.1 b) a |
            z.1 ∈ Metric.ball p b.rIn} => (extChartAt I x.1).symm z.1.1) := by
          exact continuousOn_univ.mp ((continuousOn_extChartAt_symm x.1).comp
            (Continuous.continuousOn (continuous_subtype_val.comp continuous_subtype_val))
            (by intro z hz; exact ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
              Metric.ball_subset_closedBall).trans hb z.2))
        refine (Continuous.subtype_mk hcont (by
          intro z
          change f ((extChartAt I x.1).symm z.1.1) ≤ a
          change (sublevelPullback I f x.1 z.1.1) ≤ a
          rw [← sublevelPullbackCutoff_eqOn I f x.1 b z.2]
          exact z.1.2)).congr ?_
        intro z
        simp only [Set.restrict]
        apply Subtype.ext
        change (extChartAt I x.1).symm z.1.1 = (invFun' z.1).1
        simp only [invFun']
        rw [dif_pos (show z.1.1 ∈ Metric.ball p b.rIn from z.2)]
      }

theorem mem_sublevelPullbackChart_source (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target) :
    x ∈ (sublevelPullbackChart I f a x b hb).source := by
  simpa [sublevelPullbackChart] using (show x.1 ∈ (extChartAt I x.1).source ∧
    (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn from by
      constructor
      · exact mem_extChartAt_source (I := I) x.1
      · exact Metric.mem_ball_self b.rIn_pos)

theorem sublevelPullbackChart_apply_of_mem (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target)
    {x' : SublevelSpace f a} (hx : x' ∈ (sublevelPullbackChart I f a x b hb).source) :
    (sublevelPullbackChart I f a x b hb x').1 = (extChartAt I x.1) x'.1 := by
  have hx' : x'.1 ∈ (extChartAt I x.1).source ∧
      (extChartAt I x.1) x'.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
    simpa [sublevelPullbackChart] using hx
  change x'.1 ∈ (chartAt H x.1).source ∩ (chartAt H x.1) ⁻¹' I.source ∧
      I ((chartAt H x.1) x'.1) ∈ Metric.ball (I ((chartAt H x.1) x.1)) b.rIn at hx'
  dsimp [sublevelPullbackChart]
  rw [dif_pos hx']

theorem sublevelPullbackChart_symm_value (f : M → ℝ) (a : ℝ) (x : SublevelSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target)
    {z : SublevelSpace (sublevelPullbackCutoff I f x.1 b) a}
    (hz : z ∈ (sublevelPullbackChart I f a x b hb).target) :
    ((sublevelPullbackChart I f a x b hb).symm z).1 = (extChartAt I x.1).symm z.1 := by
  have hz' : z.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
    simpa [sublevelPullbackChart] using hz
  change z.1 ∈ Metric.ball (I ((chartAt H x.1) x.1)) b.rIn at hz'
  dsimp [sublevelPullbackChart]
  rw [dif_pos hz']

noncomputable def sublevelChartTransition (x₁ x₂ : M) : MorseModel (m + 1) → MorseModel (m + 1) :=
  fun y => (extChartAt I x₂) ((extChartAt I x₁).symm y)

noncomputable def sublevelChartTransitionDomain (x₁ x₂ : M) : Set (MorseModel (m + 1)) :=
  {y : MorseModel (m + 1) | y ∈ (extChartAt I x₁).target ∧
    (extChartAt I x₁).symm y ∈ (extChartAt I x₂).source}

theorem isOpen_sublevelChartTransitionDomain [I.Boundaryless] (x₁ x₂ : M) :
    IsOpen (sublevelChartTransitionDomain I x₁ x₂) := by
  have hcont : ContinuousOn (extChartAt I x₁).symm (extChartAt I x₁).target :=
    continuousOn_extChartAt_symm x₁
  simpa [sublevelChartTransitionDomain] using
    (hcont.isOpen_inter_preimage (isOpen_extChartAt_target (I := I) x₁)
      (isOpen_extChartAt_source (I := I) x₂))

theorem contDiffOn_sublevelChartTransition [IsManifold I (⊤ : WithTop ℕ∞) M]
    (x₁ x₂ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sublevelChartTransition I x₁ x₂)
      (sublevelChartTransitionDomain I x₁ x₂) := by
  have hcomp : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, MorseModel (m + 1))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : MorseModel (m + 1) => (extChartAt I x₂) ((extChartAt I x₁).symm y))
      (sublevelChartTransitionDomain I x₁ x₂) := by
    simpa [sublevelChartTransitionDomain, extChartAt_source] using
      ((contMDiffOn_extChartAt (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := x₂)).comp'
        (contMDiffOn_extChartAt_symm (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) x₁))
  have hcf : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : MorseModel (m + 1) => (extChartAt I x₂) ((extChartAt I x₁).symm y))
      (sublevelChartTransitionDomain I x₁ x₂) :=
    (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := MorseModel (m + 1))
      (E' := MorseModel (m + 1))).mp hcomp
  simpa [sublevelChartTransition, sublevelChartTransitionDomain, extChartAt_source] using hcf

noncomputable def manifoldSublevelBoundaryChart [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (x : SublevelSpace f a) (hx : f x.1 = a)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) :=
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  sublevelPullbackChart I f a x b hb ≫ₕ
    sublevelBoundaryChart (sublevelPullbackCutoff I f x.1 b) a
      (sublevelPullbackCutoffPoint I f a x b)
      (sublevelPullbackCutoffPoint_value I f a x b hx)
      (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
      (fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x b hx)

noncomputable def manifoldSublevelInteriorChart [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (x : SublevelSpace f a) (hx : f x.1 < a)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) :
    OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) :=
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  sublevelPullbackChart I f a x b hb ≫ₕ
    sublevelInteriorChart (sublevelPullbackCutoff I f x.1 b) a
      (sublevelPullbackCutoffPoint I f a x b)
      (sublevelPullbackCutoffPoint_value_lt I f a x b hx)
      (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)

theorem mem_manifoldSublevelBoundaryChart_source [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (x : SublevelSpace f a) (hx : f x.1 = a)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    x ∈ (manifoldSublevelBoundaryChart I f a x hx hf hreg).source := by
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  dsimp [manifoldSublevelBoundaryChart]
  constructor
  · exact mem_sublevelPullbackChart_source I f a x b hb
  · change (sublevelPullbackChart I f a x b hb) x ∈
      (sublevelBoundaryChart (sublevelPullbackCutoff I f x.1 b) a
        (sublevelPullbackCutoffPoint I f a x b)
        (sublevelPullbackCutoffPoint_value I f a x b hx)
        (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
        (fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x b hx)).source
    have hpt : (sublevelPullbackChart I f a x b hb) x = sublevelPullbackCutoffPoint I f a x b := by
      apply Subtype.ext
      change ((sublevelPullbackChart I f a x b hb) x).1 = (sublevelPullbackCutoffPoint I f a x b).1
      rw [sublevelPullbackChart_apply_of_mem I f a x b hb
        (mem_sublevelPullbackChart_source I f a x b hb)]
      rfl
    rw [hpt]
    exact mem_sublevelBoundaryChart_source (sublevelPullbackCutoff I f x.1 b) a
      (sublevelPullbackCutoffPoint I f a x b)
      (sublevelPullbackCutoffPoint_value I f a x b hx)
      (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
      (fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x b hx)

theorem mem_manifoldSublevelInteriorChart_source [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (x : SublevelSpace f a) (hx : f x.1 < a)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) :
    x ∈ (manifoldSublevelInteriorChart I f a x hx hf).source := by
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  dsimp [manifoldSublevelInteriorChart]
  constructor
  · exact mem_sublevelPullbackChart_source I f a x b hb
  · change (sublevelPullbackChart I f a x b hb) x ∈
      (sublevelInteriorChart (sublevelPullbackCutoff I f x.1 b) a
        (sublevelPullbackCutoffPoint I f a x b)
        (sublevelPullbackCutoffPoint_value_lt I f a x b hx)
        (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)).source
    have hpt : (sublevelPullbackChart I f a x b hb) x = sublevelPullbackCutoffPoint I f a x b := by
      apply Subtype.ext
      change ((sublevelPullbackChart I f a x b hb) x).1 = (sublevelPullbackCutoffPoint I f a x b).1
      rw [sublevelPullbackChart_apply_of_mem I f a x b hb
        (mem_sublevelPullbackChart_source I f a x b hb)]
      rfl
    rw [hpt]
    exact mem_sublevelInteriorChart_source (sublevelPullbackCutoff I f x.1 b) a
      (sublevelPullbackCutoffPoint I f a x b)
      (sublevelPullbackCutoffPoint_value_lt I f a x b hx)
      (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)

private theorem sublevelPullbackChart_transition_mem_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : SublevelSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseHalfSpace m))
    (m₂ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseHalfSpace m))
    {y : MorseModel (m + 1)}
    (hy : y ∈ (morseModelWithCornersHalfSpace m).symm ⁻¹'
        ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
          (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source ∩
      Set.range (morseModelWithCornersHalfSpace m)) :
    (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target ∧
    m₁.symm ((morseModelWithCornersHalfSpace m).symm y) ∈
      (sublevelPullbackChart I f a x₁ b₁ hb₁).target ∧
    (sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm ((morseModelWithCornersHalfSpace m).symm y)) ∈
      (sublevelPullbackChart I f a x₂ b₂ hb₂).source ∧
    (sublevelPullbackChart I f a x₂ b₂ hb₂)
      ((sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm ((morseModelWithCornersHalfSpace m).symm y))) ∈
      m₂.source := by
  classical
  let I' : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  let e₁ : OpenPartialHomeomorph (SublevelSpace f a)
      (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a) :=
    sublevelPullbackChart I f a x₁ b₁ hb₁
  let e₂ : OpenPartialHomeomorph (SublevelSpace f a)
      (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a) :=
    sublevelPullbackChart I f a x₂ b₂ hb₂
  let c₁ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) := e₁ ≫ₕ m₁
  let c₂ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) := e₂ ≫ₕ m₂
  have hy2 : y ∈ Set.range I' := hy.2
  have hy2' : 0 ≤ y (Fin.last m) := by
    rw [range_morseModelWithCornersHalfSpace] at hy2
    exact hy2
  let z : MorseHalfSpace m := ⟨y, hy2'⟩
  have hclamp : I'.symm y = z := by
    apply Subtype.ext
    exact morseHalfSpaceClamp_of_mem m hy2'
  have hy1 : z ∈ (c₁.symm ≫ₕ c₂).source := by
    rw [← hclamp]
    exact hy.1
  have hz1 : z ∈ c₁.target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1
    simpa using hy1.1
  have hz1c : z ∈ (e₁ ≫ₕ m₁).target := by
    simpa [c₁] using hz1
  have hm₁ : z ∈ m₁.target := by
    rw [OpenPartialHomeomorph.trans_target] at hz1c
    exact hz1c.1
  have hme₁ : m₁.symm z ∈ e₁.target := by
    rw [OpenPartialHomeomorph.trans_target] at hz1c
    exact hz1c.2
  have hc₁₂ : c₁.symm z ∈ c₂.source := by
    rw [OpenPartialHomeomorph.trans_source] at hy1
    exact hy1.2
  have hcs : c₁.symm z = e₁.symm (m₁.symm z) := by
    rw [show c₁.symm = (e₁ ≫ₕ m₁).symm from rfl]
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    rfl
  have hc₁₂e₂ : e₁.symm (m₁.symm z) ∈ e₂.source := by
    simpa [hcs] using hc₁₂.1
  have hm₂ : e₂ (e₁.symm (m₁.symm z)) ∈ m₂.source := by
    rw [OpenPartialHomeomorph.trans_source] at hc₁₂
    simpa [hcs] using hc₁₂.2
  change (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target ∧
    m₁.symm ((morseModelWithCornersHalfSpace m).symm y) ∈ e₁.target ∧
    e₁.symm (m₁.symm ((morseModelWithCornersHalfSpace m).symm y)) ∈ e₂.source ∧
    e₂ (e₁.symm (m₁.symm ((morseModelWithCornersHalfSpace m).symm y))) ∈ m₂.source
  rw [hclamp]
  exact ⟨hm₁, hme₁, hc₁₂e₂, hm₂⟩

private theorem sublevelPullbackChart_transition_reduce_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : SublevelSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseHalfSpace m))
    (m₂ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseHalfSpace m))
    (w₁ : MorseHalfSpace m → MorseModel (m + 1))
    (v₂ : MorseModel (m + 1) → MorseModel (m + 1))
    (hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    (hV₂val : ∀ w : SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a,
      w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1)
    {y : MorseModel (m + 1)}
    (hy : y ∈ (morseModelWithCornersHalfSpace m).symm ⁻¹'
        ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
          (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source ∩
      Set.range (morseModelWithCornersHalfSpace m)) :
    (morseModelWithCornersHalfSpace m)
      (((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)) ((morseModelWithCornersHalfSpace m).symm y)) =
      v₂ (sublevelChartTransition I x₁.1 x₂.1 (w₁ ((morseModelWithCornersHalfSpace m).symm y))) := by
  classical
  let I' : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  let e₁ : OpenPartialHomeomorph (SublevelSpace f a)
      (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a) :=
    sublevelPullbackChart I f a x₁ b₁ hb₁
  let e₂ : OpenPartialHomeomorph (SublevelSpace f a)
      (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a) :=
    sublevelPullbackChart I f a x₂ b₂ hb₂
  let c₁ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) := e₁ ≫ₕ m₁
  let c₂ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) := e₂ ≫ₕ m₂
  have hy2 : y ∈ Set.range I' := hy.2
  have hy2' : 0 ≤ y (Fin.last m) := by
    rw [range_morseModelWithCornersHalfSpace] at hy2
    exact hy2
  let z : MorseHalfSpace m := ⟨y, hy2'⟩
  have hclamp : I'.symm y = z := by
    apply Subtype.ext
    exact morseHalfSpaceClamp_of_mem m hy2'
  have hmems := sublevelPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy
  have hm₁ : z ∈ m₁.target := by
    rw [hclamp] at hmems
    exact hmems.1
  rw [hclamp]
  change (m₂ (e₂ (e₁.symm (m₁.symm z))) : MorseModel (m + 1)) =
    v₂ (sublevelChartTransition I x₁.1 x₂.1 (w₁ z))
  rw [hV₂val (e₂ (e₁.symm (m₁.symm z))) (by
    rw [hclamp] at hmems
    exact hmems.2.2.2)]
  rw [sublevelPullbackChart_apply_of_mem I f a x₂ b₂ hb₂ (by
    rw [hclamp] at hmems
    exact hmems.2.2.1)]
  rw [sublevelPullbackChart_symm_value I f a x₁ b₁ hb₁ (by
    rw [hclamp] at hmems
    exact hmems.2.1)]
  rw [hW₁val z hm₁]
  rfl

private theorem sublevelPullbackChart_transition_w₁_mem_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : SublevelSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseHalfSpace m))
    (m₂ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseHalfSpace m))
    (w₁ : MorseHalfSpace m → MorseModel (m + 1))
    (hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    {y : MorseModel (m + 1)}
    (hy : y ∈ (morseModelWithCornersHalfSpace m).symm ⁻¹'
        ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
          (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source ∩
      Set.range (morseModelWithCornersHalfSpace m)) :
    w₁ ((morseModelWithCornersHalfSpace m).symm y) ∈
      sublevelChartTransitionDomain I x₁.1 x₂.1 := by
  classical
  let I' : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  have hy2 : y ∈ Set.range I' := hy.2
  have hy2' : 0 ≤ y (Fin.last m) := by
    rw [range_morseModelWithCornersHalfSpace] at hy2
    exact hy2
  let z : MorseHalfSpace m := ⟨y, hy2'⟩
  have hclamp : I'.symm y = z := by
    apply Subtype.ext
    exact morseHalfSpaceClamp_of_mem m hy2'
  have hmems := sublevelPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy
  have hm₁ : z ∈ m₁.target := by
    rw [hclamp] at hmems
    exact hmems.1
  have hw₁z : (m₁.symm z).1 = w₁ z := hW₁val z hm₁
  have htarget : (m₁.symm z).1 ∈ (extChartAt I x₁.1).target := by
    have hball : (m₁.symm z).1 ∈ Metric.ball ((extChartAt I x₁.1) x₁.1) b₁.rIn := by
      rw [hclamp] at hmems
      simpa [sublevelPullbackChart] using hmems.2.1
    exact ((Metric.ball_subset_ball (le_of_lt b₁.rIn_lt_rOut)).trans
      Metric.ball_subset_closedBall).trans hb₁ hball
  have hsrc : (extChartAt I x₁.1).symm ((m₁.symm z).1) ∈ (extChartAt I x₂.1).source := by
    have hmem₂ : (sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm z) ∈
        (sublevelPullbackChart I f a x₂ b₂ hb₂).source := by
      rw [hclamp] at hmems
      exact hmems.2.2.1
    have hval : ((sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm z)).1 =
        (extChartAt I x₁.1).symm ((m₁.symm z).1) :=
      sublevelPullbackChart_symm_value I f a x₁ b₁ hb₁ (by
        rw [hclamp] at hmems
        exact hmems.2.1)
    have hmem₂' : ((sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm z)).1 ∈
        (chartAt H x₂.1).source := by
      have hconj : ((sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm z)).1 ∈
          (extChartAt I x₂.1).source ∧
        (extChartAt I x₂.1) ((sublevelPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm z)).1 ∈
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn := hmem₂
      simpa [extChartAt_source] using hconj.1
    rw [← hval]
    simpa [extChartAt_source] using hmem₂'
  rw [hclamp]
  change w₁ z ∈ sublevelChartTransitionDomain I x₁.1 x₂.1
  rw [sublevelChartTransitionDomain]
  constructor
  · rwa [← hw₁z]
  · rwa [← hw₁z]

private theorem sublevelPullbackChart_transition_contDiffOn_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : SublevelSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseHalfSpace m))
    (m₂ : OpenPartialHomeomorph (SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseHalfSpace m))
    (w₁ : MorseHalfSpace m → MorseModel (m + 1))
    (v₂ : MorseModel (m + 1) → MorseModel (m + 1)) (D₁ : Set (MorseModel (m + 1)))
    (hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
      w₁ ((morseModelWithCornersHalfSpace m).symm y)) D₁)
    (hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂)
    (hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    (hV₂val : ∀ w : SublevelSpace (sublevelPullbackCutoff I f x₂.1 b₂) a,
      w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1)
    (hD₁ : ∀ y : MorseModel (m + 1), 0 ≤ y (Fin.last m) →
      (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target → y ∈ D₁) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘
        ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
          (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)) ∘
        (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
            (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  classical
  let I' : ModelWithCorners ℝ (MorseModel (m + 1)) (MorseHalfSpace m) :=
    morseModelWithCornersHalfSpace m
  let s : Set (MorseModel (m + 1)) := I'.symm ⁻¹'
      ((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source ∩ Set.range I'
  intro y hy
  have hw : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (fun y' : MorseModel (m + 1) => w₁ ((morseModelWithCornersHalfSpace m).symm y')) s y := by
    exact (hW₁.mono (by
      intro y' hy'
      have hy2' : 0 ≤ y' (Fin.last m) := by
        have hy2'' : y' ∈ Set.range (morseModelWithCornersHalfSpace m) := hy'.2
        rw [range_morseModelWithCornersHalfSpace] at hy2''
        exact hy2''
      exact hD₁ y' hy2' (by
        have hmems' := sublevelPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy'
        have hclamp' : (morseModelWithCornersHalfSpace m).symm y' = ⟨y', hy2'⟩ := by
          apply Subtype.ext
          exact morseHalfSpaceClamp_of_mem m hy2'
        simpa [hclamp'] using hmems'.1))) y hy
  have hwt : w₁ ((morseModelWithCornersHalfSpace m).symm y) ∈
      sublevelChartTransitionDomain I x₁.1 x₂.1 :=
    sublevelPullbackChart_transition_w₁_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ w₁ hW₁val hy
  have hφ : ContDiffWithinAt ℝ (⊤ : ℕ∞) (sublevelChartTransition I x₁.1 x₂.1)
      (sublevelChartTransitionDomain I x₁.1 x₂.1) (w₁ ((morseModelWithCornersHalfSpace m).symm y)) :=
    (contDiffOn_sublevelChartTransition I x₁.1 x₂.1) _ hwt
  have hφw : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (sublevelChartTransition I x₁.1 x₂.1 ∘
        fun y' : MorseModel (m + 1) => w₁ ((morseModelWithCornersHalfSpace m).symm y')) s y := by
    refine hφ.comp y hw ?_
    intro y' hy'
    exact sublevelPullbackChart_transition_w₁_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ w₁ hW₁val hy'
  have hv : ContDiffWithinAt ℝ (⊤ : ℕ∞) v₂ (Set.univ)
      (sublevelChartTransition I x₁.1 x₂.1 (w₁ ((morseModelWithCornersHalfSpace m).symm y))) :=
    hV₂.contDiffAt.contDiffWithinAt
  have hcd : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (v₂ ∘ sublevelChartTransition I x₁.1 x₂.1 ∘
        fun y' : MorseModel (m + 1) => w₁ ((morseModelWithCornersHalfSpace m).symm y')) s y := by
    refine hv.comp y hφw ?_
    intro y' hy'
    trivial
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun y' : MorseModel (m + 1) =>
      (morseModelWithCornersHalfSpace m)
        (((sublevelPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
          (sublevelPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)) ((morseModelWithCornersHalfSpace m).symm y')))
    s y
  refine hcd.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y' hy'
    simpa using (sublevelPullbackChart_transition_reduce_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ hW₁val hV₂val hy')
  · simpa using (sublevelPullbackChart_transition_reduce_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ hW₁val hV₂val hy)

theorem contDiffOn_manifoldSublevelBoundary_transition [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x₁ x₂ : SublevelSpace f a) (hx₁ : f x₁.1 = a) (hx₂ : f x₂.1 = a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘
        (manifoldSublevelBoundaryChart I f a x₁ hx₁ hf hreg).symm ≫ₕ
          (manifoldSublevelBoundaryChart I f a x₂ hx₂ hf hreg) ∘
        (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((manifoldSublevelBoundaryChart I f a x₁ hx₁ hf hreg).symm ≫ₕ
            (manifoldSublevelBoundaryChart I f a x₂ hx₂ hf hreg)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  classical
  let b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1) := sublevelPullbackBump I x₁.1
  let hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₁.1
  let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
  let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₂.1
  let g₁ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₁.1 b₁
  let g₂ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₂.1 b₂
  let p₁ : SublevelSpace g₁ a := sublevelPullbackCutoffPoint I f a x₁ b₁
  let p₂ : SublevelSpace g₂ a := sublevelPullbackCutoffPoint I f a x₂ b₂
  let hx₁' : g₁ p₁.1 = a := sublevelPullbackCutoffPoint_value I f a x₁ b₁ hx₁
  let hx₂' : g₂ p₂.1 = a := sublevelPullbackCutoffPoint_value I f a x₂ b₂ hx₂
  let hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁ := contDiff_sublevelPullbackCutoff I f hf x₁.1 b₁ hb₁
  let hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂ := contDiff_sublevelPullbackCutoff I f hf x₂.1 b₂ hb₂
  let hr₁ : fderiv ℝ g₁ p₁.1 ≠ 0 :=
    fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x₁ b₁ hx₁
  let hr₂ : fderiv ℝ g₂ p₂.1 ≠ 0 :=
    fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x₂ b₂ hx₂
  let m₁ : OpenPartialHomeomorph (SublevelSpace g₁ a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g₁ a p₁ hx₁' hg₁ hr₁
  let m₂ : OpenPartialHomeomorph (SublevelSpace g₂ a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g₂ a p₂ hx₂' hg₂ hr₂
  let w₁ : MorseHalfSpace m → MorseModel (m + 1) :=
    sublevelBoundaryChartInvValue g₁ a p₁ hx₁' hg₁ hr₁
  let v₂ : MorseModel (m + 1) → MorseModel (m + 1) :=
    sublevelBoundaryChartValue g₂ a p₂ hx₂' hg₂ hr₂
  let D₁ : Set (MorseModel (m + 1)) :=
    {y : MorseModel (m + 1) | y ∈ sublevelBoundaryChartDomain g₁ a p₁ hx₁' hg₁ hr₁ ∧
      0 ≤ y (Fin.last m)}
  have hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
      w₁ ((morseModelWithCornersHalfSpace m).symm y)) D₁ := by
    have hraw : ContDiffOn ℝ (⊤ : ℕ∞) (sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁)
        (sublevelBoundaryChartDomain g₁ a p₁ hx₁' hg₁ hr₁) :=
      contDiffOn_sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁
    have hcongr : ∀ y ∈ D₁, (fun y : MorseModel (m + 1) =>
        w₁ ((morseModelWithCornersHalfSpace m).symm y)) y =
        sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁ y := by
      intro y hy
      have hy0 : 0 ≤ y (Fin.last m) := hy.2
      have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy0⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy0
      dsimp [w₁]
      rw [hclamp]
      rfl
    exact (hraw.mono (by intro y hy; exact hy.1)).congr hcongr
  have hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂ :=
    contDiff_sublevelBoundaryChartValue g₂ a p₂ hx₂' hg₂ hr₂
  have hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z := by
    intro z hz
    rw [sublevelBoundaryChart_symm_value' g₁ a p₁ hx₁' hg₁ hr₁ hz]
  have hV₂val : ∀ w : SublevelSpace g₂ a, w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1 := by
    intro w hw
    exact sublevelBoundaryChart_apply_value' g₂ a p₂ hx₂' hg₂ hr₂ w
  have hD₁ : ∀ y : MorseModel (m + 1), 0 ≤ y (Fin.last m) →
      (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target → y ∈ D₁ := by
    intro y hy0 hz
    constructor
    · have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy0⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy0
      rw [hclamp] at hz
      simpa [sublevelBoundaryChartDomain] using hz
    · exact hy0
  simpa [manifoldSublevelBoundaryChart, b₁, b₂, hb₁, hb₂, g₁, g₂, p₁, p₂, m₁, m₂] using
    (sublevelPullbackChart_transition_contDiffOn_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ D₁ hW₁ hV₂ hW₁val hV₂val hD₁)

theorem contDiffOn_manifoldSublevelInterior_transition [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x₁ x₂ : SublevelSpace f a) (hx₁ : f x₁.1 < a) (hx₂ : f x₂.1 < a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘
        (manifoldSublevelInteriorChart I f a x₁ hx₁ hf).symm ≫ₕ
          (manifoldSublevelInteriorChart I f a x₂ hx₂ hf) ∘
        (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((manifoldSublevelInteriorChart I f a x₁ hx₁ hf).symm ≫ₕ
            (manifoldSublevelInteriorChart I f a x₂ hx₂ hf)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  classical
  let b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1) := sublevelPullbackBump I x₁.1
  let hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₁.1
  let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
  let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₂.1
  let g₁ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₁.1 b₁
  let g₂ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₂.1 b₂
  let p₁ : SublevelSpace g₁ a := sublevelPullbackCutoffPoint I f a x₁ b₁
  let p₂ : SublevelSpace g₂ a := sublevelPullbackCutoffPoint I f a x₂ b₂
  let hx₁' : g₁ p₁.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x₁ b₁ hx₁
  let hx₂' : g₂ p₂.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂
  let hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁ := contDiff_sublevelPullbackCutoff I f hf x₁.1 b₁ hb₁
  let hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂ := contDiff_sublevelPullbackCutoff I f hf x₂.1 b₂ hb₂
  let c₁ : ℝ := sublevelInteriorShift g₁ a p₁ hx₁' hg₁
  let c₂ : ℝ := sublevelInteriorShift g₂ a p₂ hx₂' hg₂
  let m₁ : OpenPartialHomeomorph (SublevelSpace g₁ a) (MorseHalfSpace m) :=
    sublevelInteriorChart g₁ a p₁ hx₁' hg₁
  let m₂ : OpenPartialHomeomorph (SublevelSpace g₂ a) (MorseHalfSpace m) :=
    sublevelInteriorChart g₂ a p₂ hx₂' hg₂
  let w₁ : MorseHalfSpace m → MorseModel (m + 1) :=
    fun z => morseHalfSpaceShift (-c₁) (z : MorseModel (m + 1))
  let v₂ : MorseModel (m + 1) → MorseModel (m + 1) := fun w => morseHalfSpaceShift c₂ w
  let D₁ : Set (MorseModel (m + 1)) := {y : MorseModel (m + 1) | 0 ≤ y (Fin.last m)}
  have hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
      w₁ ((morseModelWithCornersHalfSpace m).symm y)) D₁ := by
    have hshift : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
        morseHalfSpaceShift (-c₁) y) D₁ :=
      (contDiff_morseHalfSpaceShift (-c₁)).contDiffOn
    have hcongr : ∀ y ∈ D₁, (fun y : MorseModel (m + 1) =>
        w₁ ((morseModelWithCornersHalfSpace m).symm y)) y = morseHalfSpaceShift (-c₁) y := by
      intro y hy
      have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy
      dsimp [w₁]
      rw [hclamp]
    exact hshift.congr hcongr
  have hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂ := by
    dsimp [v₂]
    exact contDiff_morseHalfSpaceShift c₂
  have hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z := by
    intro z hz
    rw [sublevelInteriorChart_symm_value g₁ a p₁ hx₁' hg₁ hz]
  have hV₂val : ∀ w : SublevelSpace g₂ a, w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1 := by
    intro w hw
    have hw' : dist w.1 p₂.1 < sublevelInteriorRadius g₂ a p₂ hx₂' hg₂ := by
      simpa [m₂, sublevelInteriorChart] using hw
    rw [sublevelInteriorChart_apply_value g₂ a p₂ hx₂' hg₂ w hw']
  have hD₁ : ∀ y : MorseModel (m + 1), 0 ≤ y (Fin.last m) →
      (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target → y ∈ D₁ := by
    intro y hy0 hz
    exact hy0
  simpa [manifoldSublevelInteriorChart, b₁, b₂, hb₁, hb₂, g₁, g₂, p₁, p₂, m₁, m₂] using
    (sublevelPullbackChart_transition_contDiffOn_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ D₁ hW₁ hV₂ hW₁val hV₂val hD₁)

theorem contDiffOn_manifoldSublevelBoundaryInterior_transition [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x₁ x₂ : SublevelSpace f a) (hx₁ : f x₁.1 = a) (hx₂ : f x₂.1 < a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘
        (manifoldSublevelBoundaryChart I f a x₁ hx₁ hf hreg).symm ≫ₕ
          (manifoldSublevelInteriorChart I f a x₂ hx₂ hf) ∘
        (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((manifoldSublevelBoundaryChart I f a x₁ hx₁ hf hreg).symm ≫ₕ
            (manifoldSublevelInteriorChart I f a x₂ hx₂ hf)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  classical
  let b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1) := sublevelPullbackBump I x₁.1
  let hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₁.1
  let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
  let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₂.1
  let g₁ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₁.1 b₁
  let g₂ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₂.1 b₂
  let p₁ : SublevelSpace g₁ a := sublevelPullbackCutoffPoint I f a x₁ b₁
  let p₂ : SublevelSpace g₂ a := sublevelPullbackCutoffPoint I f a x₂ b₂
  let hx₁' : g₁ p₁.1 = a := sublevelPullbackCutoffPoint_value I f a x₁ b₁ hx₁
  let hx₂' : g₂ p₂.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂
  let hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁ := contDiff_sublevelPullbackCutoff I f hf x₁.1 b₁ hb₁
  let hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂ := contDiff_sublevelPullbackCutoff I f hf x₂.1 b₂ hb₂
  let hr₁ : fderiv ℝ g₁ p₁.1 ≠ 0 :=
    fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x₁ b₁ hx₁
  let c₂ : ℝ := sublevelInteriorShift g₂ a p₂ hx₂' hg₂
  let m₁ : OpenPartialHomeomorph (SublevelSpace g₁ a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g₁ a p₁ hx₁' hg₁ hr₁
  let m₂ : OpenPartialHomeomorph (SublevelSpace g₂ a) (MorseHalfSpace m) :=
    sublevelInteriorChart g₂ a p₂ hx₂' hg₂
  let w₁ : MorseHalfSpace m → MorseModel (m + 1) :=
    sublevelBoundaryChartInvValue g₁ a p₁ hx₁' hg₁ hr₁
  let v₂ : MorseModel (m + 1) → MorseModel (m + 1) := fun w => morseHalfSpaceShift c₂ w
  let D₁ : Set (MorseModel (m + 1)) :=
    {y : MorseModel (m + 1) | y ∈ sublevelBoundaryChartDomain g₁ a p₁ hx₁' hg₁ hr₁ ∧
      0 ≤ y (Fin.last m)}
  have hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
      w₁ ((morseModelWithCornersHalfSpace m).symm y)) D₁ := by
    have hraw : ContDiffOn ℝ (⊤ : ℕ∞) (sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁)
        (sublevelBoundaryChartDomain g₁ a p₁ hx₁' hg₁ hr₁) :=
      contDiffOn_sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁
    have hcongr : ∀ y ∈ D₁, (fun y : MorseModel (m + 1) =>
        w₁ ((morseModelWithCornersHalfSpace m).symm y)) y =
        sublevelBoundaryChartInvValueRaw g₁ a p₁ hx₁' hg₁ hr₁ y := by
      intro y hy
      have hy0 : 0 ≤ y (Fin.last m) := hy.2
      have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy0⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy0
      dsimp [w₁]
      rw [hclamp]
      rfl
    exact (hraw.mono (by intro y hy; exact hy.1)).congr hcongr
  have hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂ := by
    dsimp [v₂]
    exact contDiff_morseHalfSpaceShift c₂
  have hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z := by
    intro z hz
    rw [sublevelBoundaryChart_symm_value' g₁ a p₁ hx₁' hg₁ hr₁ hz]
  have hV₂val : ∀ w : SublevelSpace g₂ a, w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1 := by
    intro w hw
    have hw' : dist w.1 p₂.1 < sublevelInteriorRadius g₂ a p₂ hx₂' hg₂ := by
      simpa [m₂, sublevelInteriorChart] using hw
    rw [sublevelInteriorChart_apply_value g₂ a p₂ hx₂' hg₂ w hw']
  have hD₁ : ∀ y : MorseModel (m + 1), 0 ≤ y (Fin.last m) →
      (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target → y ∈ D₁ := by
    intro y hy0 hz
    constructor
    · have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy0⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy0
      rw [hclamp] at hz
      simpa [sublevelBoundaryChartDomain] using hz
    · exact hy0
  simpa [manifoldSublevelBoundaryChart, manifoldSublevelInteriorChart, b₁, b₂, hb₁, hb₂,
    g₁, g₂, p₁, p₂, m₁, m₂] using
    (sublevelPullbackChart_transition_contDiffOn_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ D₁ hW₁ hV₂ hW₁val hV₂val hD₁)

theorem contDiffOn_manifoldSublevelInteriorBoundary_transition [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x₁ x₂ : SublevelSpace f a) (hx₁ : f x₁.1 < a) (hx₂ : f x₂.1 = a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (morseModelWithCornersHalfSpace m ∘
        (manifoldSublevelInteriorChart I f a x₁ hx₁ hf).symm ≫ₕ
          (manifoldSublevelBoundaryChart I f a x₂ hx₂ hf hreg) ∘
        (morseModelWithCornersHalfSpace m).symm)
      ((morseModelWithCornersHalfSpace m).symm ⁻¹'
          ((manifoldSublevelInteriorChart I f a x₁ hx₁ hf).symm ≫ₕ
            (manifoldSublevelBoundaryChart I f a x₂ hx₂ hf hreg)).source ∩
        Set.range (morseModelWithCornersHalfSpace m)) := by
  classical
  let b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1) := sublevelPullbackBump I x₁.1
  let hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₁.1
  let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
  let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₂.1
  let g₁ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₁.1 b₁
  let g₂ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₂.1 b₂
  let p₁ : SublevelSpace g₁ a := sublevelPullbackCutoffPoint I f a x₁ b₁
  let p₂ : SublevelSpace g₂ a := sublevelPullbackCutoffPoint I f a x₂ b₂
  let hx₁' : g₁ p₁.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x₁ b₁ hx₁
  let hx₂' : g₂ p₂.1 = a := sublevelPullbackCutoffPoint_value I f a x₂ b₂ hx₂
  let hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁ := contDiff_sublevelPullbackCutoff I f hf x₁.1 b₁ hb₁
  let hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂ := contDiff_sublevelPullbackCutoff I f hf x₂.1 b₂ hb₂
  let hr₂ : fderiv ℝ g₂ p₂.1 ≠ 0 :=
    fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x₂ b₂ hx₂
  let c₁ : ℝ := sublevelInteriorShift g₁ a p₁ hx₁' hg₁
  let m₁ : OpenPartialHomeomorph (SublevelSpace g₁ a) (MorseHalfSpace m) :=
    sublevelInteriorChart g₁ a p₁ hx₁' hg₁
  let m₂ : OpenPartialHomeomorph (SublevelSpace g₂ a) (MorseHalfSpace m) :=
    sublevelBoundaryChart g₂ a p₂ hx₂' hg₂ hr₂
  let w₁ : MorseHalfSpace m → MorseModel (m + 1) :=
    fun z => morseHalfSpaceShift (-c₁) (z : MorseModel (m + 1))
  let v₂ : MorseModel (m + 1) → MorseModel (m + 1) :=
    sublevelBoundaryChartValue g₂ a p₂ hx₂' hg₂ hr₂
  let D₁ : Set (MorseModel (m + 1)) := {y : MorseModel (m + 1) | 0 ≤ y (Fin.last m)}
  have hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
      w₁ ((morseModelWithCornersHalfSpace m).symm y)) D₁ := by
    have hshift : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) =>
        morseHalfSpaceShift (-c₁) y) D₁ :=
      (contDiff_morseHalfSpaceShift (-c₁)).contDiffOn
    have hcongr : ∀ y ∈ D₁, (fun y : MorseModel (m + 1) =>
        w₁ ((morseModelWithCornersHalfSpace m).symm y)) y = morseHalfSpaceShift (-c₁) y := by
      intro y hy
      have hclamp : (morseModelWithCornersHalfSpace m).symm y = ⟨y, hy⟩ := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hy
      dsimp [w₁]
      rw [hclamp]
    exact hshift.congr hcongr
  have hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂ :=
    contDiff_sublevelBoundaryChartValue g₂ a p₂ hx₂' hg₂ hr₂
  have hW₁val : ∀ z : MorseHalfSpace m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z := by
    intro z hz
    rw [sublevelInteriorChart_symm_value g₁ a p₁ hx₁' hg₁ hz]
  have hV₂val : ∀ w : SublevelSpace g₂ a, w ∈ m₂.source → (m₂ w : MorseModel (m + 1)) = v₂ w.1 := by
    intro w hw
    exact sublevelBoundaryChart_apply_value' g₂ a p₂ hx₂' hg₂ hr₂ w
  have hD₁ : ∀ y : MorseModel (m + 1), 0 ≤ y (Fin.last m) →
      (morseModelWithCornersHalfSpace m).symm y ∈ m₁.target → y ∈ D₁ := by
    intro y hy0 hz
    exact hy0
  simpa [manifoldSublevelInteriorChart, manifoldSublevelBoundaryChart, b₁, b₂, hb₁, hb₂,
    g₁, g₂, p₁, p₂, m₁, m₂] using
    (sublevelPullbackChart_transition_contDiffOn_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ D₁ hW₁ hV₂ hW₁val hV₂val hD₁)

@[reducible]
noncomputable def manifoldSublevelChartedSpace [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    ChartedSpace (MorseHalfSpace m) (SublevelSpace f a) where
  atlas := Set.range (fun x : SublevelSpace f a =>
    if hx : f x.1 = a then manifoldSublevelBoundaryChart I f a x hx hf hreg
    else manifoldSublevelInteriorChart I f a x (lt_of_le_of_ne (show f x.1 ≤ a from x.2) hx) hf)
  chartAt := fun x : SublevelSpace f a =>
    if hx : f x.1 = a then manifoldSublevelBoundaryChart I f a x hx hf hreg
    else manifoldSublevelInteriorChart I f a x (lt_of_le_of_ne (show f x.1 ≤ a from x.2) hx) hf
  mem_chart_source := by
    intro x
    by_cases hx : f x.1 = a
    · simpa [hx] using mem_manifoldSublevelBoundaryChart_source I f a x hx hf hreg
    · simpa [hx] using mem_manifoldSublevelInteriorChart_source I f a x
        (lt_of_le_of_ne (show f x.1 ≤ a from x.2) hx) hf
  chart_mem_atlas := fun x => ⟨x, rfl⟩

theorem manifoldSublevelHasGroupoid [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    @HasGroupoid (MorseHalfSpace m) _ (SublevelSpace f a) _
      (manifoldSublevelChartedSpace I f a hf hreg)
      (contDiffGroupoid (⊤ : ℕ∞) (morseModelWithCornersHalfSpace m)) := by
  classical
  letI := manifoldSublevelChartedSpace I f a hf hreg
  refine hasGroupoid_of_pregroupoid (contDiffPregroupoid (⊤ : ℕ∞) (morseModelWithCornersHalfSpace m)) ?_
  intro e e' he he'
  rcases he with ⟨x₁, rfl⟩
  rcases he' with ⟨x₂, rfl⟩
  by_cases hx₁ : f x₁.1 = a
  · by_cases hx₂ : f x₂.1 = a
    · simpa [hx₁, hx₂] using
        contDiffOn_manifoldSublevelBoundary_transition I f a hf hreg x₁ x₂ hx₁ hx₂
    · simpa [hx₁, hx₂] using
        contDiffOn_manifoldSublevelBoundaryInterior_transition I f a hf hreg x₁ x₂ hx₁
          (lt_of_le_of_ne (show f x₂.1 ≤ a from x₂.2) hx₂)
  · by_cases hx₂ : f x₂.1 = a
    · simpa [hx₁, hx₂] using
        contDiffOn_manifoldSublevelInteriorBoundary_transition I f a hf hreg x₁ x₂
          (lt_of_le_of_ne (show f x₁.1 ≤ a from x₁.2) hx₁) hx₂
    · simpa [hx₁, hx₂] using
        contDiffOn_manifoldSublevelInterior_transition I f a hf x₁ x₂
          (lt_of_le_of_ne (show f x₁.1 ≤ a from x₁.2) hx₁)
          (lt_of_le_of_ne (show f x₂.1 ≤ a from x₂.2) hx₂)

theorem manifoldSublevelIsManifold [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    @IsManifold ℝ _ (MorseModel (m + 1)) _ _ (MorseHalfSpace m) _
      (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞) (SublevelSpace f a) _
      (manifoldSublevelChartedSpace I f a hf hreg) := by
  letI := manifoldSublevelChartedSpace I f a hf hreg
  exact { toHasGroupoid := manifoldSublevelHasGroupoid I f a hf hreg }

noncomputable def levelSetPullbackCutoffPoint (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) :
    LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a :=
  ⟨(extChartAt I x.1) x.1, by
    have hpball : (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn :=
      Metric.mem_ball_self b.rIn_pos
    rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
    change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a
    rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
    exact x.2⟩

theorem levelSetPullbackCutoffPoint_value (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) :
    (sublevelPullbackCutoff I f x.1 b) (levelSetPullbackCutoffPoint I f a x b).1 = a := by
  change (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) = a
  have hpball : (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn :=
    Metric.mem_ball_self b.rIn_pos
  rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
  change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a
  rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
  exact x.2

theorem fderiv_levelSetPullbackCutoffPoint_ne_zero [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1)) :
    fderiv ℝ (sublevelPullbackCutoff I f x.1 b) (levelSetPullbackCutoffPoint I f a x b).1 ≠ 0 := by
  change fderiv ℝ (sublevelPullbackCutoff I f x.1 b) ((extChartAt I x.1) x.1) ≠ 0
  apply fderiv_sublevelPullbackCutoff_ne_zero I f x.1 b
  have hx₀ : f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a := by
    rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
    exact x.2
  have hyt : (extChartAt I x.1) x.1 ∈ (extChartAt I x.1).target :=
    (extChartAt I x.1).map_source (mem_extChartAt_source (I := I) x.1)
  exact fderiv_sublevelPullback_ne_zero I f hf a hreg hx₀ hyt

noncomputable def levelSetPullbackChart (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target) :
    OpenPartialHomeomorph (LevelSetSpace f a)
      (LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a) := by
  classical
  let e : PartialEquiv M (MorseModel (m + 1)) := extChartAt I x.1
  let p : MorseModel (m + 1) := (extChartAt I x.1) x.1
  let toFun' : LevelSetSpace f a → LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a :=
    fun x' =>
      if hx : x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn then
        ⟨e x'.1, by
          rw [sublevelPullbackCutoff_eqOn I f x.1 b hx.2]
          change f ((extChartAt I x.1).symm (e x'.1)) = a
          rw [(extChartAt I x.1).left_inv hx.1]
          exact x'.2⟩
      else
        ⟨p, by
          have hpball : p ∈ Metric.ball p b.rIn := Metric.mem_ball_self b.rIn_pos
          rw [sublevelPullbackCutoff_eqOn I f x.1 b hpball]
          change f ((extChartAt I x.1).symm ((extChartAt I x.1) x.1)) = a
          rw [(extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
          exact x.2⟩
  let invFun' : LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a → LevelSetSpace f a :=
    fun z =>
      if hz : z.1 ∈ Metric.ball p b.rIn then
        ⟨(extChartAt I x.1).symm z.1, by
          change (sublevelPullback I f x.1 z.1) = a
          rw [← sublevelPullbackCutoff_eqOn I f x.1 b hz]
          exact z.2⟩
      else ⟨x.1, x.2⟩
  exact
    { toPartialEquiv :=
        { toFun := toFun'
          invFun := invFun'
          source := {x' : LevelSetSpace f a | x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn}
          target := {z : LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a |
            z.1 ∈ Metric.ball p b.rIn}
          map_source' := by
            intro x' hx'
            change x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn at hx'
            change (toFun' x').1 ∈ Metric.ball p b.rIn
            simp only [toFun']
            rw [dif_pos hx']
            exact hx'.2
          map_target' := by
            intro z hz
            change z.1 ∈ Metric.ball p b.rIn at hz
            change (invFun' z).1 ∈ e.source ∧ e ((invFun' z).1) ∈ Metric.ball p b.rIn
            simp only [invFun']
            rw [dif_pos hz]
            change (extChartAt I x.1).symm z.1 ∈ e.source ∧
              e ((extChartAt I x.1).symm z.1) ∈ Metric.ball p b.rIn
            have hzt : z.1 ∈ (extChartAt I x.1).target :=
              ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
                Metric.ball_subset_closedBall).trans hb hz
            constructor
            · exact (extChartAt I x.1).map_target hzt
            · rw [(extChartAt I x.1).right_inv hzt]
              exact hz
          left_inv' := by
            intro x' hx'
            change x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn at hx'
            apply Subtype.ext
            change (invFun' (toFun' x')).1 = x'.1
            simp only [toFun']
            rw [dif_pos hx']
            simp only [invFun']
            rw [dif_pos (by exact hx'.2)]
            change (extChartAt I x.1).symm (e x'.1) = x'.1
            exact (extChartAt I x.1).left_inv hx'.1
          right_inv' := by
            intro z hz
            change z.1 ∈ Metric.ball p b.rIn at hz
            apply Subtype.ext
            change (toFun' (invFun' z)).1 = z.1
            simp only [invFun']
            rw [dif_pos hz]
            have hzt : z.1 ∈ (extChartAt I x.1).target :=
              ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
                Metric.ball_subset_closedBall).trans hb hz
            have hsrc : (extChartAt I x.1).symm z.1 ∈ e.source :=
              (extChartAt I x.1).map_target hzt
            have hcond : (extChartAt I x.1).symm z.1 ∈ e.source ∧
                e ((extChartAt I x.1).symm z.1) ∈ Metric.ball p b.rIn := by
              constructor
              · exact hsrc
              · rw [(extChartAt I x.1).right_inv hzt]
                exact hz
            simp only [toFun']
            rw [dif_pos hcond]
            change (extChartAt I x.1) ((extChartAt I x.1).symm z.1) = z.1
            exact (extChartAt I x.1).right_inv hzt }
      open_source := by
        have hcont : Continuous (fun x' : LevelSetSpace f a => (x' : M)) := continuous_subtype_val
        have h₁ : IsOpen {x' : LevelSetSpace f a | x'.1 ∈ e.source} :=
          (isOpen_extChartAt_source (I := I) x.1).preimage hcont
        have hf : ContinuousOn (fun x' : LevelSetSpace f a => e x'.1)
            {x' : LevelSetSpace f a | x'.1 ∈ e.source} := by
          exact (continuousOn_extChartAt x.1).comp hcont.continuousOn (by intro x' hx'; exact hx')
        simpa using (hf.isOpen_inter_preimage h₁ (Metric.isOpen_ball))
      open_target := by
        have hcont : Continuous (fun z : LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a =>
            (z : MorseModel (m + 1))) := continuous_subtype_val
        exact (Metric.isOpen_ball).preimage hcont
      continuousOn_toFun := by
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hcont : Continuous (fun x' : {x' : LevelSetSpace f a |
            x'.1 ∈ e.source ∧ e x'.1 ∈ Metric.ball p b.rIn} => e x'.1.1) := by
          exact continuousOn_univ.mp ((continuousOn_extChartAt x.1).comp
            (Continuous.continuousOn (continuous_subtype_val.comp continuous_subtype_val))
            (by intro x' hx'; exact x'.2.1))
        refine (Continuous.subtype_mk hcont (by
          intro x'
          rw [sublevelPullbackCutoff_eqOn I f x.1 b x'.2.2]
          change f ((extChartAt I x.1).symm (e x'.1.1)) = a
          rw [(extChartAt I x.1).left_inv x'.2.1]
          exact x'.1.2)).congr ?_
        intro x'
        simp only [Set.restrict]
        apply Subtype.ext
        change e x'.1.1 = (toFun' x'.1).1
        simp only [toFun']
        rw [dif_pos (show x'.1.1 ∈ e.source ∧ e x'.1.1 ∈ Metric.ball p b.rIn from x'.2)]
      continuousOn_invFun := by
        refine continuousOn_iff_continuous_restrict.mpr ?_
        have hcont : Continuous (fun z : {z : LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a |
            z.1 ∈ Metric.ball p b.rIn} => (extChartAt I x.1).symm z.1.1) := by
          exact continuousOn_univ.mp ((continuousOn_extChartAt_symm x.1).comp
            (Continuous.continuousOn (continuous_subtype_val.comp continuous_subtype_val))
            (by intro z hz; exact ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
              Metric.ball_subset_closedBall).trans hb z.2))
        refine (Continuous.subtype_mk hcont (by
          intro z
          change (sublevelPullback I f x.1 z.1.1) = a
          rw [← sublevelPullbackCutoff_eqOn I f x.1 b z.2]
          exact z.1.2)).congr ?_
        intro z
        simp only [Set.restrict]
        apply Subtype.ext
        change (extChartAt I x.1).symm z.1.1 = (invFun' z.1).1
        simp only [invFun']
        rw [dif_pos (show z.1.1 ∈ Metric.ball p b.rIn from z.2)]
      }

theorem mem_levelSetPullbackChart_source (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target) :
    x ∈ (levelSetPullbackChart I f a x b hb).source := by
  simpa [levelSetPullbackChart] using (show x.1 ∈ (extChartAt I x.1).source ∧
    (extChartAt I x.1) x.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn from by
      constructor
      · exact mem_extChartAt_source (I := I) x.1
      · exact Metric.mem_ball_self b.rIn_pos)

theorem levelSetPullbackChart_apply_of_mem (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target)
    {x' : LevelSetSpace f a} (hx : x' ∈ (levelSetPullbackChart I f a x b hb).source) :
    (levelSetPullbackChart I f a x b hb x').1 = (extChartAt I x.1) x'.1 := by
  have hx' : x'.1 ∈ (extChartAt I x.1).source ∧
      (extChartAt I x.1) x'.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
    simpa [levelSetPullbackChart] using hx
  change x'.1 ∈ (chartAt H x.1).source ∩ (chartAt H x.1) ⁻¹' I.source ∧
      I ((chartAt H x.1) x'.1) ∈ Metric.ball (I ((chartAt H x.1) x.1)) b.rIn at hx'
  dsimp [levelSetPullbackChart]
  rw [dif_pos hx']

theorem levelSetPullbackChart_symm_value (f : M → ℝ) (a : ℝ) (x : LevelSetSpace f a)
    (b : ContDiffBump ((extChartAt I x.1) x.1))
    (hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target)
    {z : LevelSetSpace (sublevelPullbackCutoff I f x.1 b) a}
    (hz : z ∈ (levelSetPullbackChart I f a x b hb).target) :
    ((levelSetPullbackChart I f a x b hb).symm z).1 = (extChartAt I x.1).symm z.1 := by
  have hz' : z.1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
    simpa [levelSetPullbackChart] using hz
  change z.1 ∈ Metric.ball (I ((chartAt H x.1) x.1)) b.rIn at hz'
  dsimp [levelSetPullbackChart]
  rw [dif_pos hz']

private theorem levelSetPullbackChart_transition_mem_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : LevelSetSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseModel m))
    (m₂ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseModel m))
    {y : MorseModel m}
    (hy : y ∈ ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source) :
    y ∈ m₁.target ∧
    m₁.symm y ∈ (levelSetPullbackChart I f a x₁ b₁ hb₁).target ∧
    (levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y) ∈
      (levelSetPullbackChart I f a x₂ b₂ hb₂).source ∧
    (levelSetPullbackChart I f a x₂ b₂ hb₂)
      ((levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y)) ∈ m₂.source := by
  classical
  let e₁ : OpenPartialHomeomorph (LevelSetSpace f a)
      (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a) :=
    levelSetPullbackChart I f a x₁ b₁ hb₁
  let e₂ : OpenPartialHomeomorph (LevelSetSpace f a)
      (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a) :=
    levelSetPullbackChart I f a x₂ b₂ hb₂
  let c₁ : OpenPartialHomeomorph (LevelSetSpace f a) (MorseModel m) := e₁ ≫ₕ m₁
  let c₂ : OpenPartialHomeomorph (LevelSetSpace f a) (MorseModel m) := e₂ ≫ₕ m₂
  have hy1 : y ∈ (c₁.symm ≫ₕ c₂).source := hy
  have hz1 : y ∈ c₁.target := by
    rw [OpenPartialHomeomorph.trans_source] at hy1
    simpa using hy1.1
  have hz1c : y ∈ (e₁ ≫ₕ m₁).target := by
    simpa [c₁] using hz1
  have hm₁ : y ∈ m₁.target := by
    rw [OpenPartialHomeomorph.trans_target] at hz1c
    exact hz1c.1
  have hme₁ : m₁.symm y ∈ e₁.target := by
    rw [OpenPartialHomeomorph.trans_target] at hz1c
    exact hz1c.2
  have hc₁₂ : c₁.symm y ∈ c₂.source := by
    rw [OpenPartialHomeomorph.trans_source] at hy1
    exact hy1.2
  have hcs : c₁.symm y = e₁.symm (m₁.symm y) := by
    rw [show c₁.symm = (e₁ ≫ₕ m₁).symm from rfl]
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    rfl
  have hc₁₂e₂ : e₁.symm (m₁.symm y) ∈ e₂.source := by
    simpa [hcs] using hc₁₂.1
  have hm₂ : e₂ (e₁.symm (m₁.symm y)) ∈ m₂.source := by
    rw [OpenPartialHomeomorph.trans_source] at hc₁₂
    simpa [hcs] using hc₁₂.2
  exact ⟨hm₁, hme₁, hc₁₂e₂, hm₂⟩

private theorem levelSetPullbackChart_transition_reduce_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : LevelSetSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseModel m))
    (m₂ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseModel m))
    (w₁ : MorseModel m → MorseModel (m + 1))
    (v₂ : MorseModel (m + 1) → MorseModel m)
    (hW₁val : ∀ z : MorseModel m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    (hV₂val : ∀ w : LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a,
      w ∈ m₂.source → (m₂ w : MorseModel m) = v₂ w.1)
    {y : MorseModel m}
    (hy : y ∈ ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source) :
    (((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)) y : MorseModel m) =
      v₂ (sublevelChartTransition I x₁.1 x₂.1 (w₁ y)) := by
  classical
  let e₁ : OpenPartialHomeomorph (LevelSetSpace f a)
      (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a) :=
    levelSetPullbackChart I f a x₁ b₁ hb₁
  let e₂ : OpenPartialHomeomorph (LevelSetSpace f a)
      (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a) :=
    levelSetPullbackChart I f a x₂ b₂ hb₂
  have hmems := levelSetPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy
  change (m₂ (e₂ (e₁.symm (m₁.symm y))) : MorseModel m) =
    v₂ (sublevelChartTransition I x₁.1 x₂.1 (w₁ y))
  rw [hV₂val (e₂ (e₁.symm (m₁.symm y))) hmems.2.2.2]
  rw [levelSetPullbackChart_apply_of_mem I f a x₂ b₂ hb₂ hmems.2.2.1]
  rw [levelSetPullbackChart_symm_value I f a x₁ b₁ hb₁ hmems.2.1]
  rw [hW₁val y hmems.1]
  rfl

private theorem levelSetPullbackChart_transition_w₁_mem_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : LevelSetSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseModel m))
    (m₂ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseModel m))
    (w₁ : MorseModel m → MorseModel (m + 1))
    (hW₁val : ∀ z : MorseModel m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    {y : MorseModel m}
    (hy : y ∈ ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source) :
    w₁ y ∈ sublevelChartTransitionDomain I x₁.1 x₂.1 := by
  classical
  have hmems := levelSetPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy
  have hw₁y : (m₁.symm y).1 = w₁ y := hW₁val y hmems.1
  have htarget : (m₁.symm y).1 ∈ (extChartAt I x₁.1).target := by
    have hball : (m₁.symm y).1 ∈ Metric.ball ((extChartAt I x₁.1) x₁.1) b₁.rIn := by
      simpa [levelSetPullbackChart] using hmems.2.1
    exact ((Metric.ball_subset_ball (le_of_lt b₁.rIn_lt_rOut)).trans
      Metric.ball_subset_closedBall).trans hb₁ hball
  have hsrc : (extChartAt I x₁.1).symm ((m₁.symm y).1) ∈ (extChartAt I x₂.1).source := by
    have hmem₂ : (levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y) ∈
        (levelSetPullbackChart I f a x₂ b₂ hb₂).source := hmems.2.2.1
    have hval : ((levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y)).1 =
        (extChartAt I x₁.1).symm ((m₁.symm y).1) :=
      levelSetPullbackChart_symm_value I f a x₁ b₁ hb₁ hmems.2.1
    have hmem₂' : ((levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y)).1 ∈
        (chartAt H x₂.1).source := by
      have hconj : ((levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y)).1 ∈
          (extChartAt I x₂.1).source ∧
        (extChartAt I x₂.1) ((levelSetPullbackChart I f a x₁ b₁ hb₁).symm (m₁.symm y)).1 ∈
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn := hmem₂
      simpa [extChartAt_source] using hconj.1
    rw [← hval]
    simpa [extChartAt_source] using hmem₂'
  change w₁ y ∈ sublevelChartTransitionDomain I x₁.1 x₂.1
  rw [sublevelChartTransitionDomain]
  constructor
  · rwa [← hw₁y]
  · rwa [← hw₁y]

private theorem levelSetPullbackChart_transition_contDiffOn_aux
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (x₁ x₂ : LevelSetSpace f a)
    (b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1))
    (hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target)
    (b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1))
    (hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target)
    (m₁ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₁.1 b₁) a)
      (MorseModel m))
    (m₂ : OpenPartialHomeomorph (LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a)
      (MorseModel m))
    (w₁ : MorseModel m → MorseModel (m + 1))
    (v₂ : MorseModel (m + 1) → MorseModel m) (D₁ : Set (MorseModel m))
    (hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) w₁ D₁)
    (hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂)
    (hW₁val : ∀ z : MorseModel m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z)
    (hV₂val : ∀ w : LevelSetSpace (sublevelPullbackCutoff I f x₂.1 b₂) a,
      w ∈ m₂.source → (m₂ w : MorseModel m) = v₂ w.1)
    (hD₁ : ∀ y : MorseModel m, y ∈ m₁.target → y ∈ D₁) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂) : MorseModel m → MorseModel m)
      ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
        (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source := by
  classical
  let s : Set (MorseModel m) := ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
    (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)).source
  intro y hy
  have hw : ContDiffWithinAt ℝ (⊤ : ℕ∞) w₁ s y := by
    exact (hW₁.mono (by intro y' hy'; exact hD₁ y' (by
      have hmems' := levelSetPullbackChart_transition_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ hy'
      exact hmems'.1))) y hy
  have hwt : w₁ y ∈ sublevelChartTransitionDomain I x₁.1 x₂.1 :=
    levelSetPullbackChart_transition_w₁_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ w₁ hW₁val hy
  have hφ : ContDiffWithinAt ℝ (⊤ : ℕ∞) (sublevelChartTransition I x₁.1 x₂.1)
      (sublevelChartTransitionDomain I x₁.1 x₂.1) (w₁ y) :=
    (contDiffOn_sublevelChartTransition I x₁.1 x₂.1) _ hwt
  have hφw : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (sublevelChartTransition I x₁.1 x₂.1 ∘ w₁) s y := by
    refine hφ.comp y hw ?_
    intro y' hy'
    exact levelSetPullbackChart_transition_w₁_mem_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂ w₁ hW₁val hy'
  have hv : ContDiffWithinAt ℝ (⊤ : ℕ∞) v₂ (Set.univ)
      (sublevelChartTransition I x₁.1 x₂.1 (w₁ y)) :=
    hV₂.contDiffAt.contDiffWithinAt
  have hcd : ContDiffWithinAt ℝ (⊤ : ℕ∞)
      (v₂ ∘ sublevelChartTransition I x₁.1 x₂.1 ∘ w₁) s y := by
    refine hv.comp y hφw ?_
    intro y' hy'
    trivial
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun y' : MorseModel m => ((levelSetPullbackChart I f a x₁ b₁ hb₁ ≫ₕ m₁).symm ≫ₕ
      (levelSetPullbackChart I f a x₂ b₂ hb₂ ≫ₕ m₂)) y') s y
  refine hcd.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y' hy'
    simpa using (levelSetPullbackChart_transition_reduce_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ hW₁val hV₂val hy')
  · simpa using (levelSetPullbackChart_transition_reduce_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ hW₁val hV₂val hy)

noncomputable def manifoldLevelSetChart [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (x : LevelSetSpace f a) :
    OpenPartialHomeomorph (LevelSetSpace f a) (MorseModel m) :=
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  let g : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x.1 b
  let p : LevelSetSpace g a := levelSetPullbackCutoffPoint I f a x b
  levelSetPullbackChart I f a x b hb ≫ₕ
    levelSetChart g a p (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
      (fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x b)

theorem mem_manifoldLevelSetChart_source [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) (x : LevelSetSpace f a) :
    x ∈ (manifoldLevelSetChart I f a hf hreg x).source := by
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  let g : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x.1 b
  let p : LevelSetSpace g a := levelSetPullbackCutoffPoint I f a x b
  dsimp [manifoldLevelSetChart]
  constructor
  · exact mem_levelSetPullbackChart_source I f a x b hb
  · change (levelSetPullbackChart I f a x b hb) x ∈
      (levelSetChart g a p (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
        (fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x b)).source
    have hpt : (levelSetPullbackChart I f a x b hb) x = levelSetPullbackCutoffPoint I f a x b := by
      apply Subtype.ext
      change ((levelSetPullbackChart I f a x b hb) x).1 =
        (levelSetPullbackCutoffPoint I f a x b).1
      rw [levelSetPullbackChart_apply_of_mem I f a x b hb
        (mem_levelSetPullbackChart_source I f a x b hb)]
      rfl
    rw [hpt]
    exact mem_levelSetChart_source g a p (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
      (fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x b)

theorem contDiffOn_manifoldLevelSet_transition [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x₁ x₂ : LevelSetSpace f a) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
        (manifoldLevelSetChart I f a hf hreg x₂) : MorseModel m → MorseModel m)
      ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
        (manifoldLevelSetChart I f a hf hreg x₂)).source := by
  classical
  let b₁ : ContDiffBump ((extChartAt I x₁.1) x₁.1) := sublevelPullbackBump I x₁.1
  let hb₁ : Metric.closedBall ((extChartAt I x₁.1) x₁.1) b₁.rOut ⊆ (extChartAt I x₁.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₁.1
  let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
  let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x₂.1
  let g₁ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₁.1 b₁
  let g₂ : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₂.1 b₂
  let p₁ : LevelSetSpace g₁ a := levelSetPullbackCutoffPoint I f a x₁ b₁
  let p₂ : LevelSetSpace g₂ a := levelSetPullbackCutoffPoint I f a x₂ b₂
  let hg₁ : ContDiff ℝ (⊤ : ℕ∞) g₁ := contDiff_sublevelPullbackCutoff I f hf x₁.1 b₁ hb₁
  let hg₂ : ContDiff ℝ (⊤ : ℕ∞) g₂ := contDiff_sublevelPullbackCutoff I f hf x₂.1 b₂ hb₂
  let hr₁ : fderiv ℝ g₁ p₁.1 ≠ 0 :=
    fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x₁ b₁
  let hr₂ : fderiv ℝ g₂ p₂.1 ≠ 0 :=
    fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x₂ b₂
  let m₁ : OpenPartialHomeomorph (LevelSetSpace g₁ a) (MorseModel m) :=
    levelSetChart g₁ a p₁ hg₁ hr₁
  let m₂ : OpenPartialHomeomorph (LevelSetSpace g₂ a) (MorseModel m) :=
    levelSetChart g₂ a p₂ hg₂ hr₂
  let w₁ : MorseModel m → MorseModel (m + 1) := levelSetChartInvValue g₁ a p₁ hg₁ hr₁
  let v₂ : MorseModel (m + 1) → MorseModel m := levelSetChartValue g₂ a p₂ hg₂ hr₂
  let D₁ : Set (MorseModel m) := levelSetChartDomain g₁ a p₁ hg₁ hr₁
  have hW₁ : ContDiffOn ℝ (⊤ : ℕ∞) w₁ D₁ := by
    dsimp [w₁]
    exact contDiffOn_levelSetChartInvValueRaw g₁ a p₁ hg₁ hr₁
  have hV₂ : ContDiff ℝ (⊤ : ℕ∞) v₂ := by
    dsimp [v₂]
    exact contDiff_levelSetChartValue g₂ a p₂ hg₂ hr₂
  have hW₁val : ∀ z : MorseModel m, z ∈ m₁.target → (m₁.symm z).1 = w₁ z := by
    intro z hz
    rw [levelSetChart_symm_value' g₁ a p₁ hg₁ hr₁ hz]
    rfl
  have hV₂val : ∀ w : LevelSetSpace g₂ a, w ∈ m₂.source → (m₂ w : MorseModel m) = v₂ w.1 := by
    intro w hw
    exact levelSetChart_apply_value' g₂ a p₂ hg₂ hr₂ w
  have hD₁ : ∀ y : MorseModel m, y ∈ m₁.target → y ∈ D₁ := by
    intro y hy
    simpa [levelSetChartDomain] using hy
  simpa [manifoldLevelSetChart, b₁, b₂, hb₁, hb₂, g₁, g₂, p₁, p₂, m₁, m₂] using
    (levelSetPullbackChart_transition_contDiffOn_aux I f a x₁ x₂ b₁ hb₁ b₂ hb₂ m₁ m₂
      w₁ v₂ D₁ hW₁ hV₂ hW₁val hV₂val hD₁)

@[reducible]
noncomputable def manifoldLevelSetChartedSpace [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    ChartedSpace (MorseModel m) (LevelSetSpace f a) where
  atlas := Set.range (fun x : LevelSetSpace f a => manifoldLevelSetChart I f a hf hreg x)
  chartAt := fun x : LevelSetSpace f a => manifoldLevelSetChart I f a hf hreg x
  mem_chart_source := fun x => mem_manifoldLevelSetChart_source I f a hf hreg x
  chart_mem_atlas := fun x => ⟨x, rfl⟩

theorem manifoldLevelSetHasGroupoid [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    @HasGroupoid (MorseModel m) _ (LevelSetSpace f a) _
      (manifoldLevelSetChartedSpace I f a hf hreg)
      (contDiffGroupoid (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m))) := by
  classical
  letI := manifoldLevelSetChartedSpace I f a hf hreg
  refine hasGroupoid_of_pregroupoid (contDiffPregroupoid (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m))) ?_
  intro e e' he he'
  rcases he with ⟨x₁, rfl⟩
  rcases he' with ⟨x₂, rfl⟩
  have hfun : 𝓘(ℝ, MorseModel m) ∘
        (manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
          (manifoldLevelSetChart I f a hf hreg x₂) ∘ (𝓘(ℝ, MorseModel m)).symm =
      (manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
        (manifoldLevelSetChart I f a hf hreg x₂) := by
    ext y
    simp [modelWithCornersSelf, ModelWithCorners.ofTargetUniv]
  have hdom : (𝓘(ℝ, MorseModel m)).symm ⁻¹'
        ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
          (manifoldLevelSetChart I f a hf hreg x₂)).source ∩
      Set.range (𝓘(ℝ, MorseModel m)) =
      ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
        (manifoldLevelSetChart I f a hf hreg x₂)).source := by
    ext y
    simp [modelWithCornersSelf, ModelWithCorners.ofTargetUniv]
  change ContDiffOn ℝ (⊤ : ℕ∞) (𝓘(ℝ, MorseModel m) ∘
      ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
        (manifoldLevelSetChart I f a hf hreg x₂) : MorseModel m → MorseModel m) ∘
      (𝓘(ℝ, MorseModel m)).symm)
      ((𝓘(ℝ, MorseModel m)).symm ⁻¹'
        ((manifoldLevelSetChart I f a hf hreg x₁).symm ≫ₕ
          (manifoldLevelSetChart I f a hf hreg x₂)).source ∩
        Set.range (𝓘(ℝ, MorseModel m)))
  rw [hfun, hdom]
  exact contDiffOn_manifoldLevelSet_transition I f a hf hreg x₁ x₂

theorem manifoldLevelSetIsManifold [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) :
    @IsManifold ℝ _ (MorseModel m) _ _ (MorseModel m) _ (𝓘(ℝ, MorseModel m))
      (⊤ : ℕ∞) (LevelSetSpace f a) _ (manifoldLevelSetChartedSpace I f a hf hreg) := by
  letI := manifoldLevelSetChartedSpace I f a hf hreg
  exact { toHasGroupoid := manifoldLevelSetHasGroupoid I f a hf hreg }

theorem manifoldSublevelBoundaryChart_extend_last_zero [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (x : SublevelSpace f a) (hx : f x.1 = a) :
    (manifoldSublevelBoundaryChart I f a x hx hf hreg x : MorseModel (m + 1)) (Fin.last m) = 0 := by
  classical
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  dsimp [manifoldSublevelBoundaryChart]
  have he : (sublevelPullbackChart I f a x b hb) x = sublevelPullbackCutoffPoint I f a x b := by
    apply Subtype.ext
    change ((sublevelPullbackChart I f a x b hb) x).1 =
      (sublevelPullbackCutoffPoint I f a x b).1
    rw [sublevelPullbackChart_apply_of_mem I f a x b hb
      (mem_sublevelPullbackChart_source I f a x b hb)]
    rfl
  rw [he]
  have hzero := sublevelBoundaryChart_extend_last_zero (sublevelPullbackCutoff I f x.1 b) a
    (sublevelPullbackCutoffPoint I f a x b) (sublevelPullbackCutoffPoint_value I f a x b hx)
    (contDiff_sublevelPullbackCutoff I f hf x.1 b hb)
    (fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x b hx)
  rw [OpenPartialHomeomorph.extend_coe] at hzero
  simpa using hzero

theorem manifoldSublevelInteriorChart_extend_last_pos [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ) (a : ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x : SublevelSpace f a) (hx : f x.1 < a) :
    0 < (manifoldSublevelInteriorChart I f a x hx hf x : MorseModel (m + 1)) (Fin.last m) := by
  classical
  let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
  let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
    sublevelPullbackBump_closedBall_target (I := I) x.1
  let g : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x.1 b
  let p : SublevelSpace g a := sublevelPullbackCutoffPoint I f a x b
  let hx' : g p.1 < a := sublevelPullbackCutoffPoint_value_lt I f a x b hx
  let hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_sublevelPullbackCutoff I f hf x.1 b hb
  dsimp [manifoldSublevelInteriorChart]
  have he : (sublevelPullbackChart I f a x b hb) x = sublevelPullbackCutoffPoint I f a x b := by
    apply Subtype.ext
    change ((sublevelPullbackChart I f a x b hb) x).1 =
      (sublevelPullbackCutoffPoint I f a x b).1
    rw [sublevelPullbackChart_apply_of_mem I f a x b hb
      (mem_sublevelPullbackChart_source I f a x b hb)]
    rfl
  rw [he]
  have hval := sublevelInteriorChart_apply_value g a p hx' hg p (by
    have hmem := mem_sublevelInteriorChart_source g a p hx' hg
    simpa [sublevelInteriorChart] using hmem)
  rw [hval]
  have hnorm : |p.1 (Fin.last m)| ≤ ‖p.1‖ := by
    have hle : ‖p.1 (Fin.last m)‖ ≤ ‖p.1‖ := by
      have h := (pi_norm_le_iff_of_nonempty (ι := Fin (m + 1)) (f := p.1) (r := ‖p.1‖))
      exact h.mp le_rfl (Fin.last m)
    simpa using hle
  have hlow : -(‖p.1‖) ≤ p.1 (Fin.last m) := (abs_le.mp hnorm).1
  have hc : 0 < sublevelInteriorShift g a p hx' hg := by
    dsimp [sublevelInteriorShift]
    have hρ : 0 < sublevelInteriorRadius g a p hx' hg := by
      dsimp [sublevelInteriorRadius]
      exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
        ((isOpen_Iio.preimage hg.continuous).mem_nhds hx'))).1
    linarith [hρ, norm_nonneg p.1]
  change 0 < morseHalfSpaceShift (sublevelInteriorShift g a p hx' hg) p.1 (Fin.last m)
  rw [morseHalfSpaceShift_last]
  have hnonneg : 0 ≤ p.1 (Fin.last m) + ‖p.1‖ := by linarith [hlow]
  have hρ : 0 < sublevelInteriorRadius g a p hx' hg := by
    dsimp [sublevelInteriorRadius]
    exact (Classical.choose_spec (Metric.mem_nhds_iff.mp
      ((isOpen_Iio.preimage hg.continuous).mem_nhds hx'))).1
  have hshift : 0 < sublevelInteriorRadius g a p hx' hg + 1 := by linarith [hρ]
  dsimp [sublevelInteriorShift]
  linarith [hnonneg, hshift]

noncomputable def manifoldSublevelBoundaryEquiv (f : M → ℝ) (a : ℝ) :
    {x : SublevelSpace f a // f x.1 = a} ≃ₜ
      LevelSetSpace f a where
  toFun := fun x => ⟨x.1.1, x.2⟩
  invFun := fun y => ⟨⟨y.1, le_of_eq y.2⟩, y.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro y
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun x => x.2)
  continuous_invFun := by
    exact Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun y : LevelSetSpace f a => by
        change f y.1 ≤ a
        exact le_of_eq y.2))
      (fun y : LevelSetSpace f a => by
        simpa using y.2)

theorem contMDiff_levelSetInclusion [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hcs : ChartedSpace (MorseModel m) (LevelSetSpace f a) :=
      manifoldLevelSetChartedSpace I f a hf hreg)
    (hchart : ∀ x : LevelSetSpace f a, hcs.chartAt x = manifoldLevelSetChart I f a hf hreg x := by
      intro x
      rfl) :
    ContMDiff (𝓘(ℝ, MorseModel m)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : LevelSetSpace f a => x.1) := by
  classical
  letI := hcs
  intro x
  rw [contMDiffAt_iff]
  constructor
  · exact continuous_subtype_val.continuousAt
  · let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
    let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x.1
    let g : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x.1 b
    let p : LevelSetSpace g a := levelSetPullbackCutoffPoint I f a x b
    let hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_sublevelPullbackCutoff I f hf x.1 b hb
    let hr : fderiv ℝ g p.1 ≠ 0 := fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x b
    let c : OpenPartialHomeomorph (LevelSetSpace f a) (MorseModel m) :=
      manifoldLevelSetChart I f a hf hreg x
    let e : OpenPartialHomeomorph (LevelSetSpace f a) (LevelSetSpace g a) :=
      levelSetPullbackChart I f a x b hb
    let mc : OpenPartialHomeomorph (LevelSetSpace g a) (MorseModel m) :=
      levelSetChart g a p hg hr
    let F : MorseModel m → MorseModel (m + 1) :=
      extChartAt I x.1 ∘ (fun y : LevelSetSpace f a => y.1) ∘
        (extChartAt (𝓘(ℝ, MorseModel m)) x).symm
    let z₀ : MorseModel m := (extChartAt (𝓘(ℝ, MorseModel m)) x) x
    have hsymm₀ : ∀ z : MorseModel m, (extChartAt (𝓘(ℝ, MorseModel m)) x).symm z = c.symm z := by
      intro z
      change (hcs.chartAt x).symm z = c.symm z
      rw [hchart x]
    have hz₀ : z₀ ∈ c.target := by
      have hval₀ : c x ∈ c.target :=
        c.map_source (mem_manifoldLevelSetChart_source I f a hf hreg x)
      dsimp [z₀]
      simpa [hchart x] using hval₀
    have hval : ∀ z ∈ c.target, F z = levelSetChartInvValueRaw g a p hg hr z := by
      intro z hz
      have hz' : z ∈ mc.target := by
        dsimp [c, manifoldLevelSetChart] at hz
        exact hz.1
      have hze : mc.symm z ∈ e.target := by
        dsimp [c, manifoldLevelSetChart] at hz
        exact hz.2
      have hsymm₁ := levelSetChart_symm_value' g a p hg hr hz'
      have hsymm₂ := levelSetPullbackChart_symm_value I f a x b hb hze
      have hzball : (mc.symm z).1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
        simpa [e, levelSetPullbackChart] using hze
      have hzt : (mc.symm z).1 ∈ (extChartAt I x.1).target :=
        ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
          Metric.ball_subset_closedBall).trans hb hzball
      change (extChartAt I x.1) ((((extChartAt (𝓘(ℝ, MorseModel m)) x).symm z) :
          LevelSetSpace f a).1) = levelSetChartInvValueRaw g a p hg hr z
      rw [hsymm₀ z]
      have hc : c.symm z = e.symm (mc.symm z) := by
        dsimp [c, e, mc, manifoldLevelSetChart]
      rw [hc]
      rw [hsymm₂]
      change (extChartAt I x.1) ((extChartAt I x.1).symm ((mc.symm z).1)) =
        levelSetChartInvValueRaw g a p hg hr z
      rw [(extChartAt I x.1).right_inv hzt]
      rw [hsymm₁]
    have hF : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F c.target := by
      have hraw : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (levelSetChartInvValueRaw g a p hg hr) (levelSetChartDomain g a p hg hr) :=
        contDiffOn_levelSetChartInvValueRaw g a p hg hr
      have hsub : c.target ⊆ levelSetChartDomain g a p hg hr := by
        intro z hz
        have hz' : z ∈ mc.target := by
          dsimp [c, manifoldLevelSetChart] at hz
          exact hz.1
        simpa [levelSetChartDomain] using hz'
      exact (hraw.mono hsub).congr (by intro z hz; exact hval z hz)
    have hFAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F z₀ :=
      hF.contDiffAt (c.open_target.mem_nhds hz₀)
    simpa [F, modelWithCornersSelf, ModelWithCorners.ofTargetUniv] using hFAt.contDiffWithinAt

theorem contMDiff_levelSet_factor [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {HX : Type} [TopologicalSpace HX] {IX : ModelWithCorners ℝ E HX}
    {X : Type} [TopologicalSpace X] [ChartedSpace HX X]
    [IsManifold IX (⊤ : ℕ∞) X]
    (F : X → M) (hF : ContMDiff IX I (↑(⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFa : ∀ p : X, f (F p) = a)
    (hcs : ChartedSpace (MorseModel m) (LevelSetSpace f a) :=
      manifoldLevelSetChartedSpace I f a hf hreg)
    (hchart : ∀ x : LevelSetSpace f a, hcs.chartAt x = manifoldLevelSetChart I f a hf hreg x := by
      intro x
      rfl) :
    ContMDiff IX (𝓘(ℝ, MorseModel m)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : X => (⟨F p, hFa p⟩ : LevelSetSpace f a)) := by
  classical
  letI := hcs
  intro p0
  rw [contMDiffAt_iff]
  constructor
  · exact (Continuous.subtype_mk hF.continuous (fun p => hFa p)).continuousAt
  · let x0 : LevelSetSpace f a := ⟨F p0, hFa p0⟩
    let b : ContDiffBump ((extChartAt I x0.1) x0.1) := sublevelPullbackBump I x0.1
    let hb : Metric.closedBall ((extChartAt I x0.1) x0.1) b.rOut ⊆ (extChartAt I x0.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x0.1
    let g : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x0.1 b
    let p : LevelSetSpace g a := levelSetPullbackCutoffPoint I f a x0 b
    let hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_sublevelPullbackCutoff I f hf x0.1 b hb
    let hr : fderiv ℝ g p.1 ≠ 0 := fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x0 b
    let V : MorseModel (m + 1) → MorseModel m := levelSetChartValue g a p hg hr
    let Fhat : E → MorseModel m :=
      fun z => V ((extChartAt I x0.1) (F ((extChartAt IX p0).symm z)))
    let z0 : E := (extChartAt IX p0) p0
    have hz0 : z0 ∈ (extChartAt IX p0).target :=
      (extChartAt IX p0).map_source (mem_extChartAt_source (I := IX) p0)
    have hchartAtZ0 : ContDiffWithinAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : E => (extChartAt I x0.1) (F ((extChartAt IX p0).symm z))) (Set.range IX) z0 := by
      have hz0src : x0.1 ∈ (chartAt H x0.1).source := by
        exact mem_chart_source (H := H) (M := M) x0.1
      have hFmd : ContMDiffAt IX I (↑(⊤ : ℕ∞) : WithTop ℕ∞) F p0 := hF p0
      have hsymmAt : ContMDiffWithinAt (𝓘(ℝ, E)) IX (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (extChartAt IX p0).symm (Set.range IX) z0 :=
        contMDiffWithinAt_extChartAt_symm_range (I := IX) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
          (x := p0) (y := z0) hz0
      have hsymmVal : (extChartAt IX p0).symm z0 = p0 := by
        dsimp [z0]
        exact (extChartAt IX p0).left_inv (mem_extChartAt_source (I := IX) p0)
      have hFcompAt : ContMDiffWithinAt (𝓘(ℝ, E)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w : E => F ((extChartAt IX p0).symm w)) (Set.range IX) z0 := by
        have hF' : ContMDiffAt IX I (↑(⊤ : ℕ∞) : WithTop ℕ∞) F
            ((extChartAt IX p0).symm z0) := by
          rw [hsymmVal]
          exact hFmd
        exact ContMDiffWithinAt.comp (x := z0) (g := F) (f := (extChartAt IX p0).symm)
          (hg := hF') (hf := hsymmAt) (by intro y hy; trivial)
      have hceAt : ContMDiffAt I 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (extChartAt I x0.1) x0.1 := by
        exact contMDiffAt_extChartAt' (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := x0.1) hz0src
      have hval : (fun w : E => F ((extChartAt IX p0).symm w)) z0 = x0.1 := by
        change F ((extChartAt IX p0).symm z0) = x0.1
        rw [hsymmVal]
      have hceAt' : ContMDiffAt I 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (extChartAt I x0.1) ((fun w : E => F ((extChartAt IX p0).symm w)) z0) := by
        rw [hval]
        exact hceAt
      have hfullAt : ContMDiffWithinAt (𝓘(ℝ, E)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w : E => (extChartAt I x0.1) (F ((extChartAt IX p0).symm w))) (Set.range IX) z0 := by
        exact ContMDiffWithinAt.comp (x := z0) (g := extChartAt I x0.1)
          (f := fun w : E => F ((extChartAt IX p0).symm w))
          (hg := hceAt') (hf := hFcompAt) (by intro y hy; trivial)
      exact (contMDiffWithinAt_iff_contDiffWithinAt (𝕜 := ℝ) (E := E)
        (E' := MorseModel (m + 1))).mp hfullAt
    have hV : ContDiff ℝ (⊤ : ℕ∞) V := by
      dsimp [V]
      exact contDiff_levelSetChartValue g a p hg hr
    have hFhatAt : ContDiffWithinAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Fhat (Set.range IX) z0 := by
      dsimp [Fhat]
      exact ContDiffWithinAt.comp (g := V) (f := fun z : E =>
          (extChartAt I x0.1) (F ((extChartAt IX p0).symm z)))
        (s := Set.range IX) (t := Set.univ) (x := z0)
        hV.contDiffAt.contDiffWithinAt hchartAtZ0 (by
          intro y hy
          trivial)
    have hchartRep : ContDiffWithinAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : E => (extChartAt (𝓘(ℝ, MorseModel m)) x0) ⟨F ((extChartAt IX p0).symm z), hFa _⟩)
        (Set.range IX) z0 := by
      have hFhateq : (fun z : E =>
          (extChartAt (𝓘(ℝ, MorseModel m)) x0) ⟨F ((extChartAt IX p0).symm z), hFa _⟩) =ᶠ[nhdsWithin z0 (Set.range IX)] Fhat := by
        have hsrcNhd : (extChartAt I x0.1) x0.1 ∈ Metric.ball ((extChartAt I x0.1) x0.1) b.rIn :=
          Metric.mem_ball_self b.rIn_pos
        have hsymmVal' : (extChartAt IX p0).symm z0 = p0 := by
          dsimp [z0]
          exact (extChartAt IX p0).left_inv (mem_extChartAt_source (I := IX) p0)
        have hqNhd : {z : E |
            (⟨F ((extChartAt IX p0).symm z), hFa _⟩ : LevelSetSpace f a) ∈
              (manifoldLevelSetChart I f a hf hreg x0).source ∧
            F ((extChartAt IX p0).symm z) ∈ (extChartAt I x0.1).source ∧
            (extChartAt I x0.1) (F ((extChartAt IX p0).symm z)) ∈
              Metric.ball ((extChartAt I x0.1) x0.1) b.rIn} ∈ nhdsWithin z0 (Set.range IX) := by
          have hsrcMem0 : F p0 ∈ (extChartAt I x0.1).source := by
            change F p0 ∈ (chartAt H x0.1).source ∩ (chartAt H x0.1) ⁻¹' I.source
            exact mem_extChartAt_source (I := I) (F p0)
          have hsymmCont : ContinuousWithinAt (extChartAt IX p0).symm (Set.range IX) z0 :=
            (contMDiffWithinAt_extChartAt_symm_range (I := IX)
              (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) p0 hz0).continuousWithinAt
          have hcont : ContinuousWithinAt (fun z : E =>
              F ((extChartAt IX p0).symm z)) (Set.range IX) z0 :=
            hF.continuous.continuousWithinAt.comp hsymmCont (t := Set.univ) (by
              intro y hy
              trivial)
          have hcontQ : ContinuousWithinAt (fun z : E =>
              (⟨F ((extChartAt IX p0).symm z), hFa _⟩ : LevelSetSpace f a)) (Set.range IX) z0 :=
            (Continuous.subtype_mk hF.continuous (fun _ => hFa _)).continuousWithinAt.comp
              hsymmCont (t := Set.univ) (by
              intro y hy
              trivial)
          have hsrcPreim : (fun z : E =>
              F ((extChartAt IX p0).symm z)) ⁻¹' (extChartAt I x0.1).source ∈ nhdsWithin z0 (Set.range IX) := by
            have hsrcMem : F ((extChartAt IX p0).symm z0) ∈ (extChartAt I x0.1).source := by
              rw [hsymmVal']
              exact hsrcMem0
            have hsnhd : (extChartAt I x0.1).source ∈ nhds
                (F ((extChartAt IX p0).symm z0)) := by
              exact (isOpen_extChartAt_source (I := I) x0.1).mem_nhds hsrcMem
            exact Filter.tendsto_def.mp hcont (extChartAt I x0.1).source hsnhd
          have hsrcNhd' : (extChartAt I x0.1)
              (F ((extChartAt IX p0).symm z0)) ∈ Metric.ball ((extChartAt I x0.1) x0.1) b.rIn := by
            rw [hsymmVal']
            exact hsrcNhd
          have hpreim : (fun z : E => (extChartAt I x0.1)
              (F ((extChartAt IX p0).symm z))) ⁻¹' Metric.ball ((extChartAt I x0.1) x0.1) b.rIn ∈ nhdsWithin z0 (Set.range IX) := by
            exact ContinuousWithinAt.preimage_mem_nhdsWithin (hchartAtZ0.continuousWithinAt)
              ((Metric.isOpen_ball).mem_nhds hsrcNhd')
          have hsrcChartNhd : (manifoldLevelSetChart I f a hf hreg x0).source ∈ nhds
              (⟨F p0, hFa p0⟩ : LevelSetSpace f a) := by
            exact (manifoldLevelSetChart I f a hf hreg x0).open_source.mem_nhds
              (mem_manifoldLevelSetChart_source I f a hf hreg x0)
          have hq0eq : (⟨F ((extChartAt IX p0).symm z0), hFa _⟩ : LevelSetSpace f a) =
              ⟨F p0, hFa p0⟩ := by
            congr 1
            rw [show (extChartAt IX p0).symm z0 = p0 by
              dsimp [z0]
              exact (extChartAt IX p0).left_inv (mem_extChartAt_source (I := IX) p0)]
          have hsrcChartPreim : (fun z : E =>
              (⟨F ((extChartAt IX p0).symm z), hFa _⟩ : LevelSetSpace f a)) ⁻¹'
                (manifoldLevelSetChart I f a hf hreg x0).source ∈ nhdsWithin z0 (Set.range IX) := by
            exact Filter.tendsto_def.mp hcontQ (manifoldLevelSetChart I f a hf hreg x0).source
              (by
                change (manifoldLevelSetChart I f a hf hreg x0).source ∈
                  nhds (⟨F ((extChartAt IX p0).symm z0), hFa _⟩ : LevelSetSpace f a)
                rw [hq0eq]
                exact hsrcChartNhd)
          have hA : (fun z : E =>
              (⟨F ((extChartAt IX p0).symm z), hFa _⟩ : LevelSetSpace f a)) ⁻¹'
                (manifoldLevelSetChart I f a hf hreg x0).source ∈ nhdsWithin z0 (Set.range IX) := hsrcChartPreim
          have hB : (fun z : E =>
              F ((extChartAt IX p0).symm z)) ⁻¹' (extChartAt I x0.1).source ∈ nhdsWithin z0 (Set.range IX) := hsrcPreim
          have hC : (fun z : E =>
              (extChartAt I x0.1) (F ((extChartAt IX p0).symm z))) ⁻¹'
                Metric.ball ((extChartAt I x0.1) x0.1) b.rIn ∈ nhdsWithin z0 (Set.range IX) := hpreim
          have hall : {z : E |
              (⟨F ((extChartAt IX p0).symm z), hFa _⟩ : LevelSetSpace f a) ∈
                (manifoldLevelSetChart I f a hf hreg x0).source ∧
              F ((extChartAt IX p0).symm z) ∈ (extChartAt I x0.1).source ∧
              (extChartAt I x0.1) (F ((extChartAt IX p0).symm z)) ∈
                Metric.ball ((extChartAt I x0.1) x0.1) b.rIn} ∈ nhdsWithin z0 (Set.range IX) := by
            exact Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem hA hB) hC) (by
              intro z hz
              exact ⟨hz.1.1, hz.1.2, hz.2⟩)
          simpa using hall
        refine Filter.eventuallyEq_of_mem hqNhd ?_
        intro z hz
        change (extChartAt (𝓘(ℝ, MorseModel m)) x0) ⟨F ((extChartAt IX p0).symm z), hFa _⟩ = Fhat z
        have hchartX0' : (extChartAt (𝓘(ℝ, MorseModel m)) x0) =
            (manifoldLevelSetChart I f a hf hreg x0 : OpenPartialHomeomorph (LevelSetSpace f a) (MorseModel m)).toPartialEquiv := by
          simpa [extChartAt, OpenPartialHomeomorph.extend] using
            congrArg OpenPartialHomeomorph.toPartialEquiv (hchart x0)
        rw [hchartX0']
        dsimp [Fhat, V]
        change (manifoldLevelSetChart I f a hf hreg x0 ⟨F ((extChartAt IX p0).symm z), hFa _⟩) =
          levelSetChartValue g a p hg hr ((extChartAt I x0.1) (F ((extChartAt IX p0).symm z)))
        let e : OpenPartialHomeomorph (LevelSetSpace f a) (LevelSetSpace g a) :=
          levelSetPullbackChart I f a x0 b hb
        let mc : OpenPartialHomeomorph (LevelSetSpace g a) (MorseModel m) :=
          levelSetChart g a p hg hr
        have hmanifold : (manifoldLevelSetChart I f a hf hreg x0) = e ≫ₕ mc := rfl
        rw [hmanifold]
        have hq : (⟨F ((extChartAt IX p0).symm z), hFa _⟩ : LevelSetSpace f a) ∈ e.source := by
          dsimp [e, levelSetPullbackChart]
          exact hz.2
        have heval : (e ⟨F ((extChartAt IX p0).symm z), hFa _⟩).1 =
            (extChartAt I x0.1) (F ((extChartAt IX p0).symm z)) := by
          exact levelSetPullbackChart_apply_of_mem I f a x0 b hb hq
        have hmc : (e ⟨F ((extChartAt IX p0).symm z), hFa _⟩) ∈ mc.source := by
          have hsrcFull : (⟨F ((extChartAt IX p0).symm z), hFa _⟩ : LevelSetSpace f a) ∈
              (manifoldLevelSetChart I f a hf hreg x0).source := hz.1
          exact hsrcFull.2
        have hmcval : ((mc (e ⟨F ((extChartAt IX p0).symm z), hFa _⟩)) : MorseModel m) =
            levelSetChartValue g a p hg hr
              ((e ⟨F ((extChartAt IX p0).symm z), hFa _⟩).1) := by
          exact levelSetChart_apply_value' g a p hg hr (e ⟨F ((extChartAt IX p0).symm z), hFa _⟩)
        rw [heval] at hmcval
        exact hmcval
      have hz0mem : z0 ∈ Set.range IX := by
        simpa [ModelWithCorners.range_eq_target] using hz0.1
      exact ContDiffWithinAt.congr_of_eventuallyEq_of_mem hFhatAt hFhateq hz0mem
    simpa [Fhat, z0, x0, modelWithCornersSelf, ModelWithCorners.ofTargetUniv] using hchartRep

noncomputable def levelSetCollarMap [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) {a b : ℝ}
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v)) :
    LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) → M :=
  fun p => curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.1.1 (-(p.2 : ℝ))

theorem contMDiff_levelSetSublevelInclusion {m : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hcs₁ : ChartedSpace (MorseModel m) (LevelSetSpace f a) :=
      manifoldLevelSetChartedSpace I f a hf hreg)
    (hchart₁ : ∀ x : LevelSetSpace f a, hcs₁.chartAt x = manifoldLevelSetChart I f a hf hreg x := by
      intro x
      rfl)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f a) :=
      manifoldSublevelChartedSpace I f a hf hreg)
    (hchart₂ : ∀ x : SublevelSpace f a, hcs₂.chartAt x =
      (if hx : f x.1 = a then manifoldSublevelBoundaryChart I f a x hx hf hreg
        else manifoldSublevelInteriorChart I f a x (lt_of_le_of_ne (show f x.1 ≤ a from x.2) hx) hf) := by
      intro x
      rfl) :
    ContMDiff (𝓘(ℝ, MorseModel m)) (morseModelWithCornersHalfSpace m) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : LevelSetSpace f a => (⟨x.1, (le_of_eq x.2 : f x.1 ≤ a)⟩ : SublevelSpace f a)) := by
  classical
  letI := hcs₁
  letI := hcs₂
  intro x
  rw [contMDiffAt_iff]
  constructor
  · exact (Continuous.subtype_mk continuous_subtype_val (fun y => (le_of_eq y.2 : f y.1 ≤ a))).continuousAt
  · let b : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
    let hb : Metric.closedBall ((extChartAt I x.1) x.1) b.rOut ⊆ (extChartAt I x.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x.1
    let g : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x.1 b
    let x' : SublevelSpace f a := ⟨x.1, (le_of_eq x.2 : f x.1 ≤ a)⟩
    let p : LevelSetSpace g a := levelSetPullbackCutoffPoint I f a x b
    let p' : SublevelSpace g a := sublevelPullbackCutoffPoint I f a x' b
    let hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_sublevelPullbackCutoff I f hf x.1 b hb
    let hr : fderiv ℝ g p.1 ≠ 0 := fderiv_levelSetPullbackCutoffPoint_ne_zero I f hf a hreg x b
    let c₁ : OpenPartialHomeomorph (LevelSetSpace f a) (MorseModel m) :=
      manifoldLevelSetChart I f a hf hreg x
    let c₂ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) :=
      manifoldSublevelBoundaryChart I f a x' x.2 hf hreg
    let e₁ : OpenPartialHomeomorph (LevelSetSpace f a) (LevelSetSpace g a) :=
      levelSetPullbackChart I f a x b hb
    let e₂ : OpenPartialHomeomorph (SublevelSpace f a) (SublevelSpace g a) :=
      sublevelPullbackChart I f a x' b hb
    let mc : OpenPartialHomeomorph (LevelSetSpace g a) (MorseModel m) :=
      levelSetChart g a p hg hr
    let sc : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
      sublevelBoundaryChart g a p' (sublevelPullbackCutoffPoint_value I f a x' b x.2) hg
        (fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x' b x.2)
    let F : MorseModel m → MorseModel (m + 1) :=
      fun z => (extChartAt (morseModelWithCornersHalfSpace m) x')
        ((⟨((extChartAt (𝓘(ℝ, MorseModel m)) x).symm z : LevelSetSpace f a).1,
            (le_of_eq ((extChartAt (𝓘(ℝ, MorseModel m)) x).symm z : LevelSetSpace f a).2 :
              f (((extChartAt (𝓘(ℝ, MorseModel m)) x).symm z : LevelSetSpace f a).1) ≤ a)⟩ :
          SublevelSpace f a))
    let z₀ : MorseModel m := (extChartAt (𝓘(ℝ, MorseModel m)) x) x
    have hchart₁' : (hcs₁.chartAt x) = c₁ := by
      rw [hchart₁ x]
    have hchart₂' : (hcs₂.chartAt x') = c₂ := by
      rw [hchart₂ x']
      rw [dif_pos x.2]
    have hz₀ : z₀ ∈ c₁.target := by
      have hval₀ : c₁ x ∈ c₁.target := c₁.map_source (mem_manifoldLevelSetChart_source I f a hf hreg x)
      dsimp [z₀]
      simpa [hchart₁ x] using hval₀
    have hF_eq : ∀ z ∈ c₁.target, F z = levelSetSplit m (z, 0) := by
      intro z hz
      have hz₁ : z ∈ mc.target := by
        dsimp [c₁, manifoldLevelSetChart] at hz
        exact hz.1
      have hze : mc.symm z ∈ e₁.target := by
        dsimp [c₁, manifoldLevelSetChart] at hz
        exact hz.2
      have hzball : (mc.symm z).1 ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
        simpa [e₁, levelSetPullbackChart] using hze
      have hzt : (mc.symm z).1 ∈ (extChartAt I x.1).target :=
        ((Metric.ball_subset_ball (le_of_lt b.rIn_lt_rOut)).trans
          Metric.ball_subset_closedBall).trans hb hzball
      have hsymm₁ := levelSetChart_symm_value' g a p hg hr hz₁
      have hsymm₂ := levelSetPullbackChart_symm_value I f a x b hb hze
      have hiv : g (mc.symm z).1 = a := (mc.symm z).2
      have hp'₁ : p'.1 = p.1 := by
        dsimp [p', p, x']
        rfl
      have hc₁inv : (c₁.symm z).1 = (extChartAt I x.1).symm ((mc.symm z).1) := by
        have hc : c₁.symm z = e₁.symm (mc.symm z) := by
          dsimp [c₁, e₁, mc, manifoldLevelSetChart]
        rw [hc]
        rw [hsymm₂]
      have hzsrc₁ : c₁.symm z ∈ c₁.source := by exact c₁.symm.map_source hz
      have hzsrc₁e : c₁.symm z ∈ e₁.source := by
        dsimp [c₁, manifoldLevelSetChart] at hzsrc₁
        exact hzsrc₁.1
      have hconds : (c₁.symm z).1 ∈ (extChartAt I x.1).source ∧
          (extChartAt I x.1) ((c₁.symm z).1) ∈ Metric.ball ((extChartAt I x.1) x.1) b.rIn := by
        simpa [e₁, levelSetPullbackChart] using hzsrc₁e
      have hmap_src : (⟨(c₁.symm z).1, (le_of_eq (c₁.symm z).2 : f (c₁.symm z).1 ≤ a)⟩ : SublevelSpace f a) ∈ e₂.source := by
        simpa [e₂, sublevelPullbackChart, e₁, levelSetPullbackChart, hc₁inv, x'] using hzsrc₁e
      have he₂val : (e₂ (⟨(c₁.symm z).1, (le_of_eq (c₁.symm z).2 : f (c₁.symm z).1 ≤ a)⟩ : SublevelSpace f a)).1 =
          (mc.symm z).1 := by
        rw [sublevelPullbackChart_apply_of_mem I f a x' b hb hmap_src]
        rw [hc₁inv]
        exact (extChartAt I x.1).right_inv hzt
      have hsc_src : e₂ (⟨(c₁.symm z).1, (le_of_eq (c₁.symm z).2 : f (c₁.symm z).1 ≤ a)⟩ : SublevelSpace f a) ∈ sc.source := by
        have hzsrc₀ : mc.symm z ∈ mc.source := mc.symm.map_source hz₁
        dsimp [sc, sublevelBoundaryChart] at hzsrc₀ ⊢
        simpa [he₂val, p'] using hzsrc₀
      have hsc_val : (sc (e₂ (⟨(c₁.symm z).1, (le_of_eq (c₁.symm z).2 : f (c₁.symm z).1 ≤ a)⟩ : SublevelSpace f a)) :
          MorseModel (m + 1)) = levelSetSplit m (z, 0) := by
        have hgval : g (e₂ (⟨(c₁.symm z).1, (le_of_eq (c₁.symm z).2 : f (c₁.symm z).1 ≤ a)⟩ : SublevelSpace f a)).1 = a := by
          rw [he₂val]
          exact hiv
        have hbound := sublevelBoundaryChart_boundary_eq_levelSetSplit g a p'
          (sublevelPullbackCutoffPoint_value I f a x' b x.2) hg
          (fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x' b x.2)
          (e₂ (⟨(c₁.symm z).1, (le_of_eq (c₁.symm z).2 : f (c₁.symm z).1 ≤ a)⟩ : SublevelSpace f a)) hgval
        rw [hbound]
        have hlevel : mc (⟨(e₂ (⟨(c₁.symm z).1, (le_of_eq (c₁.symm z).2 : f (c₁.symm z).1 ≤ a)⟩ : SublevelSpace f a)).1, hgval⟩ :
            LevelSetSpace g a) = z := by
          have hval : (⟨(e₂ (⟨(c₁.symm z).1, (le_of_eq (c₁.symm z).2 : f (c₁.symm z).1 ≤ a)⟩ : SublevelSpace f a)).1, hgval⟩ :
              LevelSetSpace g a) = mc.symm z := by
            apply Subtype.ext
            exact he₂val
          rw [hval]
          exact mc.right_inv hz₁
        rw [levelSetChart_apply_value' g a ⟨p'.1, (sublevelPullbackCutoffPoint_value I f a x' b x.2)⟩ hg
          (fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg x' b x.2)
          (⟨(e₂ (⟨(c₁.symm z).1, (le_of_eq (c₁.symm z).2 : f (c₁.symm z).1 ≤ a)⟩ : SublevelSpace f a)).1, hgval⟩ :
            LevelSetSpace g a)]
        exact congrArg (fun w : MorseModel m => levelSetSplit m (w, 0)) hlevel
      dsimp [F]
      change (extChartAt (morseModelWithCornersHalfSpace m) x')
        (⟨((extChartAt (𝓘(ℝ, MorseModel m)) x).symm z : LevelSetSpace f a).1,
          (le_of_eq ((extChartAt (𝓘(ℝ, MorseModel m)) x).symm z : LevelSetSpace f a).2 :
            f (((extChartAt (𝓘(ℝ, MorseModel m)) x).symm z : LevelSetSpace f a).1) ≤ a)⟩ :
          SublevelSpace f a) = levelSetSplit m (z, 0)
      have hsymm₀ : (extChartAt (𝓘(ℝ, MorseModel m)) x).symm z = c₁.symm z := by
        change (hcs₁.chartAt x).symm z = c₁.symm z
        rw [hchart₁ x]
      rw [hsymm₀]
      simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
        ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe, Function.comp_apply,
        hchart₂']
      dsimp [c₂, manifoldSublevelBoundaryChart, e₂, sublevelPullbackChart, sc, sublevelBoundaryChart]
      change (sc (e₂ (⟨(c₁.symm z).1, (le_of_eq (c₁.symm z).2 : f (c₁.symm z).1 ≤ a)⟩ : SublevelSpace f a)) :
          MorseModel (m + 1)) = levelSetSplit m (z, 0)
      simpa using hsc_val
    have hFAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : MorseModel m => levelSetSplit m (z, (0 : ℝ))) z₀ := by
      have hlin : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun z : MorseModel m × ℝ => levelSetSplit m z) (z₀, 0) :=
        (levelSetSplit m).toContinuousLinearEquiv.contDiff.contDiffAt
      have hpair : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : MorseModel m => (z, (0 : ℝ))) z₀ := by
        fun_prop
      simpa using (hlin.comp z₀ hpair)
    have hmain : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun z : MorseModel m => levelSetSplit m (z, (0 : ℝ)))
        (Set.range (𝓘(ℝ, MorseModel m))) z₀ := by
      simpa using hFAt.contDiffWithinAt
    have heq : F =ᶠ[nhdsWithin z₀ (Set.range (𝓘(ℝ, MorseModel m)))]
        (fun z : MorseModel m => levelSetSplit m (z, (0 : ℝ))) := by
      simpa using (Filter.mem_of_superset (c₁.open_target.mem_nhds hz₀) (by
        intro z hz
        exact hF_eq z hz))
    have hrep : ContDiffWithinAt ℝ (⊤ : ℕ∞) F (Set.range (𝓘(ℝ, MorseModel m))) z₀ := by
      exact hmain.congr_of_eventuallyEq heq (hF_eq z₀ hz₀)
    simpa [F] using hrep

theorem contMDiff_levelSetCollarMap [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (f : M → ℝ) (a : ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x) {b : ℝ} [Fact (0 < b - a)]
    (v : (x : M) → TangentSpace I x)
    (hv : ContMDiff I (I.prod 𝓘(ℝ, MorseModel (m + 1))) (⊤ : ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport v))
    (hcs : ChartedSpace (MorseModel m) (LevelSetSpace f a) :=
      manifoldLevelSetChartedSpace I f a hf hreg)
    (hchart : ∀ x : LevelSetSpace f a, hcs.chartAt x = manifoldLevelSetChart I f a hf hreg x := by
      intro x
      rfl) :
    ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (levelSetCollarMap I f v hv hsupp :
        LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) → M) := by
  classical
  letI := hcs
  have hflow : ContMDiff (𝓘(ℝ, ℝ).prod I) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M => curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.2 p.1) :=
    contMDiff_globalFlow_joint_of_compactSupport (E := MorseModel (m + 1)) (I := I)
      (v := v) (hv := hv) (hsupp := hsupp)
  have hinc : ContMDiff (𝓘(ℝ, MorseModel m)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : LevelSetSpace f a => x.1) :=
    contMDiff_levelSetInclusion I f a hf hreg hcs hchart
  have hproj₁ : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (𝓘(ℝ, MorseModel m))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) => p.1) :=
    contMDiff_fst (I := 𝓘(ℝ, MorseModel m)) (J := 𝓡∂ 1) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hproj₂ : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (𝓡∂ 1)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) => p.2) :=
    contMDiff_snd (I := 𝓘(ℝ, MorseModel m)) (J := 𝓡∂ 1) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hcoe : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : Set.Icc (0 : ℝ) (b - a) => (t : ℝ)) :=
    contMDiff_subtype_coe_Icc (x := (0 : ℝ)) (y := b - a) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hneg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ => -r) := by
    exact (contDiff_neg : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => -r)).contMDiff
  have h₂ : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun p : LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) =>
        -(p.2 : ℝ)) :=
    hneg.comp (hcoe.comp hproj₂)
  have h₁ : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) (𝓘(ℝ, ℝ).prod I)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) => (-(p.2 : ℝ), p.1.1)) :=
    h₂.prodMk (hinc.comp hproj₁)
  have hcollar : ContMDiff ((𝓘(ℝ, MorseModel m)).prod (𝓡∂ 1)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : LevelSetSpace f a × Set.Icc (0 : ℝ) (b - a) =>
        curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) p.1.1 (-(p.2 : ℝ))) :=
    hflow.comp h₁
  simpa [levelSetCollarMap] using hcollar

theorem contMDiffAt_manifoldSublevelBoundaryMap [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (g₁ g₂ : M → ℝ) (a₁ a₂ : ℝ)
    (hg₁ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₁)
    (hg₂ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₂)
    (hreg₁ : ∀ x : M, g₁ x = a₁ → ¬ IsCriticalPointAt I g₁ x)
    (hreg₂ : ∀ x : M, g₂ x = a₂ → ¬ IsCriticalPointAt I g₂ x)
    (x : SublevelSpace g₁ a₁) (hx : g₁ x.1 = a₁)
    (Φ : M → M) (hΦ : ContMDiff I I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hmap : ∀ y : M, g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    (hbndx : g₂ (Φ x.1) = a₂)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₁ a₁) :=
      manifoldSublevelChartedSpace I g₁ a₁ hg₁ hreg₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₂ a₂) :=
      manifoldSublevelChartedSpace I g₂ a₂ hg₂ hreg₂)
    (hchart₁ : ∀ y : SublevelSpace g₁ a₁, hcs₁.chartAt y =
      (if h : g₁ y.1 = a₁ then manifoldSublevelBoundaryChart I g₁ a₁ y h hg₁ hreg₁
        else manifoldSublevelInteriorChart I g₁ a₁ y (lt_of_le_of_ne (show g₁ y.1 ≤ a₁ from y.2) h) hg₁) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g₂ a₂, hcs₂.chartAt y =
      (if h : g₂ y.1 = a₂ then manifoldSublevelBoundaryChart I g₂ a₂ y h hg₂ hreg₂
        else manifoldSublevelInteriorChart I g₂ a₂ y (lt_of_le_of_ne (show g₂ y.1 ≤ a₂ from y.2) h) hg₂) := by
      intro y
      rfl) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) x := by
  classical
  letI := hcs₁
  letI := hcs₂
  rw [contMDiffAt_iff]
  constructor
  · have hcont : Continuous (fun y : SublevelSpace g₁ a₁ => Φ y.1) :=
      hΦ.continuous.comp continuous_subtype_val
    exact (Continuous.subtype_mk hcont (fun y => hmap y.1 y.2)).continuousAt
  · let x₂ : SublevelSpace g₂ a₂ := ⟨Φ x.1, hmap x.1 x.2⟩
    let hx₂ : g₂ x₂.1 = a₂ := hbndx
    let c₁ : OpenPartialHomeomorph (SublevelSpace g₁ a₁) (MorseHalfSpace m) :=
      manifoldSublevelBoundaryChart I g₁ a₁ x hx hg₁ hreg₁
    let c₂ : OpenPartialHomeomorph (SublevelSpace g₂ a₂) (MorseHalfSpace m) :=
      manifoldSublevelBoundaryChart I g₂ a₂ x₂ hx₂ hg₂ hreg₂
    have hchart₁' : hcs₁.chartAt x = c₁ := by
      rw [hchart₁ x]
      rw [dif_pos hx]
    have hchart₂' : hcs₂.chartAt x₂ = c₂ := by
      rw [hchart₂ x₂]
      rw [dif_pos hx₂]
    let b₁ : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
    let hb₁ : Metric.closedBall ((extChartAt I x.1) x.1) b₁.rOut ⊆ (extChartAt I x.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x.1
    let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
    let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x₂.1
    let g₁c : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I g₁ x.1 b₁
    let g₂c : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I g₂ x₂.1 b₂
    let p₁ : SublevelSpace g₁c a₁ := sublevelPullbackCutoffPoint I g₁ a₁ x b₁
    let p₂ : SublevelSpace g₂c a₂ := sublevelPullbackCutoffPoint I g₂ a₂ x₂ b₂
    let hg₁c : ContDiff ℝ (⊤ : ℕ∞) g₁c := contDiff_sublevelPullbackCutoff I g₁ hg₁ x.1 b₁ hb₁
    let hg₂c : ContDiff ℝ (⊤ : ℕ∞) g₂c := contDiff_sublevelPullbackCutoff I g₂ hg₂ x₂.1 b₂ hb₂
    let hr₁c : fderiv ℝ g₁c p₁.1 ≠ 0 :=
      fderiv_sublevelPullbackCutoffPoint_ne_zero I g₁ hg₁ a₁ hreg₁ x b₁ hx
    let hr₂c : fderiv ℝ g₂c p₂.1 ≠ 0 :=
      fderiv_sublevelPullbackCutoffPoint_ne_zero I g₂ hg₂ a₂ hreg₂ x₂ b₂ hx₂
    let mb₁ : OpenPartialHomeomorph (SublevelSpace g₁c a₁) (MorseHalfSpace m) :=
      sublevelBoundaryChart g₁c a₁ p₁ (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c
    let mb₂ : OpenPartialHomeomorph (SublevelSpace g₂c a₂) (MorseHalfSpace m) :=
      sublevelBoundaryChart g₂c a₂ p₂ (sublevelPullbackCutoffPoint_value I g₂ a₂ x₂ b₂ hx₂) hg₂c hr₂c
    let pb₁ : OpenPartialHomeomorph (SublevelSpace g₁ a₁) (SublevelSpace g₁c a₁) :=
      sublevelPullbackChart I g₁ a₁ x b₁ hb₁
    let pb₂ : OpenPartialHomeomorph (SublevelSpace g₂ a₂) (SublevelSpace g₂c a₂) :=
      sublevelPullbackChart I g₂ a₂ x₂ b₂ hb₂
    let ψ₁ : MorseModel (m + 1) → MorseModel (m + 1) :=
      sublevelBoundaryChartInvValueRaw g₁c a₁ p₁ (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c
    let ψ₂ : MorseModel (m + 1) → MorseModel (m + 1) :=
      sublevelBoundaryChartValue g₂c a₂ p₂ (sublevelPullbackCutoffPoint_value I g₂ a₂ x₂ b₂ hx₂) hg₂c hr₂c
    let D₁ : Set (MorseModel (m + 1)) := sublevelBoundaryChartDomain g₁c a₁ p₁
      (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c
    let Φc : MorseModel (m + 1) → MorseModel (m + 1) :=
      fun y => (extChartAt I x₂.1) (Φ ((extChartAt I x.1).symm y))
    let F : MorseModel (m + 1) → MorseModel (m + 1) := fun z => ψ₂ (Φc (ψ₁ z))
    have hpb₁src : x ∈ pb₁.source := mem_sublevelPullbackChart_source I g₁ a₁ x b₁ hb₁
    have hpb₁val : (pb₁ x).1 = (extChartAt I x.1) x.1 := by
      exact sublevelPullbackChart_apply_of_mem I g₁ a₁ x b₁ hb₁ hpb₁src
    have hmb₁x : mb₁ (pb₁ x) = c₁ x := rfl
    have hz₀ : (extChartAt (morseModelWithCornersHalfSpace m) x x) =
        (morseModelWithCornersHalfSpace m) (c₁ x) := by
      simp [extChartAt, hchart₁']
    have hz₀range : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
        Set.range (morseModelWithCornersHalfSpace m) := by
      simp [extChartAt, hchart₁']
    have hz₀D₁ : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈ D₁ := by
      have hsrc : x ∈ c₁.source := mem_manifoldSublevelBoundaryChart_source I g₁ a₁ x hx hg₁ hreg₁
      have htgt : (c₁ x : MorseHalfSpace m) ∈ c₁.target := c₁.map_source hsrc
      have hmb₁tgt' : (c₁ x : MorseHalfSpace m) ∈ mb₁.target := by
        have hsplit := (by simpa [c₁, manifoldSublevelBoundaryChart] using htgt)
        exact hsplit.1
      simpa [extChartAt, hchart₁', D₁, sublevelBoundaryChartDomain] using hmb₁tgt'
    have hψ₁cd : ContDiffOn ℝ (⊤ : ℕ∞) ψ₁ D₁ :=
      contDiffOn_sublevelBoundaryChartInvValueRaw g₁c a₁ p₁
        (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c
    have hψ₁At : ContDiffAt ℝ (⊤ : ℕ∞) ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      hψ₁cd.contDiffAt ((isOpen_sublevelBoundaryChartDomain g₁c a₁ p₁
        (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c).mem_nhds hz₀D₁)
    have hψ₁z₀ : ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x) = (extChartAt I x.1) x.1 := by
      have hu : (c₁ x : MorseHalfSpace m) ∈ mb₁.target := by
        have hsrc : x ∈ c₁.source := mem_manifoldSublevelBoundaryChart_source I g₁ a₁ x hx hg₁ hreg₁
        have htgt : (c₁ x : MorseHalfSpace m) ∈ c₁.target := c₁.map_source hsrc
        have hsplit := (by simpa [c₁, manifoldSublevelBoundaryChart] using htgt)
        exact hsplit.1
      have hsm := sublevelBoundaryChart_symm_value g₁c a₁ p₁
        (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c hu
      have hsymm : (mb₁.symm (c₁ x : MorseHalfSpace m) : SublevelSpace g₁c a₁).1 = ψ₁ (c₁ x : MorseHalfSpace m) := by
        simpa [ψ₁] using congrArg Subtype.val hsm
      rw [hz₀]
      change ψ₁ (c₁ x : MorseHalfSpace m) = (extChartAt I x.1) x.1
      rw [← hsymm]
      have hleft : mb₁.symm (c₁ x : MorseHalfSpace m) = pb₁ x := by
        have hpb₁eq : pb₁ x = p₁ := by
          apply Subtype.ext
          simpa [p₁] using hpb₁val
        have hsrc' : (pb₁ x) ∈ mb₁.source := by
          rw [hpb₁eq]
          exact mem_sublevelBoundaryChart_source g₁c a₁ p₁
            (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c
        exact mb₁.left_inv hsrc'
      rw [hleft]
      exact hpb₁val
    have hΦcAt : ContDiffAt ℝ (⊤ : ℕ∞) Φc (ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x)) :=
      by
        have hiff := (contMDiffAt_iff (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).mp (hΦ x.1)
        have hcw : ContDiffWithinAt ℝ (⊤ : ℕ∞) Φc (Set.range I)
            (extChartAt I x.1 x.1) := by
          simpa [Φc] using hiff.2
        have hrng : Set.range I = Set.univ := ModelWithCorners.Boundaryless.range_eq_univ
        have hcwa : ContDiffAt ℝ (⊤ : ℕ∞) Φc
            (ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x)) := by
          rw [hψ₁z₀]
          rw [hrng] at hcw
          exact contDiffWithinAt_univ.mp hcw
        exact hcwa
    have hψ₂cd : ContDiff ℝ (⊤ : ℕ∞) ψ₂ :=
      contDiff_sublevelBoundaryChartValue g₂c a₂ p₂
        (sublevelPullbackCutoffPoint_value I g₂ a₂ x₂ b₂ hx₂) hg₂c hr₂c
    have hFAt : ContDiffAt ℝ (⊤ : ℕ∞) F (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      have hmid : ContDiffAt ℝ (⊤ : ℕ∞) (Φc ∘ ψ₁)
          (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
        ContDiffAt.comp (x := extChartAt (morseModelWithCornersHalfSpace m) x x) hΦcAt hψ₁At
      have hψ₂At : ContDiffAt ℝ (⊤ : ℕ∞) ψ₂
          ((Φc ∘ ψ₁) (extChartAt (morseModelWithCornersHalfSpace m) x x)) :=
        hψ₂cd.contDiffAt
      have hcomp := ContDiffAt.comp (x := extChartAt (morseModelWithCornersHalfSpace m) x x)
        hψ₂At hmid
      simpa [F, Function.comp_def] using hcomp
    have hFAt' : ContDiffWithinAt ℝ (⊤ : ℕ∞) F
        (Set.range (morseModelWithCornersHalfSpace m))
        (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      hFAt.contDiffWithinAt
    have hball₁ : Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∈
        nhds ((extChartAt I x.1) x.1) :=
      Metric.ball_mem_nhds ((extChartAt I x.1) x.1) b₁.rIn_pos
    have hball₂ : Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn ∈
        nhds ((extChartAt I x₂.1) x₂.1) :=
      Metric.ball_mem_nhds ((extChartAt I x₂.1) x₂.1) b₂.rIn_pos
    have hpre₁ : ψ₁ ⁻¹' Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      (ContDiffAt.continuousAt hψ₁At).preimage_mem_nhds (by rwa [hψ₁z₀])
    have hpre₂ : (fun z : MorseModel (m + 1) => Φc (ψ₁ z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      (ContDiffAt.continuousAt (ContDiffAt.comp (x := extChartAt (morseModelWithCornersHalfSpace m) x x)
        hΦcAt hψ₁At)).preimage_mem_nhds (by
        change Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn ∈
          nhds (Φc (ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x)))
        rw [hψ₁z₀]
        have hval : Φc ((extChartAt I x.1) x.1) = (extChartAt I x₂.1) (Φ x.1) := by
          dsimp [Φc]
          congr 2
          simp
        rw [hval]
        exact Metric.ball_mem_nhds ((extChartAt I x₂.1) x₂.1) b₂.rIn_pos)
    have hpre₃ : (fun z : MorseModel (m + 1) =>
          Φ ((extChartAt I x.1).symm (ψ₁ z)) ∈ (extChartAt I x₂.1).source) ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      let z₀ : MorseModel (m + 1) := extChartAt (morseModelWithCornersHalfSpace m) x x
      have hφ₁ : ContinuousAt (fun z : MorseModel (m + 1) =>
          (extChartAt I x.1).symm (ψ₁ z)) z₀ := by
        have hsm : ContinuousAt (extChartAt I x.1).symm (ψ₁ z₀) := by
          rw [hψ₁z₀]
          exact (continuousOn_extChartAt_symm x.1).continuousAt
            ((isOpen_extChartAt_target (I := I) x.1).mem_nhds
              ((extChartAt I x.1).map_source (mem_extChartAt_source (I := I) x.1)))
        exact hsm.comp (ContDiffAt.continuousAt hψ₁At)
      have hΦ₁ : ContinuousAt Φ ((extChartAt I x.1).symm (ψ₁ z₀)) :=
        hΦ.continuous.continuousAt
      have hmain : ContinuousAt (fun z : MorseModel (m + 1) =>
          Φ ((extChartAt I x.1).symm (ψ₁ z))) z₀ :=
        hΦ₁.comp (f := fun z : MorseModel (m + 1) => (extChartAt I x.1).symm (ψ₁ z)) (x := z₀) hφ₁
      have hmem : Φ ((extChartAt I x.1).symm (ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x))) ∈
          (extChartAt I x₂.1).source := by
        rw [hψ₁z₀, (extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
        exact mem_extChartAt_source (I := I) x₂.1
      exact hmain.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) x₂.1).mem_nhds hmem)
    have hnhd : D₁ ∩ (ψ₁ ⁻¹' Metric.ball ((extChartAt I x.1) x.1) b₁.rIn) ∩
        (((fun z : MorseModel (m + 1) => Φc (ψ₁ z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
          (fun z : MorseModel (m + 1) =>
            Φ ((extChartAt I x.1).symm (ψ₁ z)) ∈ (extChartAt I x₂.1).source)) ∩
        Set.range (morseModelWithCornersHalfSpace m) ∈
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m)) := by
      refine Filter.inter_mem ?_ ?_
      · refine Filter.inter_mem ?_ ?_
        · refine Filter.inter_mem ?_ ?_
          · exact nhdsWithin_le_nhds ((isOpen_sublevelBoundaryChartDomain g₁c a₁ p₁
              (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c).mem_nhds hz₀D₁)
          · exact nhdsWithin_le_nhds hpre₁
        · refine Filter.inter_mem ?_ ?_
          · exact nhdsWithin_le_nhds hpre₂
          · exact nhdsWithin_le_nhds hpre₃
      · exact self_mem_nhdsWithin
    have hval : ∀ z ∈ D₁ ∩ (ψ₁ ⁻¹' Metric.ball ((extChartAt I x.1) x.1) b₁.rIn) ∩
        (((fun z : MorseModel (m + 1) => Φc (ψ₁ z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
          (fun z : MorseModel (m + 1) =>
            Φ ((extChartAt I x.1).symm (ψ₁ z)) ∈ (extChartAt I x₂.1).source)) ∩
        Set.range (morseModelWithCornersHalfSpace m),
        (extChartAt (morseModelWithCornersHalfSpace m) x₂ ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          (extChartAt (morseModelWithCornersHalfSpace m) x).symm) z = F z := by
      intro z hz
      have hzD₁ : z ∈ D₁ := hz.1.1.1
      have hzψ₁ : ψ₁ z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn := hz.1.1.2
      have hzψ₂ : Φc (ψ₁ z) ∈ Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn := hz.1.2.1
      have hzsrc₂ : Φ ((extChartAt I x.1).symm (ψ₁ z)) ∈ (extChartAt I x₂.1).source := hz.1.2.2
      have hzrange : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.2
      have hzmem : 0 ≤ z (Fin.last m) := by
        rw [range_morseModelWithCornersHalfSpace] at hzrange
        exact hzrange
      change ((hcs₂.chartAt x₂).extend (morseModelWithCornersHalfSpace m) ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)).symm) z = F z
      rw [hchart₂']
      rw [hchart₁']
      simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
      change (morseModelWithCornersHalfSpace m)
          (c₂ ((fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂))
            (c₁.symm ((morseModelWithCornersHalfSpace m).symm z)))) = F z
      have hu : (morseModelWithCornersHalfSpace m).symm z = (⟨z, hzmem⟩ : MorseHalfSpace m) := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hzmem
      rw [hu]
      have hmb₁tgt : (⟨z, hzmem⟩ : MorseHalfSpace m) ∈ mb₁.target := by
        simpa [sublevelBoundaryChartDomain] using hzD₁
      have hmb₁sm := sublevelBoundaryChart_symm_value g₁c a₁ p₁
        (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c hmb₁tgt
      have hmb₁sm' : (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m) : SublevelSpace g₁c a₁).1 = ψ₁ z := by
        simpa [ψ₁] using congrArg Subtype.val hmb₁sm
      have hpb₁tgt : (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)) ∈ pb₁.target := by
        change (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 ∈
          Metric.ball ((extChartAt I x.1) x.1) b₁.rIn
        rwa [hmb₁sm']
      have hpb₁sm : (pb₁.symm (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m))).1 =
          (extChartAt I x.1).symm (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 :=
        sublevelPullbackChart_symm_value I g₁ a₁ x b₁ hb₁ hpb₁tgt
      have hc₁sm : (c₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 =
          (extChartAt I x.1).symm (ψ₁ z) := by
        change (pb₁.symm (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m))).1 =
          (extChartAt I x.1).symm (ψ₁ z)
        rw [hpb₁sm, hmb₁sm']
      let y₁ : SublevelSpace g₁ a₁ := c₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)
      let w₂ : SublevelSpace g₂ a₂ := ⟨Φ y₁.1, hmap y₁.1 y₁.2⟩
      have hΘ : y₁.1 = (extChartAt I x.1).symm (ψ₁ z) := hc₁sm
      have hpb₂src : w₂ ∈ pb₂.source := by
        change w₂.1 ∈ (extChartAt I x₂.1).source ∧ (extChartAt I x₂.1) w₂.1 ∈
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
        constructor
        · change Φ y₁.1 ∈ (extChartAt I x₂.1).source
          rw [hΘ]
          exact hzsrc₂
        · change (extChartAt I x₂.1) (Φ y₁.1) ∈
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
          rw [hΘ]
          exact hzψ₂
      have hpb₂val : (pb₂ w₂).1 = (extChartAt I x₂.1) w₂.1 :=
        sublevelPullbackChart_apply_of_mem I g₂ a₂ x₂ b₂ hb₂ hpb₂src
      have hmb₂val : (mb₂ (pb₂ w₂) : MorseModel (m + 1)) =
          sublevelBoundaryChartValue g₂c a₂ p₂
            (sublevelPullbackCutoffPoint_value I g₂ a₂ x₂ b₂ hx₂) hg₂c hr₂c
            ((extChartAt I x₂.1) w₂.1) := by
        rw [sublevelBoundaryChart_apply_value' g₂c a₂ p₂
          (sublevelPullbackCutoffPoint_value I g₂ a₂ x₂ b₂ hx₂) hg₂c hr₂c]
        rw [hpb₂val]
      change (morseModelWithCornersHalfSpace m)
          (mb₂ (pb₂ w₂)) = F z
      change (mb₂ (pb₂ w₂) : MorseModel (m + 1)) = F z
      rw [hmb₂val]
      dsimp [F]
      dsimp [w₂]
      rw [hΘ]
      dsimp [Φc]
    have hred : (extChartAt (morseModelWithCornersHalfSpace m) x₂ ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m))] F := by
      refine Filter.eventuallyEq_of_mem (s := D₁ ∩ (ψ₁ ⁻¹' Metric.ball ((extChartAt I x.1) x.1) b₁.rIn) ∩
        (((fun z : MorseModel (m + 1) => Φc (ψ₁ z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
          (fun z : MorseModel (m + 1) =>
            Φ ((extChartAt I x.1).symm (ψ₁ z)) ∈ (extChartAt I x₂.1).source)) ∩
        Set.range (morseModelWithCornersHalfSpace m)) hnhd ?_
      intro z hz
      exact hval z hz
    refine hFAt'.congr_of_eventuallyEq_of_mem ?_ hz₀range
    change ((extChartAt (morseModelWithCornersHalfSpace m)
        (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂)) ∘
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
      (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m))]
      (fun z : MorseModel (m + 1) => F z)
    simpa [extChartAt, hchart₁', hchart₂', x₂] using hred

theorem contMDiffAt_manifoldSublevelBoundaryToInteriorMap [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (g₁ g₂ : M → ℝ) (a₁ a₂ : ℝ)
    (hg₁ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₁)
    (hg₂ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₂)
    (hreg₁ : ∀ x : M, g₁ x = a₁ → ¬ IsCriticalPointAt I g₁ x)
    (hreg₂ : ∀ x : M, g₂ x = a₂ → ¬ IsCriticalPointAt I g₂ x)
    (x : SublevelSpace g₁ a₁) (hx : g₁ x.1 = a₁)
    (Φ : M → M) (hΦ : ContMDiff I I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hmap : ∀ y : M, g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    (hx₂lt : g₂ (Φ x.1) < a₂)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₁ a₁) :=
      manifoldSublevelChartedSpace I g₁ a₁ hg₁ hreg₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₂ a₂) :=
      manifoldSublevelChartedSpace I g₂ a₂ hg₂ hreg₂)
    (hchart₁ : ∀ y : SublevelSpace g₁ a₁, hcs₁.chartAt y =
      (if h : g₁ y.1 = a₁ then manifoldSublevelBoundaryChart I g₁ a₁ y h hg₁ hreg₁
        else manifoldSublevelInteriorChart I g₁ a₁ y (lt_of_le_of_ne (show g₁ y.1 ≤ a₁ from y.2) h) hg₁) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g₂ a₂, hcs₂.chartAt y =
      (if h : g₂ y.1 = a₂ then manifoldSublevelBoundaryChart I g₂ a₂ y h hg₂ hreg₂
        else manifoldSublevelInteriorChart I g₂ a₂ y (lt_of_le_of_ne (show g₂ y.1 ≤ a₂ from y.2) h) hg₂) := by
      intro y
      rfl) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) x := by
  classical
  letI := hcs₁
  letI := hcs₂
  rw [contMDiffAt_iff]
  constructor
  · have hcont : Continuous (fun y : SublevelSpace g₁ a₁ => Φ y.1) :=
      hΦ.continuous.comp continuous_subtype_val
    exact (Continuous.subtype_mk hcont (fun y => hmap y.1 y.2)).continuousAt
  · let x₂ : SublevelSpace g₂ a₂ := ⟨Φ x.1, hmap x.1 x.2⟩
    let hx₂lt' : g₂ x₂.1 < a₂ := hx₂lt
    let c₁ : OpenPartialHomeomorph (SublevelSpace g₁ a₁) (MorseHalfSpace m) :=
      manifoldSublevelBoundaryChart I g₁ a₁ x hx hg₁ hreg₁
    let c₂ : OpenPartialHomeomorph (SublevelSpace g₂ a₂) (MorseHalfSpace m) :=
      manifoldSublevelInteriorChart I g₂ a₂ x₂ hx₂lt' hg₂
    have hchart₁' : hcs₁.chartAt x = c₁ := by
      rw [hchart₁ x]
      rw [dif_pos hx]
    have hchart₂' : hcs₂.chartAt x₂ = c₂ := by
      rw [hchart₂ x₂]
      rw [dif_neg (ne_of_lt hx₂lt')]
    let b₁ : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
    let hb₁ : Metric.closedBall ((extChartAt I x.1) x.1) b₁.rOut ⊆ (extChartAt I x.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x.1
    let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
    let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x₂.1
    let g₁c : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I g₁ x.1 b₁
    let g₂c : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I g₂ x₂.1 b₂
    let p₁ : SublevelSpace g₁c a₁ := sublevelPullbackCutoffPoint I g₁ a₁ x b₁
    let p₂ : SublevelSpace g₂c a₂ := sublevelPullbackCutoffPoint I g₂ a₂ x₂ b₂
    let hg₁c : ContDiff ℝ (⊤ : ℕ∞) g₁c := contDiff_sublevelPullbackCutoff I g₁ hg₁ x.1 b₁ hb₁
    let hg₂c : ContDiff ℝ (⊤ : ℕ∞) g₂c := contDiff_sublevelPullbackCutoff I g₂ hg₂ x₂.1 b₂ hb₂
    let hr₁c : fderiv ℝ g₁c p₁.1 ≠ 0 :=
      fderiv_sublevelPullbackCutoffPoint_ne_zero I g₁ hg₁ a₁ hreg₁ x b₁ hx
    let mb₁ : OpenPartialHomeomorph (SublevelSpace g₁c a₁) (MorseHalfSpace m) :=
      sublevelBoundaryChart g₁c a₁ p₁ (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c
    let mi₂ : OpenPartialHomeomorph (SublevelSpace g₂c a₂) (MorseHalfSpace m) :=
      sublevelInteriorChart g₂c a₂ (sublevelPullbackCutoffPoint I g₂ a₂ x₂ b₂)
        (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt') hg₂c
    let s₂ : ℝ := sublevelInteriorShift g₂c a₂ p₂
      (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt') hg₂c
    let pb₁ : OpenPartialHomeomorph (SublevelSpace g₁ a₁) (SublevelSpace g₁c a₁) :=
      sublevelPullbackChart I g₁ a₁ x b₁ hb₁
    let pb₂ : OpenPartialHomeomorph (SublevelSpace g₂ a₂) (SublevelSpace g₂c a₂) :=
      sublevelPullbackChart I g₂ a₂ x₂ b₂ hb₂
    let ψ₁ : MorseModel (m + 1) → MorseModel (m + 1) :=
      sublevelBoundaryChartInvValueRaw g₁c a₁ p₁ (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c
    let D₁ : Set (MorseModel (m + 1)) := sublevelBoundaryChartDomain g₁c a₁ p₁
      (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c
    let Φc : MorseModel (m + 1) → MorseModel (m + 1) :=
      fun y => (extChartAt I x₂.1) (Φ ((extChartAt I x.1).symm y))
    let F : MorseModel (m + 1) → MorseModel (m + 1) := fun z => morseHalfSpaceShift s₂ (Φc (ψ₁ z))
    have hpb₁src : x ∈ pb₁.source := mem_sublevelPullbackChart_source I g₁ a₁ x b₁ hb₁
    have hpb₁val : (pb₁ x).1 = (extChartAt I x.1) x.1 := by
      exact sublevelPullbackChart_apply_of_mem I g₁ a₁ x b₁ hb₁ hpb₁src
    have hmb₁x : mb₁ (pb₁ x) = c₁ x := rfl
    have hz₀ : (extChartAt (morseModelWithCornersHalfSpace m) x x) =
        (morseModelWithCornersHalfSpace m) (c₁ x) := by
      simp [extChartAt, hchart₁']
    have hz₀range : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
        Set.range (morseModelWithCornersHalfSpace m) := by
      simp [extChartAt, hchart₁']
    have hz₀D₁ : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈ D₁ := by
      have hsrc : x ∈ c₁.source := mem_manifoldSublevelBoundaryChart_source I g₁ a₁ x hx hg₁ hreg₁
      have htgt : (c₁ x : MorseHalfSpace m) ∈ c₁.target := c₁.map_source hsrc
      have hmb₁tgt' : (c₁ x : MorseHalfSpace m) ∈ mb₁.target := by
        have hsplit := (by simpa [c₁, manifoldSublevelBoundaryChart] using htgt)
        exact hsplit.1
      simpa [extChartAt, hchart₁', D₁, sublevelBoundaryChartDomain] using hmb₁tgt'
    have hψ₁cd : ContDiffOn ℝ (⊤ : ℕ∞) ψ₁ D₁ :=
      contDiffOn_sublevelBoundaryChartInvValueRaw g₁c a₁ p₁
        (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c
    have hψ₁At : ContDiffAt ℝ (⊤ : ℕ∞) ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      hψ₁cd.contDiffAt ((isOpen_sublevelBoundaryChartDomain g₁c a₁ p₁
        (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c).mem_nhds hz₀D₁)
    have hψ₁z₀ : ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x) = (extChartAt I x.1) x.1 := by
      have hu : (c₁ x : MorseHalfSpace m) ∈ mb₁.target := by
        have hsrc : x ∈ c₁.source := mem_manifoldSublevelBoundaryChart_source I g₁ a₁ x hx hg₁ hreg₁
        have htgt : (c₁ x : MorseHalfSpace m) ∈ c₁.target := c₁.map_source hsrc
        have hsplit := (by simpa [c₁, manifoldSublevelBoundaryChart] using htgt)
        exact hsplit.1
      have hsm := sublevelBoundaryChart_symm_value g₁c a₁ p₁
        (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c hu
      have hsymm : (mb₁.symm (c₁ x : MorseHalfSpace m) : SublevelSpace g₁c a₁).1 = ψ₁ (c₁ x : MorseHalfSpace m) := by
        simpa [ψ₁] using congrArg Subtype.val hsm
      rw [hz₀]
      change ψ₁ (c₁ x : MorseHalfSpace m) = (extChartAt I x.1) x.1
      rw [← hsymm]
      have hleft : mb₁.symm (c₁ x : MorseHalfSpace m) = pb₁ x := by
        have hpb₁eq : pb₁ x = p₁ := by
          apply Subtype.ext
          simpa [p₁] using hpb₁val
        have hsrc' : (pb₁ x) ∈ mb₁.source := by
          rw [hpb₁eq]
          exact mem_sublevelBoundaryChart_source g₁c a₁ p₁
            (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c
        exact mb₁.left_inv hsrc'
      rw [hleft]
      exact hpb₁val
    have hΦcAt : ContDiffAt ℝ (⊤ : ℕ∞) Φc (ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x)) := by
      have hiff := (contMDiffAt_iff (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).mp (hΦ x.1)
      have hcw : ContDiffWithinAt ℝ (⊤ : ℕ∞) Φc (Set.range I)
          (extChartAt I x.1 x.1) := by
        simpa [Φc] using hiff.2
      have hrng : Set.range I = Set.univ := ModelWithCorners.Boundaryless.range_eq_univ
      have hcwa : ContDiffAt ℝ (⊤ : ℕ∞) Φc
          (ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x)) := by
        rw [hψ₁z₀]
        rw [hrng] at hcw
        exact contDiffWithinAt_univ.mp hcw
      exact hcwa
    have hmidAt : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z : MorseModel (m + 1) => Φc (ψ₁ z))
        (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      have hmidAt' : ContDiffAt ℝ (⊤ : ℕ∞)
          (Φc ∘ fun z : MorseModel (m + 1) => ψ₁ z)
          (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
        hΦcAt.comp (f := fun z : MorseModel (m + 1) => ψ₁ z)
          (x := extChartAt (morseModelWithCornersHalfSpace m) x x) hψ₁At
      simpa [Function.comp_def] using hmidAt'
    have hFAt : ContDiffAt ℝ (⊤ : ℕ∞) F (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      have hshift₂ : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => morseHalfSpaceShift s₂ y)
          (Φc (ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x))) :=
        (contDiff_morseHalfSpaceShift (m := m) s₂).contDiffAt
      have hcomp := ContDiffAt.comp (x := extChartAt (morseModelWithCornersHalfSpace m) x x)
        hshift₂ hmidAt
      simpa [F, Function.comp_def] using hcomp
    have hFAt' : ContDiffWithinAt ℝ (⊤ : ℕ∞) F
        (Set.range (morseModelWithCornersHalfSpace m))
        (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      hFAt.contDiffWithinAt
    have hball₁ : Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∈
        nhds ((extChartAt I x.1) x.1) :=
      Metric.ball_mem_nhds ((extChartAt I x.1) x.1) b₁.rIn_pos
    have hball₂ : Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn ∈
        nhds ((extChartAt I x₂.1) x₂.1) :=
      Metric.ball_mem_nhds ((extChartAt I x₂.1) x₂.1) b₂.rIn_pos
    have hpre₁ : ψ₁ ⁻¹' Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      (ContDiffAt.continuousAt hψ₁At).preimage_mem_nhds (by rwa [hψ₁z₀])
    have hpre₂ : (fun z : MorseModel (m + 1) => Φc (ψ₁ z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      (ContDiffAt.continuousAt hmidAt).preimage_mem_nhds (by
        change Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn ∈
          nhds (Φc (ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x)))
        rw [hψ₁z₀]
        have hval : Φc ((extChartAt I x.1) x.1) = (extChartAt I x₂.1) (Φ x.1) := by
          dsimp [Φc]
          congr 2
          simp
        rw [hval]
        exact Metric.ball_mem_nhds ((extChartAt I x₂.1) x₂.1) b₂.rIn_pos)
    have hpre₂r : (fun z : MorseModel (m + 1) =>
          Φc (ψ₁ z) ∈ Metric.ball p₂.1
            (sublevelInteriorRadius g₂c a₂ p₂
              (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt') hg₂c)) ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      (ContDiffAt.continuousAt hmidAt).preimage_mem_nhds (by
        change Metric.ball p₂.1 (sublevelInteriorRadius g₂c a₂ p₂
            (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt') hg₂c) ∈
          nhds (Φc (ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x)))
        rw [hψ₁z₀]
        have hval : Φc ((extChartAt I x.1) x.1) = (extChartAt I x₂.1) (Φ x.1) := by
          dsimp [Φc]
          congr 2
          simp
        rw [hval]
        have hρpos : 0 < sublevelInteriorRadius g₂c a₂ p₂
            (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt') hg₂c := by
          dsimp [sublevelInteriorRadius]
          exact (Classical.choose_spec (Metric.mem_nhds_iff.mp ((isOpen_Iio.preimage hg₂c.continuous).mem_nhds
            (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt')))).1
        exact Metric.ball_mem_nhds p₂.1 hρpos)
    have hpre₃ : (fun z : MorseModel (m + 1) =>
          Φ ((extChartAt I x.1).symm (ψ₁ z)) ∈ (extChartAt I x₂.1).source) ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      let z₀ : MorseModel (m + 1) := extChartAt (morseModelWithCornersHalfSpace m) x x
      have hφ₁ : ContinuousAt (fun z : MorseModel (m + 1) =>
          (extChartAt I x.1).symm (ψ₁ z)) z₀ := by
        have hsm : ContinuousAt (extChartAt I x.1).symm (ψ₁ z₀) := by
          rw [hψ₁z₀]
          exact (continuousOn_extChartAt_symm x.1).continuousAt
            ((isOpen_extChartAt_target (I := I) x.1).mem_nhds
              ((extChartAt I x.1).map_source (mem_extChartAt_source (I := I) x.1)))
        exact hsm.comp (ContDiffAt.continuousAt hψ₁At)
      have hΦ₁ : ContinuousAt Φ ((extChartAt I x.1).symm (ψ₁ z₀)) :=
        hΦ.continuous.continuousAt
      have hmain : ContinuousAt (fun z : MorseModel (m + 1) =>
          Φ ((extChartAt I x.1).symm (ψ₁ z))) z₀ :=
        hΦ₁.comp (f := fun z : MorseModel (m + 1) => (extChartAt I x.1).symm (ψ₁ z)) (x := z₀) hφ₁
      have hmem : Φ ((extChartAt I x.1).symm (ψ₁ (extChartAt (morseModelWithCornersHalfSpace m) x x))) ∈
          (extChartAt I x₂.1).source := by
        rw [hψ₁z₀, (extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
        exact mem_extChartAt_source (I := I) x₂.1
      exact hmain.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) x₂.1).mem_nhds hmem)
    have hnhd : D₁ ∩ (ψ₁ ⁻¹' Metric.ball ((extChartAt I x.1) x.1) b₁.rIn) ∩
        (((fun z : MorseModel (m + 1) => Φc (ψ₁ z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
          (fun z : MorseModel (m + 1) =>
            Φ ((extChartAt I x.1).symm (ψ₁ z)) ∈ (extChartAt I x₂.1).source) ∩
          (fun z : MorseModel (m + 1) =>
            Φc (ψ₁ z) ∈ Metric.ball p₂.1
              (sublevelInteriorRadius g₂c a₂ p₂
                (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt') hg₂c))) ∩
        Set.range (morseModelWithCornersHalfSpace m) ∈
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m)) := by
      refine Filter.inter_mem ?_ ?_
      · refine Filter.inter_mem ?_ ?_
        · refine Filter.inter_mem ?_ ?_
          · exact nhdsWithin_le_nhds ((isOpen_sublevelBoundaryChartDomain g₁c a₁ p₁
              (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c).mem_nhds hz₀D₁)
          · exact nhdsWithin_le_nhds hpre₁
        · refine Filter.inter_mem ?_ ?_
          · refine Filter.inter_mem ?_ ?_
            · exact nhdsWithin_le_nhds hpre₂
            · exact nhdsWithin_le_nhds hpre₃
          · exact nhdsWithin_le_nhds hpre₂r
      · exact self_mem_nhdsWithin
    have hval : ∀ z ∈ D₁ ∩ (ψ₁ ⁻¹' Metric.ball ((extChartAt I x.1) x.1) b₁.rIn) ∩
        (((fun z : MorseModel (m + 1) => Φc (ψ₁ z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
          (fun z : MorseModel (m + 1) =>
            Φ ((extChartAt I x.1).symm (ψ₁ z)) ∈ (extChartAt I x₂.1).source) ∩
          (fun z : MorseModel (m + 1) =>
            Φc (ψ₁ z) ∈ Metric.ball p₂.1
              (sublevelInteriorRadius g₂c a₂ p₂
                (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt') hg₂c))) ∩
        Set.range (morseModelWithCornersHalfSpace m),
        (extChartAt (morseModelWithCornersHalfSpace m) x₂ ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          (extChartAt (morseModelWithCornersHalfSpace m) x).symm) z = F z := by
      intro z hz
      have hzD₁ : z ∈ D₁ := hz.1.1.1
      have hzψ₁ : ψ₁ z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn := hz.1.1.2
      have hzψ₂ : Φc (ψ₁ z) ∈ Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn := hz.1.2.1.1
      have hzsrc₂ : Φ ((extChartAt I x.1).symm (ψ₁ z)) ∈ (extChartAt I x₂.1).source := hz.1.2.1.2
      have hz₂r : Φc (ψ₁ z) ∈ Metric.ball p₂.1
          (sublevelInteriorRadius g₂c a₂ p₂
            (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt') hg₂c) := hz.1.2.2
      have hzrange : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.2
      have hzmem : 0 ≤ z (Fin.last m) := by
        rw [range_morseModelWithCornersHalfSpace] at hzrange
        exact hzrange
      change ((hcs₂.chartAt x₂).extend (morseModelWithCornersHalfSpace m) ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)).symm) z = F z
      rw [hchart₂']
      rw [hchart₁']
      simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
      change (morseModelWithCornersHalfSpace m)
          (c₂ ((fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂))
            (c₁.symm ((morseModelWithCornersHalfSpace m).symm z)))) = F z
      have hu : (morseModelWithCornersHalfSpace m).symm z = (⟨z, hzmem⟩ : MorseHalfSpace m) := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hzmem
      rw [hu]
      have hmb₁tgt : (⟨z, hzmem⟩ : MorseHalfSpace m) ∈ mb₁.target := by
        simpa [sublevelBoundaryChartDomain] using hzD₁
      have hmb₁sm := sublevelBoundaryChart_symm_value g₁c a₁ p₁
        (sublevelPullbackCutoffPoint_value I g₁ a₁ x b₁ hx) hg₁c hr₁c hmb₁tgt
      have hmb₁sm' : (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m) : SublevelSpace g₁c a₁).1 = ψ₁ z := by
        simpa [ψ₁] using congrArg Subtype.val hmb₁sm
      have hpb₁tgt : (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)) ∈ pb₁.target := by
        change (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 ∈
          Metric.ball ((extChartAt I x.1) x.1) b₁.rIn
        rwa [hmb₁sm']
      have hpb₁sm : (pb₁.symm (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m))).1 =
          (extChartAt I x.1).symm (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 :=
        sublevelPullbackChart_symm_value I g₁ a₁ x b₁ hb₁ hpb₁tgt
      have hc₁sm : (c₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 =
          (extChartAt I x.1).symm (ψ₁ z) := by
        change (pb₁.symm (mb₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m))).1 =
          (extChartAt I x.1).symm (ψ₁ z)
        rw [hpb₁sm, hmb₁sm']
      let y₁ : SublevelSpace g₁ a₁ := c₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)
      let w₂ : SublevelSpace g₂ a₂ := ⟨Φ y₁.1, hmap y₁.1 y₁.2⟩
      have hΘ : y₁.1 = (extChartAt I x.1).symm (ψ₁ z) := hc₁sm
      have hpb₂src : w₂ ∈ pb₂.source := by
        change w₂.1 ∈ (extChartAt I x₂.1).source ∧ (extChartAt I x₂.1) w₂.1 ∈
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
        constructor
        · change Φ y₁.1 ∈ (extChartAt I x₂.1).source
          rw [hΘ]
          exact hzsrc₂
        · change (extChartAt I x₂.1) (Φ y₁.1) ∈
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
          rw [hΘ]
          exact hzψ₂
      have hpb₂val : (pb₂ w₂).1 = (extChartAt I x₂.1) w₂.1 :=
        sublevelPullbackChart_apply_of_mem I g₂ a₂ x₂ b₂ hb₂ hpb₂src
      have hmi₂val : (mi₂ (pb₂ w₂) : MorseModel (m + 1)) =
          morseHalfSpaceShift s₂ ((extChartAt I x₂.1) w₂.1) := by
        rw [sublevelInteriorChart_apply_value g₂c a₂ p₂
          (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt') hg₂c (y := pb₂ w₂) (by
            rw [hpb₂val]
            dsimp [w₂]
            rw [hΘ]
            change dist (Φc (ψ₁ z)) p₂.1 <
              sublevelInteriorRadius g₂c a₂ p₂
                (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt') hg₂c
            exact hz₂r)]
        rw [hpb₂val]
      change (morseModelWithCornersHalfSpace m)
          (mi₂ (pb₂ w₂)) = F z
      change (mi₂ (pb₂ w₂) : MorseModel (m + 1)) = F z
      rw [hmi₂val]
      dsimp [F]
      dsimp [w₂]
      rw [hΘ]
      dsimp [Φc]
    have hred : (extChartAt (morseModelWithCornersHalfSpace m) x₂ ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m))] F := by
      refine Filter.eventuallyEq_of_mem (s := D₁ ∩ (ψ₁ ⁻¹' Metric.ball ((extChartAt I x.1) x.1) b₁.rIn) ∩
        (((fun z : MorseModel (m + 1) => Φc (ψ₁ z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
          (fun z : MorseModel (m + 1) =>
            Φ ((extChartAt I x.1).symm (ψ₁ z)) ∈ (extChartAt I x₂.1).source) ∩
          (fun z : MorseModel (m + 1) =>
            Φc (ψ₁ z) ∈ Metric.ball p₂.1
              (sublevelInteriorRadius g₂c a₂ p₂
                (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt') hg₂c))) ∩
        Set.range (morseModelWithCornersHalfSpace m)) hnhd ?_
      intro z hz
      exact hval z hz
    refine hFAt'.congr_of_eventuallyEq_of_mem ?_ hz₀range
    change ((extChartAt (morseModelWithCornersHalfSpace m)
        (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂)) ∘
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
      (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m))]
      (fun z : MorseModel (m + 1) => F z)
    simpa [extChartAt, hchart₁', hchart₂', x₂] using hred

theorem contMDiffAt_manifoldSublevelInteriorMap [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (g₁ g₂ : M → ℝ) (a₁ a₂ : ℝ)
    (hg₁ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₁)
    (hg₂ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₂)
    (hreg₁ : ∀ x : M, g₁ x = a₁ → ¬ IsCriticalPointAt I g₁ x)
    (hreg₂ : ∀ x : M, g₂ x = a₂ → ¬ IsCriticalPointAt I g₂ x)
    (x : SublevelSpace g₁ a₁) (hx : g₁ x.1 < a₁)
    (Φ : M → M) (hΦ : ContMDiff I I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hmap : ∀ y : M, g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    (hstrict : ∀ y : M, g₁ y < a₁ → g₂ (Φ y) < a₂)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₁ a₁) :=
      manifoldSublevelChartedSpace I g₁ a₁ hg₁ hreg₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₂ a₂) :=
      manifoldSublevelChartedSpace I g₂ a₂ hg₂ hreg₂)
    (hchart₁ : ∀ y : SublevelSpace g₁ a₁, hcs₁.chartAt y =
      (if h : g₁ y.1 = a₁ then manifoldSublevelBoundaryChart I g₁ a₁ y h hg₁ hreg₁
        else manifoldSublevelInteriorChart I g₁ a₁ y (lt_of_le_of_ne (show g₁ y.1 ≤ a₁ from y.2) h) hg₁) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g₂ a₂, hcs₂.chartAt y =
      (if h : g₂ y.1 = a₂ then manifoldSublevelBoundaryChart I g₂ a₂ y h hg₂ hreg₂
        else manifoldSublevelInteriorChart I g₂ a₂ y (lt_of_le_of_ne (show g₂ y.1 ≤ a₂ from y.2) h) hg₂) := by
      intro y
      rfl) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) x := by
  classical
  letI := hcs₁
  letI := hcs₂
  rw [contMDiffAt_iff]
  constructor
  · have hcont : Continuous (fun y : SublevelSpace g₁ a₁ => Φ y.1) :=
      hΦ.continuous.comp continuous_subtype_val
    exact (Continuous.subtype_mk hcont (fun y => hmap y.1 y.2)).continuousAt
  · let x₂ : SublevelSpace g₂ a₂ := ⟨Φ x.1, hmap x.1 x.2⟩
    let c₁ : OpenPartialHomeomorph (SublevelSpace g₁ a₁) (MorseHalfSpace m) :=
      manifoldSublevelInteriorChart I g₁ a₁ x hx hg₁
    have hchart₁' : hcs₁.chartAt x = c₁ := by
      rw [hchart₁ x]
      rw [dif_neg (ne_of_lt hx)]
    have hx₂lt : g₂ x₂.1 < a₂ := hstrict x.1 hx
    let c₂ : OpenPartialHomeomorph (SublevelSpace g₂ a₂) (MorseHalfSpace m) :=
      manifoldSublevelInteriorChart I g₂ a₂ x₂ hx₂lt hg₂
    have hchart₂' : hcs₂.chartAt x₂ = c₂ := by
      rw [hchart₂ x₂]
      rw [dif_neg (ne_of_lt hx₂lt)]
    let b₁ : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
    let hb₁ : Metric.closedBall ((extChartAt I x.1) x.1) b₁.rOut ⊆ (extChartAt I x.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x.1
    let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
    let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x₂.1
    let g₁c : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I g₁ x.1 b₁
    let g₂c : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I g₂ x₂.1 b₂
    let p₁ : SublevelSpace g₁c a₁ := sublevelPullbackCutoffPoint I g₁ a₁ x b₁
    let p₂ : SublevelSpace g₂c a₂ := sublevelPullbackCutoffPoint I g₂ a₂ x₂ b₂
    let hg₁c : ContDiff ℝ (⊤ : ℕ∞) g₁c := contDiff_sublevelPullbackCutoff I g₁ hg₁ x.1 b₁ hb₁
    let hg₂c : ContDiff ℝ (⊤ : ℕ∞) g₂c := contDiff_sublevelPullbackCutoff I g₂ hg₂ x₂.1 b₂ hb₂
    let pb₁ : OpenPartialHomeomorph (SublevelSpace g₁ a₁) (SublevelSpace g₁c a₁) :=
      sublevelPullbackChart I g₁ a₁ x b₁ hb₁
    let pb₂ : OpenPartialHomeomorph (SublevelSpace g₂ a₂) (SublevelSpace g₂c a₂) :=
      sublevelPullbackChart I g₂ a₂ x₂ b₂ hb₂
    let mi₁ : OpenPartialHomeomorph (SublevelSpace g₁c a₁) (MorseHalfSpace m) :=
      sublevelInteriorChart g₁c a₁ (sublevelPullbackCutoffPoint I g₁ a₁ x b₁)
        (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c
    let mi₂ : OpenPartialHomeomorph (SublevelSpace g₂c a₂) (MorseHalfSpace m) :=
      sublevelInteriorChart g₂c a₂ (sublevelPullbackCutoffPoint I g₂ a₂ x₂ b₂)
        (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt) hg₂c
    let s₁ : ℝ := sublevelInteriorShift g₁c a₁ p₁ (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c
    let s₂ : ℝ := sublevelInteriorShift g₂c a₂ p₂ (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt) hg₂c
    let Φc : MorseModel (m + 1) → MorseModel (m + 1) :=
      fun y => (extChartAt I x₂.1) (Φ ((extChartAt I x.1).symm y))
    let F : MorseModel (m + 1) → MorseModel (m + 1) :=
      fun z => morseHalfSpaceShift s₂ (Φc (morseHalfSpaceShift (-s₁) z))
    have hpb₁src : x ∈ pb₁.source := mem_sublevelPullbackChart_source I g₁ a₁ x b₁ hb₁
    have hpb₁val : (pb₁ x).1 = (extChartAt I x.1) x.1 := by
      exact sublevelPullbackChart_apply_of_mem I g₁ a₁ x b₁ hb₁ hpb₁src
    have hz₀ : (extChartAt (morseModelWithCornersHalfSpace m) x x) =
        (morseModelWithCornersHalfSpace m) (c₁ x) := by
      simp [extChartAt, hchart₁']
    have hz₀range : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
        Set.range (morseModelWithCornersHalfSpace m) := by
      simp [extChartAt, hchart₁']
    have hψ₁At : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => morseHalfSpaceShift (-s₁) y)
        (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      (contDiff_morseHalfSpaceShift (m := m) (-s₁)).contDiffAt
    have hψ₁z₀ : morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x) =
        (extChartAt I x.1) x.1 := by
      have hu : (c₁ x : MorseHalfSpace m) ∈ mi₁.target := by
        have hsrc : x ∈ c₁.source := mem_manifoldSublevelInteriorChart_source I g₁ a₁ x hx hg₁
        have htgt : (c₁ x : MorseHalfSpace m) ∈ c₁.target := c₁.map_source hsrc
        have hsplit := (by simpa [c₁, manifoldSublevelInteriorChart] using htgt)
        exact hsplit.1
      have hsm := sublevelInteriorChart_symm_value g₁c a₁ p₁
        (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c (z := (c₁ x : MorseHalfSpace m)) hu
      have hsm' : (mi₁.symm (c₁ x : MorseHalfSpace m) : SublevelSpace g₁c a₁).1 =
          morseHalfSpaceShift (-s₁) (c₁ x : MorseHalfSpace m) := by
        simpa [s₁] using congrArg Subtype.val hsm
      have hleft : mi₁.symm (c₁ x : MorseHalfSpace m) = pb₁ x := by
        have hpb₁eq : pb₁ x = p₁ := by
          apply Subtype.ext
          simpa [p₁] using hpb₁val
        have hsrc' : (pb₁ x) ∈ mi₁.source := by
          rw [hpb₁eq]
          exact mem_sublevelInteriorChart_source g₁c a₁ p₁
            (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c
        exact mi₁.left_inv hsrc'
      rw [hz₀]
      change morseHalfSpaceShift (-s₁) (c₁ x : MorseHalfSpace m) = (extChartAt I x.1) x.1
      rw [← hsm']
      rw [hleft]
      exact hpb₁val
    have hΦcAt : ContDiffAt ℝ (⊤ : ℕ∞) Φc
        (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x)) := by
      have hiff := (contMDiffAt_iff (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).mp (hΦ x.1)
      have hcw : ContDiffWithinAt ℝ (⊤ : ℕ∞) Φc (Set.range I)
          (extChartAt I x.1 x.1) := by
        simpa [Φc] using hiff.2
      have hrng : Set.range I = Set.univ := ModelWithCorners.Boundaryless.range_eq_univ
      have hcwa : ContDiffAt ℝ (⊤ : ℕ∞) Φc (extChartAt I x.1 x.1) := by
        rw [hrng] at hcw
        exact contDiffWithinAt_univ.mp hcw
      rw [hψ₁z₀]
      exact hcwa
    have hmidAt : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z))
        (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      have hmidAt' : ContDiffAt ℝ (⊤ : ℕ∞)
          (Φc ∘ fun z : MorseModel (m + 1) => morseHalfSpaceShift (-s₁) z)
          (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
        hΦcAt.comp (f := fun z : MorseModel (m + 1) => morseHalfSpaceShift (-s₁) z)
          (x := extChartAt (morseModelWithCornersHalfSpace m) x x) hψ₁At
      simpa [Function.comp_def] using hmidAt'
    have hFAt : ContDiffAt ℝ (⊤ : ℕ∞) F (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      have hshift₂ : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => morseHalfSpaceShift s₂ y)
          (Φc (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x))) :=
        (contDiff_morseHalfSpaceShift (m := m) s₂).contDiffAt
      have hcomp := ContDiffAt.comp (x := extChartAt (morseModelWithCornersHalfSpace m) x x)
        hshift₂ hmidAt
      simpa [F, Function.comp_def] using hcomp
    have hFAt' : ContDiffWithinAt ℝ (⊤ : ℕ∞) F
        (Set.range (morseModelWithCornersHalfSpace m))
        (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      hFAt.contDiffWithinAt
    have hmem₀ : dist (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x)) p₁.1 <
        sublevelInteriorRadius g₁c a₁ p₁ (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c := by
      rw [hψ₁z₀]
      have hpb₁val' : p₁.1 = (extChartAt I x.1) x.1 := by
        dsimp [p₁]
        rfl
      rw [hpb₁val']
      have hρpos : 0 < sublevelInteriorRadius g₁c a₁ p₁
          (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c := by
        dsimp [sublevelInteriorRadius]
        exact (Classical.choose_spec (Metric.mem_nhds_iff.mp ((isOpen_Iio.preimage hg₁c.continuous).mem_nhds
          (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx)))).1
      exact Metric.mem_ball_self hρpos
    have hpre₁ : (fun z : MorseModel (m + 1) =>
          morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∧
          dist (morseHalfSpaceShift (-s₁) z) p₁.1 < sublevelInteriorRadius g₁c a₁ p₁
            (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c) ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      have hcont₁ : Continuous (fun z : MorseModel (m + 1) =>
          morseHalfSpaceShift (-s₁) z) :=
        (contDiff_morseHalfSpaceShift (m := m) (-s₁)).continuous
      have hcont₂ : Continuous (fun z : MorseModel (m + 1) =>
          dist (morseHalfSpaceShift (-s₁) z) p₁.1) := by
        have hshift : Continuous (fun z : MorseModel (m + 1) => morseHalfSpaceShift (-s₁) z) :=
          (contDiff_morseHalfSpaceShift (m := m) (-s₁)).continuous
        exact continuous_dist.comp (hshift.prodMk continuous_const)
      exact Filter.inter_mem
        (hcont₁.continuousAt.preimage_mem_nhds (by
          rw [hψ₁z₀]
          exact Metric.ball_mem_nhds ((extChartAt I x.1) x.1) b₁.rIn_pos))
        (hcont₂.continuousAt.preimage_mem_nhds (by
          change {y : ℝ | y < sublevelInteriorRadius g₁c a₁ p₁
              (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c} ∈
            nhds (dist (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x)) p₁.1)
          exact (isOpen_Iio.mem_nhds hmem₀)))
    have hpre₂ : (fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      (ContDiffAt.continuousAt hmidAt).preimage_mem_nhds (by
        change Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn ∈
          nhds (Φc (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x)))
        rw [hψ₁z₀]
        have hval : Φc ((extChartAt I x.1) x.1) = (extChartAt I x₂.1) (Φ x.1) := by
          dsimp [Φc]
          congr 2
          simp
        rw [hval]
        exact Metric.ball_mem_nhds ((extChartAt I x₂.1) x₂.1) b₂.rIn_pos)
    have hpre₂r : (fun z : MorseModel (m + 1) =>
          Φc (morseHalfSpaceShift (-s₁) z) ∈ Metric.ball p₂.1
            (sublevelInteriorRadius g₂c a₂ p₂
              (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt) hg₂c)) ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      (ContDiffAt.continuousAt hmidAt).preimage_mem_nhds (by
        change Metric.ball p₂.1 (sublevelInteriorRadius g₂c a₂ p₂
            (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt) hg₂c) ∈
          nhds (Φc (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x)))
        rw [hψ₁z₀]
        have hval : Φc ((extChartAt I x.1) x.1) = (extChartAt I x₂.1) (Φ x.1) := by
          dsimp [Φc]
          congr 2
          simp
        rw [hval]
        have hρpos : 0 < sublevelInteriorRadius g₂c a₂ p₂
            (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt) hg₂c := by
          dsimp [sublevelInteriorRadius]
          exact (Classical.choose_spec (Metric.mem_nhds_iff.mp ((isOpen_Iio.preimage hg₂c.continuous).mem_nhds
            (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt)))).1
        exact Metric.ball_mem_nhds p₂.1 hρpos)
    have hpre₃ : (fun z : MorseModel (m + 1) =>
          Φ ((extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z)) ∈ (extChartAt I x₂.1).source) ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      let z₀ : MorseModel (m + 1) := extChartAt (morseModelWithCornersHalfSpace m) x x
      have hφ₁ : ContinuousAt (fun z : MorseModel (m + 1) =>
          (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z)) z₀ := by
        have hsm : ContinuousAt (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z₀) := by
          rw [hψ₁z₀]
          exact (continuousOn_extChartAt_symm x.1).continuousAt
            ((isOpen_extChartAt_target (I := I) x.1).mem_nhds
              ((extChartAt I x.1).map_source (mem_extChartAt_source (I := I) x.1)))
        exact hsm.comp (ContDiffAt.continuousAt hψ₁At)
      have hΦ₁ : ContinuousAt Φ ((extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z₀)) :=
        hΦ.continuous.continuousAt
      have hmain : ContinuousAt (fun z : MorseModel (m + 1) =>
          Φ ((extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z))) z₀ :=
        hΦ₁.comp (f := fun z : MorseModel (m + 1) =>
          (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z)) (x := z₀) hφ₁
      have hmem : Φ ((extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z₀)) ∈
          (extChartAt I x₂.1).source := by
        rw [hψ₁z₀, (extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
        exact mem_extChartAt_source (I := I) x₂.1
      exact hmain.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) x₂.1).mem_nhds hmem)
    have hnhd : {z : MorseModel (m + 1) |
          morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∧
          dist (morseHalfSpaceShift (-s₁) z) p₁.1 < sublevelInteriorRadius g₁c a₁ p₁
            (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c} ∩
        (((fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
          (fun z : MorseModel (m + 1) =>
            Φ ((extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z)) ∈ (extChartAt I x₂.1).source) ∩
          (fun z : MorseModel (m + 1) =>
            Φc (morseHalfSpaceShift (-s₁) z) ∈ Metric.ball p₂.1
              (sublevelInteriorRadius g₂c a₂ p₂
                (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt) hg₂c))) ∩
        Set.range (morseModelWithCornersHalfSpace m) ∈
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m)) := by
      refine Filter.inter_mem ?_ ?_
      · refine Filter.inter_mem ?_ ?_
        · exact nhdsWithin_le_nhds hpre₁
        · refine Filter.inter_mem ?_ ?_
          · refine Filter.inter_mem ?_ ?_
            · exact nhdsWithin_le_nhds hpre₂
            · exact nhdsWithin_le_nhds hpre₃
          · exact nhdsWithin_le_nhds hpre₂r
      · exact self_mem_nhdsWithin
    have hval : ∀ z ∈ {z : MorseModel (m + 1) |
          morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∧
          dist (morseHalfSpaceShift (-s₁) z) p₁.1 < sublevelInteriorRadius g₁c a₁ p₁
            (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c} ∩
        (((fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
          (fun z : MorseModel (m + 1) =>
            Φ ((extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z)) ∈ (extChartAt I x₂.1).source) ∩
          (fun z : MorseModel (m + 1) =>
            Φc (morseHalfSpaceShift (-s₁) z) ∈ Metric.ball p₂.1
              (sublevelInteriorRadius g₂c a₂ p₂
                (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt) hg₂c))) ∩
        Set.range (morseModelWithCornersHalfSpace m),
        (extChartAt (morseModelWithCornersHalfSpace m) x₂ ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          (extChartAt (morseModelWithCornersHalfSpace m) x).symm) z = F z := by
      intro z hz
      have hz₁b : morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn := hz.1.1.1
      have hz₁ : dist (morseHalfSpaceShift (-s₁) z) p₁.1 <
          sublevelInteriorRadius g₁c a₁ p₁ (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c := hz.1.1.2
      have hz₂ : Φc (morseHalfSpaceShift (-s₁) z) ∈
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn := hz.1.2.1.1
      have hz₃ : Φ ((extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z)) ∈
          (extChartAt I x₂.1).source := hz.1.2.1.2
      have hz₂r : Φc (morseHalfSpaceShift (-s₁) z) ∈ Metric.ball p₂.1
          (sublevelInteriorRadius g₂c a₂ p₂
            (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt) hg₂c) := hz.1.2.2
      have hzrange : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.2
      have hzmem : 0 ≤ z (Fin.last m) := by
        rw [range_morseModelWithCornersHalfSpace] at hzrange
        exact hzrange
      change ((hcs₂.chartAt x₂).extend (morseModelWithCornersHalfSpace m) ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)).symm) z = F z
      rw [hchart₂']
      rw [hchart₁']
      simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
      change (morseModelWithCornersHalfSpace m)
          (c₂ ((fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂))
            (c₁.symm ((morseModelWithCornersHalfSpace m).symm z)))) = F z
      have hu : (morseModelWithCornersHalfSpace m).symm z = (⟨z, hzmem⟩ : MorseHalfSpace m) := by
        apply Subtype.ext
        exact morseHalfSpaceClamp_of_mem m hzmem
      rw [hu]
      have hmi₁tgt : (⟨z, hzmem⟩ : MorseHalfSpace m) ∈ mi₁.target := hz₁
      have hmi₁sm := sublevelInteriorChart_symm_value g₁c a₁ p₁
        (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c (z := (⟨z, hzmem⟩ : MorseHalfSpace m)) hmi₁tgt
      have hmi₁sm' : (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m) : SublevelSpace g₁c a₁).1 =
          morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m) := by
        simpa [s₁] using congrArg Subtype.val hmi₁sm
      have hpb₁tgt : (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)) ∈ pb₁.target := by
        change (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 ∈
          Metric.ball ((extChartAt I x.1) x.1) b₁.rIn
        rwa [hmi₁sm']
      have hc₁sm : (c₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 =
          (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m)) := by
        change (pb₁.symm (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m))).1 = _
        rw [sublevelPullbackChart_symm_value I g₁ a₁ x b₁ hb₁ hpb₁tgt, hmi₁sm']
      let y₁ : SublevelSpace g₁ a₁ := c₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)
      let w₂ : SublevelSpace g₂ a₂ := ⟨Φ y₁.1, hmap y₁.1 y₁.2⟩
      have hΘ : y₁.1 = (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m)) := hc₁sm
      have hpb₂src : w₂ ∈ pb₂.source := by
        change w₂.1 ∈ (extChartAt I x₂.1).source ∧ (extChartAt I x₂.1) w₂.1 ∈
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
        constructor
        · change Φ y₁.1 ∈ (extChartAt I x₂.1).source
          rw [hΘ]
          exact hz₃
        · change (extChartAt I x₂.1) (Φ y₁.1) ∈
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
          rw [hΘ]
          exact hz₂
      have hpb₂val : (pb₂ w₂).1 = (extChartAt I x₂.1) w₂.1 :=
        sublevelPullbackChart_apply_of_mem I g₂ a₂ x₂ b₂ hb₂ hpb₂src
      have hmi₂val : (mi₂ (pb₂ w₂) : MorseModel (m + 1)) =
          morseHalfSpaceShift s₂ ((extChartAt I x₂.1) w₂.1) := by
        rw [sublevelInteriorChart_apply_value g₂c a₂ p₂
          (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt) hg₂c (y := pb₂ w₂) (by
            rw [hpb₂val]
            dsimp [w₂]
            rw [hΘ]
            change dist (Φc (morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m))) p₂.1 <
              sublevelInteriorRadius g₂c a₂ p₂
                (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt) hg₂c
            exact hz₂r)]
        rw [hpb₂val]
      change (morseModelWithCornersHalfSpace m)
          (mi₂ (pb₂ w₂)) = F z
      change (mi₂ (pb₂ w₂) : MorseModel (m + 1)) = F z
      rw [hmi₂val]
      dsimp [F]
      dsimp [w₂]
      rw [hΘ]
      dsimp [Φc]
    have hred : (extChartAt (morseModelWithCornersHalfSpace m) x₂ ∘
          (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
          (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m))] F := by
      refine Filter.eventuallyEq_of_mem (s := (fun z : MorseModel (m + 1) =>
          morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∧
          dist (morseHalfSpaceShift (-s₁) z) p₁.1 < sublevelInteriorRadius g₁c a₁ p₁
            (sublevelPullbackCutoffPoint_value_lt I g₁ a₁ x b₁ hx) hg₁c) ∩
        (((fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
          (fun z : MorseModel (m + 1) =>
            Φ ((extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z)) ∈ (extChartAt I x₂.1).source) ∩
          (fun z : MorseModel (m + 1) =>
            Φc (morseHalfSpaceShift (-s₁) z) ∈ Metric.ball p₂.1
              (sublevelInteriorRadius g₂c a₂ p₂
                (sublevelPullbackCutoffPoint_value_lt I g₂ a₂ x₂ b₂ hx₂lt) hg₂c))) ∩
        Set.range (morseModelWithCornersHalfSpace m)) hnhd ?_
      intro z hz
      exact hval z hz
    refine hFAt'.congr_of_eventuallyEq_of_mem ?_ hz₀range
    change ((extChartAt (morseModelWithCornersHalfSpace m)
        (⟨Φ x.1, hmap x.1 x.2⟩ : SublevelSpace g₂ a₂)) ∘
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) ∘
      (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
        nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
          (Set.range (morseModelWithCornersHalfSpace m))]
      (fun z : MorseModel (m + 1) => F z)
    simpa [extChartAt, hchart₁', hchart₂', x₂] using hred

theorem contMDiff_manifoldSublevelMap [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M]
    (g₁ g₂ : M → ℝ) (a₁ a₂ : ℝ)
    (hg₁ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₁)
    (hg₂ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₂)
    (hreg₁ : ∀ x : M, g₁ x = a₁ → ¬ IsCriticalPointAt I g₁ x)
    (hreg₂ : ∀ x : M, g₂ x = a₂ → ¬ IsCriticalPointAt I g₂ x)
    (Φ : M → M) (hΦ : ContMDiff I I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hmap : ∀ y : M, g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    (hbnd : ∀ y : M, g₁ y = a₁ → g₂ (Φ y) = a₂)
    (hstrict : ∀ y : M, g₁ y < a₁ → g₂ (Φ y) < a₂)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₁ a₁) :=
      manifoldSublevelChartedSpace I g₁ a₁ hg₁ hreg₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₂ a₂) :=
      manifoldSublevelChartedSpace I g₂ a₂ hg₂ hreg₂)
    (hchart₁ : ∀ y : SublevelSpace g₁ a₁, hcs₁.chartAt y =
      (if h : g₁ y.1 = a₁ then manifoldSublevelBoundaryChart I g₁ a₁ y h hg₁ hreg₁
        else manifoldSublevelInteriorChart I g₁ a₁ y (lt_of_le_of_ne (show g₁ y.1 ≤ a₁ from y.2) h) hg₁) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g₂ a₂, hcs₂.chartAt y =
      (if h : g₂ y.1 = a₂ then manifoldSublevelBoundaryChart I g₂ a₂ y h hg₂ hreg₂
        else manifoldSublevelInteriorChart I g₂ a₂ y (lt_of_le_of_ne (show g₂ y.1 ≤ a₂ from y.2) h) hg₂) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) := by
  intro x
  by_cases hx : g₁ x.1 = a₁
  · exact contMDiffAt_manifoldSublevelBoundaryMap (I := I) g₁ g₂ a₁ a₂ hg₁ hg₂ hreg₁ hreg₂ x hx Φ hΦ hmap (hbnd x.1 hx)
      (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
  · have hxlt : g₁ x.1 < a₁ := lt_of_le_of_ne (show g₁ x.1 ≤ a₁ from x.2) hx
    exact contMDiffAt_manifoldSublevelInteriorMap (I := I) g₁ g₂ a₁ a₂ hg₁ hg₂ hreg₁ hreg₂ x hxlt Φ hΦ hmap hstrict
      (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)

theorem contMDiff_manifoldSublevelMap_of_interior [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (g₁ g₂ : M → ℝ) (a₁ a₂ : ℝ)
    (hg₁ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₁)
    (hg₂ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g₂)
    (hreg₁ : ∀ x : M, g₁ x = a₁ → ¬ IsCriticalPointAt I g₁ x)
    (hreg₂ : ∀ x : M, g₂ x = a₂ → ¬ IsCriticalPointAt I g₂ x)
    (Φ : M → M) (hΦ : ContMDiff I I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hmap : ∀ y : M, g₁ y ≤ a₁ → g₂ (Φ y) ≤ a₂)
    (hstrict : ∀ y : M, g₁ y < a₁ → g₂ (Φ y) < a₂)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₁ a₁) :=
      manifoldSublevelChartedSpace I g₁ a₁ hg₁ hreg₁)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g₂ a₂) :=
      manifoldSublevelChartedSpace I g₂ a₂ hg₂ hreg₂)
    (hchart₁ : ∀ y : SublevelSpace g₁ a₁, hcs₁.chartAt y =
      (if h : g₁ y.1 = a₁ then manifoldSublevelBoundaryChart I g₁ a₁ y h hg₁ hreg₁
        else manifoldSublevelInteriorChart I g₁ a₁ y (lt_of_le_of_ne (show g₁ y.1 ≤ a₁ from y.2) h) hg₁) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace g₂ a₂, hcs₂.chartAt y =
      (if h : g₂ y.1 = a₂ then manifoldSublevelBoundaryChart I g₂ a₂ y h hg₂ hreg₂
        else manifoldSublevelInteriorChart I g₂ a₂ y (lt_of_le_of_ne (show g₂ y.1 ≤ a₂ from y.2) h) hg₂) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g₁ a₁ => (⟨Φ y.1, hmap y.1 y.2⟩ : SublevelSpace g₂ a₂)) := by
  intro x
  by_cases hx : g₁ x.1 = a₁
  · have hle : g₂ (Φ x.1) ≤ a₂ := hmap x.1 x.2
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact contMDiffAt_manifoldSublevelBoundaryToInteriorMap (I := I) g₁ g₂ a₁ a₂ hg₁ hg₂ hreg₁ hreg₂ x hx Φ hΦ hmap hlt
        (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
    · exact contMDiffAt_manifoldSublevelBoundaryMap (I := I) g₁ g₂ a₁ a₂ hg₁ hg₂ hreg₁ hreg₂ x hx Φ hΦ hmap heq
        (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
  · have hxlt : g₁ x.1 < a₁ := lt_of_le_of_ne (show g₁ x.1 ≤ a₁ from x.2) hx
    exact contMDiffAt_manifoldSublevelInteriorMap (I := I) g₁ g₂ a₁ a₂ hg₁ hg₂ hreg₁ hreg₂ x hxlt Φ hΦ hmap hstrict
      (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)

theorem contMDiffAt_sublevelCorestrictInterior [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    {E' H' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {X : Type} [TopologicalSpace X] [ChartedSpace H' X]
    (g : M → ℝ) (a : ℝ)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hreg : ∀ x : M, g x = a → ¬ IsCriticalPointAt I g x)
    (f : X → M) (hf : ContMDiff I' I (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hmem : ∀ x : X, g (f x) ≤ a)
    (x : X) (hx : g (f x) < a)
    (hcs : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) :=
      manifoldSublevelChartedSpace I g a hg hreg)
    (hchart : ∀ y : SublevelSpace g a, hcs.chartAt y =
      (if h : g y.1 = a then manifoldSublevelBoundaryChart I g a y h hg hreg
        else manifoldSublevelInteriorChart I g a y (lt_of_le_of_ne (show g y.1 ≤ a from y.2) h) hg) := by
      intro y
      rfl) :
    ContMDiffAt I' (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : X => (⟨f y, hmem y⟩ : SublevelSpace g a)) x := by
  classical
  letI := hcs
  rw [contMDiffAt_iff_target]
  constructor
  · have hcont : Continuous (fun y : X => f y) := hf.continuous
    exact (Continuous.subtype_mk hcont (fun y => hmem y)).continuousAt
  · let x₂ : SublevelSpace g a := ⟨f x, hmem x⟩
    have hx₂lt : g x₂.1 < a := hx
    let c₂ : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
      manifoldSublevelInteriorChart I g a x₂ hx₂lt hg
    have hchart₂' : hcs.chartAt x₂ = c₂ := by
      rw [hchart x₂]
      rw [dif_neg (ne_of_lt hx₂lt)]
    let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
    let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x₂.1
    let g₂c : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I g x₂.1 b₂
    let p₂ : SublevelSpace g₂c a := sublevelPullbackCutoffPoint I g a x₂ b₂
    let hg₂c : ContDiff ℝ (⊤ : ℕ∞) g₂c := contDiff_sublevelPullbackCutoff I g hg x₂.1 b₂ hb₂
    let pb₂ : OpenPartialHomeomorph (SublevelSpace g a) (SublevelSpace g₂c a) :=
      sublevelPullbackChart I g a x₂ b₂ hb₂
    let mi₂ : OpenPartialHomeomorph (SublevelSpace g₂c a) (MorseHalfSpace m) :=
      sublevelInteriorChart g₂c a p₂ (sublevelPullbackCutoffPoint_value_lt I g a x₂ b₂ hx₂lt) hg₂c
    let s₂ : ℝ := sublevelInteriorShift g₂c a p₂
      (sublevelPullbackCutoffPoint_value_lt I g a x₂ b₂ hx₂lt) hg₂c
    have hshift : ContMDiffAt I' 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : X => morseHalfSpaceShift s₂ ((extChartAt I x₂.1) (f y))) x := by
      have h₁ : ContMDiffAt I' 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : X => (extChartAt I x₂.1) (f y)) x := by
        exact (contMDiffAt_extChartAt (I := I) (x := x₂.1)).comp x (hf x)
      have h₂ : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (morseHalfSpaceShift s₂) ((extChartAt I x₂.1) (f x)) :=
        (contDiff_morseHalfSpaceShift (m := m) s₂).contMDiff.contMDiffAt
      exact h₂.comp x h₁
    refine hshift.congr_of_eventuallyEq ?_
    have hρpos : 0 < sublevelInteriorRadius g₂c a p₂
          (sublevelPullbackCutoffPoint_value_lt I g a x₂ b₂ hx₂lt) hg₂c := by
      dsimp [sublevelInteriorRadius]
      exact (Classical.choose_spec (Metric.mem_nhds_iff.mp ((isOpen_Iio.preimage hg₂c.continuous).mem_nhds
        (sublevelPullbackCutoffPoint_value_lt I g a x₂ b₂ hx₂lt)))).1
    have hsrcx₂ : f x ∈ (extChartAt I x₂.1).source :=
      mem_extChartAt_source (I := I) x₂.1
    have hballx₂ : (extChartAt I x₂.1) (f x) ∈ Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn := by
      dsimp [x₂]
      exact Metric.mem_ball_self b₂.rIn_pos
    have hradx₂ : (extChartAt I x₂.1) (f x) ∈ Metric.ball p₂.1
        (sublevelInteriorRadius g₂c a p₂
          (sublevelPullbackCutoffPoint_value_lt I g a x₂ b₂ hx₂lt) hg₂c) := by
      have hp₂ : p₂.1 = (extChartAt I x₂.1) x₂.1 := by
        dsimp [p₂, sublevelPullbackCutoffPoint]
      rw [hp₂]
      exact Metric.mem_ball_self hρpos
    let S : Set X := {y : X | f y ∈ (extChartAt I x₂.1).source ∧
      (extChartAt I x₂.1) (f y) ∈ Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn ∧
      (extChartAt I x₂.1) (f y) ∈ Metric.ball p₂.1
        (sublevelInteriorRadius g₂c a p₂
          (sublevelPullbackCutoffPoint_value_lt I g a x₂ b₂ hx₂lt) hg₂c)}
    have hS : S ∈ nhds x := by
      have hcf : ContinuousAt (fun y : X => (extChartAt I x₂.1) (f y)) x :=
        ((contMDiffAt_extChartAt (I := I) (x := x₂.1)).comp x (hf x)).continuousAt
      refine Filter.inter_mem ?_ ?_
      · exact hf.continuous.continuousAt.preimage_mem_nhds
          ((isOpen_extChartAt_source (I := I) x₂.1).mem_nhds hsrcx₂)
      · exact Filter.inter_mem
          (hcf.preimage_mem_nhds (Metric.ball_mem_nhds ((extChartAt I x₂.1) x₂.1) b₂.rIn_pos))
          (hcf.preimage_mem_nhds (Metric.ball_mem_nhds p₂.1 hρpos))
    refine Filter.eventually_of_mem hS ?_
    intro y hy
    rcases hy with ⟨hsrc, hrest⟩
    rcases hrest with ⟨hball, hrad⟩
    let y₂ : SublevelSpace g a := ⟨f y, hmem y⟩
    have hpb₂src : y₂ ∈ pb₂.source := by
      change y₂.1 ∈ (extChartAt I x₂.1).source ∧
        (extChartAt I x₂.1) y₂.1 ∈ Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
      exact ⟨hsrc, hball⟩
    have hpb₂val : (pb₂ y₂).1 = (extChartAt I x₂.1) y₂.1 :=
      sublevelPullbackChart_apply_of_mem I g a x₂ b₂ hb₂ hpb₂src
    have hmi₂val : (mi₂ (pb₂ y₂) : MorseModel (m + 1)) =
        morseHalfSpaceShift s₂ ((extChartAt I x₂.1) y₂.1) := by
      rw [sublevelInteriorChart_apply_value g₂c a p₂
        (sublevelPullbackCutoffPoint_value_lt I g a x₂ b₂ hx₂lt) hg₂c (y := pb₂ y₂) (by
          rw [hpb₂val]
          exact hrad)]
      rw [hpb₂val]
    change (extChartAt (morseModelWithCornersHalfSpace m) x₂) y₂ =
      morseHalfSpaceShift s₂ ((extChartAt I x₂.1) (f y))
    have hmain : (extChartAt (morseModelWithCornersHalfSpace m) x₂) y₂ =
        (morseModelWithCornersHalfSpace m) (mi₂ (pb₂ y₂)) := by
      simp [extChartAt, hchart₂', c₂, manifoldSublevelInteriorChart, pb₂, mi₂, b₂, g₂c, p₂]
    rw [hmain]
    change (mi₂ (pb₂ y₂) : MorseModel (m + 1)) =
      morseHalfSpaceShift s₂ ((extChartAt I x₂.1) (f y))
    rw [hmi₂val]

theorem contMDiffAt_sublevelCorestrictBoundary [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    {E' H' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {X : Type} [TopologicalSpace X] [ChartedSpace H' X]
    (g : M → ℝ) (a : ℝ)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hreg : ∀ x : M, g x = a → ¬ IsCriticalPointAt I g x)
    (f : X → M) (hf : ContMDiff I' I (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hmem : ∀ x : X, g (f x) ≤ a)
    (x : X) (hx : g (f x) = a)
    (hcs : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) :=
      manifoldSublevelChartedSpace I g a hg hreg)
    (hchart : ∀ y : SublevelSpace g a, hcs.chartAt y =
      (if h : g y.1 = a then manifoldSublevelBoundaryChart I g a y h hg hreg
        else manifoldSublevelInteriorChart I g a y (lt_of_le_of_ne (show g y.1 ≤ a from y.2) h) hg) := by
      intro y
      rfl) :
    ContMDiffAt I' (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : X => (⟨f y, hmem y⟩ : SublevelSpace g a)) x := by
  classical
  letI := hcs
  rw [contMDiffAt_iff_target]
  constructor
  · have hcont : Continuous (fun y : X => f y) := hf.continuous
    exact (Continuous.subtype_mk hcont (fun y => hmem y)).continuousAt
  · let x₂ : SublevelSpace g a := ⟨f x, hmem x⟩
    have hx₂ : g x₂.1 = a := hx
    let c₂ : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
      manifoldSublevelBoundaryChart I g a x₂ hx₂ hg hreg
    have hchart₂' : hcs.chartAt x₂ = c₂ := by
      rw [hchart x₂]
      rw [dif_pos hx₂]
    let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
    let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x₂.1
    let g₂c : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I g x₂.1 b₂
    let p₂ : SublevelSpace g₂c a := sublevelPullbackCutoffPoint I g a x₂ b₂
    let hg₂c : ContDiff ℝ (⊤ : ℕ∞) g₂c := contDiff_sublevelPullbackCutoff I g hg x₂.1 b₂ hb₂
    let hr₂c : fderiv ℝ g₂c p₂.1 ≠ 0 :=
      fderiv_sublevelPullbackCutoffPoint_ne_zero I g hg a hreg x₂ b₂ hx₂
    let mb₂ : OpenPartialHomeomorph (SublevelSpace g₂c a) (MorseHalfSpace m) :=
      sublevelBoundaryChart g₂c a p₂ (sublevelPullbackCutoffPoint_value I g a x₂ b₂ hx₂) hg₂c hr₂c
    let pb₂ : OpenPartialHomeomorph (SublevelSpace g a) (SublevelSpace g₂c a) :=
      sublevelPullbackChart I g a x₂ b₂ hb₂
    let ψ₂ : MorseModel (m + 1) → MorseModel (m + 1) :=
      sublevelBoundaryChartValue g₂c a p₂ (sublevelPullbackCutoffPoint_value I g a x₂ b₂ hx₂) hg₂c hr₂c
    have hψ₂ : ContDiff ℝ (⊤ : ℕ∞) ψ₂ :=
      contDiff_sublevelBoundaryChartValue g₂c a p₂
        (sublevelPullbackCutoffPoint_value I g a x₂ b₂ hx₂) hg₂c hr₂c
    have hshift : ContMDiffAt I' 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : X => ψ₂ ((extChartAt I x₂.1) (f y))) x := by
      have h₁ : ContMDiffAt I' 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : X => (extChartAt I x₂.1) (f y)) x := by
        exact (contMDiffAt_extChartAt (I := I) (x := x₂.1)).comp x (hf x)
      have h₂ : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          ψ₂ ((extChartAt I x₂.1) (f x)) :=
        hψ₂.contMDiff.contMDiffAt
      exact h₂.comp x h₁
    refine hshift.congr_of_eventuallyEq ?_
    have hsrcx₂ : f x ∈ (extChartAt I x₂.1).source :=
      mem_extChartAt_source (I := I) x₂.1
    have hballx₂ : (extChartAt I x₂.1) (f x) ∈ Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn := by
      dsimp [x₂]
      exact Metric.mem_ball_self b₂.rIn_pos
    let S : Set X := {y : X | f y ∈ (extChartAt I x₂.1).source ∧
      (extChartAt I x₂.1) (f y) ∈ Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn}
    have hS : S ∈ nhds x := by
      have hcf : ContinuousAt (fun y : X => (extChartAt I x₂.1) (f y)) x :=
        ((contMDiffAt_extChartAt (I := I) (x := x₂.1)).comp x (hf x)).continuousAt
      refine Filter.inter_mem ?_ ?_
      · exact hf.continuous.continuousAt.preimage_mem_nhds
          ((isOpen_extChartAt_source (I := I) x₂.1).mem_nhds hsrcx₂)
      · exact hcf.preimage_mem_nhds (Metric.ball_mem_nhds ((extChartAt I x₂.1) x₂.1) b₂.rIn_pos)
    refine Filter.eventually_of_mem hS ?_
    intro y hy
    rcases hy with ⟨hsrc, hball⟩
    let y₂ : SublevelSpace g a := ⟨f y, hmem y⟩
    have hpb₂src : y₂ ∈ pb₂.source := by
      change y₂.1 ∈ (extChartAt I x₂.1).source ∧
        (extChartAt I x₂.1) y₂.1 ∈ Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
      exact ⟨hsrc, hball⟩
    have hpb₂val : (pb₂ y₂).1 = (extChartAt I x₂.1) y₂.1 :=
      sublevelPullbackChart_apply_of_mem I g a x₂ b₂ hb₂ hpb₂src
    have hmb₂val : (mb₂ (pb₂ y₂) : MorseModel (m + 1)) = ψ₂ ((extChartAt I x₂.1) y₂.1) := by
      rw [sublevelBoundaryChart_apply_value' g₂c a p₂
        (sublevelPullbackCutoffPoint_value I g a x₂ b₂ hx₂) hg₂c hr₂c (pb₂ y₂)]
      rw [hpb₂val]
    change (extChartAt (morseModelWithCornersHalfSpace m) x₂) y₂ =
      ψ₂ ((extChartAt I x₂.1) (f y))
    have hmain : (extChartAt (morseModelWithCornersHalfSpace m) x₂) y₂ =
        (morseModelWithCornersHalfSpace m) (mb₂ (pb₂ y₂)) := by
      simp [extChartAt, hchart₂', c₂, manifoldSublevelBoundaryChart, pb₂, mb₂, b₂, g₂c, p₂]
    rw [hmain]
    change (mb₂ (pb₂ y₂) : MorseModel (m + 1)) =
      ψ₂ ((extChartAt I x₂.1) (f y))
    rw [hmb₂val]

theorem contMDiff_sublevelCorestrict [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    {E' H' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} {X : Type} [TopologicalSpace X] [ChartedSpace H' X]
    (g : M → ℝ) (a : ℝ)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hreg : ∀ x : M, g x = a → ¬ IsCriticalPointAt I g x)
    (f : X → M) (hf : ContMDiff I' I (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hmem : ∀ x : X, g (f x) ≤ a)
    (hcs : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) :=
      manifoldSublevelChartedSpace I g a hg hreg)
    (hchart : ∀ y : SublevelSpace g a, hcs.chartAt y =
      (if h : g y.1 = a then manifoldSublevelBoundaryChart I g a y h hg hreg
        else manifoldSublevelInteriorChart I g a y (lt_of_le_of_ne (show g y.1 ≤ a from y.2) h) hg) := by
      intro y
      rfl) :
    ContMDiff I' (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : X => (⟨f y, hmem y⟩ : SublevelSpace g a)) := by
  intro x
  by_cases hx : g (f x) = a
  · exact contMDiffAt_sublevelCorestrictBoundary (I := I) g a hg hreg f hf hmem x hx
      (hcs := hcs) (hchart := hchart)
  · have hxlt : g (f x) < a := lt_of_le_of_ne (hmem x) hx
    exact contMDiffAt_sublevelCorestrictInterior (I := I) g a hg hreg f hf hmem x hxlt
      (hcs := hcs) (hchart := hchart)

theorem manifoldSublevelDiffeomorphOfDiffeomorph [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (g f : M → ℝ) (a b : ℝ)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg_g : ∀ x : M, g x = a → ¬ IsCriticalPointAt I g x)
    (hreg_f : ∀ x : M, f x = b → ¬ IsCriticalPointAt I f x)
    (Φ : Diffeomorph I I M M (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hmap : ∀ x : M, g x ≤ a → f (Φ x) ≤ b)
    (hbnd : ∀ x : M, g x = a → f (Φ x) = b)
    (hstrict : ∀ x : M, g x < a → f (Φ x) < b)
    (hmap' : ∀ x : M, f x ≤ b → g (Φ.symm x) ≤ a)
    (hbnd' : ∀ x : M, f x = b → g (Φ.symm x) = a)
    (hstrict' : ∀ x : M, f x < b → g (Φ.symm x) < a)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) :=
      manifoldSublevelChartedSpace I g a hg hreg_g)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f b) :=
      manifoldSublevelChartedSpace I f b hf hreg_f)
    (hchart₁ : ∀ y : SublevelSpace g a, hcs₁.chartAt y =
      (if h : g y.1 = a then manifoldSublevelBoundaryChart I g a y h hg hreg_g
        else manifoldSublevelInteriorChart I g a y (lt_of_le_of_ne (show g y.1 ≤ a from y.2) h) hg) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace f b, hcs₂.chartAt y =
      (if h : f y.1 = b then manifoldSublevelBoundaryChart I f b y h hf hreg_f
        else manifoldSublevelInteriorChart I f b y (lt_of_le_of_ne (show f y.1 ≤ b from y.2) h) hf) := by
      intro y
      rfl) :
    Nonempty (@Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace g a) _ hcs₁ (SublevelSpace f b) _ hcs₂ (⊤ : ℕ∞)) := by
  classical
  letI := hcs₁
  letI := hcs₂
  let toFun : SublevelSpace g a → SublevelSpace f b := fun x => ⟨Φ x.1, hmap x.1 x.2⟩
  let invFun : SublevelSpace f b → SublevelSpace g a := fun y => ⟨Φ.symm y.1, hmap' y.1 y.2⟩
  let e : SublevelSpace g a ≃ SublevelSpace f b := by
    refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
    · intro x
      apply Subtype.ext
      exact Φ.toEquiv.left_inv x.1
    · intro y
      apply Subtype.ext
      exact Φ.toEquiv.right_inv y.1
  let d : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace g a) _ hcs₁ (SublevelSpace f b) _ hcs₂ (⊤ : ℕ∞) := by
    refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
    · simpa [toFun] using contMDiff_manifoldSublevelMap (I := I) g f a b hg hf hreg_g hreg_f
        Φ Φ.contMDiff hmap hbnd hstrict (hcs₁ := hcs₁) (hcs₂ := hcs₂)
        (hchart₁ := hchart₁) (hchart₂ := hchart₂)
    · simpa [invFun] using contMDiff_manifoldSublevelMap (I := I) f g b a hf hg hreg_f hreg_g
        Φ.symm Φ.symm.contMDiff hmap' hbnd' hstrict' (hcs₁ := hcs₂) (hcs₂ := hcs₁)
        (hchart₁ := hchart₂) (hchart₂ := hchart₁)
  exact ⟨d⟩

theorem manifoldSublevelSetEq_boundary_imp_boundary {M : Type}
    (g f : M → ℝ) (a : ℝ)
    (hset : {x : M | g x ≤ a} = {x : M | f x ≤ a})
    (hg_le : ∀ x : M, g x ≤ f x)
    (x : M) (hgx : g x = a) : f x = a := by
  have hf_le : f x ≤ a := by
    change x ∈ {x : M | f x ≤ a}
    rw [← hset]
    exact le_of_eq hgx
  have hf_ge : a ≤ f x := by
    rw [← hgx]
    exact hg_le x
  exact le_antisymm hf_le hf_ge

theorem isCriticalPointAt_of_fderiv_chartRep_eq_zero {m : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (x : M)
    (hzero : fderiv ℝ (fun y : MorseModel (m + 1) => f ((extChartAt I x).symm y))
      ((extChartAt I x) x) = 0) :
    IsCriticalPointAt I f x := by
  let y : MorseModel (m + 1) := (extChartAt I x) x
  have hleft : ((extChartAt I x).symm ∘ (extChartAt I x)) =ᶠ[nhds x] id := by
    have hsrc : x ∈ (extChartAt I x).source := mem_extChartAt_source (I := I) x
    have hopen : IsOpen (extChartAt I x).source := isOpen_extChartAt_source (I := I) x
    exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hsrc)
      (fun z hz => (extChartAt I x).left_inv hz)
  have hright : ((extChartAt I x) ∘ (extChartAt I x).symm) =ᶠ[nhds y] id := by
    have hyt : y ∈ (extChartAt I x).target :=
      (extChartAt I x).map_source (mem_extChartAt_source (I := I) x)
    exact Filter.eventuallyEq_of_mem ((isOpen_extChartAt_target (I := I) x).mem_nhds hyt)
      (fun z hz => (extChartAt I x).right_inv hz)
  have hσmd : MDifferentiableAt I 𝓘(ℝ, MorseModel (m + 1)) (extChartAt I x) x := by
    have hsrc : x ∈ (chartAt H x).source := by
      rw [← extChartAt_source (I := I) x]
      exact mem_extChartAt_source (I := I) x
    exact (contMDiffAt_extChartAt' (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := x)
      hsrc).mdifferentiableAt (by norm_num)
  have hτmd : MDifferentiableAt 𝓘(ℝ, MorseModel (m + 1)) I (extChartAt I x).symm y := by
    have hc : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (extChartAt I x).symm y := by
      have hon : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
          (extChartAt I x).symm (extChartAt I x).target :=
        contMDiffOn_extChartAt_symm (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) x
      exact hon.contMDiffAt ((isOpen_extChartAt_target (I := I) x).mem_nhds
        ((extChartAt I x).map_source (mem_extChartAt_source (I := I) x)))
    exact hc.mdifferentiableAt (by norm_num)
  have hh : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (f ∘ (extChartAt I x).symm) y := by
    have hc : ContMDiffAt 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
        (extChartAt I x).symm y := by
      have hon : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1)) I ((↑(⊤ : ℕ∞) : WithTop ℕ∞))
          (extChartAt I x).symm (extChartAt I x).target :=
        contMDiffOn_extChartAt_symm (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) x
      exact hon.contMDiffAt ((isOpen_extChartAt_target (I := I) x).mem_nhds
        ((extChartAt I x).map_source (mem_extChartAt_source (I := I) x)))
    have hfx : ContMDiffAt I 𝓘(ℝ, ℝ) ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) f x := hf x
    have hfx' : ContMDiffAt I 𝓘(ℝ, ℝ) ((↑(⊤ : ℕ∞) : WithTop ℕ∞)) f ((extChartAt I x).symm y) := by
      simpa [y] using hfx
    exact ContMDiffAt.comp (x := y) (g := f) (f := (extChartAt I x).symm)
      (hg := hfx') (hf := hc)
  have htrans : IsCriticalPointAt I ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x)) x ↔
      fderiv ℝ (f ∘ (extChartAt I x).symm) y = 0 :=
    isCriticalPointAt_iff_fderiv_of_localInverse I (x := x) (σ := (extChartAt I x))
      (τ := (extChartAt I x).symm) (h := f ∘ (extChartAt I x).symm)
      (hleft := hleft) (hright := hright)
      (hσmd := hσmd) (hτmd := hτmd) (hh := hh)
  have hfuneq : (f ∘ (extChartAt I x).symm) ∘ (extChartAt I x) =ᶠ[nhds x] f := by
    have hsrc : x ∈ (extChartAt I x).source := mem_extChartAt_source (I := I) x
    have hopen : IsOpen (extChartAt I x).source := isOpen_extChartAt_source (I := I) x
    exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hsrc)
      (fun z hz => congrArg f ((extChartAt I x).left_inv hz))
  have hcrit_eq : IsCriticalPointAt I ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x)) x ↔
      IsCriticalPointAt I f x := by
    change mfderiv I 𝓘(ℝ, ℝ) ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x)) x = 0 ↔
      mfderiv I 𝓘(ℝ, ℝ) f x = 0
    exact Iff.of_eq (congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L = 0)
      (Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hfuneq))
  have hcrit' : IsCriticalPointAt I ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x)) x :=
    htrans.2 (by simpa [y] using hzero)
  exact hcrit_eq.mp hcrit'

theorem manifoldSublevelSetEq_boundary_imp_boundary_of_le {m : ℕ} {H : Type} [TopologicalSpace H]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (g f : M → ℝ) (a : ℝ)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg_f : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hset : {x : M | g x ≤ a} = {x : M | f x ≤ a})
    (x : M) (hfx : f x = a) : g x = a := by
  by_contra hne
  have hgxle : g x ≤ a := by
    change x ∈ {x : M | g x ≤ a}
    rw [hset]
    exact le_of_eq hfx
  have hgxlt : g x < a := lt_of_le_of_ne hgxle hne
  have hint : x ∈ interior {y : M | f y ≤ a} := by
    have hsub : {y : M | g y < a} ⊆ {y : M | f y ≤ a} := by
      intro y hy
      change y ∈ {x : M | f x ≤ a}
      rw [← hset]
      change g y ≤ a
      exact le_of_lt (by change g y < a; exact hy)
    exact (interior_maximal hsub (isOpen_Iio.preimage hg.continuous)) hgxlt
  have hmax : IsLocalMax f x := by
    rw [IsLocalMax]
    have hnhd : {y : M | f y ≤ a} ∈ nhds x := mem_interior_iff_mem_nhds.mp hint
    filter_upwards [hnhd] with y hy
    rwa [← hfx] at hy
  let y₀ : MorseModel (m + 1) := (extChartAt I x) x
  have hx0 : (extChartAt I x).symm ((extChartAt I x) x) = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)
  have hmaxc : IsLocalMax (f ∘ (extChartAt I x).symm) y₀ := by
    rw [IsLocalMax]
    have hsymm_cont : ContinuousAt (extChartAt I x).symm y₀ := by
      exact (continuousOn_extChartAt_symm x).continuousAt
        ((isOpen_extChartAt_target (I := I) x).mem_nhds
          ((extChartAt I x).map_source (mem_extChartAt_source (I := I) x)))
    have ht : Filter.Tendsto (extChartAt I x).symm (nhds y₀) (nhds x) := by
      simpa [ContinuousAt, y₀, hx0] using hsymm_cont
    have hmax' : ∀ᶠ w in nhds x, f w ≤ f x := by
      simpa [IsLocalMax] using hmax
    have hmain : ∀ᶠ z in nhds y₀, f ((extChartAt I x).symm z) ≤ f x := by
      simpa [Function.comp_def] using (ht.eventually hmax')
    filter_upwards [hmain] with z hz
    simpa [Function.comp_def, y₀, hx0] using hz
  have hzero : fderiv ℝ (fun w : MorseModel (m + 1) => f ((extChartAt I x).symm w)) y₀ = 0 :=
    hmaxc.fderiv_eq_zero
  have hcrit : IsCriticalPointAt I f x :=
    isCriticalPointAt_of_fderiv_chartRep_eq_zero (I := I) f hf x (by simpa [y₀] using hzero)
  exact hreg_f x hfx hcrit

theorem contMDiffAt_manifoldSublevelSetEqIdentityInterior [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (g f : M → ℝ) (a : ℝ)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg_g : ∀ x : M, g x = a → ¬ IsCriticalPointAt I g x)
    (hreg_f : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hset : {x : M | g x ≤ a} = {x : M | f x ≤ a})
    (x : SublevelSpace g a) (hx : g x.1 < a)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) :=
      manifoldSublevelChartedSpace I g a hg hreg_g)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f a) :=
      manifoldSublevelChartedSpace I f a hf hreg_f)
    (hchart₁ : ∀ y : SublevelSpace g a, hcs₁.chartAt y =
      (if h : g y.1 = a then manifoldSublevelBoundaryChart I g a y h hg hreg_g
        else manifoldSublevelInteriorChart I g a y (lt_of_le_of_ne (show g y.1 ≤ a from y.2) h) hg) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace f a, hcs₂.chartAt y =
      (if h : f y.1 = a then manifoldSublevelBoundaryChart I f a y h hf hreg_f
        else manifoldSublevelInteriorChart I f a y (lt_of_le_of_ne (show f y.1 ≤ a from y.2) h) hf) := by
      intro y
      rfl) :
    ContMDiffAt (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g a => (⟨y.1, by
        have : y.1 ∈ {x : M | f x ≤ a} := by
          rw [← hset]
          exact y.2
        exact this⟩ : SublevelSpace f a)) x := by
  classical
  letI := hcs₁
  letI := hcs₂
  have hmap : ∀ y : M, g y ≤ a → f y ≤ a := by
    intro y hy
    change y ∈ {x : M | f x ≤ a}
    rw [← hset]
    exact hy
  rw [contMDiffAt_iff]
  constructor
  · have hcont : Continuous (fun y : SublevelSpace g a => y.1) := continuous_subtype_val
    exact (Continuous.subtype_mk hcont (fun y => hmap y.1 y.2)).continuousAt
  · let x₂ : SublevelSpace f a := ⟨x.1, hmap x.1 x.2⟩
    let c₁ : OpenPartialHomeomorph (SublevelSpace g a) (MorseHalfSpace m) :=
      manifoldSublevelInteriorChart I g a x hx hg
    have hchart₁' : hcs₁.chartAt x = c₁ := by
      rw [hchart₁ x]
      rw [dif_neg (ne_of_lt hx)]
    let b₁ : ContDiffBump ((extChartAt I x.1) x.1) := sublevelPullbackBump I x.1
    let hb₁ : Metric.closedBall ((extChartAt I x.1) x.1) b₁.rOut ⊆ (extChartAt I x.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x.1
    let b₂ : ContDiffBump ((extChartAt I x₂.1) x₂.1) := sublevelPullbackBump I x₂.1
    let hb₂ : Metric.closedBall ((extChartAt I x₂.1) x₂.1) b₂.rOut ⊆ (extChartAt I x₂.1).target :=
      sublevelPullbackBump_closedBall_target (I := I) x₂.1
    let g₁c : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I g x.1 b₁
    let f₂c : MorseModel (m + 1) → ℝ := sublevelPullbackCutoff I f x₂.1 b₂
    let p₁ : SublevelSpace g₁c a := sublevelPullbackCutoffPoint I g a x b₁
    let p₂ : SublevelSpace f₂c a := sublevelPullbackCutoffPoint I f a x₂ b₂
    let hg₁c : ContDiff ℝ (⊤ : ℕ∞) g₁c := contDiff_sublevelPullbackCutoff I g hg x.1 b₁ hb₁
    let hf₂c : ContDiff ℝ (⊤ : ℕ∞) f₂c := contDiff_sublevelPullbackCutoff I f hf x₂.1 b₂ hb₂
    let pb₁ : OpenPartialHomeomorph (SublevelSpace g a) (SublevelSpace g₁c a) :=
      sublevelPullbackChart I g a x b₁ hb₁
    let pb₂ : OpenPartialHomeomorph (SublevelSpace f a) (SublevelSpace f₂c a) :=
      sublevelPullbackChart I f a x₂ b₂ hb₂
    let mi₁ : OpenPartialHomeomorph (SublevelSpace g₁c a) (MorseHalfSpace m) :=
      sublevelInteriorChart g₁c a (sublevelPullbackCutoffPoint I g a x b₁)
        (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c
    let s₁ : ℝ := sublevelInteriorShift g₁c a p₁ (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c
    let Φc : MorseModel (m + 1) → MorseModel (m + 1) :=
      fun y => (extChartAt I x₂.1) ((extChartAt I x.1).symm y)
    have hpb₁src : x ∈ pb₁.source := mem_sublevelPullbackChart_source I g a x b₁ hb₁
    have hpb₁val : (pb₁ x).1 = (extChartAt I x.1) x.1 := by
      exact sublevelPullbackChart_apply_of_mem I g a x b₁ hb₁ hpb₁src
    have hz₀ : (extChartAt (morseModelWithCornersHalfSpace m) x x) =
        (morseModelWithCornersHalfSpace m) (c₁ x) := by
      simp [extChartAt, hchart₁']
    have hz₀range : (extChartAt (morseModelWithCornersHalfSpace m) x x) ∈
        Set.range (morseModelWithCornersHalfSpace m) := by
      simp [extChartAt, hchart₁']
    have hψ₁At : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => morseHalfSpaceShift (-s₁) y)
        (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      (contDiff_morseHalfSpaceShift (m := m) (-s₁)).contDiffAt
    have hψ₁z₀ : morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x) =
        (extChartAt I x.1) x.1 := by
      have hu : (c₁ x : MorseHalfSpace m) ∈ mi₁.target := by
        have hsrc : x ∈ c₁.source := mem_manifoldSublevelInteriorChart_source I g a x hx hg
        have htgt : (c₁ x : MorseHalfSpace m) ∈ c₁.target := c₁.map_source hsrc
        have hsplit := (by simpa [c₁, manifoldSublevelInteriorChart] using htgt)
        exact hsplit.1
      have hsm := sublevelInteriorChart_symm_value g₁c a p₁
        (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c (z := (c₁ x : MorseHalfSpace m)) hu
      have hsm' : (mi₁.symm (c₁ x : MorseHalfSpace m) : SublevelSpace g₁c a).1 =
          morseHalfSpaceShift (-s₁) (c₁ x : MorseHalfSpace m) := by
        simpa [s₁] using congrArg Subtype.val hsm
      have hleft : mi₁.symm (c₁ x : MorseHalfSpace m) = pb₁ x := by
        have hpb₁eq : pb₁ x = p₁ := by
          apply Subtype.ext
          simpa [p₁] using hpb₁val
        have hsrc' : (pb₁ x) ∈ mi₁.source := by
          rw [hpb₁eq]
          exact mem_sublevelInteriorChart_source g₁c a p₁
            (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c
        exact mi₁.left_inv hsrc'
      rw [hz₀]
      change morseHalfSpaceShift (-s₁) (c₁ x : MorseHalfSpace m) = (extChartAt I x.1) x.1
      rw [← hsm']
      rw [hleft]
      exact hpb₁val
    have hΦcAt : ContDiffAt ℝ (⊤ : ℕ∞) Φc
        (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x)) := by
      have hright : Φc =ᶠ[nhds (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x))]
          (id : MorseModel (m + 1) → MorseModel (m + 1)) := by
        refine Filter.eventuallyEq_of_mem ((isOpen_extChartAt_target (I := I) x.1).mem_nhds ?_) ?_
        · rw [hψ₁z₀]
          exact (extChartAt I x.1).map_source (mem_extChartAt_source (I := I) x.1)
        · intro w hw
          simpa [Φc, x₂] using (extChartAt I x.1).right_inv hw
      exact (contDiffAt_id : ContDiffAt ℝ (⊤ : ℕ∞)
        (id : MorseModel (m + 1) → MorseModel (m + 1))
        (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x))).congr_of_eventuallyEq
        hright
    have hmidAt : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z))
        (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      have hmidAt' : ContDiffAt ℝ (⊤ : ℕ∞)
          (Φc ∘ fun z : MorseModel (m + 1) => morseHalfSpaceShift (-s₁) z)
          (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
        hΦcAt.comp (f := fun z : MorseModel (m + 1) => morseHalfSpaceShift (-s₁) z)
          (x := extChartAt (morseModelWithCornersHalfSpace m) x x) hψ₁At
      simpa [Function.comp_def] using hmidAt'
    have hmem₀ : dist (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x)) p₁.1 <
        sublevelInteriorRadius g₁c a p₁ (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c := by
      rw [hψ₁z₀]
      have hpb₁val' : p₁.1 = (extChartAt I x.1) x.1 := by
        dsimp [p₁]
        rfl
      rw [hpb₁val']
      have hρpos : 0 < sublevelInteriorRadius g₁c a p₁
          (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c := by
        dsimp [sublevelInteriorRadius]
        exact (Classical.choose_spec (Metric.mem_nhds_iff.mp ((isOpen_Iio.preimage hg₁c.continuous).mem_nhds
          (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx)))).1
      exact Metric.mem_ball_self hρpos
    have hpre₁ : (fun z : MorseModel (m + 1) =>
          morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∧
          dist (morseHalfSpaceShift (-s₁) z) p₁.1 < sublevelInteriorRadius g₁c a p₁
            (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c) ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      have hcont₁ : Continuous (fun z : MorseModel (m + 1) =>
          morseHalfSpaceShift (-s₁) z) :=
        (contDiff_morseHalfSpaceShift (m := m) (-s₁)).continuous
      have hcont₂ : Continuous (fun z : MorseModel (m + 1) =>
          dist (morseHalfSpaceShift (-s₁) z) p₁.1) := by
        have hshift : Continuous (fun z : MorseModel (m + 1) => morseHalfSpaceShift (-s₁) z) :=
          (contDiff_morseHalfSpaceShift (m := m) (-s₁)).continuous
        exact continuous_dist.comp (hshift.prodMk continuous_const)
      exact Filter.inter_mem
        (hcont₁.continuousAt.preimage_mem_nhds (by
          rw [hψ₁z₀]
          exact Metric.ball_mem_nhds ((extChartAt I x.1) x.1) b₁.rIn_pos))
        (hcont₂.continuousAt.preimage_mem_nhds (by
          change {y : ℝ | y < sublevelInteriorRadius g₁c a p₁
              (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c} ∈
            nhds (dist (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x)) p₁.1)
          exact (isOpen_Iio.mem_nhds hmem₀)))
    have hpre₂ : (fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z)) ⁻¹'
          Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
      (ContDiffAt.continuousAt hmidAt).preimage_mem_nhds (by
        change Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn ∈
          nhds (Φc (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x)))
        rw [hψ₁z₀]
        have hval : Φc ((extChartAt I x.1) x.1) = (extChartAt I x₂.1) x.1 := by
          simp [Φc, x₂]
        rw [hval]
        exact Metric.ball_mem_nhds ((extChartAt I x₂.1) x₂.1) b₂.rIn_pos)
    have hpre₃ : (fun z : MorseModel (m + 1) =>
          (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z) ∈ (extChartAt I x₂.1).source) ∈
        nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
      let z₀ : MorseModel (m + 1) := extChartAt (morseModelWithCornersHalfSpace m) x x
      have hφ₁ : ContinuousAt (fun z : MorseModel (m + 1) =>
          (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z)) z₀ := by
        have hsm : ContinuousAt (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z₀) := by
          rw [hψ₁z₀]
          exact (continuousOn_extChartAt_symm x.1).continuousAt
            ((isOpen_extChartAt_target (I := I) x.1).mem_nhds
              ((extChartAt I x.1).map_source (mem_extChartAt_source (I := I) x.1)))
        exact hsm.comp (ContDiffAt.continuousAt hψ₁At)
      have hmem : (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z₀) ∈
          (extChartAt I x₂.1).source := by
        rw [hψ₁z₀, (extChartAt I x.1).left_inv (mem_extChartAt_source (I := I) x.1)]
        exact mem_extChartAt_source (I := I) x₂.1
      exact hφ₁.preimage_mem_nhds ((isOpen_extChartAt_source (I := I) x₂.1).mem_nhds hmem)
    by_cases hxb : f x.1 = a
    · let c₂ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) :=
        manifoldSublevelBoundaryChart I f a x₂ hxb hf hreg_f
      have hchart₂' : hcs₂.chartAt x₂ = c₂ := by
        rw [hchart₂ x₂]
        rw [dif_pos hxb]
      let hx₂b : f x₂.1 = a := hxb
      let hr₂c : fderiv ℝ f₂c p₂.1 ≠ 0 :=
        fderiv_sublevelPullbackCutoffPoint_ne_zero I f hf a hreg_f x₂ b₂ hx₂b
      let mi₂ : OpenPartialHomeomorph (SublevelSpace f₂c a) (MorseHalfSpace m) :=
        sublevelBoundaryChart f₂c a p₂ (sublevelPullbackCutoffPoint_value I f a x₂ b₂ hx₂b) hf₂c hr₂c
      let F : MorseModel (m + 1) → MorseModel (m + 1) :=
        fun z => sublevelBoundaryChartValue f₂c a p₂ (sublevelPullbackCutoffPoint_value I f a x₂ b₂ hx₂b)
          hf₂c hr₂c (Φc (morseHalfSpaceShift (-s₁) z))
      have hFAt : ContDiffAt ℝ (⊤ : ℕ∞) F (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
        have hstep : ContDiffAt ℝ (⊤ : ℕ∞)
            (fun y : MorseModel (m + 1) => sublevelBoundaryChartValue f₂c a p₂
              (sublevelPullbackCutoffPoint_value I f a x₂ b₂ hx₂b) hf₂c hr₂c y)
            (Φc (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x))) :=
          (contDiff_sublevelBoundaryChartValue f₂c a p₂ (sublevelPullbackCutoffPoint_value I f a x₂ b₂ hx₂b)
            hf₂c hr₂c).contDiffAt
        have hcomp := ContDiffAt.comp (x := extChartAt (morseModelWithCornersHalfSpace m) x x)
          hstep hmidAt
        simpa [F] using hcomp
      have hFAt' : ContDiffWithinAt ℝ (⊤ : ℕ∞) F
          (Set.range (morseModelWithCornersHalfSpace m))
          (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
        hFAt.contDiffWithinAt
      have hnhd : {z : MorseModel (m + 1) |
            morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∧
            dist (morseHalfSpaceShift (-s₁) z) p₁.1 < sublevelInteriorRadius g₁c a p₁
              (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c} ∩
          (((fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z)) ⁻¹'
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
            (fun z : MorseModel (m + 1) =>
              (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z) ∈ (extChartAt I x₂.1).source)) ∩
          Set.range (morseModelWithCornersHalfSpace m) ∈
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m)) := by
        refine Filter.inter_mem ?_ ?_
        · refine Filter.inter_mem ?_ ?_
          · exact nhdsWithin_le_nhds hpre₁
          · refine Filter.inter_mem ?_ ?_
            · exact nhdsWithin_le_nhds hpre₂
            · exact nhdsWithin_le_nhds hpre₃
        · exact self_mem_nhdsWithin
      have hval : ∀ z ∈ {z : MorseModel (m + 1) |
            morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∧
            dist (morseHalfSpaceShift (-s₁) z) p₁.1 < sublevelInteriorRadius g₁c a p₁
              (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c} ∩
          (((fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z)) ⁻¹'
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
            (fun z : MorseModel (m + 1) =>
              (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z) ∈ (extChartAt I x₂.1).source)) ∩
          Set.range (morseModelWithCornersHalfSpace m),
          (extChartAt (morseModelWithCornersHalfSpace m) x₂ ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : M | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            (extChartAt (morseModelWithCornersHalfSpace m) x).symm) z = F z := by
        intro z hz
        have hz₁b : morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn := hz.1.1.1
        have hz₁ : dist (morseHalfSpaceShift (-s₁) z) p₁.1 <
            sublevelInteriorRadius g₁c a p₁ (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c := hz.1.1.2
        have hz₂ : Φc (morseHalfSpaceShift (-s₁) z) ∈
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn := hz.1.2.1
        have hz₃ : (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z) ∈
            (extChartAt I x₂.1).source := hz.1.2.2
        have hzrange : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.2
        have hzmem : 0 ≤ z (Fin.last m) := by
          rw [range_morseModelWithCornersHalfSpace] at hzrange
          exact hzrange
        change ((hcs₂.chartAt x₂).extend (morseModelWithCornersHalfSpace m) ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : M | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)).symm) z = F z
        rw [hchart₂']
        rw [hchart₁']
        simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
        change (morseModelWithCornersHalfSpace m)
            (c₂ ((fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : M | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a))
              (c₁.symm ((morseModelWithCornersHalfSpace m).symm z)))) = F z
        have hu : (morseModelWithCornersHalfSpace m).symm z = (⟨z, hzmem⟩ : MorseHalfSpace m) := by
          apply Subtype.ext
          exact morseHalfSpaceClamp_of_mem m hzmem
        rw [hu]
        have hmi₁tgt : (⟨z, hzmem⟩ : MorseHalfSpace m) ∈ mi₁.target := hz₁
        have hmi₁sm := sublevelInteriorChart_symm_value g₁c a p₁
          (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c (z := (⟨z, hzmem⟩ : MorseHalfSpace m)) hmi₁tgt
        have hmi₁sm' : (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m) : SublevelSpace g₁c a).1 =
            morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m) := by
          simpa [s₁] using congrArg Subtype.val hmi₁sm
        have hpb₁tgt : (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)) ∈ pb₁.target := by
          change (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 ∈
            Metric.ball ((extChartAt I x.1) x.1) b₁.rIn
          rwa [hmi₁sm']
        have hc₁sm : (c₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 =
            (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m)) := by
          change (pb₁.symm (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m))).1 = _
          rw [sublevelPullbackChart_symm_value I g a x b₁ hb₁ hpb₁tgt, hmi₁sm']
        let y₁ : SublevelSpace g a := c₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)
        let w₂ : SublevelSpace f a := ⟨y₁.1, hmap y₁.1 y₁.2⟩
        have hΘ : y₁.1 = (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m)) := hc₁sm
        have hpb₂src : w₂ ∈ pb₂.source := by
          change w₂.1 ∈ (extChartAt I x₂.1).source ∧ (extChartAt I x₂.1) w₂.1 ∈
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
          constructor
          · change y₁.1 ∈ (extChartAt I x₂.1).source
            rw [hΘ]
            exact hz₃
          · change (extChartAt I x₂.1) y₁.1 ∈
              Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
            rw [hΘ]
            change Φc (morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m)) ∈
              Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
            simpa using hz₂
        have hpb₂val : (pb₂ w₂).1 = (extChartAt I x₂.1) w₂.1 :=
          sublevelPullbackChart_apply_of_mem I f a x₂ b₂ hb₂ hpb₂src
        have hmi₂val : (mi₂ (pb₂ w₂) : MorseModel (m + 1)) =
            sublevelBoundaryChartValue f₂c a p₂ (sublevelPullbackCutoffPoint_value I f a x₂ b₂ hx₂b)
              hf₂c hr₂c (pb₂ w₂).1 := by
          rw [sublevelBoundaryChart_apply_value' f₂c a p₂ (sublevelPullbackCutoffPoint_value I f a x₂ b₂ hx₂b)
            hf₂c hr₂c (pb₂ w₂)]
        change (morseModelWithCornersHalfSpace m) (mi₂ (pb₂ w₂)) = F z
        change (mi₂ (pb₂ w₂) : MorseModel (m + 1)) = F z
        rw [hmi₂val]
        rw [hpb₂val]
        dsimp [F]
        dsimp [w₂]
        rw [hΘ]
        dsimp [Φc]
      have hred : (extChartAt (morseModelWithCornersHalfSpace m) x₂ ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : M | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
            nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
              (Set.range (morseModelWithCornersHalfSpace m))] F := by
        refine Filter.eventuallyEq_of_mem (s := (fun z : MorseModel (m + 1) =>
            morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∧
            dist (morseHalfSpaceShift (-s₁) z) p₁.1 < sublevelInteriorRadius g₁c a p₁
              (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c) ∩
          (((fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z)) ⁻¹'
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
            (fun z : MorseModel (m + 1) =>
              (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z) ∈ (extChartAt I x₂.1).source)) ∩
          Set.range (morseModelWithCornersHalfSpace m)) hnhd ?_
        intro z hz
        exact hval z hz
      refine hFAt'.congr_of_eventuallyEq_of_mem ?_ hz₀range
      change ((extChartAt (morseModelWithCornersHalfSpace m) x₂) ∘
          (fun y : SublevelSpace g a => (⟨y.1, by
            have : y.1 ∈ {x : M | f x ≤ a} := by
              rw [← hset]
              exact y.2
            exact this⟩ : SublevelSpace f a)) ∘
          (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m))]
        (fun z : MorseModel (m + 1) => F z)
      simpa [extChartAt, hchart₁', hchart₂', x₂] using hred
    · have hx₂lt : f x.1 < a := lt_of_le_of_ne (hmap x.1 x.2) hxb
      let c₂ : OpenPartialHomeomorph (SublevelSpace f a) (MorseHalfSpace m) :=
        manifoldSublevelInteriorChart I f a x₂ hx₂lt hf
      have hchart₂' : hcs₂.chartAt x₂ = c₂ := by
        rw [hchart₂ x₂]
        rw [dif_neg (ne_of_lt hx₂lt)]
      let hx₂lt' : f x₂.1 < a := hx₂lt
      let mi₂ : OpenPartialHomeomorph (SublevelSpace f₂c a) (MorseHalfSpace m) :=
        sublevelInteriorChart f₂c a p₂ (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt') hf₂c
      let s₂ : ℝ := sublevelInteriorShift f₂c a p₂ (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt') hf₂c
      let F : MorseModel (m + 1) → MorseModel (m + 1) :=
        fun z => morseHalfSpaceShift s₂ (Φc (morseHalfSpaceShift (-s₁) z))
      have hFAt : ContDiffAt ℝ (⊤ : ℕ∞) F (extChartAt (morseModelWithCornersHalfSpace m) x x) := by
        have hshift₂ : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : MorseModel (m + 1) => morseHalfSpaceShift s₂ y)
            (Φc (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x))) :=
          (contDiff_morseHalfSpaceShift (m := m) s₂).contDiffAt
        have hcomp := ContDiffAt.comp (x := extChartAt (morseModelWithCornersHalfSpace m) x x)
          hshift₂ hmidAt
        simpa [F, Function.comp_def] using hcomp
      have hFAt' : ContDiffWithinAt ℝ (⊤ : ℕ∞) F
          (Set.range (morseModelWithCornersHalfSpace m))
          (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
        hFAt.contDiffWithinAt
      have hpre₂r : (fun z : MorseModel (m + 1) =>
            Φc (morseHalfSpaceShift (-s₁) z) ∈ Metric.ball p₂.1
              (sublevelInteriorRadius f₂c a p₂
                (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt') hf₂c)) ∈
          nhds (extChartAt (morseModelWithCornersHalfSpace m) x x) :=
        (ContDiffAt.continuousAt hmidAt).preimage_mem_nhds (by
          change Metric.ball p₂.1 (sublevelInteriorRadius f₂c a p₂
              (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt') hf₂c) ∈
            nhds (Φc (morseHalfSpaceShift (-s₁) (extChartAt (morseModelWithCornersHalfSpace m) x x)))
          rw [hψ₁z₀]
          have hval : Φc ((extChartAt I x.1) x.1) = (extChartAt I x₂.1) x.1 := by
            simp [Φc, x₂]
          rw [hval]
          have hρpos : 0 < sublevelInteriorRadius f₂c a p₂
              (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt') hf₂c := by
            dsimp [sublevelInteriorRadius]
            exact (Classical.choose_spec (Metric.mem_nhds_iff.mp ((isOpen_Iio.preimage hf₂c.continuous).mem_nhds
              (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt')))).1
          exact Metric.ball_mem_nhds p₂.1 hρpos)
      have hnhd : {z : MorseModel (m + 1) |
            morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∧
            dist (morseHalfSpaceShift (-s₁) z) p₁.1 < sublevelInteriorRadius g₁c a p₁
              (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c} ∩
          (((fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z)) ⁻¹'
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
            (fun z : MorseModel (m + 1) =>
              (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z) ∈ (extChartAt I x₂.1).source) ∩
            (fun z : MorseModel (m + 1) =>
              Φc (morseHalfSpaceShift (-s₁) z) ∈ Metric.ball p₂.1
                (sublevelInteriorRadius f₂c a p₂
                  (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt') hf₂c))) ∩
          Set.range (morseModelWithCornersHalfSpace m) ∈
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m)) := by
        refine Filter.inter_mem ?_ ?_
        · refine Filter.inter_mem ?_ ?_
          · exact nhdsWithin_le_nhds hpre₁
          · refine Filter.inter_mem ?_ ?_
            · refine Filter.inter_mem ?_ ?_
              · exact nhdsWithin_le_nhds hpre₂
              · exact nhdsWithin_le_nhds hpre₃
            · exact nhdsWithin_le_nhds hpre₂r
        · exact self_mem_nhdsWithin
      have hval : ∀ z ∈ {z : MorseModel (m + 1) |
            morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∧
            dist (morseHalfSpaceShift (-s₁) z) p₁.1 < sublevelInteriorRadius g₁c a p₁
              (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c} ∩
          (((fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z)) ⁻¹'
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
            (fun z : MorseModel (m + 1) =>
              (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z) ∈ (extChartAt I x₂.1).source) ∩
            (fun z : MorseModel (m + 1) =>
              Φc (morseHalfSpaceShift (-s₁) z) ∈ Metric.ball p₂.1
                (sublevelInteriorRadius f₂c a p₂
                  (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt') hf₂c))) ∩
          Set.range (morseModelWithCornersHalfSpace m),
          (extChartAt (morseModelWithCornersHalfSpace m) x₂ ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : M | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            (extChartAt (morseModelWithCornersHalfSpace m) x).symm) z = F z := by
        intro z hz
        have hz₁b : morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn := hz.1.1.1
        have hz₁ : dist (morseHalfSpaceShift (-s₁) z) p₁.1 <
            sublevelInteriorRadius g₁c a p₁ (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c := hz.1.1.2
        have hz₂ : Φc (morseHalfSpaceShift (-s₁) z) ∈
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn := hz.1.2.1.1
        have hz₃ : (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z) ∈
            (extChartAt I x₂.1).source := hz.1.2.1.2
        have hz₂r : Φc (morseHalfSpaceShift (-s₁) z) ∈ Metric.ball p₂.1
            (sublevelInteriorRadius f₂c a p₂
              (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt') hf₂c) := hz.1.2.2
        have hzrange : z ∈ Set.range (morseModelWithCornersHalfSpace m) := hz.2
        have hzmem : 0 ≤ z (Fin.last m) := by
          rw [range_morseModelWithCornersHalfSpace] at hzrange
          exact hzrange
        change ((hcs₂.chartAt x₂).extend (morseModelWithCornersHalfSpace m) ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : M | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            ((hcs₁.chartAt x).extend (morseModelWithCornersHalfSpace m)).symm) z = F z
        rw [hchart₂']
        rw [hchart₁']
        simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
        change (morseModelWithCornersHalfSpace m)
            (c₂ ((fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : M | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a))
              (c₁.symm ((morseModelWithCornersHalfSpace m).symm z)))) = F z
        have hu : (morseModelWithCornersHalfSpace m).symm z = (⟨z, hzmem⟩ : MorseHalfSpace m) := by
          apply Subtype.ext
          exact morseHalfSpaceClamp_of_mem m hzmem
        rw [hu]
        have hmi₁tgt : (⟨z, hzmem⟩ : MorseHalfSpace m) ∈ mi₁.target := hz₁
        have hmi₁sm := sublevelInteriorChart_symm_value g₁c a p₁
          (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c (z := (⟨z, hzmem⟩ : MorseHalfSpace m)) hmi₁tgt
        have hmi₁sm' : (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m) : SublevelSpace g₁c a).1 =
            morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m) := by
          simpa [s₁] using congrArg Subtype.val hmi₁sm
        have hpb₁tgt : (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)) ∈ pb₁.target := by
          change (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 ∈
            Metric.ball ((extChartAt I x.1) x.1) b₁.rIn
          rwa [hmi₁sm']
        have hc₁sm : (c₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)).1 =
            (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m)) := by
          change (pb₁.symm (mi₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m))).1 = _
          rw [sublevelPullbackChart_symm_value I g a x b₁ hb₁ hpb₁tgt, hmi₁sm']
        let y₁ : SublevelSpace g a := c₁.symm (⟨z, hzmem⟩ : MorseHalfSpace m)
        let w₂ : SublevelSpace f a := ⟨y₁.1, hmap y₁.1 y₁.2⟩
        have hΘ : y₁.1 = (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m)) := hc₁sm
        have hpb₂src : w₂ ∈ pb₂.source := by
          change w₂.1 ∈ (extChartAt I x₂.1).source ∧ (extChartAt I x₂.1) w₂.1 ∈
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
          constructor
          · change y₁.1 ∈ (extChartAt I x₂.1).source
            rw [hΘ]
            exact hz₃
          · change (extChartAt I x₂.1) y₁.1 ∈
              Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
            rw [hΘ]
            change Φc (morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m)) ∈
              Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn
            simpa using hz₂
        have hpb₂val : (pb₂ w₂).1 = (extChartAt I x₂.1) w₂.1 :=
          sublevelPullbackChart_apply_of_mem I f a x₂ b₂ hb₂ hpb₂src
        have hmi₂val : (mi₂ (pb₂ w₂) : MorseModel (m + 1)) =
            morseHalfSpaceShift s₂ ((extChartAt I x₂.1) w₂.1) := by
          rw [sublevelInteriorChart_apply_value f₂c a p₂
            (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt') hf₂c (y := pb₂ w₂) (by
              rw [hpb₂val]
              dsimp [w₂]
              rw [hΘ]
              change dist (Φc (morseHalfSpaceShift (-s₁) (⟨z, hzmem⟩ : MorseHalfSpace m))) p₂.1 <
                sublevelInteriorRadius f₂c a p₂
                  (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt') hf₂c
              exact hz₂r)]
          rw [hpb₂val]
        change (morseModelWithCornersHalfSpace m) (mi₂ (pb₂ w₂)) = F z
        change (mi₂ (pb₂ w₂) : MorseModel (m + 1)) = F z
        rw [hmi₂val]
        dsimp [F]
        dsimp [w₂]
        rw [hΘ]
        dsimp [Φc]
      have hred : (extChartAt (morseModelWithCornersHalfSpace m) x₂ ∘
            (fun y : SublevelSpace g a => (⟨y.1, by
              have : y.1 ∈ {x : M | f x ≤ a} := by
                rw [← hset]
                exact y.2
              exact this⟩ : SublevelSpace f a)) ∘
            (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
            nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
              (Set.range (morseModelWithCornersHalfSpace m))] F := by
        refine Filter.eventuallyEq_of_mem (s := (fun z : MorseModel (m + 1) =>
            morseHalfSpaceShift (-s₁) z ∈ Metric.ball ((extChartAt I x.1) x.1) b₁.rIn ∧
            dist (morseHalfSpaceShift (-s₁) z) p₁.1 < sublevelInteriorRadius g₁c a p₁
              (sublevelPullbackCutoffPoint_value_lt I g a x b₁ hx) hg₁c) ∩
          (((fun z : MorseModel (m + 1) => Φc (morseHalfSpaceShift (-s₁) z)) ⁻¹'
            Metric.ball ((extChartAt I x₂.1) x₂.1) b₂.rIn) ∩
            (fun z : MorseModel (m + 1) =>
              (extChartAt I x.1).symm (morseHalfSpaceShift (-s₁) z) ∈ (extChartAt I x₂.1).source) ∩
            (fun z : MorseModel (m + 1) =>
              Φc (morseHalfSpaceShift (-s₁) z) ∈ Metric.ball p₂.1
                (sublevelInteriorRadius f₂c a p₂
                  (sublevelPullbackCutoffPoint_value_lt I f a x₂ b₂ hx₂lt') hf₂c))) ∩
          Set.range (morseModelWithCornersHalfSpace m)) hnhd ?_
        intro z hz
        exact hval z hz
      refine hFAt'.congr_of_eventuallyEq_of_mem ?_ hz₀range
      change ((extChartAt (morseModelWithCornersHalfSpace m) x₂) ∘
          (fun y : SublevelSpace g a => (⟨y.1, by
            have : y.1 ∈ {x : M | f x ≤ a} := by
              rw [← hset]
              exact y.2
            exact this⟩ : SublevelSpace f a)) ∘
          (extChartAt (morseModelWithCornersHalfSpace m) x).symm) =ᶠ[
          nhdsWithin (extChartAt (morseModelWithCornersHalfSpace m) x x)
            (Set.range (morseModelWithCornersHalfSpace m))]
        (fun z : MorseModel (m + 1) => F z)
      simpa [extChartAt, hchart₁', hchart₂', x₂] using hred

theorem contMDiff_manifoldSublevelSetEqMap [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (g f : M → ℝ) (a : ℝ)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg_g : ∀ x : M, g x = a → ¬ IsCriticalPointAt I g x)
    (hreg_f : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hset : {x : M | g x ≤ a} = {x : M | f x ≤ a})
    (hbnd : ∀ x : M, g x = a → f x = a)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) :=
      manifoldSublevelChartedSpace I g a hg hreg_g)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f a) :=
      manifoldSublevelChartedSpace I f a hf hreg_f)
    (hchart₁ : ∀ y : SublevelSpace g a, hcs₁.chartAt y =
      (if h : g y.1 = a then manifoldSublevelBoundaryChart I g a y h hg hreg_g
        else manifoldSublevelInteriorChart I g a y (lt_of_le_of_ne (show g y.1 ≤ a from y.2) h) hg) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace f a, hcs₂.chartAt y =
      (if h : f y.1 = a then manifoldSublevelBoundaryChart I f a y h hf hreg_f
        else manifoldSublevelInteriorChart I f a y (lt_of_le_of_ne (show f y.1 ≤ a from y.2) h) hf) := by
      intro y
      rfl) :
    ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      (fun y : SublevelSpace g a => (⟨y.1, by
        have : y.1 ∈ {x : M | f x ≤ a} := by
          rw [← hset]
          exact y.2
        exact this⟩ : SublevelSpace f a)) := by
  intro x
  by_cases hx : g x.1 = a
  · exact contMDiffAt_manifoldSublevelBoundaryMap (I := I) g f a a hg hf hreg_g hreg_f x hx id
      contMDiff_id
      (fun y hy => by
        change f y ≤ a
        have : y ∈ {x : M | f x ≤ a} := by
          rw [← hset]
          exact hy
        exact this)
      (hbnd x.1 hx) (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
  · have hxlt : g x.1 < a := lt_of_le_of_ne (show g x.1 ≤ a from x.2) hx
    exact contMDiffAt_manifoldSublevelSetEqIdentityInterior (I := I) g f a hg hf hreg_g hreg_f hset
      x hxlt (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)

theorem manifoldSublevelDiffeomorphOfSetEq [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M]
    (g f : M → ℝ) (a : ℝ)
    (hg : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hreg_g : ∀ x : M, g x = a → ¬ IsCriticalPointAt I g x)
    (hreg_f : ∀ x : M, f x = a → ¬ IsCriticalPointAt I f x)
    (hset : {x : M | g x ≤ a} = {x : M | f x ≤ a})
    (hg_le : ∀ x : M, g x ≤ f x)
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace g a) :=
      manifoldSublevelChartedSpace I g a hg hreg_g)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace f a) :=
      manifoldSublevelChartedSpace I f a hf hreg_f)
    (hchart₁ : ∀ y : SublevelSpace g a, hcs₁.chartAt y =
      (if h : g y.1 = a then manifoldSublevelBoundaryChart I g a y h hg hreg_g
        else manifoldSublevelInteriorChart I g a y (lt_of_le_of_ne (show g y.1 ≤ a from y.2) h) hg) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace f a, hcs₂.chartAt y =
      (if h : f y.1 = a then manifoldSublevelBoundaryChart I f a y h hf hreg_f
        else manifoldSublevelInteriorChart I f a y (lt_of_le_of_ne (show f y.1 ≤ a from y.2) h) hf) := by
      intro y
      rfl) :
    Nonempty (@Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace g a) _ hcs₁ (SublevelSpace f a) _ hcs₂ (⊤ : ℕ∞)) := by
  classical
  letI := hcs₁
  letI := hcs₂
  let toFun : SublevelSpace g a → SublevelSpace f a := fun y => ⟨y.1, by
    change y.1 ∈ {x : M | f x ≤ a}
    rw [← hset]
    exact y.2⟩
  let invFun : SublevelSpace f a → SublevelSpace g a := fun y => ⟨y.1, by
    change y.1 ∈ {x : M | g x ≤ a}
    rw [hset]
    exact y.2⟩
  let e : SublevelSpace g a ≃ SublevelSpace f a :=
    { toFun := toFun, invFun := invFun, left_inv := by intro y; rfl,
      right_inv := by intro y; rfl }
  have hbnd : ∀ x : M, g x = a → f x = a :=
    manifoldSublevelSetEq_boundary_imp_boundary g f a hset hg_le
  have hbnd' : ∀ x : M, f x = a → g x = a :=
    manifoldSublevelSetEq_boundary_imp_boundary_of_le (I := I) g f a hg hf hreg_f hset
  have hto : ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      toFun := by
    simpa [toFun] using contMDiff_manifoldSublevelSetEqMap (I := I) g f a hg hf hreg_g hreg_f hset hbnd
      (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
  have hinv : ContMDiff (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m) (⊤ : ℕ∞)
      invFun := by
    simpa [invFun] using contMDiff_manifoldSublevelSetEqMap (I := I) f g a hf hg hreg_f hreg_g hset.symm hbnd'
      (hcs₁ := hcs₂) (hcs₂ := hcs₁) (hchart₁ := hchart₂) (hchart₂ := hchart₁)
  let d : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace g a) _ hcs₁ (SublevelSpace f a) _ hcs₂ (⊤ : ℕ∞) := by
    refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
    · simpa [toFun] using hto
    · simpa [invFun] using hinv
  exact ⟨d⟩

end

end DifferentialGeometry.Topology.Morse
