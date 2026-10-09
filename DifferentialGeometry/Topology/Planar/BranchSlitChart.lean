import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

noncomputable section
set_option autoImplicit false
open Set Metric Manifold
open scoped ContDiff Topology

namespace DifferentialGeometry.Topology.Planar

/-- The punctured chart for the already selected radial straightening of an
original branch coordinate. Both total maps and both domains remain literal. -/
theorem exists_branch_slit_chart
    (e S : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} {R : ℝ}
    (hea : e a = 0)
    (heSource : e.source ⊆ Metric.ball (0 : ℂ) 1)
    (heBall : Metric.closedBall (0 : ℂ) R ⊆ e.target)
    (heForward : ContDiffOn ℝ ∞ (e : ℂ → ℂ) (e.source \ {a}))
    (heInverse : ContDiffOn ℝ ∞ (e.symm : ℂ → ℂ) (e.target \ {0}))
    (hSsource : S.source = Metric.ball 0 R)
    (hStarget : S.target = Metric.ball 0 R)
    (hSnorm : ∀ w ∈ Metric.closedBall (0 : ℂ) R,
      ‖S w‖ = ‖w‖ ∧ ‖S.symm w‖ = ‖w‖)
    (hSsmooth : ContDiffOn ℝ ∞ (S : ℂ → ℂ) (Metric.ball 0 R \ {0}))
    (hSismooth : ContDiffOn ℝ ∞ (S.symm : ℂ → ℂ) (Metric.ball 0 R \ {0})) :
    ∃ κ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
      κ.source = Metric.ball 0 R \ {0} ∧
      κ.target = e.source ∩ (e : ℂ → ℂ) ⁻¹' (Metric.ball 0 R \ {0}) ∧
      (∀ w, κ w = e.symm (S w)) ∧
      (∀ z, κ.symm z = S.symm (e z)) ∧
      κ.target ⊆ Metric.ball (0 : ℂ) 1 ∧
      Set.MapsTo κ κ.source (Metric.ball (0 : ℂ) 1) ∧
      (∀ ell : ℝ, 0 < ell → ell < 4 * R →
        ((ell / 4 : ℝ) : ℂ) ∈ κ.source ∧
        (-((ell / 4 : ℝ) : ℂ)) ∈ κ.source ∧
        Complex.I * ((ell / 4 : ℝ) : ℂ) ∈ κ.source) := by
  let D : Set ℂ := Metric.ball 0 R \ {0}
  let T : Set ℂ := e.source ∩ (e : ℂ → ℂ) ⁻¹' D
  have hDopen : IsOpen D := Metric.isOpen_ball.sdiff isClosed_singleton
  have hSmap : Set.MapsTo (S : ℂ → ℂ) D D := by
    intro w hw
    have hws : w ∈ S.source := by rw [hSsource]; exact hw.1
    refine ⟨?_, ?_⟩
    · rw [← hStarget]
      exact S.map_source hws
    · change S w ≠ 0
      intro hz
      have hn : ‖w‖ = 0 := by
        simpa only [hz, norm_zero] using (hSnorm w (Metric.ball_subset_closedBall hw.1)).1.symm
      exact hw.2 (norm_eq_zero.mp hn)
  have hSimap : Set.MapsTo (S.symm : ℂ → ℂ) D D := by
    intro w hw
    have hwt : w ∈ S.target := by rw [hStarget]; exact hw.1
    refine ⟨?_, ?_⟩
    · rw [← hSsource]
      exact S.map_target hwt
    · change S.symm w ≠ 0
      intro hz
      have hn : ‖w‖ = 0 := by
        simpa only [hz, norm_zero] using (hSnorm w (Metric.ball_subset_closedBall hw.1)).2.symm
      exact hw.2 (norm_eq_zero.mp hn)
  have heSD (w : ℂ) (hw : w ∈ D) : S w ∈ e.target \ {0} :=
    ⟨heBall (Metric.ball_subset_closedBall (hSmap hw).1), (hSmap hw).2⟩
  have hTsource : T ⊆ e.source \ {a} := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    change z ≠ a
    intro hza
    have hez : e z ≠ 0 := hz.2.2
    exact hez (by rw [hza, hea])
  have hforward : ContDiffOn ℝ ∞ (fun w => e.symm (S w)) D :=
    heInverse.comp hSsmooth heSD
  have hinverse : ContDiffOn ℝ ∞ (fun z => S.symm (e z)) T :=
    hSismooth.comp (heForward.mono hTsource) (fun _ hz => hz.2)
  let κ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ :=
    { toFun := fun w => e.symm (S w)
      invFun := fun z => S.symm (e z)
      source := D
      target := T
      map_source' := by
        intro w hw
        have hew := (heSD w hw).1
        refine ⟨e.map_target hew, ?_⟩
        change e (e.symm (S w)) ∈ D
        rw [e.right_inv hew]
        exact hSmap hw
      map_target' := fun _ hz => hSimap hz.2
      left_inv' := by
        intro w hw
        rw [e.right_inv (heSD w hw).1]
        exact S.left_inv (by rw [hSsource]; exact hw.1)
      right_inv' := by
        intro z hz
        have hezS : e z ∈ S.target := by rw [hStarget]; exact hz.2.1
        rw [S.right_inv hezS]
        exact e.left_inv hz.1
      open_source := hDopen
      open_target := e.continuousOn.isOpen_inter_preimage e.open_source hDopen
      contMDiffOn_toFun := hforward.contMDiffOn
      contMDiffOn_invFun := hinverse.contMDiffOn }
  refine ⟨κ, rfl, rfl, fun _ => rfl, fun _ => rfl,
    (fun _ hz => heSource hz.1), ?_, ?_⟩
  · intro w hw
    exact heSource (κ.toPartialEquiv.map_source hw).1
  · intro ell hell hellR
    have hr : 0 < ell / 4 := by linarith
    have hrR : ell / 4 < R := by linarith
    have hpoint (z : ℂ) (hz : ‖z‖ = ell / 4) : z ∈ D := by
      refine ⟨?_, ?_⟩
      · simpa only [Metric.mem_ball, dist_zero_right, hz] using hrR
      · change z ≠ 0
        intro hz0
        have hzero : (0 : ℝ) = ell / 4 := by simpa only [hz0, norm_zero] using hz
        linarith
    exact ⟨hpoint _ (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]),
      hpoint _ (by rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]),
      hpoint _ (by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr])⟩

end DifferentialGeometry.Topology.Planar
