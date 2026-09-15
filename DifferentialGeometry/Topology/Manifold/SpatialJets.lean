import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.SpaceJets
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

variable {E F S : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem contDiffOn_and_continuousOn_spatial_iteratedFDeriv_extChartAt_of_leftInverse
    {G : ℝ → S → M} {f : M → F} {r : F → M} {J : Set ℝ} {V : Set S}
    {U : Set F} (p : M) (hV : IsOpen V) (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U) (hleft : Function.LeftInverse r f)
    (hUmap : MapsTo (fun q : ℝ × S => f (G q.1 q.2)) (J ×ˢ V) U)
    (hchart : MapsTo (Function.uncurry G) (J ×ˢ V) (extChartAt I p).source)
    (hGs : ∀ t ∈ J, ContDiffOn ℝ ∞ (fun x => f (G t x)) V)
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun q : ℝ × S => iteratedFDeriv ℝ k (fun x => f (G q.1 x)) q.2) (J ×ˢ V)) :
    (∀ t ∈ J, ContDiffOn ℝ ∞ (fun x => extChartAt I p (G t x)) V) ∧
      ∀ k : ℕ, ContinuousOn
        (fun q : ℝ × S => iteratedFDeriv ℝ k
          (fun x => extChartAt I p (G q.1 x)) q.2) (J ×ˢ V) := by
  let Ω : Set F := U ∩ r ⁻¹' (extChartAt I p).source
  have hΩ : IsOpen Ω := by
    apply hr.continuousOn.isOpen_inter_preimage hU
    rw [extChartAt_source]
    exact (chartAt H p).open_source
  have hR : ContDiffOn ℝ ∞ (fun y => extChartAt I p (r y)) Ω := by
    apply ContMDiffOn.contDiffOn
    apply (contMDiffOn_extChartAt (I := I) (x := p)).comp (hr.mono inter_subset_left)
    intro y hy
    simpa only [extChartAt_source] using hy.2
  have hmap : MapsTo (fun q : ℝ × S => f (G q.1 q.2)) (J ×ˢ V) Ω := by
    intro q hq
    refine ⟨hUmap hq, ?_⟩
    change r (f (G q.1 q.2)) ∈ (extChartAt I p).source
    rw [hleft]
    exact hchart hq
  have hcomp := contDiffOn_and_continuousOn_spatial_iteratedFDeriv_comp
    (G := fun t x => f (G t x)) (R := fun y => extChartAt I p (r y))
    hV hΩ hmap hR hGs hjets
  refine ⟨?_, ?_⟩
  · intro t ht
    have hc := hcomp.1 t ht
    have hfun : (fun x => extChartAt I p (r (f (G t x)))) =
        (fun x => extChartAt I p (G t x)) := by
      funext x
      rw [hleft (G t x)]
    rw [hfun] at hc
    exact hc
  · intro k
    apply ContinuousOn.congr (hcomp.2 k)
    intro q hq
    have hfun : (fun x => extChartAt I p (r (f (G q.1 x)))) =
        (fun x => extChartAt I p (G q.1 x)) := by
      funext x
      rw [hleft (G q.1 x)]
    exact congrArg (fun u : S → E => iteratedFDeriv ℝ k u q.2) hfun.symm

end DifferentialGeometry.Analysis
