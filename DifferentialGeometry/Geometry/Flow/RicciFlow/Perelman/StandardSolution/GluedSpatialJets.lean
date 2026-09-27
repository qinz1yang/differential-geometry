import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Limit.Smooth
import DifferentialGeometry.Geometry.Operator.Hessian.Basic
import Mathlib.Topology.ContinuousOn

set_option autoImplicit false
noncomputable section

open Set Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem gluedFamily_spatial_gram_jets
    (G H : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (T τ : ℝ) (hT : 0 < T) (hτ : 0 < τ)
    (hzero : H 0 = G T)
    (hG : ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × E =>
          iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
        (Icc 0 T ×ˢ interior (extChartAt 𝓘(ℝ, E) x₀).target))
    (hH : ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × E =>
          iteratedFDeriv ℝ r (chartGramOnE (H p.1) x₀ i j) p.2)
        (Icc 0 τ ×ˢ interior (extChartAt 𝓘(ℝ, E) x₀).target)) :
    ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × E =>
          iteratedFDeriv ℝ r
            (chartGramOnE (gluedFamily G H T p.1) x₀ i j) p.2)
        (Icc 0 (T + τ) ×ˢ
          interior (extChartAt 𝓘(ℝ, E) x₀).target) := by
  intro r x₀ i j
  have htarget :
      interior (extChartAt 𝓘(ℝ, E) x₀).target = (univ : Set E) := by
    simp only [extChartAt_model_space_eq_id,
      PartialEquiv.refl_target, interior_univ]
  rw [htarget]
  have hGc := hG r x₀ i j
  have hHc := hH r x₀ i j
  rw [htarget] at hGc hHc
  let f : ℝ × E → E [×r]→L[ℝ] ℝ := fun p =>
    iteratedFDeriv ℝ r
      (chartGramOnE (gluedFamily G H T p.1) x₀ i j) p.2
  change ContinuousOn f (Icc 0 (T + τ) ×ˢ (univ : Set E))
  have hleftSlice (t : ℝ) (ht : t ∈ Icc 0 T) :
      gluedFamily G H T t = G t := by
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact gluedFamily_of_lt G H T hlt
    · rw [heq, gluedFamily_at_endpoint, hzero]
  have hleft : ContinuousOn f (Icc 0 T ×ˢ (univ : Set E)) := by
    apply hGc.congr
    intro p hp
    dsimp only [f]
    rw [hleftSlice p.1 hp.1]
  have hshift : Continuous (fun p : ℝ × E => (p.1 - T, p.2)) :=
    (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hmaps :
      MapsTo (fun p : ℝ × E => (p.1 - T, p.2))
        (Icc T (T + τ) ×ˢ (univ : Set E))
        (Icc 0 τ ×ˢ (univ : Set E)) := by
    intro p hp
    refine ⟨⟨sub_nonneg.mpr hp.1.1, ?_⟩, mem_univ _⟩
    linarith [hp.1.2]
  have hrightTranslated := hHc.comp hshift.continuousOn hmaps
  have hright :
      ContinuousOn f (Icc T (T + τ) ×ˢ (univ : Set E)) := by
    apply hrightTranslated.congr
    intro p hp
    change
      iteratedFDeriv ℝ r
          (chartGramOnE (gluedFamily G H T p.1) x₀ i j) p.2 =
        iteratedFDeriv ℝ r
          (chartGramOnE (H (p.1 - T)) x₀ i j) p.2
    rw [gluedFamily_of_ge G H T hp.1.1]
  have hunion := hleft.union_of_isClosed hright
    (isClosed_Icc.prod isClosed_univ)
    (isClosed_Icc.prod isClosed_univ)
  rw [← union_prod,
    Icc_union_Icc_eq_Icc hT.le
      (le_add_of_nonneg_right hτ.le)] at hunion
  exact hunion

end DifferentialGeometry.PDE.RicciFlow
