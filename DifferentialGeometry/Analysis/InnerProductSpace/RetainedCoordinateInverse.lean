import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinateGraph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Smooth inverse of the actual retained coordinate on a graph

The equal-dimensional differential lower bound gives local inverses. Quantitative
injectivity glues their inverse functions on the whole open graph image.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_smooth_inverse_retained_coordinate_graph
    (L : Submodule ℝ H) (π : H →L[ℝ] F) (hπ : ‖π‖ ≤ 1)
    {m a R : ℝ} (hm : ∀ v ∈ L, m * ‖v‖ ≤ ‖π v‖) (hma : a < m)
    (hdim : Module.finrank ℝ L = Module.finrank ℝ F)
    (g : L → H) (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 R))
    (hDg : ∀ t ∈ Metric.ball (0 : L) R, ‖fderiv ℝ g t‖ ≤ a) (x : H) :
    IsOpen ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) ∧
    ∃ σ : F → L,
      Set.InvOn σ (fun t : L => π (x + t + g t)) (Metric.ball 0 R)
        ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) ∧
      ContDiffOn ℝ ∞ σ ((fun t : L => π (x + t + g t)) '' Metric.ball 0 R) := by
  classical
  let f : L → F := fun t => π (x + t + g t)
  let U : Set L := Metric.ball 0 R
  have hgd (t : L) (ht : t ∈ U) : DifferentiableAt ℝ g t :=
    (hg.contDiffAt (Metric.isOpen_ball.mem_nhds ht)).differentiableAt (by simp)
  have hinj : InjOn f U := injOn_retained_coordinate_graph L π hπ hm hma g hgd hDg x
  have hlocal (t : L) (ht : t ∈ U) :
      ∃ e : OpenPartialHomeomorph L F, t ∈ e.source ∧ e.source ⊆ U ∧
        (e : L → F) = f ∧ ContDiffAt ℝ ∞ e.symm (f t) := by
    have hgt := hg.contDiffAt (Metric.isOpen_ball.mem_nhds ht)
    have hft : ContDiffAt ℝ ∞ f t :=
      π.contDiff.contDiffAt.comp t ((contDiffAt_const.add L.subtypeL.contDiff.contDiffAt).add hgt)
    let A : L →L[ℝ] F := π.comp (L.subtypeL + fderiv ℝ g t)
    have hA : HasFDerivAt f A t := by
      exact π.hasFDerivAt.comp t
        (by
          convert! (((hasFDerivAt_const x t).add L.subtypeL.hasFDerivAt).add
            (hgd t ht).hasFDerivAt) using 1
          simp)
    have hAi : Function.Injective A := by
      apply (LinearMap.ker_eq_bot).mp
      apply le_antisymm _ bot_le
      intro v hv
      change A v = 0 at hv
      change v = 0
      have hl := retained_coordinate_fderiv_lower_bound L π hπ hm (fderiv ℝ g t) (hDg t ht) v
      change (m - a) * ‖v‖ ≤ ‖A v‖ at hl
      rw [hv, norm_zero] at hl
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
    have hAs : Function.Surjective A := by
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hAi
    let T : L ≃L[ℝ] F := ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr hAi) (LinearMap.range_eq_top.mpr hAs)
    have hT : HasFDerivAt f (T : L →L[ℝ] F) t := hA
    let e₀ := hft.toOpenPartialHomeomorph f hT (by simp)
    let e := e₀.restr U
    have hts : t ∈ e.source := by
      change t ∈ e₀.source ∩ interior U
      exact ⟨hft.mem_toOpenPartialHomeomorph_source hT (by simp),
        by simpa only [U, Metric.isOpen_ball.interior_eq] using ht⟩
    refine ⟨e, hts, ?_, rfl, ?_⟩
    · intro z hz
      have hz' : z ∈ interior (Metric.ball (0 : L) R) := hz.2
      rwa [Metric.isOpen_ball.interior_eq] at hz'
    · exact hft.to_localInverse hT (by simp)
  have hopen : IsOpen (f '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨e, hte, heU, he, _hes⟩ := hlocal t ht
    have hfe : f t ∈ e.target := he ▸ e.map_source hte
    apply Filter.mem_of_superset (e.open_target.mem_nhds hfe)
    intro z hz
    refine ⟨e.symm z, heU (e.map_target hz), ?_⟩
    rw [← he]
    exact e.right_inv hz
  let σ : F → L := fun y => if hy : y ∈ f '' U then (Classical.choose hy) else 0
  have hσ (y : F) (hy : y ∈ f '' U) : σ y ∈ U ∧ f (σ y) = y := by
    simpa only [σ, dite_eq_left hy] using Classical.choose_spec hy
  have hleft (t : L) (ht : t ∈ U) : σ (f t) = t :=
    hinj (hσ (f t) (mem_image_of_mem f ht)).1 ht
      (hσ (f t) (mem_image_of_mem f ht)).2
  refine ⟨hopen, σ, ⟨hleft, fun y hy => (hσ y hy).2⟩, ?_⟩
  intro y hy
  obtain ⟨e, hte, heU, he, hes⟩ := hlocal (σ y) (hσ y hy).1
  have hye : y ∈ e.target := by
    rw [← (hσ y hy).2, ← he]
    exact e.map_source hte
  have heImage : e.target ⊆ f '' U := by
    intro z hz
    refine ⟨e.symm z, heU (e.map_target hz), ?_⟩
    rw [← he]
    exact e.right_inv hz
  have hagree : σ =ᶠ[𝓝 y] e.symm := by
    filter_upwards [e.open_target.mem_nhds hye] with z hz
    apply hinj (hσ z (heImage hz)).1 (heU (e.map_target hz))
    rw [(hσ z (heImage hz)).2, ← he]
    exact (e.right_inv hz).symm
  rw [(hσ y hy).2] at hes
  exact (hes.congr_of_eventuallyEq hagree).contDiffWithinAt

end DifferentialGeometry.Analysis
