import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The zero set of a regular function in the plane is a smooth curve, with its coordinate
(lane S-BCF03; analytic kernel of the half charts of the circle-base curve of BCF03)

For two functions `u, w` smooth near `0` of the plane `ℝ²`, vanishing at `0`, with linearly
independent differentials at `0` (`Ξ = (u, w)` has an injective, hence invertible, derivative),
the inverse function theorem gives an open neighbourhood `N` of `0` and a smooth curve
`c : (−ε, ε) → ℝ²` with `c 0 = 0`, `u ∘ c = 0`, `w ∘ c = id` and `N ∩ {u = 0} = c ((−ε, ε))`
(the second coordinate `w` of the corner chart): the curve is `s ↦ Ξ⁻¹(0, s)`. With `w` the
face function of a second face this describes the corner `{u = 0, w ≤ 0}` as `c ((−ε, 0])`; with
`w` a linear functional independent of `du` it describes `{u = 0}` near `0`.

* `exists_curve_of_independent_BCF`: the statement; no condition on `u, w` away from a neighbourhood
  of `0`.
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **A smooth curve through `0` cut out by `u = 0`, parametrized by `w`.** -/
theorem exists_curve_of_independent_BCF {u w : E2 → ℝ} {P : Set E2} (hP : IsOpen P)
    (h0 : (0 : E2) ∈ P)
    (hu : ContDiffOn ℝ ∞ u P) (hw : ContDiffOn ℝ ∞ w P) (hu0 : u 0 = 0) (hw0 : w 0 = 0)
    (hind : Injective fun v : E2 => (fderiv ℝ u 0 v, fderiv ℝ w 0 v)) :
    ∃ (ε : ℝ) (N : Set E2) (c : ℝ → E2), 0 < ε ∧ IsOpen N ∧ (0 : E2) ∈ N ∧ N ⊆ P ∧
      ContDiffOn ℝ ∞ c (Ioo (-ε) ε) ∧ c 0 = 0 ∧
      (∀ s ∈ Ioo (-ε) ε, c s ∈ N ∧ u (c s) = 0 ∧ w (c s) = s) ∧
      (∀ x ∈ N, u x = 0 → w x ∈ Ioo (-ε) ε ∧ c (w x) = x) ∧
      (∀ s ∈ Ioo (-ε) ε, deriv c s ≠ 0) := by
  classical
  set Ξ : E2 → ℝ × ℝ := fun x => (u x, w x) with hΞ
  have hΞc : ContDiffOn ℝ ∞ Ξ P := hu.prodMk hw
  have hΞat : ∀ x ∈ P, ContDiffAt ℝ ∞ Ξ x := fun x hx => hΞc.contDiffAt (hP.mem_nhds hx)
  have hdiff : ∀ x ∈ P, HasFDerivAt Ξ (fderiv ℝ Ξ x) x := fun x hx =>
    ((hΞat x hx).differentiableAt (by simp)).hasFDerivAt
  -- the derivative at `0`
  have hdu : DifferentiableAt ℝ u 0 := ((hu.contDiffAt (hP.mem_nhds h0)).differentiableAt (by simp))
  have hdw : DifferentiableAt ℝ w 0 := ((hw.contDiffAt (hP.mem_nhds h0)).differentiableAt (by simp))
  have hf0 : fderiv ℝ Ξ 0 = (fderiv ℝ u 0).prod (fderiv ℝ w 0) :=
    (hdu.hasFDerivAt.prodMk hdw.hasFDerivAt).fderiv
  have hinj0 : Injective (fderiv ℝ Ξ 0) := by
    rw [hf0]
    exact hind
  have hrank : Module.finrank ℝ E2 = Module.finrank ℝ (ℝ × ℝ) := by
    simp [Module.finrank_prod]
  have hsurj0 : Surjective (fderiv ℝ Ξ 0) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj0
  let g0 : E2 ≃L[ℝ] ℝ × ℝ := ContinuousLinearEquiv.ofBijective (fderiv ℝ Ξ 0)
    (LinearMap.ker_eq_bot.mpr hinj0) (LinearMap.range_eq_top.mpr hsurj0)
  have hg0 : (g0 : E2 →L[ℝ] ℝ × ℝ) = fderiv ℝ Ξ 0 :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  let e : OpenPartialHomeomorph E2 (ℝ × ℝ) :=
    (hΞat 0 h0).toOpenPartialHomeomorph Ξ (f' := g0) (by rw [hg0]; exact hdiff 0 h0) (by simp)
  have he_coe : (e : E2 → ℝ × ℝ) = Ξ := rfl
  have he0 : (0 : E2) ∈ e.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _
  -- the set where the derivative is invertible
  have hfd : ContinuousOn (fderiv ℝ Ξ) P := hΞc.continuousOn_fderiv_of_isOpen hP (by simp)
  have hOpenEq : IsOpen (range ((↑) : (E2 ≃L[ℝ] ℝ × ℝ) → E2 →L[ℝ] ℝ × ℝ)) :=
    ContinuousLinearEquiv.isOpen
  have hUinv : IsOpen (P ∩ fderiv ℝ Ξ ⁻¹' range ((↑) : (E2 ≃L[ℝ] ℝ × ℝ) → E2 →L[ℝ] ℝ × ℝ)) :=
    hfd.isOpen_inter_preimage hP hOpenEq
  have h0inv : (0 : E2) ∈ P ∩ fderiv ℝ Ξ ⁻¹' range ((↑) : (E2 ≃L[ℝ] ℝ × ℝ) → E2 →L[ℝ] ℝ × ℝ) :=
    ⟨h0, g0, hg0⟩
  set S : Set E2 := e.source ∩ (P ∩ fderiv ℝ Ξ ⁻¹'
    range ((↑) : (E2 ≃L[ℝ] ℝ × ℝ) → E2 →L[ℝ] ℝ × ℝ)) with hS
  have hSo : IsOpen S := e.open_source.inter hUinv
  have hS0 : (0 : E2) ∈ S := ⟨he0, h0inv⟩
  have heS : IsOpen (e '' S) := e.isOpen_image_of_subset_source hSo inter_subset_left
  have he0t : ((0 : ℝ), (0 : ℝ)) ∈ e '' S := ⟨0, hS0, by simp [he_coe, hΞ, hu0, hw0]⟩
  -- the interval
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.mp heS _ he0t
  -- `w` is continuous on `P`; the neighbourhood `N`
  have hwc : ContinuousOn w P := hw.continuousOn
  have hNo' : IsOpen {x | x ∈ P ∧ |w x| < ε₁} := by
    have : {x | x ∈ P ∧ |w x| < ε₁} = P ∩ w ⁻¹' Ioo (-ε₁) ε₁ := by
      ext x
      simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo, abs_lt]
    rw [this]
    exact hwc.isOpen_inter_preimage hP isOpen_Ioo
  set N : Set E2 := S ∩ {x | x ∈ P ∧ |w x| < ε₁} with hN
  have hN0 : (0 : E2) ∈ N := ⟨hS0, h0, by simp [hw0, hε₁]⟩
  have hNP : N ⊆ P := fun x hx => hx.2.1
  let c : ℝ → E2 := fun s => e.symm (0, s)
  have hJ : ∀ s ∈ Ioo (-ε₁) ε₁, ((0 : ℝ), s) ∈ e '' S := fun s hs =>
    hball (by
      rw [Metric.mem_ball, Prod.dist_eq]
      simp only [dist_zero_right, norm_zero]
      rw [max_lt_iff]
      exact ⟨hε₁, abs_lt.mpr hs⟩)
  have hJt : ∀ s ∈ Ioo (-ε₁) ε₁, ((0 : ℝ), s) ∈ e.target := fun s hs => by
    obtain ⟨x, hx, hxe⟩ := hJ s hs
    rw [← hxe]
    exact e.map_source hx.1
  have hcS : ∀ s ∈ Ioo (-ε₁) ε₁, c s ∈ S := fun s hs => by
    obtain ⟨x, hx, hxe⟩ := hJ s hs
    have : e.symm (e x) = x := e.left_inv hx.1
    change e.symm (0, s) ∈ S
    rw [← hxe, this]
    exact hx
  have hΞc' : ∀ s ∈ Ioo (-ε₁) ε₁, Ξ (c s) = (0, s) := fun s hs => by
    have := e.right_inv (hJt s hs)
    exact this
  have hcat : ∀ s ∈ Ioo (-ε₁) ε₁, ContDiffAt ℝ ∞ c s := by
    intro s hs
    have hxS := hcS s hs
    obtain ⟨hxsrc, hxP, g, hg⟩ := hxS
    have hsymm := e.contDiffAt_symm (n := ∞) (f₀' := g) (a := ((0 : ℝ), s)) (hJt s hs)
      (by
        have : HasFDerivAt Ξ (fderiv ℝ Ξ (c s)) (c s) := hdiff _ hxP
        rw [← hg] at this
        exact this)
      (hΞat _ hxP)
    exact hsymm.comp s (contDiffAt_const.prodMk contDiffAt_id)
  refine ⟨ε₁, N, c, hε₁, ?_, hN0, hNP, fun s hs => (hcat s hs).contDiffWithinAt, ?_, ?_, ?_, ?_⟩
  · exact hSo.inter hNo'
  · have h00 : e 0 = ((0 : ℝ), (0 : ℝ)) := by simp [he_coe, hΞ, hu0, hw0]
    change e.symm (0, 0) = 0
    rw [← h00]
    exact e.left_inv he0
  · intro s hs
    have h1 := hΞc' s hs
    have hu1 : u (c s) = 0 := (Prod.mk.inj h1).1
    have hw1 : w (c s) = s := (Prod.mk.inj h1).2
    obtain ⟨hxsrc, hxP, -⟩ := hcS s hs
    refine ⟨⟨hcS s hs, hxP, ?_⟩, hu1, hw1⟩
    rw [hw1]
    exact abs_lt.mpr hs
  · rintro x ⟨hxS, hxP, hxw⟩ hux
    have hxw' : w x ∈ Ioo (-ε₁) ε₁ := abs_lt.mp hxw
    refine ⟨hxw', ?_⟩
    have h1 : e x = ((0 : ℝ), w x) := by
      change Ξ x = _
      simp [hΞ, hux]
    change e.symm (0, w x) = x
    rw [← h1]
    exact e.left_inv hxS.1
  · intro s hs
    have hcd : DifferentiableAt ℝ c s := (hcat s hs).differentiableAt (by simp)
    have hxP : c s ∈ P := (hcS s hs).2.1
    have hwd : DifferentiableAt ℝ w (c s) :=
      (hw.contDiffAt (hP.mem_nhds hxP)).differentiableAt (by simp)
    have h1 : HasDerivAt (w ∘ c) (fderiv ℝ w (c s) (deriv c s)) s :=
      hwd.hasFDerivAt.comp_hasDerivAt s hcd.hasDerivAt
    have h2 : HasDerivAt (w ∘ c) 1 s := by
      refine (hasDerivAt_id s).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      exact (hΞc' t ht |> Prod.mk.inj).2
    have h3 : fderiv ℝ w (c s) (deriv c s) = 1 := h1.unique h2
    intro h0
    rw [h0, map_zero] at h3
    exact zero_ne_one h3

end DifferentialGeometry.Topology
