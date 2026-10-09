import DifferentialGeometry.Analysis.Calculus.Inverse.GraphTransversality
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold Bundle DifferentialGeometry
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

private theorem transverse_regular_pair_of_graph_height_derivatives_ne
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    (proj : E →L[ℝ] ℂ) (height : E →L[ℝ] ℝ) (N : E) (lift : ℂ → E)
    (hsplit : ∀ v : E, v = lift (proj v) + height v • N)
    (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ)
    (he₁s : e₁.source ⊆ s) (he₂s : e₂.source ⊆ s)
    (hdisj : Disjoint e₁.source e₂.source)
    (he₁ : (e₁ : ℂ → ℂ) = fun z => proj (extChartAt 𝓘(ℝ, E) p (U z)))
    (he₂ : (e₂ : ℂ → ℂ) = fun z => proj (extChartAt 𝓘(ℝ, E) p (U z)))
    (hei₁ : ContDiffOn ℝ ∞ e₁.symm e₁.target)
    (hei₂ : ContDiffOn ℝ ∞ e₂.symm e₂.target)
    (x₀ : E) {y : ℂ} (hy₁ : y ∈ e₁.target) (hy₂ : y ∈ e₂.target)
    (hheight : height (extChartAt 𝓘(ℝ, E) p (U (e₁.symm y)) - x₀) =
      height (extChartAt 𝓘(ℝ, E) p (U (e₂.symm y)) - x₀))
    (hderiv : fderiv ℝ (fun w => height (extChartAt 𝓘(ℝ, E) p (U (e₁.symm w)) - x₀)) y ≠
      fderiv ℝ (fun w => height (extChartAt 𝓘(ℝ, E) p (U (e₂.symm w)) - x₀)) y) :
    e₁.symm y ≠ e₂.symm y ∧ U (e₁.symm y) = U (e₂.symm y) ∧
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e₁.symm y)) ∧
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e₂.symm y)) ∧
      Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e₁.symm y)).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e₂.symm y)))) := by
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
  let F : ℂ → ℂ := fun z => proj (X z)
  change (e₁ : ℂ → ℂ) = F at he₁
  change (e₂ : ℂ → ℂ) = F at he₂
  let h₁ : ℂ → ℝ := fun w => height (X (e₁.symm w) - x₀)
  let h₂ : ℂ → ℝ := fun w => height (X (e₂.symm w) - x₀)
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart z hz)).comp z (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hchain (z : ℂ) (hz : z ∈ s) :
      fderiv ℝ X z =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (U z)).comp
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
    have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart z hz)
    have hh := mfderiv_comp z (hc.mdifferentiableAt (by simp))
      ((hU.contMDiffAt (hs.mem_nhds hz)).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hcalc (e : OpenPartialHomeomorph ℂ ℂ) (hes : e.source ⊆ s)
      (he : (e : ℂ → ℂ) = F) (hei : ContDiffOn ℝ ∞ e.symm e.target)
      (hye : y ∈ e.target) :
      proj.comp ((fderiv ℝ X (e.symm y)).comp (fderiv ℝ e.symm y)) =
        ContinuousLinearMap.id ℝ ℂ ∧
      fderiv ℝ (fun w => height (X (e.symm w) - x₀)) y =
        height.comp ((fderiv ℝ X (e.symm y)).comp (fderiv ℝ e.symm y)) ∧
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e.symm y)) := by
    let x := e.symm y
    have hx : x ∈ s := hes (e.map_target hye)
    have hdx := (hX.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
    have hde := (hei.contDiffAt (e.open_target.mem_nhds hye)).differentiableAt (by simp)
    have hdF : DifferentiableAt ℝ F x := proj.differentiableAt.comp x hdx
    have hDF : fderiv ℝ F x = proj.comp (fderiv ℝ X x) :=
      (proj.hasFDerivAt.comp x hdx.hasFDerivAt).fderiv
    have heq : (fun w => F (e.symm w)) =ᶠ[𝓝 y] id := by
      filter_upwards [e.open_target.mem_nhds hye] with w hw
      rw [← he]
      exact e.right_inv hw
    have hFR : (fderiv ℝ F x).comp (fderiv ℝ e.symm y) =
        ContinuousLinearMap.id ℝ ℂ :=
      ((hdF.hasFDerivAt.comp y hde.hasFDerivAt).congr_of_eventuallyEq heq.symm).unique
        (hasFDerivAt_id y)
    have hproj : proj.comp ((fderiv ℝ X x).comp (fderiv ℝ e.symm y)) =
        ContinuousLinearMap.id ℝ ℂ := by
      rw [← ContinuousLinearMap.comp_assoc, ← hDF]
      exact hFR
    have hheightD : fderiv ℝ (fun w => height (X (e.symm w) - x₀)) y =
        height.comp ((fderiv ℝ X x).comp (fderiv ℝ e.symm y)) :=
      (height.hasFDerivAt.comp y
        ((hdx.hasFDerivAt.comp y hde.hasFDerivAt).sub_const x₀)).fderiv
    have hDFsurj : Function.Surjective (fderiv ℝ F x) := by
      intro v
      exact ⟨fderiv ℝ e.symm y v, congrArg (fun K : ℂ →L[ℝ] ℂ => K v) hFR⟩
    have hDFinj : Function.Injective (fderiv ℝ F x) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr hDFsurj
    have hDXinj : Function.Injective (fderiv ℝ X x) := by
      intro v w hvw
      apply hDFinj
      rw [hDF]
      exact congrArg proj hvw
    refine ⟨hproj, hheightD, ?_⟩
    intro v w hvw
    apply hDXinj
    rw [hchain x hx]
    exact congrArg (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) p) (U x)) hvw
  obtain ⟨hproj₁, hell₁, hmi₁⟩ := hcalc e₁ he₁s he₁ hei₁ hy₁
  obtain ⟨hproj₂, hell₂, hmi₂⟩ := hcalc e₂ he₂s he₂ hei₂ hy₂
  let x₁ := e₁.symm y
  let x₂ := e₂.symm y
  let R₁ := fderiv ℝ e₁.symm y
  let R₂ := fderiv ℝ e₂.symm y
  let T₁ := (fderiv ℝ X x₁).comp R₁
  let T₂ := (fderiv ℝ X x₂).comp R₂
  let ell₁ := fderiv ℝ h₁ y
  let ell₂ := fderiv ℝ h₂ y
  let L : ℂ →L[ℝ] E := T₁ - ell₁.smulRight N
  have hT₁ (v : ℂ) : T₁ v = lift v + ell₁ v • N := by
    have hp := congrArg (fun A : ℂ →L[ℝ] ℂ => A v) hproj₁
    have he := congrArg (fun A : ℂ →L[ℝ] ℝ => A v) hell₁
    have h := hsplit (T₁ v)
    change proj (T₁ v) = v at hp
    change ell₁ v = height (T₁ v) at he
    rwa [hp, ← he] at h
  have hT₂ (v : ℂ) : T₂ v = lift v + ell₂ v • N := by
    have hp := congrArg (fun A : ℂ →L[ℝ] ℂ => A v) hproj₂
    have he := congrArg (fun A : ℂ →L[ℝ] ℝ => A v) hell₂
    have h := hsplit (T₂ v)
    change proj (T₂ v) = v at hp
    change ell₂ v = height (T₂ v) at he
    rwa [hp, ← he] at h
  have hL (v : ℂ) : L v = lift v := by
    change T₁ v - ell₁ v • N = lift v
    rw [hT₁, add_sub_cancel_right]
  have hspan : ∀ v : E, ∃ (w : ℂ) (t : ℝ), v = L w + t • N := by
    intro v
    refine ⟨proj v, height v, ?_⟩
    rw [hL]
    exact hsplit v
  have hTL₁ : L + ell₁.smulRight N = T₁ :=
    ContinuousLinearMap.ext fun v => by
      change L v + ell₁ v • N = T₁ v
      rw [hL, hT₁]
  have hTL₂ : L + ell₂.smulRight N = T₂ :=
    ContinuousLinearMap.ext fun v => by
      change L v + ell₂ v • N = T₂ v
      rw [hL, hT₂]
  have htransT := Analysis.surjective_coprod_graphs_of_ne L N ell₁ ell₂ hspan hderiv
  rw [hTL₁, hTL₂] at htransT
  have htransX : Function.Surjective
      ((fderiv ℝ X x₁).coprod (-(fderiv ℝ X x₂))) := by
    intro v
    obtain ⟨z, hz⟩ := htransT v
    exact ⟨(R₁ z.1, R₂ z.2), hz⟩
  have hx₁s : x₁ ∈ s := he₁s (e₁.map_target hy₁)
  have hx₂s : x₂ ∈ s := he₂s (e₂.map_target hy₂)
  have hP₁ : proj (X x₁) = y := by
    change F (e₁.symm y) = y
    rw [← he₁]
    exact e₁.right_inv hy₁
  have hP₂ : proj (X x₂) = y := by
    change F (e₂.symm y) = y
    rw [← he₂]
    exact e₂.right_inv hy₂
  have hh : height (X x₁) = height (X x₂) := by
    change height (X x₁ - x₀) = height (X x₂ - x₀) at hheight
    rw [map_sub, map_sub] at hheight
    linarith
  have hXeq : X x₁ = X x₂ := by
    calc
      X x₁ = lift y + height (X x₁) • N := by rw [← hP₁]; exact hsplit _
      _ = lift y + height (X x₂) • N := by rw [hh]
      _ = X x₂ := by rw [← hP₂]; exact (hsplit _).symm
  have hUeq : U x₁ = U x₂ :=
    (extChartAt 𝓘(ℝ, E) p).injOn
      (by simpa only [extChartAt_source] using hchart x₁ hx₁s)
      (by simpa only [extChartAt_source] using hchart x₂ hx₂s) hXeq
  have hne : x₁ ≠ x₂ := by
    intro h
    have hx₁ := e₁.map_target hy₁
    have hx₂ := e₂.map_target hy₂
    change x₁ ∈ e₁.source at hx₁
    change x₂ ∈ e₂.source at hx₂
    rw [h] at hx₁
    exact disjoint_left.mp hdisj hx₁ hx₂
  let C : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (U x₁)
  let D₁ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x₁
  let D₂ : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U x₂
  have hC : Function.Injective C :=
    (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E))
      (show U x₁ ∈ (extChartAt 𝓘(ℝ, E) p).source by
        simpa only [extChartAt_source] using hchart x₁ hx₁s)).injective
  have hD₁ : fderiv ℝ X x₁ = C.comp D₁ := hchain x₁ hx₁s
  have hD₂ : fderiv ℝ X x₂ = C.comp D₂ := by
    have h := hchain x₂ hx₂s
    rw [← hUeq] at h
    exact h
  refine ⟨hne, hUeq, hmi₁, hmi₂, ?_⟩
  intro v
  obtain ⟨z, hz⟩ := htransX (C v)
  refine ⟨z, hC ?_⟩
  change C (D₁ z.1 + -(D₂ z.2)) = C v
  change fderiv ℝ X x₁ z.1 + -(fderiv ℝ X x₂ z.2) = C v at hz
  rw [hD₁, hD₂] at hz
  simpa only [map_add, map_neg, ContinuousLinearMap.comp_apply] using hz

/-- At the original nontransverse collision, the two chart heights have the same
value and derivative in their common projection coordinates. -/
theorem chart_height_difference_value_fderiv_zero_of_nontransverse_collision
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    (proj : E →L[ℝ] ℂ) (height : E →L[ℝ] ℝ) (N : E) (lift : ℂ → E)
    (hsplit : ∀ v : E, v = lift (proj v) + height v • N)
    (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ)
    (he₁s : e₁.source ⊆ s) (he₂s : e₂.source ⊆ s)
    (hdisj : Disjoint e₁.source e₂.source)
    (he₁ : (e₁ : ℂ → ℂ) = fun z => proj (extChartAt 𝓘(ℝ, E) p (U z)))
    (he₂ : (e₂ : ℂ → ℂ) = fun z => proj (extChartAt 𝓘(ℝ, E) p (U z)))
    (hei₁ : ContDiffOn ℝ ∞ e₁.symm e₁.target)
    (hei₂ : ContDiffOn ℝ ∞ e₂.symm e₂.target)
    {a b : ℂ} (ha : a ∈ e₁.source) (hb : b ∈ e₂.source)
    (hvalue : U a = U b)
    (hnot : ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b))))
    (x₀ : E) :
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => proj (X z)
    let w : ℂ → ℝ := fun y =>
      height (X (e₁.symm y) - x₀) - height (X (e₂.symm y) - x₀)
    w (F a) = 0 ∧ fderiv ℝ w (F a) = 0 := by
  intro X F w
  change (e₁ : ℂ → ℂ) = F at he₁
  change (e₂ : ℂ → ℂ) = F at he₂
  have hFvalue : F a = F b :=
    congrArg proj (congrArg (extChartAt 𝓘(ℝ, E) p) hvalue)
  have he₁a : e₁.symm (F a) = a := by
    rw [← he₁]
    exact e₁.left_inv ha
  have he₂b : e₂.symm (F a) = b := by
    rw [hFvalue, ← he₂]
    exact e₂.left_inv hb
  have hy₁ : F a ∈ e₁.target := by
    rw [← he₁]
    exact e₁.map_source ha
  have hy₂ : F a ∈ e₂.target := by
    rw [hFvalue, ← he₂]
    exact e₂.map_source hb
  have hXvalue : X a = X b := congrArg (extChartAt 𝓘(ℝ, E) p) hvalue
  have hheight : height (X (e₁.symm (F a)) - x₀) =
      height (X (e₂.symm (F a)) - x₀) := by
    rw [he₁a, he₂b, hXvalue]
  refine ⟨sub_eq_zero.mpr hheight, ?_⟩
  by_contra hDw
  let h₁ : ℂ → ℝ := fun y => height (X (e₁.symm y) - x₀)
  let h₂ : ℂ → ℝ := fun y => height (X (e₂.symm y) - x₀)
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart z hz)).comp z (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hdiff (e : OpenPartialHomeomorph ℂ ℂ) (hes : e.source ⊆ s)
      (hei : ContDiffOn ℝ ∞ e.symm e.target) (hye : F a ∈ e.target) :
      DifferentiableAt ℝ (fun y => height (X (e.symm y) - x₀)) (F a) := by
    have hdx := (hX.contDiffAt (hs.mem_nhds (hes (e.map_target hye)))).differentiableAt
      (by simp)
    have hde := (hei.contDiffAt (e.open_target.mem_nhds hye)).differentiableAt (by simp)
    exact (height.hasFDerivAt.comp (F a)
      ((hdx.hasFDerivAt.comp (F a) hde.hasFDerivAt).sub_const x₀)).differentiableAt
  have hderiv : fderiv ℝ h₁ (F a) ≠ fderiv ℝ h₂ (F a) := by
    intro hequal
    apply hDw
    have hd : fderiv ℝ w (F a) = fderiv ℝ h₁ (F a) - fderiv ℝ h₂ (F a) :=
      fderiv_fun_sub (hdiff e₁ he₁s hei₁ hy₁) (hdiff e₂ he₂s hei₂ hy₂)
    rw [hd, hequal, sub_self]
  obtain ⟨_, _, _, _, hsurj⟩ :=
    transverse_regular_pair_of_graph_height_derivatives_ne hs hU hchart
      proj height N lift hsplit e₁ e₂ he₁s he₂s hdisj he₁ he₂ hei₁ hei₂
      x₀ hy₁ hy₂ hheight hderiv
  have hD₁ :
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e₁.symm (F a))) =
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a) :=
    congrArg (fun z : ℂ => (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) he₁a
  have hD₂ :
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (e₂.symm (F a))) =
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b) :=
    congrArg (fun z : ℂ => (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) he₂b
  apply hnot
  rwa [hD₁, hD₂] at hsurj

end DifferentialGeometry.Geometry
