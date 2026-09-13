import DifferentialGeometry.Analysis.InnerProductSpace.ConformalPair
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem coordinate_eq_zero_of_conformal_smul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {B : V →L[ℝ] V →L[ℝ] ℝ} {l : V →L[ℝ] ℝ} {t v : V} {a : ℝ}
    (hB : LinearMap.IsPosSemidef B.toBilinForm) (ht : B t t ≠ 0)
    (hl : ∀ w, B t w = B t t * l w)
    (ho : B (a • t) v = 0) (he : B (a • t) (a • t) = B v v) : l v = 0 := by
  have h := hB.apply_eq_zero_of_conformal_smul ho he
  change B t v = 0 at h
  rw [hl] at h
  exact (mul_eq_zero.mp h).resolve_left ht

private theorem fderivWithin_apply_one_eq_zero_of_trace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set ℂ} {Y : ℂ → V} {x a b : ℝ}
    (hY : DifferentiableWithinAt ℝ Y s (x : ℂ))
    (hx : x ∈ Ioo a b) (hseg : ∀ r ∈ Ioo a b, (r : ℂ) ∈ s)
    (hzero : ∀ r ∈ Ioo a b, Y (r : ℂ) = 0) :
    fderivWithin ℝ Y s (x : ℂ) 1 = 0 := by
  have hmem : ∀ᶠ r : ℝ in 𝓝 x, (r : ℂ) ∈ s := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with r hr
    exact hseg r hr
  have hd := hY.hasFDerivWithinAt.comp_hasDerivAt x Complex.ofRealCLM.hasDerivAt hmem
  change HasDerivAt (fun r : ℝ => Y (r : ℂ)) (fderivWithin ℝ Y s (x : ℂ) 1) x at hd
  have he : (fun r : ℝ => Y (r : ℂ)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with r hr
    exact hzero r hr
  exact hd.unique ((hasDerivAt_const x (0 : V)).congr_of_eventuallyEq he)

theorem fderivWithin_normal_eq_zero_of_conformal_trace
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set ℂ} {X : ℂ → V} {x a b : ℝ}
    (hX : DifferentiableWithinAt ℝ X s (x : ℂ)) (hu : UniqueDiffWithinAt ℝ s (x : ℂ))
    (hx : x ∈ Ioo a b) (hseg : ∀ r ∈ Ioo a b, (r : ℂ) ∈ s)
    {l : V →L[ℝ] ℝ} {t : V}
    (htrace : ∀ r ∈ Ioo a b, X (r : ℂ) - l (X (r : ℂ)) • t = 0)
    {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : LinearMap.IsPosSemidef B.toBilinForm) (ht : B t t ≠ 0)
    (hl : ∀ w, B t w = B t t * l w)
    (ho : B (fderivWithin ℝ X s (x : ℂ) 1) (fderivWithin ℝ X s (x : ℂ) Complex.I) = 0)
    (he : B (fderivWithin ℝ X s (x : ℂ) 1) (fderivWithin ℝ X s (x : ℂ) 1) =
      B (fderivWithin ℝ X s (x : ℂ) Complex.I) (fderivWithin ℝ X s (x : ℂ) Complex.I)) :
    fderivWithin ℝ (fun z => l (X z)) s (x : ℂ) Complex.I = 0 := by
  have hf := l.hasFDerivAt.comp_hasFDerivWithinAt (x : ℂ) hX.hasFDerivWithinAt
  change HasFDerivWithinAt (fun z => l (X z)) (l.comp (fderivWithin ℝ X s (x : ℂ))) s (x : ℂ) at hf
  have hY := hX.hasFDerivWithinAt.sub (hf.smul_const t)
  change HasFDerivWithinAt (fun z => X z - l (X z) • t)
    (fderivWithin ℝ X s (x : ℂ) - (l.comp (fderivWithin ℝ X s (x : ℂ))).smulRight t) s (x : ℂ) at hY
  have hzero := fderivWithin_apply_one_eq_zero_of_trace hY.differentiableWithinAt hx hseg htrace
  rw [hY.fderivWithin hu] at hzero
  change fderivWithin ℝ X s (x : ℂ) 1 - l (fderivWithin ℝ X s (x : ℂ) 1) • t = 0 at hzero
  have htan := sub_eq_zero.mp hzero
  have ho' := ho
  have he' := he
  rw [htan] at ho' he'
  have hn := coordinate_eq_zero_of_conformal_smul hB ht hl ho' he'
  rw [hf.fderivWithin hu]
  exact hn

theorem fderivWithin_normal_eq_zero_of_conformal_interior
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set ℂ} (hs : IsOpen s) (hu : UniqueDiffOn ℝ (closure s))
    {X : ℂ → V} (hX : ContDiffOn ℝ 1 X (closure s)) {x a b : ℝ}
    (hx : x ∈ Ioo a b) (hseg : ∀ r ∈ Ioo a b, (r : ℂ) ∈ closure s)
    {l : V →L[ℝ] ℝ} {t : V}
    (htrace : ∀ r ∈ Ioo a b, X (r : ℂ) - l (X (r : ℂ)) • t = 0)
    {g : V → V →L[ℝ] V →L[ℝ] ℝ} (hg : ContinuousOn g (X '' closure s))
    (hB : LinearMap.IsPosSemidef (g (X (x : ℂ))).toBilinForm)
    (ht : g (X (x : ℂ)) t t ≠ 0)
    (hl : ∀ w, g (X (x : ℂ)) t w = g (X (x : ℂ)) t t * l w)
    (ho : ∀ z ∈ s, g (X z) (fderiv ℝ X z 1) (fderiv ℝ X z Complex.I) = 0)
    (he : ∀ z ∈ s, g (X z) (fderiv ℝ X z 1) (fderiv ℝ X z 1) =
      g (X z) (fderiv ℝ X z Complex.I) (fderiv ℝ X z Complex.I)) :
    fderivWithin ℝ (fun z => l (X z)) (closure s) (x : ℂ) Complex.I = 0 := by
  let D := fderivWithin ℝ X (closure s)
  have hD : ContinuousOn D (closure s) := hX.continuousOn_fderivWithin hu (by norm_num)
  have hv : ContinuousOn (fun z => D z 1) (closure s) := hD.clm_apply continuousOn_const
  have hw : ContinuousOn (fun z => D z Complex.I) (closure s) := hD.clm_apply continuousOn_const
  have hgX : ContinuousOn (fun z => g (X z)) (closure s) :=
    hg.comp hX.continuousOn (fun z hz => mem_image_of_mem X hz)
  have horthc := (hgX.clm_apply hv).clm_apply hw
  have hvc := (hgX.clm_apply hv).clm_apply hv
  have hwc := (hgX.clm_apply hw).clm_apply hw
  have hDi (z : ℂ) (hz : z ∈ s) : D z = fderiv ℝ X z :=
    fderivWithin_of_mem_nhds (mem_of_superset (hs.mem_nhds hz) subset_closure)
  have hoi : EqOn (fun z => g (X z) (D z 1) (D z Complex.I)) (fun _ => 0) s := by
    intro z hz
    dsimp only
    rw [hDi z hz]
    exact ho z hz
  have hei : EqOn (fun z => g (X z) (D z 1) (D z 1))
      (fun z => g (X z) (D z Complex.I) (D z Complex.I)) s := by
    intro z hz
    dsimp only
    rw [hDi z hz]
    exact he z hz
  have hxc := hseg x hx
  exact fderivWithin_normal_eq_zero_of_conformal_trace
    ((hX.differentiableOn (by norm_num)) (x : ℂ) hxc) (hu (x : ℂ) hxc) hx hseg htrace hB ht hl
    (hoi.of_subset_closure horthc continuousOn_const subset_closure Subset.rfl hxc)
    (hei.of_subset_closure hvc hwc subset_closure Subset.rfl hxc)

end DifferentialGeometry.Analysis
