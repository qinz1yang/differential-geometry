import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.LocalDefining
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Set DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.EmbeddedHypersurface

section Immersion

variable {E F H G S M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
  [I.Boundaryless] [J.Boundaryless]

theorem injective_mfderiv_of_isImmersionAt {e : S → M} {x : S}
    (he : Manifold.IsImmersionAt I J ∞ e x) :
    Function.Injective (mfderiv I J e x) := by
  let h := he.isImmersionAtOfComplement_complement
  let d := extendedChartOfMemMaximalAtlas I h.domChart h.domChart_mem_maximalAtlas
  let c := extendedChartOfMemMaximalAtlas J h.codChart h.codChart_mem_maximalAtlas
  let p : M → E := fun y => (h.equiv.symm (c y)).1
  let r : M → S := d.symm ∘ p
  have hxD : x ∈ d.source := by
    change x ∈ (h.domChart.extend I).source
    rw [OpenPartialHomeomorph.extend_source]
    exact h.mem_domChart_source
  have hxC : e x ∈ c.source := by
    change e x ∈ (h.codChart.extend J).source
    rw [OpenPartialHomeomorph.extend_source]
    exact h.mem_codChart_source
  have hp (s : S) (hs : s ∈ d.source) : p (e s) = d s := by
    have hh := h.writtenInCharts (d.map_source hs)
    change c (e (d.symm (d s))) = h.equiv (d s, 0) at hh
    erw [d.left_inv hs] at hh
    change (h.equiv.symm (c (e s))).1 = d s
    rw [hh, h.equiv.symm_apply_apply]
  have hpe : ContMDiffAt J 𝓘(ℝ, E) ∞ p (e x) :=
    ((contDiff_fst.comp h.equiv.symm.contDiff).contMDiff.contMDiffAt).comp (e x)
      (c.contMDiffOn.contMDiffAt (c.open_source.mem_nhds hxC))
  have hr : ContMDiffAt J I ∞ r (e x) := by
    apply ContMDiffAt.comp (e x) _ hpe
    apply d.symm.contMDiffOn.contMDiffAt
    apply d.open_target.mem_nhds
    rw [hp x hxD]
    exact d.map_source hxD
  have hEq : r ∘ e =ᶠ[𝓝 x] id :=
    Filter.eventuallyEq_of_mem (d.open_source.mem_nhds hxD) (fun s hs => by
      change d.symm (p (e s)) = s
      rw [hp s hs]
      exact d.left_inv hs)
  have hd := mfderiv_comp x (hr.mdifferentiableAt (by simp))
    (he.contMDiffAt.mdifferentiableAt (by simp))
  erw [hEq.mfderiv_eq, mfderiv_id] at hd
  have hleft : Function.LeftInverse (mfderiv J I r (e x)) (mfderiv I J e x) := by
    intro v
    exact (congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hd).symm
  exact hleft.injective

end Immersion

variable {m : ℕ} {H G S M : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G)
  [I.Boundaryless] [J.Boundaryless]

theorem ker_mfderiv_eq_range_of_vanishing {e : S → M} {x : S} {f : M → ℝ}
    (he : Manifold.IsImmersionAt I J ∞ e x)
    (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (e x))
    (hz : f ∘ e =ᶠ[𝓝 x] fun _ => 0)
    (hreg : mfderiv J 𝓘(ℝ, ℝ) f (e x) ≠ 0) :
    (mfderiv J 𝓘(ℝ, ℝ) f (e x)).ker = (mfderiv I J e x).range := by
  let : FiniteDimensional ℝ (TangentSpace J (e x)) :=
    inferInstanceAs (FiniteDimensional ℝ (MorseModel (m + 1)))
  let : IsSimpleModule ℝ (TangentSpace 𝓘(ℝ, ℝ) (f (e x))) :=
    inferInstanceAs (IsSimpleModule ℝ ℝ)
  let L := mfderiv J 𝓘(ℝ, ℝ) f (e x)
  let A := mfderiv I J e x
  have hA : Function.Injective A := injective_mfderiv_of_isImmersionAt I J he
  have hcomp := mfderiv_comp x hf (he.contMDiffAt.mdifferentiableAt (by simp))
  erw [hz.mfderiv_eq, mfderiv_const] at hcomp
  have hle : A.range ≤ L.ker := by
    rintro v ⟨w, rfl⟩
    change L (A w) = 0
    exact (congrArg (fun B : TangentSpace I x →L[ℝ] ℝ => B w) hcomp).symm
  have hL : L.toLinearMap ≠ 0 := by
    intro hzero
    apply hreg
    ext v
    exact congrArg (fun B : TangentSpace J (e x) →ₗ[ℝ] ℝ => B v) hzero
  have hsurj : Function.Surjective L.toLinearMap := LinearMap.surjective_of_ne_zero hL
  have hdim := L.toLinearMap.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ L.range = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
    exact Module.finrank_self ℝ
  have hdimM : Module.finrank ℝ (TangentSpace J (e x)) = m + 1 :=
    Module.finrank_fin_fun ℝ
  have hdimS : Module.finrank ℝ (TangentSpace I x) = m := Module.finrank_fin_fun ℝ
  rw [hrange, hdimM] at hdim
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [LinearMap.finrank_range_of_inj hA, hdimS]
  omega

theorem mfderiv_apply_ne_zero_of_transverse {e : S → M} {x : S} {f : M → ℝ}
    (he : Manifold.IsImmersionAt I J ∞ e x)
    (hf : MDifferentiableAt J 𝓘(ℝ, ℝ) f (e x))
    (hz : f ∘ e =ᶠ[𝓝 x] fun _ => 0)
    (hreg : mfderiv J 𝓘(ℝ, ℝ) f (e x) ≠ 0)
    {v : TangentSpace J (e x)} (hv : v ∉ (mfderiv I J e x).range) :
    mfderiv J 𝓘(ℝ, ℝ) f (e x) v ≠ 0 := by
  intro hzero
  apply hv
  rw [← ker_mfderiv_eq_range_of_vanishing I J he hf hz hreg]
  exact hzero

end DifferentialGeometry.Manifold.EmbeddedHypersurface
