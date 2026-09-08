import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph

open scoped ContDiff Manifold Topology

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]

noncomputable def unitSphereProd (n : ℕ∞ω) :
    let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
    Diffeomorph 𝓘(ℝ, E) ((𝓡 d).prod 𝓘(ℝ, ℝ)) U
      (Metric.sphere (0 : E) 1 × V) n := by
  let U : TopologicalSpace.Opens E := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let V : TopologicalSpace.Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
  let _ : ChartedSpace E ({0}ᶜ : Set E) := inferInstanceAs (ChartedSpace E U)
  let _ : ChartedSpace ℝ (Set.Ioi (0 : ℝ)) := inferInstanceAs (ChartedSpace ℝ V)
  let h : U ≃ₜ (Metric.sphere (0 : E) 1 × V) := homeomorphUnitSphereProd E
  have hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n (Subtype.val : U → E) :=
    contMDiff_subtype_val
  have hn : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n (fun x : U => ‖x.val‖) := by
    intro x
    apply contMDiffAt_subtype_iff.mpr
    exact (contDiffAt_norm ℝ (show x.val ≠ 0 from x.property)).contMDiffAt
  have hn0 : ∀ x : U, ‖x.val‖ ≠ 0 := fun x => norm_ne_zero_iff.mpr x.property
  refine { toEquiv := h.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · have hs : ContMDiff 𝓘(ℝ, E) (𝓡 d) n (fun x : U => (h x).1) := by
      have hs' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) n
          (fun x : U => ((h x).1 : E)) := by
        apply ((hn.inv₀ hn0).smul hv).congr
        intro x
        exact homeomorphUnitSphereProd_apply_fst_coe E x
      exact hs'.codRestrict_sphere (fun x => (h x).1.property)
    have hr : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n (fun x : U => (h x).2) := by
      have hr' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n (fun x : U => ((h x).2 : ℝ)) := by
        apply hn.congr
        intro x
        exact homeomorphUnitSphereProd_apply_snd_coe E x
      intro x
      exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
        (P := ContDiffWithinAtProp 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n) (U := V)
        (fun x : U => (h x).2) Set.univ x).mp (hr' x)
    exact hs.prodMk hr
  · have hi : ContMDiff ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n
        (fun p : Metric.sphere (0 : E) 1 × V => (h.symm p).val) :=
      (contMDiff_subtype_val.comp contMDiff_snd).smul
        (contMDiff_coe_sphere.comp contMDiff_fst)
    intro p
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp ((𝓡 d).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) n) (U := U)
      (h.symm : Metric.sphere (0 : E) 1 × V → U) Set.univ p).mp (hi p)

@[simp] theorem unitSphereProd_toHomeomorph (n : ℕ∞ω) :
    (unitSphereProd (E := E) (d := d) n).toHomeomorph = homeomorphUnitSphereProd E := rfl

@[simp] theorem unitSphereProd_apply_fst_val (n : ℕ∞ω) (x : ({0}ᶜ : Set E)) :
    ((unitSphereProd (E := E) (d := d) n x).1 : E) = ‖x.val‖⁻¹ • x.val := by
  exact homeomorphUnitSphereProd_apply_fst_coe E x

@[simp] theorem unitSphereProd_apply_snd_val (n : ℕ∞ω) (x : ({0}ᶜ : Set E)) :
    ((unitSphereProd (E := E) (d := d) n x).2 : ℝ) = ‖x.val‖ := by
  exact homeomorphUnitSphereProd_apply_snd_coe E x

@[simp] theorem unitSphereProd_symm_apply_val (n : ℕ∞ω)
    (p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) :
    ((unitSphereProd (E := E) (d := d) n).symm p : E) = p.2.val • p.1.val := rfl

end Diffeomorph
