import DifferentialGeometry.Geometry.Curvature.RestrictedRoundCylinderLeastRicci
import DifferentialGeometry.Geometry.Curvature.SmoothRicciEigenpair
import DifferentialGeometry.Geometry.Curvature.RestrictedRoundCylinderRicciGap
import DifferentialGeometry.Geometry.Curvature.LeastRicciGap
import DifferentialGeometry.Tensor.LinearAlgebra.OrientedUnitLine

noncomputable section
open Set Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open Poincare.Geometry.Metric

namespace Poincare.Geometry.Curvature

theorem exists_smooth_least_ricci_direction_on_restricted_roundCylinder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    (O : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ)) O)
    {U : Set O} (hU : IsOpen U)
    (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : ∀ x ∈ U, ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k g ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O) x ≤ ε)
    {x₀ : O} (hx₀ : x₀ ∈ U) :
    ∃ V : Set O, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ U ∧
      ∃ (μ : O → ℝ)
        (w : ∀ x : O, TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x),
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ μ V ∧
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod 𝓘(ℝ)).tangent ∞
          (fun x ↦ (⟨x, w x⟩ : TangentBundle ((𝓡 2).prod 𝓘(ℝ)) O)) V ∧
        ∀ x ∈ V, g.inner x (w x) (w x) = 1 ∧ ricciSharp g x (w x) = μ x • w x ∧
          (∀ z : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x,
            g.inner x z z = 1 → μ x ≤ ricciTensor g x z z) ∧
          |μ x| ≤ 5772 * ε ∧
          Module.End.eigenspace (ricciSharp g x).toLinearMap (μ x) = Submodule.span ℝ {w x} ∧
          0 < mvfderiv ((𝓡 2).prod 𝓘(ℝ)) (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) x (w x) ∧
          Real.sqrt (((roundCylinderMetric (E := E) (n := 2)).restrictOpen O).inner x
            (w x - restrictedCylinderAxis O x) (w x - restrictedCylinderAxis O x)) ≤ 92354 * ε := by
  let IC := (𝓡 2).prod 𝓘(ℝ)
  let gS := scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := 2))
  let gRef := (roundCylinderMetric (E := E) (n := 2)).restrictOpen O
  obtain ⟨μ₀, w₀, hw₀, heig₀, _, hμ₀, hsimple₀, hpos₀, _⟩ :=
    exists_least_ricci_direction_on_restricted_roundCylinder O g x₀ ε hε (hsmall x₀ hx₀)
  obtain ⟨V, hVo, hxV, hVU, μ, w, hμ, hw, hμbase, hwbase, heq⟩ :=
    exists_smooth_ricci_eigenpair_near_simple g hU hx₀ μ₀ w₀ hw₀ heig₀ hsimple₀
  let f : O → ℝ := fun x ↦ gRef.inner x (restrictedCylinderAxis O x) (w x)
  have hf : ContMDiffOn IC 𝓘(ℝ) ∞ f V := by
    have ht := ContMDiffOn.clm_bundle_apply₂ (E₁ := TangentSpace IC) (E₂ := TangentSpace IC)
      (E₃ := fun _ : O ↦ ℝ) (b := id) (ψ := gRef.inner)
      (v := restrictedCylinderAxis O) (w := w) gRef.contMDiff.contMDiffOn
      (contMDiff_restrictedCylinderAxis O).contMDiffOn hw
    intro x hx
    exact (contMDiffWithinAt_totalSpace.mp (ht x hx)).2
  have hfderiv (x : O) :
      f x = mvfderiv IC (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) x (w x) := restrictedCylinderAxis_inner gS O x (w x)
  let W := (V ∩ μ ⁻¹' Iio (1 / 2 - 5772 * ε)) ∩ (V ∩ f ⁻¹' Ioi 0)
  have hWo : IsOpen W :=
    (hμ.continuousOn.isOpen_inter_preimage hVo isOpen_Iio).inter
      (hf.continuousOn.isOpen_inter_preimage hVo isOpen_Ioi)
  have hxW : x₀ ∈ W := by
    refine ⟨⟨hxV, ?_⟩, hxV, ?_⟩
    · change μ x₀ < 1 / 2 - 5772 * ε
      rw [hμbase]
      have hb := (le_abs_self μ₀).trans hμ₀
      linarith only [hb, hε]
    · change 0 < f x₀
      rw [hfderiv, hwbase]
      exact hpos₀
  have hWV : W ⊆ V := fun _ hx ↦ hx.1.1
  refine ⟨W, hWo, hxW, hWV.trans hVU, μ, w, hμ.mono hWV, hw.mono hWV, ?_⟩
  intro x hx
  have hxU := hVU (hWV hx)
  obtain ⟨hwunit, hweigen⟩ := heq x (hWV hx)
  have haxis := ricciSharp_restricted_roundCylinder_normalized_axis_bound O g x ε (by linarith only [hε])
    (hsmall x hxU)
  obtain ⟨hmin, habs, hspace⟩ := least_ricci_eigenpair_of_axis_error g x _ haxis.1
    (1 / 2) (5772 * ε) (by norm_num) (by linarith only [hε]) haxis.2
    (μ x) (w x) hwunit hweigen hx.1.2
  have hpos : 0 < mvfderiv IC (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) x (w x) := (hfderiv x) ▸ hx.2.2
  refine ⟨hwunit, hweigen, hmin, habs, hspace, hpos, ?_⟩
  obtain ⟨ν, u, hu, hueigen, humin, _, _, hupos, huclose⟩ :=
    exists_least_ricci_direction_on_restricted_roundCylinder O g x ε hε (hsmall x hxU)
  have hRayleigh (a : ℝ) (v : TangentSpace IC x) (hv : g.inner x v v = 1)
      (he : ricciSharp g x v = a • v) : ricciTensor g x v v = a := by
    rw [← inner_ricciSharp, he, map_smul, smul_apply, hv]
    exact mul_one a
  have heval : ν = μ x := le_antisymm
    ((humin (w x) hwunit).trans_eq (hRayleigh (μ x) (w x) hwunit hweigen))
    ((hmin u hu).trans_eq (hRayleigh ν u hu hueigen))
  have hmem : u ∈ Submodule.span ℝ {w x} := by
    rw [← hspace]
    apply Module.End.mem_eigenspace_iff.mpr
    exact hueigen.trans (congrArg (fun a : ℝ ↦ a • u) heval)
  have heqw : u = w x := Poincare.Analysis.eq_of_unit_of_mem_span_of_positive_functional
    (g.inner x).toBilinForm (mvfderiv IC (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) x).toLinearMap
    u (w x) hu hwunit hmem hupos hpos
  rwa [heqw] at huclose

end Poincare.Geometry.Curvature
