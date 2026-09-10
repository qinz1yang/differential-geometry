import DifferentialGeometry.Geometry.Neck.ChartAxis
import DifferentialGeometry.Geometry.Neck.InwardCurve
import DifferentialGeometry.Topology.Manifold.ProductChartGraph
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Operator
open Poincare.Topology.Manifold

namespace Poincare.Geometry.Neck

private abbrev S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
private instance : PathConnectedSpace S :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (by simp [← Module.finrank_eq_rank] :
      1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3))) _ zero_le_one)

theorem cylindricalChart.exists_graph_of_full_cross_section_and_gradient_close
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    (t : ℝ)
    (hsection : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t) ∈ C₀.domain)
    (htarget : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (C₀.chart ⟨(p, t), hsection p⟩ : M) ∈ C₁.target)
    {U : Set C₁.domain} (ε : ℝ) (hε : ε < 1) (hsmall : C₁.metricCloseOn g ε U)
    (hU : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      C₁.chart.symm ⟨(C₀.chart ⟨(p, t), hsection p⟩ : M), htarget p⟩ ∈ U)
    (σ c δ B : ℝ) (hσ : σ = 1 ∨ σ = -1) (hδ : δ * Real.sqrt (1 + ε) < 1)
    (hgrad : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      let y : M := C₀.chart ⟨(p, t), hsection p⟩
      Real.sqrt (g.inner y (gradFun g C₀.axial y - σ • gradFun g C₁.axial y)
        (gradFun g C₀.axial y - σ • gradFun g C₁.axial y)) ≤ δ)
    (hvalue : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      let y : M := C₀.chart ⟨(p, t), hsection p⟩
      |C₀.axial y - σ * C₁.axial y - c| ≤ B) :
    ∃ (η : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (h : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ), ContMDiff (𝓡 2) 𝓘(ℝ) ∞ h ∧
      ∃ hmem : ∀ p, (p, h p) ∈ C₁.domain,
        (∀ p, (C₁.chart ⟨(p, h p), hmem p⟩ : M) =
          (C₀.chart ⟨(η p, t), hsection (η p)⟩ : M)) ∧
        ∀ p, |(Real.sqrt C₀.scale)⁻¹ * t - σ * ((Real.sqrt C₁.scale)⁻¹ * h p) - c| ≤ B := by
  let e₀ : S → M := fun p ↦ C₀.chart ⟨(p, t), hsection p⟩
  obtain ⟨he₀, -, -⟩ := contMDiff_injective_and_injective_mfderiv_of_product_chart_section
    C₀.domain C₀.target C₀.chart t hsection
  let f : S → C₁.target := fun p ↦ ⟨e₀ p, htarget p⟩
  have hf : ContMDiff (𝓡 2) J ∞ f := (ContMDiff.subtypeVal_comp_iff C₁.target f).mp he₀
  let ψ : S → C₁.domain := C₁.chart.symm ∘ f
  have hψ : ContMDiff (𝓡 2) IC ∞ ψ := C₁.chart.symm.contMDiff.comp hf
  let e : S → S × ℝ := fun p ↦ (ψ p : S × ℝ)
  let Φ : C₁.domain → M := fun x ↦ (C₁.chart x : M)
  have hΦ : ContMDiff IC J ∞ Φ := contMDiff_subtype_val.comp C₁.chart.contMDiff
  have hpoint (p : S) : Φ (ψ p) = e₀ p := by
    change (C₁.chart (C₁.chart.symm (f p)) : M) = e₀ p
    rw [C₁.chart.apply_symm_apply]
  have hax (p : S) : ContMDiffAt J 𝓘(ℝ) ∞ C₀.axial (e₀ p) := by
    let y : C₀.target := C₀.chart ⟨(p, t), hsection p⟩
    have hs : ContMDiff J 𝓘(ℝ) ∞ (fun y : C₀.target ↦ C₀.axial (y : M)) := by
      change ContMDiff J 𝓘(ℝ) ∞ (C₀.axial ∘ Subtype.val)
      unfold cylindricalChart.axial
      rw [Function.extend_comp Subtype.val_injective]
      exact contMDiff_const.mul
        (contMDiff_snd.comp (contMDiff_subtype_val.comp C₀.chart.symm.contMDiff))
    exact (contMDiffAt_subtype_iff (x := y)).mp (hs.contMDiffAt)
  have htransverse (p : S) : (0, 1) ∉ range (mfderiv (𝓡 2) IC e p) := by
    rintro ⟨z, hz⟩
    let w : TangentSpace IC (ψ p) := (0, 1)
    have hdψ : mfderiv (𝓡 2) IC ψ p z = w := by
      have hd := mfderiv_comp p
        ((contMDiff_subtype_val (I := IC) (n := ∞)).mdifferentiable (by decide) (ψ p))
        (hψ.mdifferentiable (by decide) p)
      rw [mfderiv_subtype_val] at hd
      have hv := DFunLike.congr_fun hd z
      change mfderiv (𝓡 2) IC e p z = mfderiv (𝓡 2) IC ψ p z at hv
      exact hv.symm.trans hz
    have hax' : MDifferentiableAt J 𝓘(ℝ) C₀.axial (Φ (ψ p)) := by
      rw [hpoint]
      exact (hax p).mdifferentiableAt (by decide)
    let q : C₁.domain → ℝ := C₀.axial ∘ Φ
    have hq : MDifferentiableAt IC 𝓘(ℝ) q (ψ p) :=
      hax'.comp (ψ p) (hΦ.mdifferentiable (by decide) (ψ p))
    have hconst : q ∘ ψ = fun _ : S ↦ (Real.sqrt C₀.scale)⁻¹ * t := by
      funext p
      change C₀.axial (Φ (ψ p)) = _
      rw [hpoint]
      exact C₀.axial_chart ⟨(p, t), hsection p⟩
    have hzero := mvfderiv_comp_apply p hq (hψ.mdifferentiable (by decide) p) z
    rw [hconst, mvfderiv_const] at hzero
    have hqw : mvfderiv IC q (ψ p) w = 0 := by
      rw [← hdψ]
      exact hzero.symm
    have hchain := mvfderiv_comp_apply (ψ p) hax'
      (hΦ.mdifferentiable (by decide) (ψ p)) w
    have hv : C₁.axialVector (ψ p) =
        Real.sqrt C₁.scale • mfderiv IC J Φ (ψ p) w := by
      have hd := mfderiv_comp (ψ p)
        ((contMDiff_subtype_val (I := J) (n := ∞)).mdifferentiable (by decide) (C₁.chart (ψ p)))
        (C₁.chart.contMDiff.mdifferentiable (by decide) (ψ p))
      have hdw := DFunLike.congr_fun hd w
      change mfderiv IC J Φ (ψ p) w =
        mfderiv J J (Subtype.val : C₁.target → M) (C₁.chart (ψ p))
          (mfderiv IC J C₁.chart (ψ p) w) at hdw
      change mfderiv J J (Subtype.val : C₁.target → M) (C₁.chart (ψ p))
        (Real.sqrt C₁.scale • mfderiv IC J C₁.chart (ψ p) w) = _
      exact (map_smul _ _ _).trans (congrArg (fun v ↦ Real.sqrt C₁.scale • v) hdw.symm)
    have hn := C₁.mvfderiv_axialVector_ne_zero_of_gradient_close g ε hε hsmall C₀.axial
      σ δ hσ hδ (ψ p) (hU p) (by
        change Real.sqrt (g.inner (Φ (ψ p))
          (gradFun g C₀.axial (Φ (ψ p)) - σ • gradFun g C₁.axial (Φ (ψ p)))
          (gradFun g C₀.axial (Φ (ψ p)) - σ • gradFun g C₁.axial (Φ (ψ p)))) ≤ δ
        rw [hpoint]
        exact hgrad p)
    apply hn
    rw [hv, map_smul, smul_eq_mul]
    change Real.sqrt C₁.scale * mvfderiv J C₀.axial (Φ (ψ p)) (mfderiv IC J Φ (ψ p) w) = 0
    rw [← hchain, hqw, mul_zero]
  obtain ⟨η, h, hh, hmem, heq⟩ := exists_diffeomorph_graph_of_product_chart_section
    C₀.domain C₁.domain C₀.target C₁.target C₀.chart C₁.chart t hsection htarget htransverse
  refine ⟨η, h, hh, hmem, heq, ?_⟩
  intro p
  have hb := hvalue (η p)
  dsimp only at hb
  have h₀ := C₀.axial_chart ⟨(η p, t), hsection (η p)⟩
  have h₁ := C₁.axial_chart ⟨(p, h p), hmem p⟩
  rw [heq p] at h₁
  rwa [h₀, h₁] at hb

end Poincare.Geometry.Neck
