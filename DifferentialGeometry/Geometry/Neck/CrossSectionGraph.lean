import DifferentialGeometry.Geometry.Neck.ChartAxis
import DifferentialGeometry.Geometry.Neck.InwardCurve
import DifferentialGeometry.Geometry.Neck.LeastRicciField
import DifferentialGeometry.Topology.Manifold.ProductChartGraph
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Neck

private abbrev S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
private instance : PathConnectedSpace S :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_sphere (by simp [← Module.finrank_eq_rank] :
      1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3))) _ zero_le_one)

theorem cylindricalChart.transverse_full_cross_section_of_axial_derivative_ne_zero
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M]
    (C₀ C₁ : cylindricalChart J (M := M)) (t : ℝ)
    (hsection : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t) ∈ C₀.domain)
    (htarget : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (C₀.chart ⟨(p, t), hsection p⟩ : M) ∈ C₁.target)
    (haxial : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      let x := C₁.chart.symm ⟨(C₀.chart ⟨(p, t), hsection p⟩ : M), htarget p⟩
      mvfderiv J C₀.axial (C₁.chart x : M) (C₁.axialVector x) ≠ 0) :
    ∀ p, (0, 1) ∉ range (mfderiv (𝓡 2) ((𝓡 2).prod 𝓘(ℝ))
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦
        (C₁.chart.symm ⟨(C₀.chart ⟨(p, t), hsection p⟩ : M), htarget p⟩ :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)) p) := by
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
    have hn := haxial p
    apply hn
    change mvfderiv J C₀.axial (Φ (ψ p)) (C₁.axialVector (ψ p)) = 0
    rw [hv, map_smul, smul_eq_mul]
    rw [← hchain, hqw, mul_zero]
  exact htransverse

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
  have haxial (p : S) :
      let x := C₁.chart.symm ⟨(C₀.chart ⟨(p, t), hsection p⟩ : M), htarget p⟩
      mvfderiv J C₀.axial (C₁.chart x : M) (C₁.axialVector x) ≠ 0 :=
    C₁.mvfderiv_axialVector_ne_zero_of_gradient_close g ε hε hsmall C₀.axial
      σ δ hσ hδ _ (hU p) (by
        have heq : (C₁.chart (C₁.chart.symm
            ⟨(C₀.chart ⟨(p, t), hsection p⟩ : M), htarget p⟩) : M) =
            (C₀.chart ⟨(p, t), hsection p⟩ : M) :=
          congrArg Subtype.val (C₁.chart.apply_symm_apply _)
        rw [heq]
        exact hgrad p)
  have htransverse := C₀.transverse_full_cross_section_of_axial_derivative_ne_zero
    C₁ t hsection htarget haxial
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

theorem cylindricalChart.exists_smoothTwoSidedCollar_of_full_cross_section_of_metric_close
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    [BoundarylessManifold J M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M) (t : ℝ)
    (hsection : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t) ∈ C₀.domain)
    (htarget : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (C₀.chart ⟨(p, t), hsection p⟩ : M) ∈ C₁.target)
    {U₀ : Set C₀.domain} {U₁ : Set C₁.domain} (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (ε : ℝ) (hε : ε < 1 / 1000000)
    (hsmall₀ : C₀.metricCloseOn g ε U₀) (hsmall₁ : C₁.metricCloseOn g ε U₁)
    (hinside₀ : ∀ p, (⟨(p, t), hsection p⟩ : C₀.domain) ∈ U₀)
    (hinside₁ : ∀ p,
      C₁.chart.symm ⟨(C₀.chart ⟨(p, t), hsection p⟩ : M), htarget p⟩ ∈ U₁)
    {r : ℝ} (hr : 0 < r) :
    ∃ (η : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ), ContMDiff (𝓡 2) 𝓘(ℝ) ∞ a ∧
      ∃ hmem : ∀ p, (p, a p) ∈ C₁.domain,
        (∀ p, (C₁.chart ⟨(p, a p), hmem p⟩ : M) =
          (C₀.chart ⟨(η p, t), hsection (η p)⟩ : M)) ∧
        ∃ c : DifferentialGeometry.Topology.SmoothTwoSidedCollar (𝓡 2) J
            (fun p ↦ (C₀.chart ⟨(p, t), hsection p⟩ : M)),
          c.radius < r ∧
          (∀ p s, s ∈ Icc (-c.radius) c.radius → (p, a p + s) ∈ C₁.domain) ∧
          ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
              DifferentialGeometry.Topology.symmetricOpenInterval c.radius,
            ∃ hp : (η.symm p.1, a (η.symm p.1) + (p.2 : ℝ)) ∈ C₁.domain,
              c.toFun p =
                (C₁.chart ⟨(η.symm p.1, a (η.symm p.1) + (p.2 : ℝ)), hp⟩ : M) := by
  have haxial (p : S) :
      let x := C₁.chart.symm ⟨(C₀.chart ⟨(p, t), hsection p⟩ : M), htarget p⟩
      mvfderiv J C₀.axial (C₁.chart x : M) (C₁.axialVector x) ≠ 0 := by
    let x := C₁.chart.symm ⟨(C₀.chart ⟨(p, t), hsection p⟩ : M), htarget p⟩
    have hpoint : (C₁.chart x : M) = (C₀.chart ⟨(p, t), hsection p⟩ : M) := by
      simp only [x, C₁.chart.apply_symm_apply]
    have hx₀ : (C₁.chart x : M) ∈ C₀.region U₀ := by
      rw [hpoint]
      exact ⟨_, ⟨_, hinside₀ p, rfl⟩, rfl⟩
    have hx₁ : (C₁.chart x : M) ∈ C₁.region U₁ :=
      ⟨_, ⟨x, hinside₁ p, rfl⟩, rfl⟩
    obtain ⟨σ, hσ, hgrad⟩ := C₀.exists_sign_axial_gradient_bound C₁ g hU₀ hU₁ ε ε
      (by linarith) (by linarith) hsmall₀ hsmall₁ hx₀ hx₁
    have heq : 184712 * (ε + ε) = 369424 * ε := by ring
    rw [heq] at hgrad
    have hδ0 : 0 ≤ 369424 * ε := (Real.sqrt_nonneg _).trans hgrad
    have hsqrt : Real.sqrt (1 + ε) ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
    have hδ : (369424 * ε) * Real.sqrt (1 + ε) < 1 :=
      (mul_le_mul_of_nonneg_left hsqrt hδ0).trans_lt (by linarith)
    exact C₁.mvfderiv_axialVector_ne_zero_of_gradient_close g ε (by linarith) hsmall₁
      C₀.axial σ (369424 * ε) hσ hδ x (hinside₁ p) hgrad
  exact exists_smoothTwoSidedCollar_of_transverse_product_chart_section
    C₀.domain C₁.domain C₀.target C₁.target C₀.chart C₁.chart t hsection htarget
    (C₀.transverse_full_cross_section_of_axial_derivative_ne_zero C₁ t hsection htarget haxial) hr

end DifferentialGeometry.Geometry.Neck
