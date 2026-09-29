import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Truncation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.GramIndexBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.JacobiMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.MovingEndpointSecondVariation
import DifferentialGeometry.Geometry.Comparison.Variation.Field.PairRealization
import DifferentialGeometry.Analysis.Calculus.SecondDerivative.Minimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobi.Uniqueness
import DifferentialGeometry.Geometry.Metric.VectorField.SmoothGlobalExtension
import DifferentialGeometry.Bundle.Section

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Variation

section ChartCorrection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem IsSmoothVariation.contMDiff_slice {f : ℝ → ℝ → M}
    (hf : IsSmoothVariation (I := 𝓘(ℝ, E)) f) (u : ℝ) : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 8 (f u) :=
  hf.comp (contMDiff_const.prodMk contMDiff_id)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem IsSmoothVariation.contMDiff_curve {f : ℝ → ℝ → M}
    (hf : IsSmoothVariation (I := 𝓘(ℝ, E)) f) (s : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 8 (fun u => f u s) :=
  hf.comp (contMDiff_id.prodMk contMDiff_const)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem mfderiv_extChartAt_congr (x₀ : M) {x y : M} (h : x = y)
    (a : TangentSpace 𝓘(ℝ, E) x) (b : TangentSpace 𝓘(ℝ, E) y) (hab : (a : E) = b) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) x a =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) y b := by
  subst h
  rw [show a = b from hab]

private theorem hasFDerivAt_extChartAt_comp (x₀ : M) {γ : ℝ → M}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0)
    (hs : γ 0 ∈ (chartAt E x₀).source) :
    HasFDerivAt (fun u => extChartAt 𝓘(ℝ, E) x₀ (γ u))
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) (γ 0)).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ 0)) 0 := by
  have h := ((mdifferentiableAt_extChartAt hs).hasMFDerivAt.comp 0 hγ.hasMFDerivAt)
  rwa [hasMFDerivAt_iff_hasFDerivAt] at h

private theorem mfderiv_symm_comp_eq (x₀ : M) {g₀ g₁ : ℝ → E} {L : ℝ →L[ℝ] E}
    (hg₀ : HasFDerivAt g₀ L 0) (hg₁ : HasFDerivAt g₁ L 0) (h0 : g₁ 0 = g₀ 0)
    (ht : g₀ 0 ∈ (extChartAt 𝓘(ℝ, E) x₀).target) :
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u => (extChartAt 𝓘(ℝ, E) x₀).symm (g₁ u)) 0 1 : E) =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u => (extChartAt 𝓘(ℝ, E) x₀).symm (g₀ u)) 0 1 := by
  have hs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm (g₀ 0) :=
    ((contMDiffOn_extChartAt_symm (n := 1) x₀).contMDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds ht)).mdifferentiableAt (by norm_num)
  have hs₁ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm (g₁ 0) := by
    rw [h0]
    exact hs
  have h₀ := (hs.hasMFDerivAt.comp 0 (hasMFDerivAt_iff_hasFDerivAt.2 hg₀)).mfderiv
  have h₁ := (hs₁.hasMFDerivAt.comp 0 (hasMFDerivAt_iff_hasFDerivAt.2 hg₁)).mfderiv
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ g₁) 0 1 : E) =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ g₀) 0 1
  rw [h₁, h₀]
  exact congrArg (fun x => ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm x).comp L)
    (1 : ℝ)) h0

theorem exists_isSmoothVariation_eq_curve (f₀ : ℝ → ℝ → M)
    (hf : IsSmoothVariation (I := 𝓘(ℝ, E)) f₀) (c ε : ℝ) (hε : 0 < ε) (σ : ℝ → M)
    (hσ : ∀ᶠ u in 𝓝 (0 : ℝ), ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 8 σ u) (hσ0 : σ 0 = f₀ 0 c)
    (hσ' : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) σ 0 1 : E) =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u => f₀ u c) 0 1) :
    ∃ f : ℝ → ℝ → M, IsSmoothVariation (I := 𝓘(ℝ, E)) f ∧ (∀ s, f 0 s = f₀ 0 s) ∧
      (∀ s, (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u => f u s) 0 1 : E) =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u => f₀ u s) 0 1) ∧
      (∀ᶠ u in 𝓝 (0 : ℝ), f u c = σ u) ∧ (∀ u s, ε ≤ |s - c| → f u s = f₀ u s) := by
  classical
  set x₀ := f₀ 0 c with hx₀
  set φ := extChartAt 𝓘(ℝ, E) x₀
  have hsrc : φ.source = (chartAt E x₀).source := extChartAt_source 𝓘(ℝ, E) x₀
  have hsrcO : IsOpen φ.source := isOpen_extChartAt_source x₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) x₀)
    (φ x₀) (mem_extChartAt_target x₀)
  have hfc : Continuous (fun p : ℝ × ℝ => f₀ p.1 p.2) := hf.continuous
  have hP : ∀ᶠ y in 𝓝 x₀, y ∈ φ.source ∧ dist (φ y) (φ x₀) < r / 2 :=
    (Filter.eventually_of_mem (hsrcO.mem_nhds (mem_extChartAt_source x₀)) fun _ hy => hy).and
      ((continuousAt_extChartAt (I := 𝓘(ℝ, E)) x₀).eventually
        (Metric.ball_mem_nhds _ (half_pos hr)))
  have hP' : ∀ᶠ p in 𝓝 ((0 : ℝ), c), f₀ p.1 p.2 ∈ φ.source ∧
      dist (φ (f₀ p.1 p.2)) (φ x₀) < r / 2 := (hfc.continuousAt (x := ((0 : ℝ), c))).eventually hP
  have hσc : ContinuousAt σ 0 := (hσ.self_of_nhds).continuousAt
  have hf₀c : Continuous (fun u => f₀ u c) :=
    hfc.comp (continuous_id.prodMk continuous_const)
  have hσs : ∀ᶠ u in 𝓝 (0 : ℝ), σ u ∈ φ.source :=
    hσc.preimage_mem_nhds (by rw [hσ0]; exact hsrcO.mem_nhds (mem_extChartAt_source x₀))
  have hfs : ∀ᶠ u in 𝓝 (0 : ℝ), f₀ u c ∈ φ.source :=
    (hf₀c.continuousAt (x := (0 : ℝ))).preimage_mem_nhds
      (hsrcO.mem_nhds (mem_extChartAt_source x₀))
  have hD : Filter.Tendsto (fun u => φ (σ u) - φ (f₀ u c)) (𝓝 0) (𝓝 0) := by
    have h1 : Filter.Tendsto (fun u => φ (σ u)) (𝓝 0) (𝓝 (φ x₀)) := by
      have := (continuousAt_extChartAt (I := 𝓘(ℝ, E)) x₀).tendsto.comp
        (show Filter.Tendsto σ (𝓝 0) (𝓝 x₀)
        from hσ0 ▸ hσc.tendsto)
      exact this
    have h2 : Filter.Tendsto (fun u => φ (f₀ u c)) (𝓝 0) (𝓝 (φ x₀)) :=
      (continuousAt_extChartAt (I := 𝓘(ℝ, E)) x₀).tendsto.comp hf₀c.continuousAt.tendsto
    simpa using h1.sub h2
  have hQ : ∀ᶠ u in 𝓝 (0 : ℝ), σ u ∈ φ.source ∧ f₀ u c ∈ φ.source ∧
      ‖φ (σ u) - φ (f₀ u c)‖ < r / 2 ∧ ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 8 σ u :=
    hσs.and (hfs.and ((hD.eventually (Metric.ball_mem_nhds _ (half_pos hr))).mono
      (fun u hu => by simpa using hu) |>.and hσ))
  obtain ⟨η₁, hη₁, h₁⟩ := Metric.eventually_nhds_iff.1 hP'
  obtain ⟨η₂, hη₂, h₂⟩ := Metric.eventually_nhds_iff.1 hQ
  set η := min (min η₁ η₂) ε
  have hη : 0 < η := lt_min (lt_min hη₁ hη₂) hε
  have hbox : ∀ u s, |u| < η → |s - c| < η →
      (f₀ u s ∈ φ.source ∧ dist (φ (f₀ u s)) (φ x₀) < r / 2) ∧
      (σ u ∈ φ.source ∧ f₀ u c ∈ φ.source ∧ ‖φ (σ u) - φ (f₀ u c)‖ < r / 2 ∧
        ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 8 σ u) := by
    intro u s hu hs
    have hη1 : η ≤ η₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hη2 : η ≤ η₂ := (min_le_left _ _).trans (min_le_right _ _)
    refine ⟨h₁ (y := (u, s)) ?_, h₂ ?_⟩
    · rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, sub_zero]
      exact ⟨hu.trans_le hη1, hs.trans_le hη1⟩
    · rw [Real.dist_eq, sub_zero]
      exact hu.trans_le hη2
  let ψ : ContDiffBump (0 : ℝ) := ⟨η / 4, η / 2, by positivity, by linarith⟩
  let ρ : ContDiffBump c := ⟨η / 4, η / 2, by positivity, by linarith⟩
  let κ : ℝ → ℝ → ℝ := fun u s => ρ s * ψ u
  have hκ0 : ∀ u s, (η / 2 ≤ |u| ∨ η / 2 ≤ |s - c|) → κ u s = 0 := by
    intro u s h
    rcases h with h | h
    · have : ψ u = 0 := Function.notMem_support.1 (by
        rw [ψ.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
        exact not_lt.2 h)
      simp [κ, this]
    · have : ρ s = 0 := Function.notMem_support.1 (by
        rw [ρ.support_eq, Metric.mem_ball, Real.dist_eq]
        exact not_lt.2 h)
      simp [κ, this]
  have hκ01 : ∀ u s, 0 ≤ κ u s ∧ κ u s ≤ 1 := fun u s =>
    ⟨mul_nonneg ρ.nonneg ψ.nonneg, mul_le_one₀ ρ.le_one ψ.nonneg ψ.le_one⟩
  let G : ℝ × ℝ → E := fun p => φ (f₀ p.1 p.2) + κ p.1 p.2 • (φ (σ p.1) - φ (f₀ p.1 c))
  let B : Set (ℝ × ℝ) := {p | |p.1| < η ∧ |p.2 - c| < η}
  have hBo : IsOpen B :=
    (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
      (isOpen_lt (continuous_abs.comp (continuous_snd.sub continuous_const)) continuous_const)
  have hGt : ∀ p ∈ B, G p ∈ φ.target := by
    intro p hp
    obtain ⟨⟨_, hd⟩, ⟨_, _, hn, _⟩⟩ := hbox p.1 p.2 hp.1 hp.2
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖G p - φ x₀‖ ≤ ‖φ (f₀ p.1 p.2) - φ x₀‖ + ‖κ p.1 p.2 • (φ (σ p.1) - φ (f₀ p.1 c))‖ := by
          simp only [G]; rw [add_sub_right_comm]; exact norm_add_le _ _
      _ < r / 2 + r / 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hκ01 _ _).1]
          rw [← dist_eq_norm]
          exact add_lt_add_of_lt_of_le hd ((mul_le_of_le_one_left (norm_nonneg _)
            (hκ01 _ _).2).trans hn.le)
      _ = r := by ring
  let f : ℝ → ℝ → M := fun u s => if (u, s) ∈ B then φ.symm (G (u, s)) else f₀ u s
  have hfB : ∀ p ∈ B, f p.1 p.2 = φ.symm (G p) := fun p hp => by simp [f, hp]
  have hf₀B : ∀ p ∈ B, κ p.1 p.2 = 0 → f p.1 p.2 = f₀ p.1 p.2 := by
    intro p hp hκ
    rw [hfB p hp]
    simp only [G, hκ, zero_smul, add_zero]
    exact φ.left_inv (hbox p.1 p.2 hp.1 hp.2).1.1
  let C : Set (ℝ × ℝ) := {p | |p.1| < η / 2 ∧ |p.2 - c| < η / 2}
  have hCB : C ⊆ B := fun p hp => ⟨hp.1.trans (by linarith), hp.2.trans (by linarith)⟩
  have hout : ∀ p, p ∉ C → f p.1 p.2 = f₀ p.1 p.2 := by
    intro p hp
    by_cases hB : p ∈ B
    · refine hf₀B p hB (hκ0 _ _ ?_)
      rcases not_and_or.1 hp with h | h
      · exact Or.inl (not_lt.1 h)
      · exact Or.inr (not_lt.1 h)
    · simp [f, hB]
  have hCc : IsClosed {p : ℝ × ℝ | |p.1| ≤ η / 2 ∧ |p.2 - c| ≤ η / 2} :=
    (isClosed_le (continuous_abs.comp continuous_fst) continuous_const).inter
      (isClosed_le (continuous_abs.comp (continuous_snd.sub continuous_const)) continuous_const)
  have hGs : ∀ p ∈ B, ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 8 G p := by
    intro p hp
    obtain ⟨⟨hs₁, _⟩, ⟨hs₂, hs₃, _, hσp⟩⟩ := hbox p.1 p.2 hp.1 hp.2
    rw [hsrc] at hs₁ hs₂ hs₃
    have e1 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 8 (fun q : ℝ × ℝ => φ (f₀ q.1 q.2)) p :=
      (contMDiffAt_extChartAt' hs₁).comp p (hf p)
    have e2 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 8 (fun q : ℝ × ℝ => φ (σ q.1)) p :=
      ((contMDiffAt_extChartAt' hs₂).comp p.1 hσp).comp p contMDiffAt_fst
    have e3 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 8 (fun q : ℝ × ℝ => φ (f₀ q.1 c)) p :=
      ((contMDiffAt_extChartAt' hs₃).comp p.1 ((hf.comp (contMDiff_id.prodMk
        contMDiff_const)).contMDiffAt)).comp p contMDiffAt_fst
    have e4 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 8 (fun q : ℝ × ℝ => κ q.1 q.2) p :=
      ((ρ.contDiff.contMDiff.comp contMDiff_snd).mul
        (ψ.contDiff.contMDiff.comp contMDiff_fst)).contMDiffAt
    exact e1.add (e4.smul (e2.sub e3))
  have hG0 : ∀ s, G (0, s) = φ (f₀ 0 s) := by
    intro s
    simp only [G, hσ0, ← hx₀, sub_self, smul_zero, add_zero]
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    by_cases hp : p ∈ B
    · have hev : (fun q : ℝ × ℝ => f q.1 q.2) =ᶠ[𝓝 p] fun q => φ.symm (G q) := by
        filter_upwards [hBo.mem_nhds hp] with q hq
        exact hfB q hq
      refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
      exact ((contMDiffOn_extChartAt_symm x₀).contMDiffAt
        ((isOpen_extChartAt_target x₀).mem_nhds (hGt p hp))).comp p (hGs p hp)
    · have hpC : p ∉ {q : ℝ × ℝ | |q.1| ≤ η / 2 ∧ |q.2 - c| ≤ η / 2} := by
        intro h
        exact hp ⟨h.1.trans_lt (by linarith), h.2.trans_lt (by linarith)⟩
      have hev : (fun q : ℝ × ℝ => f q.1 q.2) =ᶠ[𝓝 p] fun q => f₀ q.1 q.2 := by
        filter_upwards [hCc.isOpen_compl.mem_nhds hpC] with q hq
        exact hout q fun h => hq ⟨h.1.le, h.2.le⟩
      exact (hf p).congr_of_eventuallyEq hev
  · intro s
    by_cases hB : ((0 : ℝ), s) ∈ B
    · rw [hfB _ hB, hG0]
      exact φ.left_inv (hbox 0 s hB.1 hB.2).1.1
    · simp [f, hB]
  · intro s
    by_cases hB : ((0 : ℝ), s) ∈ B
    · obtain ⟨⟨hs₁, _⟩, ⟨hs₂, hs₃, _, hσp⟩⟩ := hbox 0 s hB.1 hB.2
      have hBu : ∀ᶠ u in 𝓝 (0 : ℝ), (u, s) ∈ B :=
        (hBo.preimage (continuous_id.prodMk continuous_const)).mem_nhds hB
      have hev₁ : (fun u => f u s) =ᶠ[𝓝 0] fun u => φ.symm (G (u, s)) := by
        filter_upwards [hBu] with u hu
        exact hfB (u, s) hu
      have hev₀ : (fun u => f₀ u s) =ᶠ[𝓝 0] fun u => φ.symm (φ (f₀ u s)) := by
        filter_upwards [hBu] with u hu
        exact (φ.left_inv (hbox u s hu.1 hu.2).1.1).symm
      rw [hev₁.mfderiv_eq, hev₀.mfderiv_eq]
      have hg₀ := hasFDerivAt_extChartAt_comp x₀ (γ := fun u => f₀ u s)
        (((hf.comp (contMDiff_id.prodMk contMDiff_const)) 0).mdifferentiableAt (by norm_num))
        (hsrc ▸ hs₁)
      have hσd := hasFDerivAt_extChartAt_comp x₀ (γ := σ) (hσp.mdifferentiableAt (by norm_num))
        (hsrc ▸ hs₂)
      have hfd := hasFDerivAt_extChartAt_comp x₀ (γ := fun u => f₀ u c)
        (((hf.comp (contMDiff_id.prodMk contMDiff_const)) 0).mdifferentiableAt (by norm_num))
        (hsrc ▸ hs₃)
      have hA : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) (σ 0)).comp
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) σ 0) =
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) (f₀ 0 c)).comp
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun u => f₀ u c) 0) := by
        refine ContinuousLinearMap.ext_ring ?_
        exact mfderiv_extChartAt_congr x₀ hσ0 _ _ hσ'
      have hDd : HasFDerivAt (fun u => φ (σ u) - φ (f₀ u c)) (0 : ℝ →L[ℝ] E) 0 :=
        (hσd.sub hfd).congr_fderiv (sub_eq_zero.2 hA)
      have hκd := ((ψ.contDiff (n := 1)).differentiable one_ne_zero 0).hasFDerivAt.const_mul
        (ρ s)
      have hD0 : φ (σ 0) - φ (f₀ 0 c) = 0 := by rw [hσ0, ← hx₀, sub_self]
      have hκD : HasFDerivAt (fun u => κ u s • (φ (σ u) - φ (f₀ u c))) (0 : ℝ →L[ℝ] E) 0 :=
        (hκd.smul hDd).congr_fderiv (by
          refine ContinuousLinearMap.ext_ring ?_
          simp [hD0])
      have hg₁' : HasFDerivAt (fun u => G (u, s)) ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
          (extChartAt 𝓘(ℝ, E) x₀) (f₀ 0 s)).comp (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
            (fun u => f₀ u s) 0)) 0 :=
        (hg₀.add hκD).congr_fderiv (add_zero _)
      exact mfderiv_symm_comp_eq x₀ hg₀ hg₁' (hG0 s) (φ.map_source hs₁)
    · have hs : ∀ u, f u s = f₀ u s := fun u => hout (u, s) fun h => hB
        ⟨by simpa using hη, h.2.trans (by linarith)⟩
      rw [show (fun u => f u s) = fun u => f₀ u s from funext hs]
      rfl
  · have hu : ∀ᶠ u in 𝓝 (0 : ℝ), |u| < η / 4 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < η / 4)] with u hu
      simpa [Real.dist_eq] using hu
    filter_upwards [hu] with u hu
    have hB : (u, c) ∈ B := ⟨hu.trans (by linarith), by simpa using hη⟩
    rw [hfB (u, c) hB]
    have hκ1 : κ u c = 1 := by
      simp only [κ]
      rw [ρ.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)),
        ψ.one_of_mem_closedBall (by simpa [Real.dist_eq] using hu.le), one_mul]
    simp only [G, hκ1, one_smul, add_sub_cancel]
    exact φ.left_inv (hbox u c hB.1 hB.2).2.1
  · intro u s hs
    apply hout (u, s)
    intro hC
    have h1 := hC.2
    have h2 : η ≤ ε := min_le_right _ _
    change |s - c| < η / 2 at h1
    linarith

end ChartCorrection

end DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation (IsSmoothVariation)

universe u

structure LWindowChain (H : ObservedHistory.{u}) {first last : Fin (H.eventCount + 1)} (T v : ℝ)
    (α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier) where
  n : ℕ
  c : ℕ → ℝ
  c_zero : c 0 = 0
  c_n : c n = v
  lt : ∀ k < n, c k < c (k + 1)
  lo : ℕ → Fin (H.eventCount + 1)
  hi : ℕ → Fin (H.eventCount + 1)
  first_le : ∀ k, first ≤ lo k
  le_last : ∀ k, hi k ≤ last
  W : (k : ℕ) → H.LWindow (lo k) (hi k) T
  γ : (k : ℕ) → ℝ → (W k).X
  geodesic : ∀ k < n, ∃ a b : ℝ, a < c k ∧ c (k + 1) < b ∧
    IsLRegularizedGeodesicOn (W k).S T (γ k) (Ioo a b)
  piece : ∀ k < n, Icc (c k) (c (k + 1)) ⊆ Icc (W k).a (W k).b
  eqOn : ∀ k < n, ∀ j : H.StageInterval (lo k) (hi k),
    EqOn ((W k).f j ∘ γ k)
      (α ⟨j.val, (first_le k).trans j.property.1, j.property.2.trans (le_last k)⟩)
      (Icc (H.regularizedStageStart T (W k).a j.val) (H.regularizedStageEnd T (W k).b j.val))
  contMDiff : ∀ k, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (γ k)
  stage : ℕ → Fin (H.eventCount + 1)
  stage_zero : stage 0 = last
  stage_n : stage n = first
  mem_stageDomain : ∀ m ≤ n, T - c m ^ 2 ∈ H.stageDomain (stage m)
  lo_le_stage : ∀ k < n, lo k ≤ stage (k + 1)
  stage_le_hi : ∀ k < n, stage k ≤ hi k
  node : ∀ k, k + 1 < n →
    c (k + 1) ∈ Ioo (H.regularizedStageStart T (W k).a (stage (k + 1)))
      (H.regularizedStageEnd T (W k).b (stage (k + 1))) ∧
    c (k + 1) ∈ Ioo (H.regularizedStageStart T (W (k + 1)).a (stage (k + 1)))
      (H.regularizedStageEnd T (W (k + 1)).b (stage (k + 1)))

private theorem le_of_mem_stageDomain {H : ObservedHistory.{u}} {j k : Fin (H.eventCount + 1)}
    {t t' : ℝ} (ht : t ∈ H.stageDomain j) (ht' : t' ∈ H.stageDomain k) (htt' : t ≤ t') :
    j ≤ k := by
  by_contra h
  have h1 := H.stageEndTime_le_time_of_lt (not_le.1 h)
  have h2 : t' < H.stageEndTime k := by
    cases k using Fin.lastCases with
    | last => exact absurd (not_le.1 h) (not_lt.2 (Fin.le_last j))
    | cast i =>
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at ht'
      rw [stageEndTime_castSucc]
      exact ht'.2
  linarith [H.time_le_of_mem_stageDomain ht]

namespace LWindowChain

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {T v : ℝ}
  {α : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier}
  (ch : H.LWindowChain T v α)

abbrev Field : Type := (k : ℕ) → (s : ℝ) → TangentSpace ThreeModel (ch.γ k s)

def historyLIndex (Y Y' : ch.Field) : ℝ :=
  ∑ k ∈ Finset.range ch.n,
    lRegularizedIndex (ch.W k).S T (ch.γ k) (Y k) (Y' k) (ch.c k) (ch.c (k + 1))

theorem c_nonneg {k : ℕ} (hk : k < ch.n) : 0 ≤ ch.c k :=
  (ch.W k).nonneg.trans (ch.piece k hk (left_mem_Icc.2 (ch.lt k hk).le)).1

theorem stage_succ_le {k : ℕ} (hk : k < ch.n) : ch.stage (k + 1) ≤ ch.stage k := by
  have h0 := ch.c_nonneg hk
  have h1 := ch.lt k hk
  exact le_of_mem_stageDomain (ch.mem_stageDomain (k + 1) hk) (ch.mem_stageDomain k hk.le)
    (by nlinarith)

def bottom {k : ℕ} (hk : k < ch.n) : H.StageInterval (ch.lo k) (ch.hi k) :=
  ⟨ch.stage (k + 1), ch.lo_le_stage k hk, (ch.stage_succ_le hk).trans (ch.stage_le_hi k hk)⟩

def top {k : ℕ} (hk : k < ch.n) : H.StageInterval (ch.lo k) (ch.hi k) :=
  ⟨ch.stage k, (ch.lo_le_stage k hk).trans (ch.stage_succ_le hk), ch.stage_le_hi k hk⟩

theorem bottom_eq_top {k : ℕ} (hk : k + 1 < ch.n) :
    (ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)) (ch.γ k (ch.c (k + 1))) =
      (ch.W (k + 1)).f (ch.top hk) (ch.γ (k + 1) (ch.c (k + 1))) :=
  (ch.eqOn k (Nat.lt_of_succ_lt hk) (ch.bottom (Nat.lt_of_succ_lt hk))
    (Ioo_subset_Icc_self (ch.node k hk).1)).trans
    (ch.eqOn (k + 1) hk (ch.top hk) (Ioo_subset_Icc_self (ch.node k hk).2)).symm

def GluedAt (Y : ch.Field) {k : ℕ} (hk : k + 1 < ch.n) : Prop :=
  (mfderiv ThreeModel ThreeModel ((ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)))
      (ch.γ k (ch.c (k + 1))) (Y k (ch.c (k + 1))) : ThreeSpace) =
    mfderiv ThreeModel ThreeModel ((ch.W (k + 1)).f (ch.top hk))
      (ch.γ (k + 1) (ch.c (k + 1))) (Y (k + 1) (ch.c (k + 1)))

def IsGlued (Y : ch.Field) : Prop :=
  ∀ k (hk : k + 1 < ch.n), ch.GluedAt Y hk


def IsRegularField (Y : ch.Field) : Prop :=
  ∀ k < ch.n, ∀ s ∈ uIcc (ch.c k) (ch.c (k + 1)),
    DifferentiableAt ℝ (chartRepAt (I := ThreeModel) (ch.γ k) (Y k) s) s

def covDerivField (Y : ch.Field) : ch.Field := fun k s =>
  covDerivAlong (I := ThreeModel) ((ch.W k).S.base.metric (T - s ^ 2)) (ch.γ k) (Y k) s

def IsHistoryLJacobi (J : ch.Field) : Prop :=
  (∀ k < ch.n, IsLRegularizedJacobi (ch.W k).S T (ch.γ k) (J k) (uIcc (ch.c k) (ch.c (k + 1)))) ∧
    ch.IsGlued J ∧ ch.IsGlued (ch.covDerivField J)

def evalAt (k : ℕ) (s : ℝ) : ch.Field →ₗ[ℝ] TangentSpace ThreeModel (ch.γ k s) where
  toFun Y := Y k s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem historyLIndex_symm (Y Y' : ch.Field) :
    ch.historyLIndex Y Y' = ch.historyLIndex Y' Y :=
  Finset.sum_congr rfl fun _ _ => lRegularizedIndex_symm _ _ _ _ _ _ _

theorem historyLIndex_smul (r : ℝ) (Y Y' : ch.Field) :
    ch.historyLIndex (r • Y) Y' = r * ch.historyLIndex Y Y' := by
  rw [historyLIndex, historyLIndex, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => lRegularizedIndex_smul _ _ r _ _ _ _ _

theorem historyLIndex_add {Y Z Y' : ch.Field} (hY : ch.IsRegularField Y)
    (hZ : ch.IsRegularField Z)
    (hYi : ∀ k < ch.n, IntervalIntegrable
      (lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (Y k) (Y' k)) MeasureTheory.volume
      (ch.c k) (ch.c (k + 1)))
    (hZi : ∀ k < ch.n, IntervalIntegrable
      (lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (Z k) (Y' k)) MeasureTheory.volume
      (ch.c k) (ch.c (k + 1))) :
    ch.historyLIndex (Y + Z) Y' = ch.historyLIndex Y Y' + ch.historyLIndex Z Y' := by
  rw [historyLIndex, historyLIndex, historyLIndex, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  exact lRegularizedIndex_add _ _ _ _ _ _ _ _ (hY k hk') (hZ k hk') (hYi k hk') (hZi k hk')

def boundaryForm (J : ch.Field) (k : ℕ) (s : ℝ) : TangentSpace ThreeModel (ch.γ k s) →ₗ[ℝ] ℝ :=
  ((ch.W k).S.base.metric (T - s ^ 2)).inner (ch.γ k s) (ch.covDerivField J k s) |>.toLinearMap

private theorem inner_congr_point {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] (g : SmoothRiemannianMetric ThreeModel N) {p q : N} (h : p = q)
    (a b : TangentSpace ThreeModel p) (a' b' : TangentSpace ThreeModel q)
    (ha : (a : ThreeSpace) = a') (hb : (b : ThreeSpace) = b') :
    g.inner p a b = g.inner q a' b' := by
  subst h
  rw [show a = a' from ha, show b = b' from hb]

theorem boundaryForm_node {J X : ch.Field} {k : ℕ} (hk : k + 1 < ch.n)
    (hJ : ch.GluedAt (ch.covDerivField J) hk) (hX : ch.GluedAt X hk) :
    ch.boundaryForm J k (ch.c (k + 1)) (X k (ch.c (k + 1))) =
      ch.boundaryForm J (k + 1) (ch.c (k + 1)) (X (k + 1) (ch.c (k + 1))) := by
  simp only [boundaryForm, ContinuousLinearMap.coe_coe]
  rw [(ch.W k).metric (ch.bottom (Nat.lt_of_succ_lt hk)) _ (ch.node k hk).1,
    (ch.W (k + 1)).metric (ch.top hk) _ (ch.node k hk).2, localPullMetric_inner,
    localPullMetric_inner]
  exact inner_congr_point _ (ch.bottom_eq_top hk) _ _ _ _ hJ hX

theorem lRegularizedIndex_piece_eq_half_boundary {J X : ch.Field} {k : ℕ} (hk : k < ch.n)
    (hJ : IsLRegularizedJacobi (ch.W k).S T (ch.γ k) (J k) (uIcc (ch.c k) (ch.c (k + 1))))
    (hX : ∀ s ∈ uIcc (ch.c k) (ch.c (k + 1)),
      DifferentiableAt ℝ (chartRepAt (I := ThreeModel) (ch.γ k) (X k) s) s)
    (hint : IntervalIntegrable (lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (J k) (X k))
      MeasureTheory.volume (ch.c k) (ch.c (k + 1))) :
    lRegularizedIndex (ch.W k).S T (ch.γ k) (J k) (X k) (ch.c k) (ch.c (k + 1)) =
      (1 / 2) * (ch.boundaryForm J k (ch.c (k + 1)) (X k (ch.c (k + 1))) -
        ch.boundaryForm J k (ch.c k) (X k (ch.c k))) := by
  obtain ⟨a, b, ha, hb, hgeo⟩ := ch.geodesic k hk
  have hsub : uIcc (ch.c k) (ch.c (k + 1)) ⊆ Ioo a b := by
    rw [uIcc_of_le (ch.lt k hk).le]
    exact Icc_subset_Ioo ha hb
  exact lRegularizedIndex_eq_half_boundary_of_isLRegularizedJacobi (ch.W k).S (ch.W k).solution T
    (ch.γ k) (J k) (X k) (ch.c k) (ch.c (k + 1)) (fun s hs => (hgeo s (hsub hs)).1)
    (fun s hs => by
      filter_upwards [isOpen_Ioo.mem_nhds (hsub hs)] with r hr
      exact (hgeo r hr).2.1)
    (fun s hs => (hgeo s (hsub hs)).2.2.1) hJ hX hint

theorem sum_range_lRegularizedIndex_eq_half_boundary {J X : ch.Field} {m : ℕ} (hm : m ≤ ch.n)
    (hJ : ∀ k < m, IsLRegularizedJacobi (ch.W k).S T (ch.γ k) (J k)
      (uIcc (ch.c k) (ch.c (k + 1))))
    (hJg : ∀ k (hk : k + 1 < ch.n), k + 1 < m → ch.GluedAt (ch.covDerivField J) hk)
    (hX : ∀ k < m, ∀ s ∈ uIcc (ch.c k) (ch.c (k + 1)),
      DifferentiableAt ℝ (chartRepAt (I := ThreeModel) (ch.γ k) (X k) s) s)
    (hXg : ∀ k (hk : k + 1 < ch.n), k + 1 < m → ch.GluedAt X hk)
    (hint : ∀ k < m, IntervalIntegrable
      (lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (J k) (X k)) MeasureTheory.volume
      (ch.c k) (ch.c (k + 1))) :
    ∑ k ∈ Finset.range m,
      lRegularizedIndex (ch.W k).S T (ch.γ k) (J k) (X k) (ch.c k) (ch.c (k + 1)) =
      (1 / 2) * (ch.boundaryForm J (m - 1) (ch.c m) (X (m - 1) (ch.c m)) -
        ch.boundaryForm J 0 (ch.c 0) (X 0 (ch.c 0))) := by
  let F : ℕ → ℝ := fun m =>
    ch.boundaryForm J (m - 1) (ch.c m) (X (m - 1) (ch.c m))
  have hstep : ∀ k < m, lRegularizedIndex (ch.W k).S T (ch.γ k) (J k) (X k) (ch.c k)
      (ch.c (k + 1)) = (1 / 2) * (F (k + 1) - F k) := by
    intro k hk
    rw [ch.lRegularizedIndex_piece_eq_half_boundary (hk.trans_le hm) (hJ k hk) (hX k hk)
      (hint k hk)]
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rfl
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have := ch.boundaryForm_node (k := j) (by omega) (hJg j (by omega) hk) (hXg j (by omega) hk)
      change (1 / 2) * (_ - _) = (1 / 2) * (ch.boundaryForm J (j + 1) (ch.c (j + 1 + 1))
        (X (j + 1) (ch.c (j + 1 + 1))) - ch.boundaryForm J j (ch.c (j + 1)) (X j (ch.c (j + 1))))
      rw [this]
  rw [Finset.sum_congr rfl fun k hk => hstep k (Finset.mem_range.1 hk), ← Finset.mul_sum,
    Finset.sum_range_sub F]

theorem historyLIndex_eq_half_boundary {J X : ch.Field}
    (hJ : ch.IsHistoryLJacobi J) (hX : ch.IsRegularField X) (hXg : ch.IsGlued X)
    (hint : ∀ k < ch.n, IntervalIntegrable
      (lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (J k) (X k)) MeasureTheory.volume
      (ch.c k) (ch.c (k + 1))) :
    ch.historyLIndex J X = (1 / 2) * (ch.boundaryForm J (ch.n - 1) v (ch.evalAt (ch.n - 1) v X) -
      ch.boundaryForm J 0 0 (ch.evalAt 0 0 X)) := by
  rw [historyLIndex, ch.sum_range_lRegularizedIndex_eq_half_boundary le_rfl hJ.1
    (fun k hk _ => hJ.2.2 k hk) hX (fun k hk _ => hXg k hk) hint]
  simp only [evalAt, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ch.c_n, ch.c_zero]

section Span

variable {lo hi : Fin (H.eventCount + 1)} (Wd : H.LWindow lo hi T) (γ : ℝ → Wd.X)

private theorem differentiableAt_chartRepAt_of_mem_span
    (G : Set (∀ r, TangentSpace ThreeModel (γ r))) (K : Set ℝ)
    (hG : ∀ Y ∈ G, ∀ s ∈ K, DifferentiableAt ℝ (chartRepAt (I := ThreeModel) γ Y s) s)
    {Y : ∀ r, TangentSpace ThreeModel (γ r)} (hY : Y ∈ Submodule.span ℝ G) :
    ∀ s ∈ K, DifferentiableAt ℝ (chartRepAt (I := ThreeModel) γ Y s) s := by
  induction hY using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero =>
    intro s _
    have h0 : chartRepAt (I := ThreeModel) γ (0 : ∀ r, TangentSpace ThreeModel (γ r)) s =
        fun _ => 0 := by
      funext u
      simp [chartRepAt]
    rw [h0]
    exact differentiableAt_const _
  | add x y _ _ hx hy =>
    intro s hs
    rw [show x + y = fun r => x r + y r from rfl, chartRepAt_add]
    exact (hx s hs).add (hy s hs)
  | smul r x _ hx =>
    intro s hs
    rw [show r • x = fun t => r • x t from rfl, chartRepAt_smul]
    exact (hx s hs).const_smul r

private theorem intervalIntegrable_integrand_of_mem_span
    (G : Set (∀ r, TangentSpace ThreeModel (γ r))) (a b : ℝ)
    (hG : ∀ Y ∈ G, ∀ s ∈ uIcc a b, DifferentiableAt ℝ (chartRepAt (I := ThreeModel) γ Y s) s)
    (hGint : ∀ Y ∈ G, ∀ Y' ∈ G, IntervalIntegrable (lRegularizedIndexIntegrand Wd.S T γ Y Y')
      MeasureTheory.volume a b)
    {Y Y' : ∀ r, TangentSpace ThreeModel (γ r)} (hY : Y ∈ Submodule.span ℝ G)
    (hY' : Y' ∈ Submodule.span ℝ G) :
    IntervalIntegrable (lRegularizedIndexIntegrand Wd.S T γ Y Y') MeasureTheory.volume a b := by
  have hd := fun {Z : ∀ r, TangentSpace ThreeModel (γ r)} (hZ : Z ∈ Submodule.span ℝ G) =>
    differentiableAt_chartRepAt_of_mem_span Wd γ G (uIcc a b) hG hZ
  have hstep : ∀ X ∈ G, ∀ Z ∈ Submodule.span ℝ G,
      IntervalIntegrable (lRegularizedIndexIntegrand Wd.S T γ X Z) MeasureTheory.volume a b := by
    intro X hXG Z hZ
    induction hZ using Submodule.span_induction with
    | mem z hz => exact hGint X hXG z hz
    | zero =>
      have h0 : lRegularizedIndexIntegrand Wd.S T γ X 0 = fun _ => 0 := by
        funext s
        have h := lRegularizedIndexIntegrand_smul_right Wd.S T 0 γ X X s
        simp only [zero_smul, zero_mul] at h
        exact h
      rw [h0]
      exact intervalIntegrable_const
    | add y z hy hz iy iz =>
      refine (intervalIntegrable_congr (fun s hs => ?_)).mp (iy.add iz)
      exact (lRegularizedIndexIntegrand_add_right Wd.S T γ X y z s
        (hd hy s (uIoc_subset_uIcc hs)) (hd hz s (uIoc_subset_uIcc hs))).symm
    | smul r y _ iy =>
      have hc : lRegularizedIndexIntegrand Wd.S T γ X (r • y) =
          fun s => r * lRegularizedIndexIntegrand Wd.S T γ X y s := by
        funext s
        exact lRegularizedIndexIntegrand_smul_right Wd.S T r γ X y s
      rw [hc]
      exact iy.const_mul r
  induction hY using Submodule.span_induction with
  | mem x hx => exact hstep x hx Y' hY'
  | zero =>
    have h0 : lRegularizedIndexIntegrand Wd.S T γ 0 Y' = fun _ => 0 := by
      funext s
      have h := lRegularizedIndexIntegrand_smul Wd.S T 0 γ Y' Y' s
      simp only [zero_smul, zero_mul] at h
      exact h
    rw [h0]
    exact intervalIntegrable_const
  | add x z hx hz ix iz =>
    refine (intervalIntegrable_congr (fun s hs => ?_)).mp (ix.add iz)
    exact (lRegularizedIndexIntegrand_add Wd.S T γ x z Y' s
      (hd hx s (uIoc_subset_uIcc hs)) (hd hz s (uIoc_subset_uIcc hs))).symm
  | smul r x _ ix =>
    have hc : lRegularizedIndexIntegrand Wd.S T γ (r • x) Y' =
        fun s => r * lRegularizedIndexIntegrand Wd.S T γ x Y' s := by
      funext s
      exact lRegularizedIndexIntegrand_smul Wd.S T r γ x Y' s
    rw [hc]
    exact ix.const_mul r

end Span

theorem isGlued_of_mem_span {G : Set ch.Field} (hG : ∀ Y ∈ G, ch.IsGlued Y) {Y : ch.Field}
    (hY : Y ∈ Submodule.span ℝ G) : ch.IsGlued Y := by
  induction hY using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero =>
    intro k hk
    exact (map_zero (mfderiv ThreeModel ThreeModel ((ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)))
      (ch.γ k (ch.c (k + 1))))).trans (map_zero _).symm
  | add x y _ _ hx hy =>
    intro k hk
    have h := congrArg₂ (· + ·) (hx k hk) (hy k hk)
    exact (map_add _ _ _).trans (h.trans (map_add _ _ _).symm)
  | smul r x _ hx =>
    intro k hk
    have h := congrArg (r • ·) (hx k hk)
    exact (map_smul _ _ _).trans (h.trans (map_smul _ _ _).symm)

theorem isRegularField_of_mem_span {G : Set ch.Field} (hG : ∀ Y ∈ G, ch.IsRegularField Y)
    {Y : ch.Field} (hY : Y ∈ Submodule.span ℝ G) : ch.IsRegularField Y := by
  intro k hk
  have hmem : Y k ∈ Submodule.span ℝ ((LinearMap.proj k : ch.Field →ₗ[ℝ] _) '' G) :=
    Submodule.apply_mem_span_image_of_mem_span _ hY
  exact differentiableAt_chartRepAt_of_mem_span (ch.W k) (ch.γ k) _ _
    (by rintro _ ⟨Z, hZ, rfl⟩; exact hG Z hZ k hk) hmem

theorem intervalIntegrable_of_mem_span {G : Set ch.Field} (hG : ∀ Y ∈ G, ch.IsRegularField Y)
    (hGint : ∀ Y ∈ G, ∀ Y' ∈ G, ∀ k < ch.n, IntervalIntegrable
      (lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (Y k) (Y' k)) MeasureTheory.volume
      (ch.c k) (ch.c (k + 1)))
    {Y Y' : ch.Field} (hY : Y ∈ Submodule.span ℝ G) (hY' : Y' ∈ Submodule.span ℝ G)
    {k : ℕ} (hk : k < ch.n) :
    IntervalIntegrable (lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (Y k) (Y' k))
      MeasureTheory.volume (ch.c k) (ch.c (k + 1)) := by
  have hmem : ∀ {Z : ch.Field}, Z ∈ Submodule.span ℝ G →
      Z k ∈ Submodule.span ℝ ((LinearMap.proj k : ch.Field →ₗ[ℝ] _) '' G) :=
    fun hZ => Submodule.apply_mem_span_image_of_mem_span _ hZ
  exact intervalIntegrable_integrand_of_mem_span (ch.W k) (ch.γ k) _ _ _
    (by rintro _ ⟨Z, hZ, rfl⟩; exact hG Z hZ k hk)
    (by rintro _ ⟨Z, hZ, rfl⟩ _ ⟨Z', hZ', rfl⟩; exact hGint Z hZ Z' hZ' k hk) (hmem hY)
    (hmem hY')

theorem trace_inv_gram_mul_boundaryForm_le_sum_historyLIndex {ι : Type*} [Fintype ι]
    [DecidableEq ι] (J Y : ι → ch.Field) (hJ : ∀ i, ch.IsHistoryLJacobi (J i))
    (hYr : ∀ l, ch.IsRegularField (Y l)) (hYg : ∀ l, ch.IsGlued (Y l))
    (hint : ∀ X ∈ range J ∪ range Y, ∀ X' ∈ range J ∪ range Y, ∀ k < ch.n, IntervalIntegrable
      (lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (X k) (X' k)) MeasureTheory.volume
      (ch.c k) (ch.c (k + 1)))
    (hnonneg : ∀ X ∈ Submodule.span ℝ (range J ∪ range Y), X 0 0 = 0 → X (ch.n - 1) v = 0 →
      0 ≤ ch.historyLIndex X X)
    (hJa : ∀ i, J i 0 0 = 0) (hYa : ∀ l, Y l 0 0 = 0)
    (hspan : ∀ l, Y l (ch.n - 1) v ∈ Submodule.span ℝ (range fun i => J i (ch.n - 1) v))
    (hON : ∀ l l', ((ch.W (ch.n - 1)).S.base.metric (T - v ^ 2)).inner (ch.γ (ch.n - 1) v)
      (Y l (ch.n - 1) v) (Y l' (ch.n - 1) v) = if l = l' then 1 else 0) :
    Matrix.trace ((Matrix.of fun i i' => ((ch.W (ch.n - 1)).S.base.metric (T - v ^ 2)).inner
        (ch.γ (ch.n - 1) v) (J i (ch.n - 1) v) (J i' (ch.n - 1) v))⁻¹ *
      Matrix.of fun i i' => ch.boundaryForm (J i) (ch.n - 1) v (J i' (ch.n - 1) v)) ≤
      2 * ∑ l, ch.historyLIndex (Y l) (Y l) := by
  let G : Set ch.Field := range J ∪ range Y
  have hGr : ∀ X ∈ G, ch.IsRegularField X := by
    rintro X (⟨i, rfl⟩ | ⟨l, rfl⟩)
    · exact fun k hk s hs => ((hJ i).1 k hk s hs).2.1
    · exact hYr l
  have hGg : ∀ X ∈ G, ch.IsGlued X := by
    rintro X (⟨i, rfl⟩ | ⟨l, rfl⟩)
    · exact (hJ i).2.1
    · exact hYg l
  let A : Submodule ℝ ch.Field := Submodule.span ℝ G
  have hr : ∀ X ∈ A, ch.IsRegularField X := fun X hX => ch.isRegularField_of_mem_span hGr hX
  have hi : ∀ X ∈ A, ∀ X' ∈ A, ∀ k < ch.n, IntervalIntegrable
      (lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (X k) (X' k)) MeasureTheory.volume
      (ch.c k) (ch.c (k + 1)) :=
    fun X hX X' hX' k hk => ch.intervalIntegrable_of_mem_span hGr hint hX hX' hk
  have hJA : ∀ i, J i ∈ A := fun i => Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  have hYA : ∀ l, Y l ∈ A := fun l => Submodule.subset_span (Or.inr ⟨l, rfl⟩)
  exact trace_inv_gram_mul_boundary_le_sum_index ch.historyLIndex A (ch.evalAt 0 0)
    (ch.evalAt (ch.n - 1) v)
    (ContinuousLinearMap.toLinearMap₁₂ (((ch.W (ch.n - 1)).S.base.metric (T - v ^ 2)).inner
      (ch.γ (ch.n - 1) v)))
    (fun i => ch.boundaryForm (J i) 0 0) (fun i => ch.boundaryForm (J i) (ch.n - 1) v) J Y
    (fun x hx y hy z hz => ch.historyLIndex_add (hr x hx) (hr y hy) (hi x hx z hz) (hi y hy z hz))
    (fun r x _ z _ => ch.historyLIndex_smul r x z)
    (fun x _ y _ => ch.historyLIndex_symm x y)
    (fun i x hx => ch.historyLIndex_eq_half_boundary (hJ i) (hr x hx)
      (ch.isGlued_of_mem_span hGg hx) (fun k hk => hi _ (hJA i) x hx k hk))
    (fun x hx hxa hxb => hnonneg x hx hxa hxb) hJA hYA hJa hYa hspan hON

section Competitor

variable {B : ℝ}

theorem c_mono {m m' : ℕ} (h : m ≤ m') (hm' : m' ≤ ch.n) : ch.c m ≤ ch.c m' := by
  induction h with
  | refl => exact le_rfl
  | step h ih => exact (ih (Nat.le_of_succ_le hm')).trans (ch.lt _ hm').le

theorem stage_anti {m m' : ℕ} (h : m ≤ m') (hm' : m' ≤ ch.n) : ch.stage m' ≤ ch.stage m := by
  induction h with
  | refl => exact le_rfl
  | step h ih => exact (ch.stage_succ_le hm').trans (ih (Nat.le_of_succ_le hm'))

theorem mem_Icc_stage_zero :
    T - ch.c 0 ^ 2 ∈ Icc (H.time (ch.stage 0)) (H.stageEndTime (ch.stage 0)) :=
  ⟨H.time_le_of_mem_stageDomain (ch.mem_stageDomain 0 (Nat.zero_le _)),
    H.le_stageEndTime_of_mem_stageDomain (ch.mem_stageDomain 0 (Nat.zero_le _))⟩

def restrictPiece {k : ℕ} (hk : k < ch.n) : H.LWindow (ch.stage (k + 1)) (ch.stage k) T :=
  (ch.W k).restrict (ch.lo_le_stage k hk) (ch.stage_le_hi k hk) (ch.stage_succ_le hk)
    (ch.piece k hk (left_mem_Icc.2 (ch.lt k hk).le)).1 (ch.lt k hk)
    (ch.piece k hk (right_mem_Icc.2 (ch.lt k hk).le)).2 (ch.mem_stageDomain k hk.le)
    (ch.mem_stageDomain (k + 1) hk)

private theorem scalar_of_floor (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
    -B ≤ metricScalarAt (H.stageMetric j t) x) (j : Fin (H.eventCount + 1)) (a b : ℝ) :
    ∀ t ∈ Ioo (H.regularizedStageStart T a j) (H.regularizedStageEnd T b j),
      ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j (T - t ^ 2)) x :=
  fun _ ht x => hfloor j _ (H.mapsTo_regularizedStage_Ioo T a b j ht) x

variable (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
  -B ≤ metricScalarAt (H.stageMetric j t) x)
include hfloor

theorem coe_lRegularizedAction_mem {k : ℕ} (hk : k < ch.n) (δ : ℝ → (ch.W k).X)
    (hδ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ) :
    (lRegularizedAction (ch.W k).S T δ (ch.c k) (ch.c (k + 1)) : WithTop ℝ) ∈
      H.regularizedActionValues (ch.stage (k + 1)) (ch.stage k) (ch.stage_succ_le hk) T B
        (ch.c k) (ch.c (k + 1)) ((ch.W k).f (ch.top hk) (δ (ch.c k)))
        ((ch.W k).f (ch.bottom hk) (δ (ch.c (k + 1)))) :=
  (ch.restrictPiece hk).coe_lRegularizedAction_mem_regularizedActionValues
    (fun j => scalar_of_floor hfloor j.val _ _) δ hδ

theorem sum_mem_regularizedActionValues (δ : (k : ℕ) → ℝ → (ch.W k).X)
    (hδ : ∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (δ k))
    (hmatch : ∀ k (hk : k + 1 < ch.n),
      (ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)) (δ k (ch.c (k + 1))) =
        (ch.W (k + 1)).f (ch.top hk) (δ (k + 1) (ch.c (k + 1)))) :
    ∀ m (hm : m < ch.n), ((∑ k ∈ Finset.range (m + 1),
      lRegularizedAction (ch.W k).S T (δ k) (ch.c k) (ch.c (k + 1)) : ℝ) : WithTop ℝ) ∈
      H.regularizedActionValues (ch.stage (m + 1)) (ch.stage 0)
        (ch.stage_anti (Nat.zero_le _) hm) T B (ch.c 0) (ch.c (m + 1))
        ((ch.W 0).f (ch.top (Nat.zero_lt_of_lt hm)) (δ 0 (ch.c 0)))
        ((ch.W m).f (ch.bottom hm) (δ m (ch.c (m + 1)))) := by
  intro m
  induction m with
  | zero =>
    intro hm
    rw [Finset.sum_range_one]
    exact ch.coe_lRegularizedAction_mem hfloor hm (δ 0) (hδ 0 hm)
  | succ m ih =>
    intro hm
    have h1 := ih (Nat.lt_of_succ_lt hm)
    have h2 := ch.coe_lRegularizedAction_mem hfloor hm (δ (m + 1)) (hδ _ hm)
    rw [← hmatch m hm] at h2
    rw [Finset.sum_range_succ, WithTop.coe_add]
    exact (H.mem_regularizedActionValues_split_at_parameter _ (ch.stage (m + 1))
      (ch.stage_succ_le hm) (ch.stage_anti (Nat.zero_le _) (Nat.le_of_lt hm))
      (ch.c_nonneg (Nat.zero_lt_of_lt hm)) (ch.c_mono (Nat.zero_le _) (Nat.le_of_lt hm))
      (ch.lt (m + 1) hm).le ch.mem_Icc_stage_zero (ch.mem_stageDomain (m + 2) hm)
      (ch.mem_stageDomain (m + 1) hm.le) (scalar_of_floor hfloor _ _ _) _ _).2
      ⟨_, _, _, h1, h2, rfl⟩

end Competitor

section Action

variable {B : ℝ}

theorem first_le_stage {m : ℕ} (hm : m ≤ ch.n) : first ≤ ch.stage m :=
  ch.stage_n.symm.le.trans (ch.stage_anti hm le_rfl)

theorem stage_le_last {m : ℕ} (hm : m ≤ ch.n) : ch.stage m ≤ last :=
  (ch.stage_anti (Nat.zero_le m) hm).trans ch.stage_zero.le

private theorem mem_regularizedStage_Icc {T a b r : ℝ} (ha : 0 ≤ a) (hr : r ∈ Icc a b)
    {j : Fin (H.eventCount + 1)} (ht : T - r ^ 2 ∈ Icc (H.time j) (H.stageEndTime j)) :
    r ∈ Icc (H.regularizedStageStart T a j) (H.regularizedStageEnd T b j) := by
  have hr0 : 0 ≤ r := ha.trans hr.1
  have ha2 : a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha hr.1 2
  have hb2 : r ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hr0 hr.2 2
  constructor
  · apply (Real.sqrt_le_left hr0).2
    have := le_min (show T - r ^ 2 ≤ T - a ^ 2 by linarith) ht.2
    linarith
  · apply (Real.le_sqrt hr0 ?_).2
    · have := max_le (show T - b ^ 2 ≤ T - r ^ 2 by linarith) ht.1
      linarith
    · have := max_le (show T - b ^ 2 ≤ T - r ^ 2 by linarith) ht.1
      nlinarith

theorem mem_piece_stage {k m : ℕ} (hk : k < ch.n) (hm : m = k ∨ m = k + 1) :
    ch.c m ∈ Icc (H.regularizedStageStart T (ch.W k).a (ch.stage m))
      (H.regularizedStageEnd T (ch.W k).b (ch.stage m)) := by
  have hm' : m ≤ ch.n := by omega
  refine mem_regularizedStage_Icc (ch.W k).nonneg (ch.piece k hk ?_)
    ⟨H.time_le_of_mem_stageDomain (ch.mem_stageDomain m hm'),
      H.le_stageEndTime_of_mem_stageDomain (ch.mem_stageDomain m hm')⟩
  rcases hm with rfl | rfl
  · exact left_mem_Icc.2 (ch.lt _ hk).le
  · exact right_mem_Icc.2 (ch.lt _ hk).le

theorem regularizedExtendedAction_piece (hfloor : ∀ j, ∀ t ∈ H.stageDomain j,
    ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x)
    {k : ℕ} (hk : k < ch.n) :
    H.regularizedExtendedAction (ch.stage (k + 1)) (ch.stage k) T B (ch.c k) (ch.c (k + 1))
      (fun j => α ⟨j.val, (ch.first_le_stage hk).trans j.property.1,
        j.property.2.trans (ch.stage_le_last hk.le)⟩) =
      (lRegularizedAction (ch.W k).S T (ch.γ k) (ch.c k) (ch.c (k + 1)) : WithTop ℝ) := by
  have hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (ch.γ k) := (ch.contMDiff k).of_le (by decide)
  have hsub := ch.piece k hk
  have hlt := ch.lt k hk
  refine (ch.restrictPiece hk).regularizedExtendedAction_eq_coe
    (fun j => scalar_of_floor hfloor j.val _ _) _ (ch.γ k)
    (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hγ.contMDiffOn)
    (fun j s hs => ch.eqOn k hk ⟨j.val, (ch.lo_le_stage k hk).trans j.property.1,
      j.property.2.trans (ch.stage_le_hi k hk)⟩
      ⟨(regularizedStageStart_le_of_le (ch.W k).nonneg (hsub (left_mem_Icc.2 hlt.le)).1
        j.val).trans hs.1, hs.2.trans (regularizedStageEnd_le_of_le
          ((ch.c_nonneg hk).trans hlt.le) (hsub (right_mem_Icc.2 hlt.le)).2 j.val)⟩) ?_
  have hc := lRegularizedLagrangian_continuousOn_carrier (ch.W k).S (ch.W k).solution (ch.γ k) hγ
  have hh := hc.comp (s := Icc (ch.c k) (ch.c (k + 1)))
    (continuous_const.prodMk continuous_id).continuousOn
    (fun t ht => (ch.W k).mem_carrier (hsub ht))
  exact hh.intervalIntegrable_of_Icc hlt.le

theorem regularizedExtendedAction_eq_sum_range (hfloor : ∀ j, ∀ t ∈ H.stageDomain j,
    ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    ∀ m (hm : m < ch.n), H.regularizedExtendedAction (ch.stage (m + 1)) (ch.stage 0) T B
      (ch.c 0) (ch.c (m + 1)) (fun j => α ⟨j.val, (ch.first_le_stage hm).trans j.property.1,
        j.property.2.trans (ch.stage_le_last (Nat.zero_le _))⟩) =
      ((∑ k ∈ Finset.range (m + 1),
        lRegularizedAction (ch.W k).S T (ch.γ k) (ch.c k) (ch.c (k + 1)) : ℝ) : WithTop ℝ) := by
  intro m
  induction m with
  | zero =>
    intro hm
    rw [Finset.sum_range_one]
    exact ch.regularizedExtendedAction_piece hfloor hm
  | succ m ih =>
    intro hm
    rw [Finset.sum_range_succ, WithTop.coe_add,
      H.regularizedExtendedAction_eq_add_at_parameter (ch.stage (m + 1)) (ch.stage_succ_le hm)
        (ch.stage_anti (Nat.zero_le _) (Nat.le_of_lt hm)) (ch.c_nonneg (Nat.zero_lt_of_lt hm))
        (ch.c_mono (Nat.zero_le _) (Nat.le_of_lt hm)) (ch.lt (m + 1) hm).le
        (ch.mem_stageDomain (m + 1) hm.le) (scalar_of_floor hfloor _ _ _) _ ?_]
    · exact congrArg₂ (· + ·) (ih (Nat.lt_of_succ_lt hm)) (ch.regularizedExtendedAction_piece
        hfloor hm)
    · intro j
      apply Manifold.absolutelyContinuousOnInterval_mono (hα _)
      have hb := H.regularizedStage_bounds (ch.c_nonneg (Nat.zero_lt_of_lt hm))
        (ch.c_mono (Nat.zero_le _) hm) ch.mem_Icc_stage_zero (ch.mem_stageDomain (m + 2) hm) j
      have hv : ch.c (m + 2) ≤ v := (ch.c_mono hm le_rfl).trans_eq ch.c_n
      rw [uIcc_of_le hb.2.1, uIcc_of_le (hb.2.1.trans' (regularizedStageStart_le_of_le le_rfl
        (ch.c_nonneg (Nat.zero_lt_of_lt hm)) j.val) |>.trans (regularizedStageEnd_le_of_le
          ((ch.c_nonneg (Nat.zero_lt_of_lt hm)).trans (ch.c_mono (Nat.zero_le _) hm)) hv j.val))]
      exact Icc_subset_Icc (regularizedStageStart_le_of_le le_rfl
        (ch.c_nonneg (Nat.zero_lt_of_lt hm)) j.val) (regularizedStageEnd_le_of_le
          ((ch.c_nonneg (Nat.zero_lt_of_lt hm)).trans (ch.c_mono (Nat.zero_le _) hm)) hv j.val)

private theorem regularizedExtendedAction_transport {K₁ K₂ L₁ L₂ : Fin (H.eventCount + 1)}
    (hK : K₁ = K₂) (hL : L₁ = L₂) {u₁ u₂ w₁ w₂ : ℝ} (hu : u₁ = u₂) (hw : w₁ = w₂)
    {β₁ : (j : H.StageInterval K₁ L₁) → ℝ → (H.stage j.val).Carrier}
    {β₂ : (j : H.StageInterval K₂ L₂) → ℝ → (H.stage j.val).Carrier} (hβ : HEq β₁ β₂) :
    H.regularizedExtendedAction K₁ L₁ T B u₁ w₁ β₁ =
      H.regularizedExtendedAction K₂ L₂ T B u₂ w₂ β₂ := by
  subst hK hL hu hw
  obtain rfl := eq_of_heq hβ
  rfl

private theorem mem_regularizedActionValues_transport {K₁ K₂ L₁ L₂ : Fin (H.eventCount + 1)}
    (hK : K₁ = K₂) (hL : L₁ = L₂) {h₁ : K₁ ≤ L₁} {h₂ : K₂ ≤ L₂} {u₁ u₂ w₁ w₂ : ℝ}
    (hu : u₁ = u₂) (hw : w₁ = w₂) {p₁ : (H.stage L₁).Carrier} {p₂ : (H.stage L₂).Carrier}
    {q₁ : (H.stage K₁).Carrier} {q₂ : (H.stage K₂).Carrier} (hp : HEq p₁ p₂) (hq : HEq q₁ q₂)
    {A : WithTop ℝ} (hA : A ∈ H.regularizedActionValues K₁ L₁ h₁ T B u₁ w₁ p₁ q₁) :
    A ∈ H.regularizedActionValues K₂ L₂ h₂ T B u₂ w₂ p₂ q₂ := by
  subst hK hL hu hw
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hq
  exact hA

private theorem heq_restrict {K L : Fin (H.eventCount + 1)} (hK : K = first) (hL : L = last)
    (h₁ : ∀ j : H.StageInterval K L, first ≤ j.val) (h₂ : ∀ j : H.StageInterval K L, j.val ≤ last) :
    HEq (fun j : H.StageInterval K L => α ⟨j.val, h₁ j, h₂ j⟩) α := by
  subst hK hL
  rfl

private theorem heq_apply {j j' : H.StageInterval first last} (h : j.val = j'.val) {s s' : ℝ}
    (hs : s = s') : HEq (α j s) (α j' s') := by
  obtain rfl : j = j' := Subtype.ext h
  subst hs
  rfl

theorem stage_n_sub_one_add_one (hn : 0 < ch.n) : ch.stage (ch.n - 1 + 1) = first := by
  rw [Nat.sub_add_cancel hn]
  exact ch.stage_n

theorem regularizedExtendedAction_eq_sum (hn : 0 < ch.n)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j,
    ∀ x : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    H.regularizedExtendedAction first last T B 0 v α =
      ((∑ k ∈ Finset.range ch.n,
        lRegularizedAction (ch.W k).S T (ch.γ k) (ch.c k) (ch.c (k + 1)) : ℝ) : WithTop ℝ) := by
  have h := ch.regularizedExtendedAction_eq_sum_range hfloor hα (ch.n - 1) (by omega)
  have hs : Finset.range (ch.n - 1 + 1) = Finset.range ch.n := by rw [Nat.sub_add_cancel hn]
  rw [hs] at h
  rw [← h]
  exact regularizedExtendedAction_transport (ch.stage_n_sub_one_add_one hn).symm
    ch.stage_zero.symm ch.c_zero.symm (by rw [Nat.sub_add_cancel hn, ch.c_n])
    (heq_restrict (ch.stage_n_sub_one_add_one hn) ch.stage_zero
      (fun j => (ch.first_le_stage (by omega)).trans j.property.1)
      (fun j => j.property.2.trans (ch.stage_le_last (Nat.zero_le _)))).symm

end Action

section SecondVariation

variable {B : ℝ}

theorem sum_mem_regularizedActionValues_of_endpoints (hn : 0 < ch.n) (hle : first ≤ last)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (δ : (k : ℕ) → ℝ → (ch.W k).X) (hδ : ∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (δ k))
    (hmatch : ∀ k (hk : k + 1 < ch.n),
      (ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)) (δ k (ch.c (k + 1))) =
        (ch.W (k + 1)).f (ch.top hk) (δ (k + 1) (ch.c (k + 1))))
    (h0 : δ 0 (ch.c 0) = ch.γ 0 (ch.c 0))
    (h1 : δ (ch.n - 1) (ch.c ch.n) = ch.γ (ch.n - 1) (ch.c ch.n)) :
    ((∑ k ∈ Finset.range ch.n, lRegularizedAction (ch.W k).S T (δ k) (ch.c k) (ch.c (k + 1)) :
      ℝ) : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B 0 v
        (α ⟨last, hle, le_rfl⟩ 0) (α ⟨first, le_rfl, hle⟩ v) := by
  have h := ch.sum_mem_regularizedActionValues hfloor δ hδ hmatch (ch.n - 1) (by omega)
  have hs : Finset.range (ch.n - 1 + 1) = Finset.range ch.n := by rw [Nat.sub_add_cancel hn]
  rw [hs] at h
  have hc : ch.c (ch.n - 1 + 1) = ch.c ch.n := by rw [Nat.sub_add_cancel hn]
  refine mem_regularizedActionValues_transport (ch.stage_n_sub_one_add_one hn) ch.stage_zero
    ch.c_zero (hc.trans ch.c_n) ?_ ?_ h
  · have e := ch.eqOn 0 hn (ch.top hn) (ch.mem_piece_stage (k := 0) (m := 0) hn (Or.inl rfl))
    rw [h0]
    exact (heq_of_eq e).trans (heq_apply ch.stage_zero ch.c_zero)
  · have h1' : δ (ch.n - 1) (ch.c (ch.n - 1 + 1)) = ch.γ (ch.n - 1) (ch.c (ch.n - 1 + 1)) := by
      rw [hc]
      exact h1
    have e := ch.eqOn (ch.n - 1) (by omega) (ch.bottom (by omega))
      (ch.mem_piece_stage (k := ch.n - 1) (m := ch.n - 1 + 1) (by omega) (Or.inr rfl))
    rw [h1']
    exact (heq_of_eq e).trans (heq_apply (ch.stage_n_sub_one_add_one hn) (hc.trans ch.c_n))

private theorem differentiableAt_lRegularizedAction {X : Type u} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X] {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S) (f : ℝ → ℝ → X)
    (hf : IsSmoothVariation (I := ThreeModel) f) (a b : ℝ)
    (ht : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular) (u : ℝ) :
    DifferentiableAt ℝ (fun w => lRegularizedAction S T (f w) a b) u := by
  have hF : IsSmoothVariation (I := ThreeModel) (fun w s => f (u + w) s) :=
    hf.comp ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
  have h := (lRegularizedAction_first_variation S hS T _ hF a b ht).differentiableAt
  have h₀ : DifferentiableAt ℝ (fun w => lRegularizedAction S T (fun s => f (u + w) s) a b)
      (u - u) := by
    rw [sub_self]
    exact h
  refine (h₀.comp (f := fun x : ℝ => x - u) u
    (differentiableAt_id.sub_const u)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun w => ?_)
  simp only [Function.comp_apply, add_sub_cancel]

private theorem lVelocity_eq_of_eventuallyEq {N : Type*} [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] {γ δ : ℝ → N} {t : ℝ} (h : γ =ᶠ[𝓝 t] δ) :
    (lVelocity (I := ThreeModel) γ t : ThreeSpace) = lVelocity (I := ThreeModel) δ t := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel) h
  with_unfolding_all exact congrArg (fun L => L (1 : ℝ)) hmf

def boundaryAccel (f : (k : ℕ) → ℝ → ℝ → (ch.W k).X) (k : ℕ) (s : ℝ) : ℝ :=
  ((ch.W k).S.base.metric (T - s ^ 2)).inner (f k 0 s)
    (covDerivAlong (I := ThreeModel) ((ch.W k).S.base.metric (T - s ^ 2)) (fun u => f k u s)
      (fun u => lVelocity (I := ThreeModel) (fun w => f k w s) u) 0)
    (lVelocity (I := ThreeModel) (f k 0) s)

theorem boundaryAccel_node (f : (k : ℕ) → ℝ → ℝ → (ch.W k).X)
    (hf : ∀ k < ch.n, IsSmoothVariation (I := ThreeModel) (f k))
    (hf0 : ∀ k < ch.n, ∀ s, f k 0 s = ch.γ k s)
    (hmatch : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ k (hk : k + 1 < ch.n),
      (ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)) (f k u (ch.c (k + 1))) =
        (ch.W (k + 1)).f (ch.top hk) (f (k + 1) u (ch.c (k + 1))))
    {k : ℕ} (hk : k + 1 < ch.n) :
    ch.boundaryAccel f k (ch.c (k + 1)) = ch.boundaryAccel f (k + 1) (ch.c (k + 1)) := by
  have hk' := Nat.lt_of_succ_lt hk
  set c := ch.c (k + 1)
  set F₁ := (ch.W k).f (ch.bottom hk')
  set F₂ := (ch.W (k + 1)).f (ch.top hk)
  have hF₁ := (ch.W k).localDiffeomorph (ch.bottom hk')
  have hF₂ := (ch.W (k + 1)).localDiffeomorph (ch.top hk)
  have hm₁ := (ch.W k).metric (ch.bottom hk') c (ch.node k hk).1
  have hm₂ := (ch.W (k + 1)).metric (ch.top hk) c (ch.node k hk).2
  have hσ₁ := (hf k hk').contMDiff_curve c
  have hσ₂ := (hf (k + 1) hk).contMDiff_curve c
  have hcurve : (fun u => F₁ (f k u c)) =ᶠ[𝓝 0] fun u => F₂ (f (k + 1) u c) := by
    filter_upwards [hmatch] with u hu
    exact hu k hk
  have hvel : ∀ᶠ u in 𝓝 (0 : ℝ),
      (mfderiv ThreeModel ThreeModel F₁ (f k u c)
        (lVelocity (I := ThreeModel) (fun w => f k w c) u) : ThreeSpace) =
      mfderiv ThreeModel ThreeModel F₂ (f (k + 1) u c)
        (lVelocity (I := ThreeModel) (fun w => f (k + 1) w c) u) := by
    filter_upwards [hcurve.eventuallyEq_nhds] with u hu
    rw [← lVelocity_comp_of_isLocalDiffeomorph hF₁ ((hσ₁ u).mdifferentiableAt (by norm_num)),
      ← lVelocity_comp_of_isLocalDiffeomorph hF₂ ((hσ₂ u).mdifferentiableAt (by norm_num))]
    exact lVelocity_eq_of_eventuallyEq hu
  have hacc₁ := mfderiv_covDerivAlong_of_isLocalDiffeomorph
    ((ch.W k).S.base.metric (T - c ^ 2)) (H.stageMetric (ch.bottom hk').val (T - c ^ 2)) hF₁
    (fun x v w => by rw [hm₁, localPullMetric_inner]) (fun u => f k u c)
    (fun u => lVelocity (I := ThreeModel) (fun w => f k w c) u)
    ((hσ₁ 0).mdifferentiableAt (by norm_num))
    (differentiableAt_chartRepAt_lVelocity _ _ ((hσ₁ 0).of_le (by norm_num)))
  have hacc₂ := mfderiv_covDerivAlong_of_isLocalDiffeomorph
    ((ch.W (k + 1)).S.base.metric (T - c ^ 2)) (H.stageMetric (ch.top hk).val (T - c ^ 2))
    hF₂ (fun x v w => by rw [hm₂, localPullMetric_inner]) (fun u => f (k + 1) u c)
    (fun u => lVelocity (I := ThreeModel) (fun w => f (k + 1) w c) u)
    ((hσ₂ 0).mdifferentiableAt (by norm_num))
    (differentiableAt_chartRepAt_lVelocity _ _ ((hσ₂ 0).of_le (by norm_num)))
  have hγeq : (F₁ ∘ f k 0) =ᶠ[𝓝 c] (F₂ ∘ f (k + 1) 0) := by
    filter_upwards [isOpen_Ioo.mem_nhds (ch.node k hk).1,
      isOpen_Ioo.mem_nhds (ch.node k hk).2] with s h₁ h₂
    exact (congrArg F₁ (hf0 k hk' s)).trans ((ch.eqOn k hk' (ch.bottom hk')
      (Ioo_subset_Icc_self h₁)).trans ((ch.eqOn (k + 1) hk (ch.top hk)
        (Ioo_subset_Icc_self h₂)).symm.trans (congrArg F₂ (hf0 (k + 1) hk s).symm)))
  rw [hm₁] at hacc₁
  rw [hm₂] at hacc₂
  have hsm₁ : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel (f k 0) c :=
    ((hf k hk').contMDiff_slice 0 c).mdifferentiableAt (by norm_num)
  have hsm₂ : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel (f (k + 1) 0) c :=
    ((hf (k + 1) hk).contMDiff_slice 0 c).mdifferentiableAt (by norm_num)
  simp only [boundaryAccel]
  rw [hm₁, hm₂, localPullMetric_inner, localPullMetric_inner]
  refine inner_congr_point _ ?_ _ _ _ _ ?_ ?_
  · exact hγeq.eq_of_nhds
  · rw [hacc₁, hacc₂]
    exact DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve _ _ _ hcurve hvel
  · rw [← lVelocity_comp_of_isLocalDiffeomorph hF₁ hsm₁,
      ← lVelocity_comp_of_isLocalDiffeomorph hF₂ hsm₂]
    exact lVelocity_eq_of_eventuallyEq hγeq

end SecondVariation

section SecondVariationNonneg

variable {B : ℝ}

theorem regular_of_mem_piece {k : ℕ} (hk : k < ch.n) :
    ∀ s ∈ uIcc (ch.c k) (ch.c (k + 1)), T - s ^ 2 ∈ (ch.W k).D.regular := by
  intro s hs
  rw [uIcc_of_le (ch.lt k hk).le] at hs
  exact (ch.W k).regular s (ch.piece k hk hs)

theorem isLRegularizedGeodesicOn_piece {k : ℕ} (hk : k < ch.n) :
    IsLRegularizedGeodesicOn (ch.W k).S T (ch.γ k) (uIcc (ch.c k) (ch.c (k + 1))) := by
  obtain ⟨a, b, ha, hb, hgeo⟩ := ch.geodesic k hk
  intro s hs
  rw [uIcc_of_le (ch.lt k hk).le] at hs
  exact hgeo s ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩

theorem boundaryAccel_eq_zero_of_const (f : (k : ℕ) → ℝ → ℝ → (ch.W k).X) {k : ℕ} {s : ℝ}
    (hconst : ∀ u, f k u s = f k 0 s) : ch.boundaryAccel f k s = 0 := by
  have hc : (fun w => f k w s) = fun _ => f k 0 s := funext hconst
  have h1 := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve (I := ThreeModel)
    ((ch.W k).S.base.metric (T - s ^ 2)) (γ := fun u => f k u s) (γ' := fun u => f k u s)
    (fun u => lVelocity (I := ThreeModel) (fun w => f k w s) u)
    (fun u => (0 : TangentSpace ThreeModel (f k u s))) (t := 0) (Filter.EventuallyEq.refl _ _)
    (Filter.Eventually.of_forall fun u => by
      change (mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun w => f k w s) u 1 : ThreeSpace) = 0
      rw [hc, mfderiv_const]
      rfl)
  rw [covDerivAlong_zero] at h1
  unfold boundaryAccel
  rw [show covDerivAlong (I := ThreeModel) ((ch.W k).S.base.metric (T - s ^ 2))
    (fun u => f k u s) (fun u => lVelocity (I := ThreeModel) (fun w => f k w s) u) 0 = 0 from h1,
    map_zero]
  rfl

theorem historyLIndex_nonneg_of_variation (hn : 0 < ch.n) (hle : first ≤ last)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hmin : H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0) (α ⟨first, le_rfl, hle⟩ v))
    (f : (k : ℕ) → ℝ → ℝ → (ch.W k).X)
    (hf : ∀ k < ch.n, IsSmoothVariation (I := ThreeModel) (f k))
    (hf0 : ∀ k < ch.n, ∀ s, f k 0 s = ch.γ k s)
    (hmatch : ∀ᶠ u in 𝓝 (0 : ℝ), ∀ k (hk : k + 1 < ch.n),
      (ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)) (f k u (ch.c (k + 1))) =
        (ch.W (k + 1)).f (ch.top hk) (f (k + 1) u (ch.c (k + 1))))
    (hstart : ∀ u, f 0 u (ch.c 0) = ch.γ 0 (ch.c 0))
    (hend : ∀ u, f (ch.n - 1) u (ch.c ch.n) = ch.γ (ch.n - 1) (ch.c ch.n)) :
    0 ≤ ch.historyLIndex (fun k s => lVelocity (I := ThreeModel) (fun u => f k u s) 0)
      (fun k s => lVelocity (I := ThreeModel) (fun u => f k u s) 0) := by
  set L : ℕ → ℝ → ℝ := fun k u => lRegularizedAction (ch.W k).S T (f k u) (ch.c k) (ch.c (k + 1))
  set A : ℝ → ℝ := fun u => ∑ k ∈ Finset.range ch.n, L k u
  have hdiff : ∀ k ∈ Finset.range ch.n, ∀ u, DifferentiableAt ℝ (L k) u := fun k hk u =>
    differentiableAt_lRegularizedAction (ch.W k).S (ch.W k).solution (f k) (hf k
      (Finset.mem_range.1 hk)) _ _ (ch.regular_of_mem_piece (Finset.mem_range.1 hk)) u
  have hderivA : deriv A = fun u => ∑ k ∈ Finset.range ch.n, deriv (L k) u := by
    funext u
    exact deriv_fun_sum fun k hk => hdiff k hk u
  have hgeo : ∀ k < ch.n, IsLRegularizedGeodesicOn (ch.W k).S T (f k 0)
      (uIcc (ch.c k) (ch.c (k + 1))) := by
    intro k hk
    rw [show f k 0 = ch.γ k from funext (hf0 k hk)]
    exact ch.isLRegularizedGeodesicOn_piece hk
  have hsec := HasDerivAt.fun_sum (u := Finset.range ch.n) fun k hk =>
    lRegularizedAction_second_variation_moving_endpoints (ch.W k).S (ch.W k).solution T (f k)
      (hf k (Finset.mem_range.1 hk)) (ch.c k) (ch.c (k + 1)) (hgeo k (Finset.mem_range.1 hk))
  rw [← hderivA] at hsec
  have hsum : ∑ k ∈ Finset.range ch.n, (ch.boundaryAccel f k (ch.c (k + 1)) -
      ch.boundaryAccel f k (ch.c k)) = 0 := by
    have htel : ∀ k ∈ Finset.range ch.n, ch.boundaryAccel f k (ch.c (k + 1)) -
        ch.boundaryAccel f k (ch.c k) = (fun m => ch.boundaryAccel f (m - 1) (ch.c m)) (k + 1) -
          (fun m => ch.boundaryAccel f (m - 1) (ch.c m)) k := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rfl
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        have := ch.boundaryAccel_node f hf hf0 hmatch (k := m) (Finset.mem_range.1 hk)
        change _ - _ = ch.boundaryAccel f (m + 1) (ch.c (m + 1 + 1)) -
          ch.boundaryAccel f m (ch.c (m + 1))
        rw [this]
    rw [Finset.sum_congr rfl htel,
      Finset.sum_range_sub (fun m => ch.boundaryAccel f (m - 1) (ch.c m))]
    change ch.boundaryAccel f (ch.n - 1) (ch.c ch.n) - ch.boundaryAccel f 0 (ch.c 0) = 0
    rw [ch.boundaryAccel_eq_zero_of_const f (fun u => (hstart u).trans (hstart 0).symm),
      ch.boundaryAccel_eq_zero_of_const f (fun u => (hend u).trans (hend 0).symm), sub_zero]
  have hderiv2 : deriv (deriv A) 0 = 2 * ch.historyLIndex
      (fun k s => lVelocity (I := ThreeModel) (fun u => f k u s) 0)
      (fun k s => lVelocity (I := ThreeModel) (fun u => f k u s) 0) := by
    have hterm : ∀ k ∈ Finset.range ch.n,
        2 * lRegularizedIndex (ch.W k).S T (f k 0)
          (fun s => lVelocity (I := ThreeModel) (fun u => f k u s) 0)
          (fun s => lVelocity (I := ThreeModel) (fun u => f k u s) 0) (ch.c k) (ch.c (k + 1)) +
          ch.boundaryAccel f k (ch.c (k + 1)) - ch.boundaryAccel f k (ch.c k) =
        2 * lRegularizedIndex (ch.W k).S T (ch.γ k)
          (fun s => lVelocity (I := ThreeModel) (fun u => f k u s) 0)
          (fun s => lVelocity (I := ThreeModel) (fun u => f k u s) 0) (ch.c k) (ch.c (k + 1)) +
          (ch.boundaryAccel f k (ch.c (k + 1)) - ch.boundaryAccel f k (ch.c k)) := by
      intro k hk
      rw [show f k 0 = ch.γ k from funext (hf0 k (Finset.mem_range.1 hk))]
      ring
    rw [hsec.deriv]
    refine (Finset.sum_congr rfl hterm).trans ?_
    rw [Finset.sum_add_distrib, hsum, add_zero, ← Finset.mul_sum]
    rfl
  have hloc : IsLocalMin A 0 := by
    filter_upwards [hmatch] with u hu
    have hmem := ch.sum_mem_regularizedActionValues_of_endpoints hn hle hfloor
      (fun k => f k u) (fun k hk => ((hf k hk).contMDiff_slice u).of_le (by norm_num))
      hu (hstart u) (hend u)
    have hc := H.regularizedCost_le_of_competitor first last hle T B 0 v _ _ hmem
    rw [← hmin, ch.regularizedExtendedAction_eq_sum hn hfloor hα] at hc
    have h0 : ∀ k ∈ Finset.range ch.n, L k 0 =
        lRegularizedAction (ch.W k).S T (ch.γ k) (ch.c k) (ch.c (k + 1)) := fun k hk => by
      simp only [L, show f k 0 = ch.γ k from funext (hf0 k (Finset.mem_range.1 hk))]
    change A 0 ≤ A u
    rw [show A 0 = _ from Finset.sum_congr rfl h0]
    exact WithTop.coe_le_coe.1 hc
  have hcont : ContinuousAt A 0 :=
    (DifferentiableAt.fun_sum fun k hk => hdiff k hk 0).continuousAt
  have hnn := DifferentialGeometry.Analysis.second_deriv_nonneg_of_isLocalMin hloc hcont
  rw [hderiv2] at hnn
  linarith

end SecondVariationNonneg

section Realization

open DifferentialGeometry.Geometry.Riemannian.Variation
  (exists_var_pair exists_isSmoothVariation_eq_curve)

private theorem contMDiffAt_invFun_f {lo hi : Fin (H.eventCount + 1)} (Wd : H.LWindow lo hi T)
    (j : H.StageInterval lo hi) [Nonempty Wd.X] (x : Wd.X) :
    ContMDiffAt ThreeModel ThreeModel 8 (Function.invFun (Wd.f j)) (Wd.f j x) := by
  have hx := Wd.localDiffeomorph j x
  have hev : Function.invFun (Wd.f j) =ᶠ[𝓝 (Wd.f j x)] hx.localInverse := by
    filter_upwards [hx.localInverse_open_source.mem_nhds hx.localInverse_mem_source] with y hy
    apply Wd.injective j
    rw [Function.invFun_eq ⟨_, hx.localInverse_right_inv hy⟩, hx.localInverse_right_inv hy]
  exact (hx.contMDiffAt_localInverse.of_le (by decide)).congr_of_eventuallyEq hev

private theorem mfderiv_congr_point {X N : Type u} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [TopologicalSpace N] [ChartedSpace ThreeSpace N] {F : X → N}
    {x y : X} (h : x = y) (a : TangentSpace ThreeModel x) (b : TangentSpace ThreeModel y)
    (hab : (a : ThreeSpace) = b) :
    (mfderiv ThreeModel ThreeModel F x a : ThreeSpace) = mfderiv ThreeModel ThreeModel F y b := by
  subst h
  rw [show a = b from hab]

private theorem mfderiv_injective_congr {X N : Type u} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [TopologicalSpace N] [ChartedSpace ThreeSpace N] {F : X → N}
    (hF : IsLocalDiffeomorph ThreeModel ThreeModel ∞ F) {x y : X} (h : x = y)
    (a : TangentSpace ThreeModel x) (b : TangentSpace ThreeModel y)
    (hab : (mfderiv ThreeModel ThreeModel F x a : ThreeSpace) =
      mfderiv ThreeModel ThreeModel F y b) :
    (a : ThreeSpace) = b := by
  subst h
  rw [← hF.mfderivToContinuousLinearEquiv_coe infty_ne_zero] at hab
  exact (hF.mfderivToContinuousLinearEquiv infty_ne_zero x).injective hab

theorem exists_isSmoothVariation_zero (V : ch.Field) (hV : ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent 8
    (fun t => (Bundle.TotalSpace.mk' ThreeSpace
      (E := (TangentSpace ThreeModel : (ch.W 0).X → Type _)) (ch.γ 0 t) (V 0 t) :
        TangentBundle ThreeModel (ch.W 0).X))) :
    ∃ f : ℝ → ℝ → (ch.W 0).X, IsSmoothVariation (I := ThreeModel) f ∧
      (∀ s, f 0 s = ch.γ 0 s) ∧
      (∀ s ∈ uIcc (ch.c 0) (ch.c 1),
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun u => f u s) 0 1 : ThreeSpace) = V 0 s) ∧
      (∀ s, V 0 s = 0 → ∀ u, f u s = ch.γ 0 s) := by
  obtain ⟨f, -, hf, -, hf0, -, hfV, -, -, hz, -⟩ := exists_var_pair (I := ThreeModel)
    ((ch.W 0).S.base.metric T) (ch.γ 0) (fun t => (V 0 t : ThreeSpace))
    (fun t => (V 0 t : ThreeSpace)) (ch.c 0) (ch.c 1) hV hV
  exact ⟨f, hf, hf0, hfV, hz⟩

theorem exists_isSmoothVariation_succ (V : ch.Field) {k : ℕ} (hk : k + 1 < ch.n)
    (hVg : ch.IsGlued V)
    (hV : ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent 8 (fun t => (Bundle.TotalSpace.mk' ThreeSpace
      (E := (TangentSpace ThreeModel : (ch.W (k + 1)).X → Type _)) (ch.γ (k + 1) t)
        (V (k + 1) t) : TangentBundle ThreeModel (ch.W (k + 1)).X)))
    (g : ℝ → ℝ → (ch.W k).X) (hg : IsSmoothVariation (I := ThreeModel) g)
    (hg0 : ∀ s, g 0 s = ch.γ k s)
    (hgV : (mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun u => g u (ch.c (k + 1))) 0 1 : ThreeSpace) =
      V k (ch.c (k + 1))) :
    ∃ f : ℝ → ℝ → (ch.W (k + 1)).X, IsSmoothVariation (I := ThreeModel) f ∧
      (∀ s, f 0 s = ch.γ (k + 1) s) ∧
      (∀ s ∈ uIcc (ch.c (k + 1)) (ch.c (k + 2)),
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun u => f u s) 0 1 : ThreeSpace) = V (k + 1) s) ∧
      (∀ᶠ u in 𝓝 (0 : ℝ), (ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)) (g u (ch.c (k + 1))) =
        (ch.W (k + 1)).f (ch.top hk) (f u (ch.c (k + 1)))) ∧
      (V (k + 1) (ch.c (k + 2)) = 0 → ∀ u, f u (ch.c (k + 2)) = ch.γ (k + 1) (ch.c (k + 2))) := by
  obtain ⟨f₀, -, hf₀, -, hf₀0, -, hf₀V, -, -, hz, -⟩ := exists_var_pair (I := ThreeModel)
    ((ch.W (k + 1)).S.base.metric T) (ch.γ (k + 1)) (fun t => (V (k + 1) t : ThreeSpace))
    (fun t => (V (k + 1) t : ThreeSpace)) (ch.c (k + 1)) (ch.c (k + 2)) hV hV
  have hk' := Nat.lt_of_succ_lt hk
  set c := ch.c (k + 1)
  set F₁ := (ch.W k).f (ch.bottom hk')
  set F₂ := (ch.W (k + 1)).f (ch.top hk)
  have hF₁ := (ch.W k).localDiffeomorph (ch.bottom hk')
  have hF₂ := (ch.W (k + 1)).localDiffeomorph (ch.top hk)
  have : Nonempty (ch.W (k + 1)).X := ⟨ch.γ (k + 1) 0⟩
  have hgc : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 8 (fun u => g u c) := hg.contMDiff_curve c
  have hnode : F₁ (g 0 c) = F₂ (ch.γ (k + 1) c) := by rw [hg0]; exact ch.bottom_eq_top hk
  have hrange : ∀ᶠ u in 𝓝 (0 : ℝ), F₁ (g u c) ∈ range F₂ :=
    (((hF₁.contMDiff.of_le (by decide)).comp hgc).continuous.continuousAt
      (x := (0 : ℝ))).preimage_mem_nhds
      (hF₂.isOpen_range.mem_nhds ⟨_, hnode.symm⟩)
  let σ : ℝ → (ch.W (k + 1)).X := fun u => Function.invFun F₂ (F₁ (g u c))
  have hσF : ∀ᶠ u in 𝓝 (0 : ℝ), F₂ (σ u) = F₁ (g u c) := by
    filter_upwards [hrange] with u hu
    exact Function.invFun_eq hu
  have hσ : ∀ᶠ u in 𝓝 (0 : ℝ), ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel 8 σ u := by
    filter_upwards [hrange] with u hu
    obtain ⟨x, hx⟩ := hu
    have h := contMDiffAt_invFun_f (ch.W (k + 1)) (ch.top hk) x
    rw [show (ch.W (k + 1)).f (ch.top hk) x = F₁ (g u c) from hx] at h
    exact h.comp u ((hF₁.contMDiff.of_le (by decide)).comp hgc).contMDiffAt
  have hσ0 : σ 0 = f₀ 0 c := by
    simp only [σ, hnode, hf₀0]
    exact Function.leftInverse_invFun ((ch.W (k + 1)).injective _) _
  have hVc : (V (k + 1) c : ThreeSpace) =
      mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun u => f₀ u c) 0 1 :=
    (hf₀V c left_mem_uIcc).symm
  have hσ' : (mfderiv 𝓘(ℝ, ℝ) ThreeModel σ 0 1 : ThreeSpace) =
      mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun u => f₀ u c) 0 1 := by
    rw [← hVc]
    refine mfderiv_injective_congr hF₂ (hσ0.trans (hf₀0 c)) _ _ ?_
    have h1 := lVelocity_comp_of_isLocalDiffeomorph hF₂ (hσ.self_of_nhds.mdifferentiableAt
      (by norm_num))
    have h2 := lVelocity_comp_of_isLocalDiffeomorph hF₁ ((hgc 0).mdifferentiableAt
      (by norm_num))
    have h3 : (lVelocity (I := ThreeModel) (F₂ ∘ σ) 0 : ThreeSpace) =
        lVelocity (I := ThreeModel) (F₁ ∘ fun u => g u c) 0 :=
      lVelocity_eq_of_eventuallyEq hσF
    rw [h1, h2] at h3
    refine h3.trans ?_
    exact (mfderiv_congr_point (hg0 c) _ _ hgV).trans (hVg k hk)
  obtain ⟨f, hf, hf0, hfV, hfc, hfout⟩ := exists_isSmoothVariation_eq_curve f₀ hf₀ c
    (ch.c (k + 2) - c) (by linarith [ch.lt (k + 1) hk]) σ hσ hσ0 hσ'
  refine ⟨f, hf, fun s => (hf0 s).trans (hf₀0 s), fun s hs => (hfV s).trans (hf₀V s hs), ?_,
    fun h u => ?_⟩
  · filter_upwards [hfc, hσF] with u h₁ h₂
    rw [h₁, h₂]
  · rw [hfout u _ (by rw [abs_of_nonneg (by linarith [ch.lt (k + 1) hk])])]
    exact hz _ h u

end Realization

section Nonnegativity

theorem exists_isSmoothVariation_glued (V : ch.Field)
    (hV : ∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent 8 (fun t => (Bundle.TotalSpace.mk'
      ThreeSpace (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t) (V k t) :
        TangentBundle ThreeModel (ch.W k).X)))
    (hVg : ch.IsGlued V) :
    ∀ m < ch.n, ∃ f : (k : ℕ) → ℝ → ℝ → (ch.W k).X,
      (∀ k ≤ m, IsSmoothVariation (I := ThreeModel) (f k)) ∧ (∀ k ≤ m, ∀ s, f k 0 s = ch.γ k s) ∧
      (∀ k ≤ m, ∀ s ∈ uIcc (ch.c k) (ch.c (k + 1)),
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun u => f k u s) 0 1 : ThreeSpace) = V k s) ∧
      (∀ᶠ u in 𝓝 (0 : ℝ), ∀ k (hk : k + 1 < ch.n), k + 1 ≤ m →
        (ch.W k).f (ch.bottom (Nat.lt_of_succ_lt hk)) (f k u (ch.c (k + 1))) =
          (ch.W (k + 1)).f (ch.top hk) (f (k + 1) u (ch.c (k + 1)))) ∧
      (∀ s, V 0 s = 0 → ∀ u, f 0 u s = ch.γ 0 s) ∧
      (∀ k ≤ m, V k (ch.c (k + 1)) = 0 → ∀ u, f k u (ch.c (k + 1)) = ch.γ k (ch.c (k + 1))) := by
  intro m
  induction m with
  | zero =>
    intro hm
    obtain ⟨f₀, hf, hf0, hfV, hz⟩ := ch.exists_isSmoothVariation_zero V (hV 0 hm)
    refine ⟨Function.update (fun k u s => ch.γ k s) 0 f₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      obtain rfl := Nat.le_zero.1 hk
      rw [Function.update_self]
      exact hf
    · intro k hk
      obtain rfl := Nat.le_zero.1 hk
      rw [Function.update_self]
      exact hf0
    · intro k hk
      obtain rfl := Nat.le_zero.1 hk
      rw [Function.update_self]
      exact hfV
    · exact Filter.Eventually.of_forall fun u k hk h => absurd h (by omega)
    · rw [Function.update_self]
      exact hz
    · intro k hk
      obtain rfl := Nat.le_zero.1 hk
      rw [Function.update_self]
      exact hz _
  | succ m ih =>
    intro hm
    obtain ⟨f, hf, hf0, hfV, hmatch, hz0, hz⟩ := ih (Nat.lt_of_succ_lt hm)
    obtain ⟨g, hg, hg0, hgV, hgm, hgz⟩ := ch.exists_isSmoothVariation_succ V hm hVg (hV _ hm) (f m)
      (hf m le_rfl) (hf0 m le_rfl) (hfV m le_rfl _ right_mem_uIcc)
    have hne : ∀ k ≤ m, k ≠ m + 1 := fun k hk => by omega
    refine ⟨Function.update f (m + 1) g, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hk | rfl
      · rw [Function.update_of_ne (hne k (Nat.lt_succ_iff.1 hk))]
        exact hf k (Nat.lt_succ_iff.1 hk)
      · rw [Function.update_self]
        exact hg
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hk | rfl
      · rw [Function.update_of_ne (hne k (Nat.lt_succ_iff.1 hk))]
        exact hf0 k (Nat.lt_succ_iff.1 hk)
      · rw [Function.update_self]
        exact hg0
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hk | rfl
      · rw [Function.update_of_ne (hne k (Nat.lt_succ_iff.1 hk))]
        exact hfV k (Nat.lt_succ_iff.1 hk)
      · rw [Function.update_self]
        exact hgV
    · filter_upwards [hmatch, hgm] with u hu hgu
      intro k hk hkm
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hkm) with hkm | hkm
      · rw [Function.update_of_ne (hne k (by omega)),
          Function.update_of_ne (hne (k + 1) (Nat.lt_succ_iff.1 hkm))]
        exact hu k hk (Nat.lt_succ_iff.1 hkm)
      · obtain rfl : k = m := by omega
        rw [Function.update_of_ne (hne k le_rfl), Function.update_self]
        exact hgu
    · rw [Function.update_of_ne (by omega)]
      exact hz0
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hk) with hk | rfl
      · rw [Function.update_of_ne (hne k (Nat.lt_succ_iff.1 hk))]
        exact hz k (Nat.lt_succ_iff.1 hk)
      · rw [Function.update_self]
        exact hgz

variable {B : ℝ}

theorem historyLIndex_nonneg (hn : 0 < ch.n) (hle : first ≤ last)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hmin : H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0) (α ⟨first, le_rfl, hle⟩ v))
    (V : ch.Field)
    (hV : ∀ k < ch.n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent 8 (fun t => (Bundle.TotalSpace.mk'
      ThreeSpace (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t) (V k t) :
        TangentBundle ThreeModel (ch.W k).X)))
    (hVg : ch.IsGlued V) (hV0 : V 0 0 = 0) (hVv : V (ch.n - 1) v = 0) :
    0 ≤ ch.historyLIndex V V := by
  obtain ⟨f, hf, hf0, hfV, hmatch, hz0, hz⟩ :=
    ch.exists_isSmoothVariation_glued V hV hVg (ch.n - 1) (by omega)
  have hend : ∀ u, f (ch.n - 1) u (ch.c ch.n) = ch.γ (ch.n - 1) (ch.c ch.n) := by
    have h := hz (ch.n - 1) le_rfl
    rw [Nat.sub_add_cancel hn, ch.c_n] at h
    rw [ch.c_n]
    exact h hVv
  have key := ch.historyLIndex_nonneg_of_variation hn hle hfloor hα hmin f
    (fun k hk => hf k (by omega)) (fun k hk => hf0 k (by omega))
    (by
      filter_upwards [hmatch] with u hu
      exact fun k hk => hu k hk (by omega))
    (hz0 _ (by rw [ch.c_zero]; exact hV0)) hend
  refine key.trans_eq (Finset.sum_congr rfl fun k hk => ?_)
  have hk' := Finset.mem_range.1 hk
  refine lRegularizedIndex_congr_of_eqOn _ _ _ _ _ _ _ _ _ ?_ ?_ <;>
    exact fun s hs => hfV k (by omega) s (uIoo_subset_uIcc_self hs)

end Nonnegativity

section NonConjugacy

private theorem exists_neg_scale {a b : ℝ} (ha : 0 < a) : ∃ ε : ℝ, 2 * ε * a + ε ^ 2 * b < 0 := by
  have hden : 0 < |b| + 1 := by positivity
  refine ⟨-a / (|b| + 1), ?_⟩
  have hneg : -a / (|b| + 1) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos ha) hden
  have hsb : |(-a / (|b| + 1)) * b| < a := by
    rw [abs_mul, abs_div, abs_neg, abs_of_pos ha, abs_of_pos hden, div_mul_eq_mul_div,
      div_lt_iff₀ hden]
    nlinarith [abs_nonneg b]
  have hsum : 0 < 2 * a + (-a / (|b| + 1)) * b := by linarith [(abs_lt.mp hsb).1]
  calc 2 * (-a / (|b| + 1)) * a + (-a / (|b| + 1)) ^ 2 * b =
        (-a / (|b| + 1)) * (2 * a + (-a / (|b| + 1)) * b) := by ring
    _ < 0 := mul_neg_of_neg_of_pos hneg hsum

theorem exists_testField {k : ℕ} (hk : k + 1 < ch.n)
    (P : TangentSpace ThreeModel (ch.γ k (ch.c (k + 1)))) :
    ∃ Y : ch.Field, (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun s => (Bundle.TotalSpace.mk'
      ThreeSpace (E := (TangentSpace ThreeModel : (ch.W j).X → Type _)) (ch.γ j s) (Y j s) :
        TangentBundle ThreeModel (ch.W j).X))) ∧ ch.IsGlued Y ∧ Y 0 (ch.c 0) = 0 ∧
      Y (ch.n - 1) (ch.c ch.n) = 0 ∧ Y k (ch.c (k + 1)) = P ∧
      (∀ j, j ≠ k → j ≠ k + 1 → Y j = fun _ => 0) := by
  have hk' := Nat.lt_of_succ_lt hk
  have hl₁ := ch.lt k hk'
  have hl₂ := ch.lt (k + 1) hk
  obtain ⟨A, hA, hA0, -, hAc⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_contMDiff_vectorFieldAlong_zero_endpoints
    (I := ThreeModel) (ch.γ k) (ch.contMDiff k) (ch.c k) (ch.c (k + 1)) (ch.c (k + 1) + 1)
    (((ch.c (k + 1) - ch.c k) * (ch.c (k + 1) + 1 - ch.c (k + 1)))⁻¹ • P)
  have hF₂ := (ch.W (k + 1)).localDiffeomorph (ch.top hk)
  let Q : TangentSpace ThreeModel (ch.γ (k + 1) (ch.c (k + 1))) :=
    (hF₂.mfderivToContinuousLinearEquiv infty_ne_zero (ch.γ (k + 1) (ch.c (k + 1)))).symm
      (mfderiv ThreeModel ThreeModel ((ch.W k).f (ch.bottom hk')) (ch.γ k (ch.c (k + 1))) P)
  obtain ⟨C, hC, -, hCb, hCc⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_contMDiff_vectorFieldAlong_zero_endpoints
    (I := ThreeModel) (ch.γ (k + 1)) (ch.contMDiff (k + 1)) (ch.c (k + 1) - 1) (ch.c (k + 1))
    (ch.c (k + 2)) (((ch.c (k + 1) - (ch.c (k + 1) - 1)) * (ch.c (k + 2) - ch.c (k + 1)))⁻¹ • Q)
  have hAP : A (ch.c (k + 1)) = P := by
    rw [hAc, smul_smul, mul_inv_cancel₀ (by nlinarith), one_smul]
  have hCQ : C (ch.c (k + 1)) = Q := by
    rw [hCc, smul_smul, mul_inv_cancel₀ (by nlinarith), one_smul]
  let Z : ch.Field := fun j s => (0 : TangentSpace ThreeModel (ch.γ j s))
  let Ak : (s : ℝ) → TangentSpace ThreeModel (ch.γ k s) := fun s => A s
  let Ck : (s : ℝ) → TangentSpace ThreeModel (ch.γ (k + 1) s) := fun s => C s
  let Y : ch.Field := Function.update (Function.update Z k Ak) (k + 1) Ck
  have hYk : Y k = Ak := by
    simp only [Y]
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hYk1 : Y (k + 1) = Ck := by
    simp only [Y]
    rw [Function.update_self]
  have hYz : ∀ j, j ≠ k → j ≠ k + 1 → Y j = fun _ => 0 := by
    intro j h₁ h₂
    simp only [Y]
    rw [Function.update_of_ne h₂, Function.update_of_ne h₁]
  have hZs : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun s => (Bundle.TotalSpace.mk'
      ThreeSpace (E := (TangentSpace ThreeModel : (ch.W j).X → Type _)) (ch.γ j s)
        (0 : TangentSpace ThreeModel (ch.γ j s)) : TangentBundle ThreeModel (ch.W j).X)) :=
    fun j => (Bundle.contMDiff_zeroSection _ _).comp (ch.contMDiff j)
  refine ⟨Y, ?_, ?_, ?_, ?_, ?_, hYz⟩
  · intro j
    by_cases h₁ : j = k
    · subst h₁
      rw [hYk]
      exact hA
    by_cases h₂ : j = k + 1
    · subst h₂
      rw [hYk1]
      exact hC
    rw [hYz j h₁ h₂]
    exact hZs j
  · intro j hj
    unfold GluedAt
    by_cases h₁ : j = k
    · subst h₁
      rw [hYk, hYk1]
      change (mfderiv ThreeModel ThreeModel ((ch.W j).f (ch.bottom hk')) (ch.γ j (ch.c (j + 1)))
        (Ak (ch.c (j + 1))) : ThreeSpace) = mfderiv ThreeModel ThreeModel
          ((ch.W (j + 1)).f (ch.top hk)) (ch.γ (j + 1) (ch.c (j + 1))) (Ck (ch.c (j + 1)))
      rw [show Ak (ch.c (j + 1)) = P from hAP, show Ck (ch.c (j + 1)) = Q from hCQ]
      exact (ContinuousLinearEquiv.apply_symm_apply
        (hF₂.mfderivToContinuousLinearEquiv infty_ne_zero _) _).symm
    by_cases h₂ : j + 1 = k
    · subst h₂
      rw [hYz j (by omega) (by omega), hYk]
      beta_reduce
      rw [show Ak (ch.c (j + 1)) = 0 from hA0, map_zero, map_zero]
      rfl
    by_cases h₃ : j = k + 1
    · subst h₃
      rw [hYk1, hYz (k + 1 + 1) (by omega) (by omega)]
      beta_reduce
      rw [show Ck (ch.c (k + 1 + 1)) = 0 from hCb, map_zero, map_zero]
      rfl
    rw [hYz j h₁ h₃, hYz (j + 1) (by omega) (by omega)]
    beta_reduce
    rw [map_zero, map_zero]
    rfl
  · by_cases h₀ : k = 0
    · subst h₀
      rw [hYk]
      exact hA0
    · rw [hYz 0 (Ne.symm h₀) (by omega)]
  · by_cases h₁ : ch.n - 1 = k + 1
    · rw [h₁, hYk1, show ch.c ch.n = ch.c (k + 2) by congr 1; omega]
      exact hCb
    · rw [hYz (ch.n - 1) (by omega) h₁]
  · rw [hYk]
    exact hAP

end NonConjugacy

section NonConjugacyMain

variable {B : ℝ}

private theorem lRegularizedIndex_zero_left {k : ℕ} (Y : ∀ s, TangentSpace ThreeModel (ch.γ k s))
    (a b : ℝ) :
    lRegularizedIndex (ch.W k).S T (ch.γ k) (fun _ => 0) Y a b = 0 := by
  rw [show (fun _ => (0 : TangentSpace ThreeModel _)) =
      fun s => (0 : ℝ) • Y s from funext fun s => (zero_smul ℝ _).symm,
    lRegularizedIndex_smul, zero_mul]

theorem covDerivAlong_eq_zero_of_eventually_eq_zero {k : ℕ}
    (Y : ∀ s, TangentSpace ThreeModel (ch.γ k s)) {s : ℝ} (hY : ∀ᶠ r in 𝓝 s, Y r = 0) :
    covDerivAlong (I := ThreeModel) ((ch.W k).S.base.metric (T - s ^ 2)) (ch.γ k) Y s = 0 := by
  have h := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve (I := ThreeModel)
    ((ch.W k).S.base.metric (T - s ^ 2)) Y (fun r => (0 : TangentSpace ThreeModel (ch.γ k r)))
    (Filter.EventuallyEq.refl _ _) (hY.mono fun r hr => by rw [hr])
  rw [covDerivAlong_zero] at h
  exact h

theorem exists_eqOn_zero_of_isLRegularizedJacobi {k : ℕ} (hk : k < ch.n)
    (Y : ∀ s, TangentSpace ThreeModel (ch.γ k s)) {a b : ℝ} (ha : a < ch.c k)
    (hb : ch.c (k + 1) < b) (hY : IsLRegularizedJacobi (ch.W k).S T (ch.γ k) Y (Ioo a b))
    (h0 : Y (ch.c (k + 1)) = 0)
    (hD : covDerivAlong (I := ThreeModel) ((ch.W k).S.base.metric (T - ch.c (k + 1) ^ 2))
      (ch.γ k) Y (ch.c (k + 1)) = 0) :
    ∃ a' b', a' < ch.c k ∧ ch.c (k + 1) < b' ∧ ∀ s ∈ Ioo a' b', Y s = 0 := by
  obtain ⟨a₁, b₁, ha₁, hb₁, hgeo⟩ := ch.geodesic k hk
  refine ⟨max a a₁, min b b₁, max_lt ha ha₁, lt_min hb hb₁, ?_⟩
  have hO : Ioo (max a a₁) (min b b₁) ⊆ Ioo a b :=
    Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hO₁ : Ioo (max a a₁) (min b b₁) ⊆ Ioo a₁ b₁ :=
    Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have hs0 : ch.c (k + 1) ∈ Ioo (max a a₁) (min b b₁) :=
    ⟨(max_lt ha ha₁).trans (ch.lt k hk), lt_min hb hb₁⟩
  have hYO : IsLRegularizedJacobi (ch.W k).S T (ch.γ k) Y (Ioo (max a a₁) (min b b₁)) :=
    fun s hs => hY s (hO hs)
  have hsub := hYO.sub isOpen_Ioo hYO
  have hz : (fun r => Y r - Y r) = fun r => (0 : TangentSpace ThreeModel (ch.γ k r)) :=
    funext fun r => sub_self _
  have heq := lRegularizedJacobi_unique (ch.W k).S (ch.W k).solution T isOpen_Ioo
    isPreconnected_Ioo hs0 (fun s hs => (hgeo s (hO₁ hs)).1) (fun s hs => (hgeo s (hO₁ hs)).2.2.1)
    hYO hsub (by rw [h0, sub_self]) (by rw [hD, hz, covDerivAlong_zero])
  intro s hs
  rw [heq hs]
  exact sub_self _

theorem covDerivField_eq_zero_of_conjugate (hle : first ≤ last)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hmin : H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0) (α ⟨first, le_rfl, hle⟩ v))
    {k₀ : ℕ} (hk₀ : k₀ + 1 < ch.n) (J : ch.Field)
    (hJs : ∀ k ≤ k₀, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun t => (Bundle.TotalSpace.mk'
      ThreeSpace (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t) (J k t) :
        TangentBundle ThreeModel (ch.W k).X)))
    (hJj : ∀ k ≤ k₀, IsLRegularizedJacobi (ch.W k).S T (ch.γ k) (J k)
      (uIcc (ch.c k) (ch.c (k + 1))))
    (hJg : ∀ k (hk : k + 1 < ch.n), k + 1 ≤ k₀ →
      ch.GluedAt J hk ∧ ch.GluedAt (ch.covDerivField J) hk)
    (hJ0 : J 0 0 = 0) (hJ1 : J k₀ (ch.c (k₀ + 1)) = 0) :
    ch.covDerivField J k₀ (ch.c (k₀ + 1)) = 0 := by
  have hn : 0 < ch.n := by omega
  by_contra hP
  set P := ch.covDerivField J k₀ (ch.c (k₀ + 1)) with hPdef
  obtain ⟨Wt, hWs, hWg, hW0, hWn, hWP, hWz⟩ := ch.exists_testField hk₀ P
  let X : ch.Field := fun k s => if k ≤ k₀ then J k s else 0
  have hXk : ∀ k ≤ k₀, X k = J k := fun k hk => funext fun s => ite_eq_left hk
  have hXz : ∀ k, k₀ < k → X k = fun _ => 0 := fun k hk => funext fun s => ite_eq_right (by omega)
  have hZ : ∀ k, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun t => (Bundle.TotalSpace.mk'
      ThreeSpace (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t)
        (0 : TangentSpace ThreeModel (ch.γ k t)) : TangentBundle ThreeModel (ch.W k).X)) :=
    fun k => (Bundle.contMDiff_zeroSection _ _).comp (ch.contMDiff k)
  have hXs : ∀ k, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun t => (Bundle.TotalSpace.mk'
      ThreeSpace (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t) (X k t) :
        TangentBundle ThreeModel (ch.W k).X)) := by
    intro k
    by_cases hk : k ≤ k₀
    · rw [hXk k hk]
      exact hJs k hk
    · rw [hXz k (by omega)]
      exact hZ k
  have hXg : ch.IsGlued X := by
    intro k hk
    unfold GluedAt
    by_cases h : k + 1 ≤ k₀
    · rw [hXk k (by omega), hXk (k + 1) h]
      exact (hJg k hk h).1
    by_cases h' : k = k₀
    · subst h'
      rw [hXk k le_rfl, hXz (k + 1) (by omega)]
      beta_reduce
      rw [hJ1, map_zero, map_zero]
      rfl
    · rw [hXz k (by omega), hXz (k + 1) (by omega)]
      beta_reduce
      rw [map_zero, map_zero]
      rfl
  have hW0' : Wt 0 0 = 0 := by
    have h := hW0
    rw [ch.c_zero] at h
    exact h
  have hWn' : Wt (ch.n - 1) v = 0 := by
    have h := hWn
    rw [ch.c_n] at h
    exact h
  have hX0 : X 0 0 = 0 := by rw [hXk 0 (Nat.zero_le _)]; exact hJ0
  have hXn : X (ch.n - 1) v = 0 := by rw [hXz (ch.n - 1) (by omega)]
  have hdiff : ∀ (Y : ch.Field), (∀ k, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞
      (fun t => (Bundle.TotalSpace.mk' ThreeSpace
        (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t) (Y k t) :
          TangentBundle ThreeModel (ch.W k).X))) → ch.IsRegularField Y :=
    fun Y hY k _ s _ => chartRep_diff (I := ThreeModel) (ch.γ k) (Y k) (hY k) s
  have hint : ∀ (Y Y' : ch.Field), (∀ k, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞
      (fun t => (Bundle.TotalSpace.mk' ThreeSpace
        (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t) (Y k t) :
          TangentBundle ThreeModel (ch.W k).X))) → (∀ k, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞
      (fun t => (Bundle.TotalSpace.mk' ThreeSpace
        (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t) (Y' k t) :
          TangentBundle ThreeModel (ch.W k).X))) → ∀ k < ch.n, IntervalIntegrable
      (lRegularizedIndexIntegrand (ch.W k).S T (ch.γ k) (Y k) (Y' k)) MeasureTheory.volume
      (ch.c k) (ch.c (k + 1)) :=
    fun Y Y' hY hY' k hk => intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiff
      (ch.W k).S (ch.W k).solution T _ _ (ch.γ k) (Y k) (Y' k) ((hY k).of_le (by decide))
      ((hY' k).of_le (by decide)) (ch.regular_of_mem_piece hk)
  have hexp : ∀ ε : ℝ, ch.historyLIndex (X + ε • Wt) (X + ε • Wt) =
      ch.historyLIndex X X + 2 * ε * ch.historyLIndex X Wt +
        ε ^ 2 * ch.historyLIndex Wt Wt := by
    intro ε
    unfold historyLIndex
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    exact lRegularizedIndex_add_smul_self (ch.W k).S T ε (ch.γ k) (X k) (Wt k) _ _
      (hdiff X hXs k hk') (hdiff Wt hWs k hk') (hint X X hXs hXs k hk')
      (hint X Wt hXs hWs k hk') (hint Wt Wt hWs hWs k hk')
  have hsplit : ∀ Y : ch.Field, ch.historyLIndex X Y = ∑ k ∈ Finset.range (k₀ + 1),
      lRegularizedIndex (ch.W k).S T (ch.γ k) (J k) (Y k) (ch.c k) (ch.c (k + 1)) := by
    intro Y
    unfold historyLIndex
    rw [← Finset.sum_range_add_sum_Ico _ (show k₀ + 1 ≤ ch.n by omega),
      Finset.sum_eq_zero (s := Finset.Ico (k₀ + 1) ch.n) fun k hk => by
        rw [hXz k (by simp at hk; omega)]
        exact ch.lRegularizedIndex_zero_left (Y k) _ _, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hXk k (by simp at hk; omega)]
  have hβ : ∀ Y : ch.Field, (∀ k, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞
      (fun t => (Bundle.TotalSpace.mk' ThreeSpace
        (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t) (Y k t) :
          TangentBundle ThreeModel (ch.W k).X))) → ch.IsGlued Y →
      ch.historyLIndex X Y = (1 / 2) * (ch.boundaryForm J k₀ (ch.c (k₀ + 1))
        (Y k₀ (ch.c (k₀ + 1))) - ch.boundaryForm J 0 (ch.c 0) (Y 0 (ch.c 0))) := by
    intro Y hY hYg
    rw [hsplit, ch.sum_range_lRegularizedIndex_eq_half_boundary (by omega)
      (fun k hk => hJj k (by omega)) (fun k hk h => (hJg k hk (by omega)).2)
      (fun k hk => hdiff Y hY k (by omega)) (fun k hk _ => hYg k hk)
      (fun k hk => by
        have := hint X Y hXs hY k (by omega)
        rwa [hXk k (by omega)] at this)]
    rfl
  have hXX : ch.historyLIndex X X = 0 := by
    rw [hβ X hXs hXg, show X k₀ (ch.c (k₀ + 1)) = J k₀ (ch.c (k₀ + 1)) by rw [hXk k₀ le_rfl],
      hJ1, show X 0 (ch.c 0) = J 0 (ch.c 0) by rw [hXk 0 (Nat.zero_le _)], ch.c_zero, hJ0]
    simp
  have hXW : ch.historyLIndex X Wt = (1 / 2) *
      ((ch.W k₀).S.base.metric (T - ch.c (k₀ + 1) ^ 2)).inner (ch.γ k₀ (ch.c (k₀ + 1))) P P := by
    rw [hβ Wt hWs hWg, hWP, hW0, map_zero, sub_zero]
    rfl
  have hPpos : 0 < ((ch.W k₀).S.base.metric (T - ch.c (k₀ + 1) ^ 2)).inner
      (ch.γ k₀ (ch.c (k₀ + 1))) P P := ((ch.W k₀).S.base.metric _).pos _ P hP
  obtain ⟨ε, hε⟩ := exists_neg_scale (a := ch.historyLIndex X Wt) (b := ch.historyLIndex Wt Wt)
    (by rw [hXW]; positivity)
  have hnn := ch.historyLIndex_nonneg hn hle hfloor hα hmin (X + ε • Wt)
    (fun k _ => ((hXs k).add_bundle (contMDiff_const.smul_bundle (hWs k))).of_le (by decide))
    (ch.isGlued_of_mem_span (G := {X, Wt}) (by
      rintro Y (rfl | rfl)
      · exact hXg
      · exact hWg) (Submodule.add_mem _ (Submodule.subset_span (Or.inl rfl))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl)))))
    (by
      change X 0 0 + ε • Wt 0 0 = 0
      rw [hX0, hW0', smul_zero, add_zero])
    (by
      change X (ch.n - 1) v + ε • Wt (ch.n - 1) v = 0
      rw [hXn, hWn', smul_zero, add_zero])
  rw [hexp, hXX, zero_add] at hnn
  linarith

end NonConjugacyMain

section NotConjugate

variable {B : ℝ}

theorem eqOn_zero_of_conjugate (hle : first ≤ last)
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hα : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (α j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hmin : H.regularizedExtendedAction first last T B 0 v α =
      H.regularizedCost first last hle T B 0 v (α ⟨last, hle, le_rfl⟩ 0) (α ⟨first, le_rfl, hle⟩ v))
    {k₀ : ℕ} (hk₀ : k₀ + 1 < ch.n) (J : ch.Field)
    (hJs : ∀ k ≤ k₀, ContMDiff 𝓘(ℝ, ℝ) ThreeModel.tangent ∞ (fun t => (Bundle.TotalSpace.mk'
      ThreeSpace (E := (TangentSpace ThreeModel : (ch.W k).X → Type _)) (ch.γ k t) (J k t) :
        TangentBundle ThreeModel (ch.W k).X)))
    (hJj : ∀ k ≤ k₀, ∃ a b, a < ch.c k ∧ ch.c (k + 1) < b ∧
      IsLRegularizedJacobi (ch.W k).S T (ch.γ k) (J k) (Ioo a b))
    (hJg : ∀ k (hk : k + 1 < ch.n), k + 1 ≤ k₀ →
      ch.GluedAt J hk ∧ ch.GluedAt (ch.covDerivField J) hk)
    (hJ0 : J 0 0 = 0) (hJ1 : J k₀ (ch.c (k₀ + 1)) = 0) :
    ∀ k ≤ k₀, ∀ s ∈ Icc (ch.c k) (ch.c (k + 1)), J k s = 0 := by
  have hJj' : ∀ k ≤ k₀, IsLRegularizedJacobi (ch.W k).S T (ch.γ k) (J k)
      (uIcc (ch.c k) (ch.c (k + 1))) := by
    intro k hk s hs
    obtain ⟨a, b, ha, hb, h⟩ := hJj k hk
    rw [uIcc_of_le (ch.lt k (by omega)).le] at hs
    exact h s ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have hP := ch.covDerivField_eq_zero_of_conjugate hle hfloor hα hmin hk₀ J hJs hJj' hJg hJ0 hJ1
  have key : ∀ i ≤ k₀, ∃ a b, a < ch.c (k₀ - i) ∧ ch.c (k₀ - i + 1) < b ∧
      ∀ s ∈ Ioo a b, J (k₀ - i) s = 0 := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨a, b, ha, hb, h⟩ := hJj k₀ le_rfl
      exact ch.exists_eqOn_zero_of_isLRegularizedJacobi (Nat.lt_of_succ_lt hk₀) (J k₀) ha hb h
        hJ1 hP
    | succ i ih =>
      intro hi
      obtain ⟨a, b, ha, hb, hzero⟩ := ih (by omega)
      set k := k₀ - (i + 1) with hkdef
      have hk1 : k₀ - i = k + 1 := by omega
      rw [hk1] at ha hb hzero
      have hkn : k + 1 < ch.n := by omega
      have hk' : k < ch.n := by omega
      have hmem : ch.c (k + 1) ∈ Ioo a b := ⟨ha, (ch.lt (k + 1) hkn).trans hb⟩
      have hev : ∀ᶠ r in 𝓝 (ch.c (k + 1)), J (k + 1) r = 0 :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hmem) hzero
      have hJc : J (k + 1) (ch.c (k + 1)) = 0 := hev.self_of_nhds
      have hDc := ch.covDerivAlong_eq_zero_of_eventually_eq_zero (J (k + 1)) hev
      obtain ⟨hg₁, hg₂⟩ := hJg k hkn (by omega)
      have hF := (ch.W k).localDiffeomorph (ch.bottom hk')
      have h0 : (J k (ch.c (k + 1)) : ThreeSpace) = 0 := by
        refine mfderiv_injective_congr hF rfl _ (0 : TangentSpace ThreeModel _) ?_
        refine hg₁.trans ?_
        rw [hJc, map_zero, map_zero]
        rfl
      have hD : (ch.covDerivField J k (ch.c (k + 1)) : ThreeSpace) = 0 := by
        refine mfderiv_injective_congr hF rfl _ (0 : TangentSpace ThreeModel _) ?_
        refine hg₂.trans ?_
        rw [show ch.covDerivField J (k + 1) (ch.c (k + 1)) = 0 from hDc, map_zero, map_zero]
        rfl
      obtain ⟨a', b', ha', hb', h'⟩ := hJj k (by omega)
      exact ch.exists_eqOn_zero_of_isLRegularizedJacobi hk' (J k) ha' hb' h' h0 hD
  intro k hk s hs
  obtain ⟨a, b, ha, hb, h⟩ := key (k₀ - k) (Nat.sub_le _ _)
  rw [show k₀ - (k₀ - k) = k by omega] at ha hb h
  exact h s ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩

end NotConjugate

end LWindowChain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
