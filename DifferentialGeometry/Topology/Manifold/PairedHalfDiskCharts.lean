import DifferentialGeometry.Analysis.Calculus.Inverse.TransverseFiberProduct
import DifferentialGeometry.Analysis.Calculus.Inverse.TransverseImmersion
import DifferentialGeometry.Analysis.Calculus.Inverse.CoordinateDerivativeEquiv
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section

open Set Filter _root_.Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

private theorem exists_open_injective_immersion_patch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℂ → E} {A : Set ℂ} {a : ℂ}
    (hA : IsOpen A) (ha : a ∈ A) (hf : ContDiffOn ℝ ∞ f A)
    (hi : Function.Injective (fderiv ℝ f a)) :
    ∃ V : Set ℂ, IsOpen V ∧ a ∈ V ∧ V ⊆ A ∧ Set.InjOn f V ∧
      ∀ z ∈ V, Function.Injective (fderiv ℝ f z) := by
  have : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  have h : IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ f a :=
    isImmersionAt_of_injective_hasFDerivAt (by simp) hA ha hf
      ((hf.contDiffAt (hA.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt hi
  have hnormal (z : ℂ) (hz : z ∈ h.domChart.source) :
      (h.codChart.extend 𝓘(ℝ, E)) (f z) =
        h.equiv ((h.domChart.extend 𝓘(ℝ, ℂ)) z, 0) := by
    have hz' : z ∈ (h.domChart.extend 𝓘(ℝ, ℂ)).source := by
      rwa [OpenPartialHomeomorph.extend_source]
    have hh := h.writtenInCharts ((h.domChart.extend 𝓘(ℝ, ℂ)).map_source hz')
    simpa only [Function.comp_apply, (h.domChart.extend 𝓘(ℝ, ℂ)).left_inv hz'] using hh
  have hinj : Set.InjOn f h.domChart.source := by
    intro z hz w hw hzw
    have hh := (hnormal z hz).symm.trans
      ((congrArg (h.codChart.extend 𝓘(ℝ, E)) hzw).trans (hnormal w hw))
    apply (h.domChart.extend 𝓘(ℝ, ℂ)).injOn
    · rwa [OpenPartialHomeomorph.extend_source]
    · rwa [OpenPartialHomeomorph.extend_source]
    · exact congrArg Prod.fst (h.equiv.injective hh)
  let L : Set ℂ := {z | IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ f z}
  have hL : IsOpen L := IsOpen.isImmersionAt
  refine ⟨(A ∩ h.domChart.source) ∩ L, (hA.inter h.domChart.open_source).inter hL,
    ⟨⟨ha, h.mem_domChart_source⟩, h⟩, fun _ hz => hz.1.1,
    hinj.mono (fun _ hz => hz.1.2), ?_⟩
  intro z hz
  have hzi : IsImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ f z := hz.2
  have hi' := hzi.mfderiv_injective (by simp)
  change Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f z : ℂ →L[ℝ] E) at hi'
  rw [mfderiv_eq_fderiv] at hi'
  exact hi'

private theorem exists_planar_curve_chart
    {c : ℝ → ℂ} {I : Set ℝ} {A : Set ℂ}
    (hI : IsOpen I) (h0 : (0 : ℝ) ∈ I) (hc : ContDiffOn ℝ ∞ c I)
    (hder : deriv c 0 ≠ 0) (hA : IsOpen A) (hcA : c 0 ∈ A) :
    ∃ ψ : OpenPartialHomeomorph ℂ ℂ,
      (0 : ℂ) ∈ ψ.source ∧ ψ 0 = c 0 ∧ ψ.target ⊆ A ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      (∀ z ∈ ψ.source, Function.Bijective (fderiv ℝ ψ z)) ∧
      ∀ t : ℝ, (t : ℂ) ∈ ψ.source → t ∈ I ∧ ψ (t : ℂ) = c t := by
  classical
  have : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  have hinj : Function.Injective (fderiv ℝ c 0) := by
    intro s t hst
    apply smul_left_injective ℝ hder
    simpa only [fderiv_eq_smul_deriv] using hst
  have hnsurj : ¬ Function.Surjective (fderiv ℝ c 0) := by
    intro hs
    have hdim := LinearMap.finrank_le_finrank_of_surjective
      (f := (fderiv ℝ c 0).toLinearMap) hs
    norm_num [Module.finrank_eq_card_basis Complex.basisOneI] at hdim
  obtain ⟨v, hv⟩ := not_forall.mp hnsurj
  obtain ⟨e, he0, heI, hesm, heism, heval⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_transverse_immersion
      hc hI h0 hinj
      (by norm_num [Module.finrank_eq_card_basis Complex.basisOneI]) hv
  let L := Complex.equivRealProdCLM
  let e₀ := L.toHomeomorph.toOpenPartialHomeomorph.trans e
  have he₀0 : (0 : ℂ) ∈ e₀.source := by
    refine ⟨mem_univ _, ?_⟩
    change L (0 : ℂ) ∈ e.source
    have hL0 : L (0 : ℂ) = ((0 : ℝ), (0 : ℝ)) := rfl
    rw [hL0]
    exact he0
  have he₀sm : ContDiffOn ℝ ∞ e₀ e₀.source :=
    hesm.comp L.contDiff.contDiffOn (fun _ hz => hz.2)
  have he₀ism : ContDiffOn ℝ ∞ e₀.symm e₀.target :=
    L.symm.contDiff.comp_contDiffOn (heism.mono inter_subset_left)
  have he₀val (z : ℂ) : e₀ z = c z.re + z.im • v := by
    change e (L z) = _
    rw [heval]
    rfl
  have he₀center : e₀ 0 = c 0 := by simp only [he₀val, Complex.zero_re,
    Complex.zero_im, zero_smul, add_zero]
  let N : Set ℂ := e₀.source ∩ e₀ ⁻¹' A
  have hN : IsOpen N := e₀.isOpen_inter_preimage hA
  let ψ := e₀.restrOpen N hN
  have hψ0 : (0 : ℂ) ∈ ψ.source := by
    refine ⟨he₀0, he₀0, ?_⟩
    change e₀ (0 : ℂ) ∈ A
    rw [he₀center]
    exact hcA
  have hψA : ψ.target ⊆ A := by
    intro y hy
    have hh : ψ (ψ.symm y) ∈ A := (ψ.map_target hy).2.2
    simpa only [ψ.right_inv hy] using hh
  have hψsm : ContDiffOn ℝ ∞ ψ ψ.source := he₀sm.mono inter_subset_left
  have hψism : ContDiffOn ℝ ∞ ψ.symm ψ.target := he₀ism.mono inter_subset_left
  let d : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ :=
    { toPartialEquiv := ψ.toPartialEquiv
      open_source := ψ.open_source
      open_target := ψ.open_target
      contMDiffOn_toFun := hψsm.contMDiffOn
      contMDiffOn_invFun := hψism.contMDiffOn }
  refine ⟨ψ, hψ0, he₀center, hψA, hψsm, hψism, ?_, ?_⟩
  · intro z hz
    exact DifferentialGeometry.Analysis.bijective_fderiv_of_partialDiffeomorph d hz
  · intro t ht
    have htE : (t, (0 : ℝ)) ∈ e.source := ht.1.2
    refine ⟨(heI htE).1, ?_⟩
    change e₀ (t : ℂ) = c t
    rw [he₀val]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A regular transverse double point has two source charts with a common
closed-disk buffer and the same real seam parameter. The original map is
injective and immersed on each chart target. -/
theorem exists_paired_halfdisk_charts_of_transverse_double_point
    {U : ℂ → M} {S : Set ℂ} {a b : ℂ}
    (hS : IsOpen S)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U S)
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (heq : U a = U b)
    (hia : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a))
    (hib : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b))
    (htrans : Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b))))
    (hdim : Module.finrank ℝ E = 3) :
    ∃ (r : ℝ) (ψ₁ ψ₂ : OpenPartialHomeomorph ℂ ℂ),
      0 < r ∧ ψ₁ 0 = a ∧ ψ₂ 0 = b ∧
      Metric.closedBall (0 : ℂ) (2 * r) ⊆ ψ₁.source ∩ ψ₂.source ∧
      ψ₁.target ⊆ S ∧ ψ₂.target ⊆ S ∧ Disjoint ψ₁.target ψ₂.target ∧
      ContDiffOn ℝ ∞ ψ₁ ψ₁.source ∧ ContDiffOn ℝ ∞ ψ₁.symm ψ₁.target ∧
      ContDiffOn ℝ ∞ ψ₂ ψ₂.source ∧ ContDiffOn ℝ ∞ ψ₂.symm ψ₂.target ∧
      (∀ z ∈ ψ₁.source, Function.Bijective (fderiv ℝ ψ₁ z)) ∧
      (∀ z ∈ ψ₂.source, Function.Bijective (fderiv ℝ ψ₂ z)) ∧
      Set.InjOn U ψ₁.target ∧ Set.InjOn U ψ₂.target ∧
      (∀ z ∈ ψ₁.target,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) ∧
      (∀ z ∈ ψ₂.target,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) ∧
      (∀ t ∈ Set.Icc (-2 * r) (2 * r), U (ψ₁ (t : ℂ)) = U (ψ₂ (t : ℂ))) := by
  have : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  let χ := extChartAt 𝓘(ℝ, E) (U a)
  let X : ℂ → E := fun z => χ (U z)
  let T : Set ℂ := S ∩ U ⁻¹' χ.source
  have hT : IsOpen T := hU.continuousOn.isOpen_inter_preimage
    hS (isOpen_extChartAt_source (U a))
  have haT : a ∈ T := ⟨ha, mem_extChartAt_source (U a)⟩
  have hbT : b ∈ T := by
    refine ⟨hb, ?_⟩
    change U b ∈ (extChartAt 𝓘(ℝ, E) (U a)).source
    rw [← heq]
    exact mem_extChartAt_source (U a)
  have hchart (z : ℂ) (hz : z ∈ T) :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ χ (U z) :=
    contMDiffAt_extChartAt' (by
      have hzχ : U z ∈ χ.source := hz.2
      simpa only [χ, extChartAt_source] using hzχ)
  have hX : ContDiffOn ℝ ∞ X T := by
    intro z hz
    exact ((hchart z hz).comp z
      (hU.contMDiffAt (hS.mem_nhds hz.1))).contDiffAt.contDiffWithinAt
  let D (z : ℂ) : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z
  let C (z : ℂ) : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) χ (U z)
  have hchain (z : ℂ) (hz : z ∈ T) (v : ℂ) :
      fderiv ℝ X z v = C z (D z v) := by
    have hh := mfderiv_comp_apply z
      ((hchart z hz).mdifferentiableAt (by simp))
      ((hU.contMDiffAt (hS.mem_nhds hz.1)).mdifferentiableAt (by simp)) v
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hC (z : ℂ) (hz : z ∈ T) : (C z).IsInvertible :=
    isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E)) hz.2
  have hiaX : Function.Injective (fderiv ℝ X a) := by
    intro v w hvw
    apply (show Function.Injective (D a) from hia)
    apply (hC a haT).injective
    simpa only [hchain a haT] using hvw
  have hibX : Function.Injective (fderiv ℝ X b) := by
    intro v w hvw
    apply (show Function.Injective (D b) from hib)
    apply (hC b hbT).injective
    simpa only [hchain b hbT] using hvw
  have hCb : C b = C a :=
    congrArg (fun p : M =>
      (show E →L[ℝ] E from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) χ p)) heq.symm
  have htransX : Function.Surjective
      ((fderiv ℝ X a).coprod (-(fderiv ℝ X b))) := by
    intro y
    obtain ⟨w, hw⟩ := (hC a haT).surjective y
    obtain ⟨z, hz⟩ := htrans w
    refine ⟨z, ?_⟩
    change fderiv ℝ X a z.1 + -(fderiv ℝ X b z.2) = y
    rw [hchain a haT, hchain b hbT, hCb, ← map_neg, ← map_add]
    exact (congrArg (C a) hz).trans hw
  obtain ⟨A₀, hA₀, ha₀, hA₀T, hjA₀, hiA₀⟩ :=
    exists_open_injective_immersion_patch hT haT hX hiaX
  obtain ⟨B₀, hB₀, hb₀, hB₀T, hjB₀, hiB₀⟩ :=
    exists_open_injective_immersion_patch hT hbT hX hibX
  obtain ⟨A₁, B₁, hA₁, hB₁, ha₁, hb₁, hdisj⟩ := t2_separation hab
  let A := A₀ ∩ A₁
  let B := B₀ ∩ B₁
  have hA : IsOpen A := hA₀.inter hA₁
  have hB : IsOpen B := hB₀.inter hB₁
  have haA : a ∈ A := ⟨ha₀, ha₁⟩
  have hbB : b ∈ B := ⟨hb₀, hb₁⟩
  have hAT : A ⊆ T := fun _ hz => hA₀T hz.1
  have hBT : B ⊆ T := fun _ hz => hB₀T hz.1
  have hAB : Disjoint A B := hdisj.mono inter_subset_right inter_subset_right
  have hjA : InjOn U A := by
    intro z hz w hw hzw
    exact hjA₀ hz.1 hw.1 (congrArg χ hzw)
  have hjB : InjOn U B := by
    intro z hz w hw hzw
    exact hjB₀ hz.1 hw.1 (congrArg χ hzw)
  have hiA (z : ℂ) (hz : z ∈ A) : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
    change Function.Injective (D z)
    intro v w hvw
    apply hiA₀ z hz.1
    exact (hchain z (hAT hz) v).trans
      ((congrArg (C z) hvw).trans (hchain z (hAT hz) w).symm)
  have hiB (z : ℂ) (hz : z ∈ B) : Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
    change Function.Injective (D z)
    intro v w hvw
    apply hiB₀ z hz.1
    exact (hchain z (hBT hz) v).trans
      ((congrArg (C z) hvw).trans (hchain z (hBT hz) w).symm)
  have hdim' : Module.finrank ℝ ℂ + Module.finrank ℝ ℂ = Module.finrank ℝ E + 1 := by
    norm_num [Module.finrank_eq_card_basis Complex.basisOneI, hdim]
  obtain ⟨R, W, c, hR, _, _, hWAB, hcsm, hc0, hcf, _, _, hcd⟩ :=
    DifferentialGeometry.Analysis.exists_local_transverse_fiber_curve
      hA hB haA hbB (hX.mono hAT) (hX.mono hBT)
      (congrArg χ heq) hiaX hibX htransX hdim'
  have h0R : (0 : ℝ) ∈ Ioo (-R) R := ⟨neg_neg_of_pos hR, hR⟩
  have hc₁ : ContDiffOn ℝ ∞ (fun t : ℝ => (c t).1) (Ioo (-R) R) :=
    contDiff_fst.comp_contDiffOn hcsm
  have hc₂ : ContDiffOn ℝ ∞ (fun t : ℝ => (c t).2) (Ioo (-R) R) :=
    contDiff_snd.comp_contDiffOn hcsm
  obtain ⟨ψ₁, hψ₁0, hψ₁center, hψ₁A, hψ₁sm, hψ₁ism, hψ₁bij, hψ₁seam⟩ :=
    exists_planar_curve_chart isOpen_Ioo h0R hc₁ (hcd 0 h0R).1 hA
      (by simpa only [hc0] using haA)
  obtain ⟨ψ₂, hψ₂0, hψ₂center, hψ₂B, hψ₂sm, hψ₂ism, hψ₂bij, hψ₂seam⟩ :=
    exists_planar_curve_chart isOpen_Ioo h0R hc₂ (hcd 0 h0R).2 hB
      (by simpa only [hc0] using hbB)
  have hN : ψ₁.source ∩ ψ₂.source ∈ 𝓝 (0 : ℂ) :=
    (ψ₁.open_source.inter ψ₂.open_source).mem_nhds ⟨hψ₁0, hψ₂0⟩
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.mp hN
  let r := δ / 4
  have hr : 0 < r := div_pos hδ (by norm_num)
  have hbuffer : Metric.closedBall (0 : ℂ) (2 * r) ⊆ ψ₁.source ∩ ψ₂.source :=
    (Metric.closedBall_subset_ball (by dsimp only [r]; linarith)).trans hδN
  refine ⟨r, ψ₁, ψ₂, hr, ?_, ?_, hbuffer,
    fun _ hz => (hAT (hψ₁A hz)).1, fun _ hz => (hBT (hψ₂B hz)).1,
    hAB.mono hψ₁A hψ₂B, hψ₁sm, hψ₁ism, hψ₂sm, hψ₂ism,
    hψ₁bij, hψ₂bij, hjA.mono hψ₁A, hjB.mono hψ₂B,
    fun z hz => hiA z (hψ₁A hz), fun z hz => hiB z (hψ₂B hz), ?_⟩
  · simpa only [hc0] using hψ₁center
  · simpa only [hc0] using hψ₂center
  · intro t ht
    have htball : (t : ℂ) ∈ Metric.closedBall (0 : ℂ) (2 * r) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith only [ht.1], ht.2⟩
    have ht₁ := hψ₁seam t (hbuffer htball).1
    have ht₂ := hψ₂seam t (hbuffer htball).2
    rw [ht₁.2, ht₂.2]
    have hcW := (hcf t ht₁.1).1
    exact χ.injOn (hAT (hWAB hcW).1).2 (hBT (hWAB hcW).2).2 (hcf t ht₁.1).2

end DifferentialGeometry.Topology.Manifold
