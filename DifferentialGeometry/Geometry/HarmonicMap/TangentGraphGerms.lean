import DifferentialGeometry.Analysis.Calculus.Inverse.CommonProjection
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingPlane
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientZero

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem tangent_range_le_of_not_transverse
    (L K : ℂ →L[ℝ] E) (hd3 : Module.finrank ℝ E = 3)
    (hL : Function.Injective L)
    (hnot : ¬ Function.Surjective (L.coprod (-K))) :
    LinearMap.range K.toLinearMap ≤ LinearMap.range L.toLinearMap := by
  let S := LinearMap.range (L.coprod (-K)).toLinearMap
  have hLS : LinearMap.range L.toLinearMap ≤ S := by
    rintro v ⟨w, rfl⟩
    refine ⟨(w, 0), ?_⟩
    simp
  have hKS : LinearMap.range K.toLinearMap ≤ S := by
    rintro v ⟨w, rfl⟩
    refine ⟨(0, -w), ?_⟩
    simp
  have hSne : S ≠ ⊤ := fun h => hnot (LinearMap.range_eq_top.mp h)
  have hSdim : Module.finrank ℝ S < 3 := by
    have h := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hSne)
    simpa only [finrank_top, hd3] using h
  have hLdim : Module.finrank ℝ (LinearMap.range L.toLinearMap) = 2 := by
    rw [LinearMap.finrank_range_of_inj hL]
    rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
  have hEq : LinearMap.range L.toLinearMap = S :=
    Submodule.eq_of_le_of_finrank_eq hLS (by
      have hle := Submodule.finrank_mono hLS
      omega)
  exact hKS.trans hEq.ge

private theorem smooth_chart_gradient
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source) :
    ContDiffOn ℝ ∞ (fun z (i : Fin (Module.finrank ℝ E)) =>
      chartComplexGradient (E := E) p U i z) s := by
  have hX : ContDiffOn ℝ ∞ (fun z => extChartAt 𝓘(ℝ, E) p (U z)) s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart z hz)).comp z (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  apply contDiffOn_pi.mpr
  intro i
  have hc := (chartCoordCLM E i).contDiff.comp_contDiffOn hX
  have hd := hc.fderiv_of_isOpen (m := ∞) hs (by simp)
  have ha := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hb := hd.clm_apply (contDiffOn_const (c := Complex.I))
  have hp := (ha.mul (contDiffOn_const (c := (2 : ℝ)⁻¹))).prodMk
    (hb.neg.mul (contDiffOn_const (c := (2 : ℝ)⁻¹)))
  refine (Complex.equivRealProdCLM.symm.contDiff.comp_contDiffOn hp).congr ?_
  intro z _
  change (⟨fderiv ℝ (fun q => chartCoordCLM E i (extChartAt 𝓘(ℝ, E) p (U q))) z 1 / 2,
      -fderiv ℝ (fun q => chartCoordCLM E i (extChartAt 𝓘(ℝ, E) p (U q))) z Complex.I / 2⟩ : ℂ) =
    Complex.equivRealProdCLM.symm _
  apply Complex.ext <;> simp [Function.comp_def,
    Complex.equivRealProdCLM_symm_apply, div_eq_mul_inv]

/-- Two distinct regular preimages with the same tangent plane admit disjoint
graph germs for the original metric leading projection. Unlike the branch-local
graph supplier, these preimages need not lie near one source base point. -/
theorem chartLeadingPlaneProjection_exists_tangent_collision_germs
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd3 : Module.finrank ℝ E = 3)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    {a b : ℂ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hvalue : U a = U b) {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    (hDa : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a))
    (hDb : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b))
    (hnot : ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b)))) :
    let B : ℂ → (Fin (Module.finrank ℝ E) → ℂ) := fun z i => chartComplexGradient p U i z
    let Q := chartGramBilin g p (U a)
    let proj := chartLeadingPlaneProjection g p (U a) (B a)
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => proj (X z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * B a i).re)
    ∃ (N : E) (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ),
      Q N N = 1 ∧ proj N = 0 ∧
      (∀ v : E, v = lift (proj v) + (Q N v) • N) ∧
      a ∈ e₁.source ∧ b ∈ e₂.source ∧
      e₁.source ⊆ s ∧ e₂.source ⊆ s ∧ Disjoint e₁.source e₂.source ∧
      (e₁ : ℂ → ℂ) = F ∧ (e₂ : ℂ → ℂ) = F ∧
      ContDiffOn ℝ ∞ e₁.symm e₁.target ∧
      ContDiffOn ℝ ∞ e₂.symm e₂.target ∧
      IsOpen O ∧ F a ∈ O ∧ O ⊆ e₁.target ∩ e₂.target ∧
      ∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
        (1 - t) • X (e₂.symm y) + t • X (e₁.symm y) ∈
          (extChartAt 𝓘(ℝ, E) p).target := by
  classical
  intro B Q proj X F lift
  have hrange := tangent_range_le_of_not_transverse _ _ hd3 hDa hnot
  have hUa := hU.contMDiffAt (hs.mem_nhds ha)
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart z hz)).comp z (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hB : ContDiffAt ℝ 1 B a :=
    ((smooth_chart_gradient hs hU hchart).contDiffAt (hs.mem_nhds ha)).of_le (by simp)
  have hBne : B a ≠ 0 := by
    intro hzero
    have hgrad : ∀ i, chartComplexGradient p U i a = 0 := fun i => congrFun hzero i
    have hDzero := (chartComplexGradient_eq_zero_iff_mfderiv_eq_zero
      (hUa.of_le (by simp)) (hchart a ha)).mp hgrad
    apply one_ne_zero (α := ℂ)
    apply hDa
    rw [hDzero]
    rfl
  have hfactor : ∀ᶠ z in 𝓝 a,
      (fun i => chartComplexGradient p U i z) = (z - a) ^ (0 : ℕ) • B z := by
    filter_upwards [] with z
    simp only [pow_zero, one_smul]
    rfl
  obtain ⟨C, r, _, hr, _, _, herr⟩ :=
    chartComplexGradient_leading_projection_fderiv_error g hs (hU.of_le (by simp))
      hconformal ha (hchart a ha) hB hBne hfactor
  have hFa : fderiv ℝ F a = ContinuousLinearMap.id ℝ ℂ := by
    ext v
    have hbound := herr a (Metric.mem_ball_self hr) v
    change ‖fderiv ℝ F a v - (a - a) ^ (0 : ℕ) * v‖ ≤
      C * ‖a - a‖ ^ (0 + 1) * ‖v‖ at hbound
    have hnorm : ‖fderiv ℝ F a v - v‖ ≤ 0 := by simpa only
      [sub_self, norm_zero, Nat.zero_add, pow_zero, pow_one, one_mul, mul_zero, zero_mul]
      using hbound
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  have hF : ContDiffOn ℝ ∞ F s := proj.contDiff.comp_contDiffOn hX
  have hDF (z : ℂ) (hz : z ∈ s) :
      fderiv ℝ F z = proj.comp (fderiv ℝ X z) :=
    (proj.hasFDerivAt.comp z ((hX.contDiffAt (hs.mem_nhds hz)).differentiableAt
      (by simp)).hasFDerivAt).fderiv
  have hPa : (proj.comp (fderiv ℝ X a)).IsInvertible := by
    rw [← hDF a ha, hFa]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℂ, rfl⟩
  let chartD (q : M) : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) q
  have hDX (z : ℂ) (hz : z ∈ s) :
      fderiv ℝ X z = (chartD (U z)).comp
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
    have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart z hz)
    exact mfderiv_eq_fderiv.symm.trans
      (mfderiv_comp z (hc.mdifferentiableAt (by simp))
        ((hU.contMDiffAt (hs.mem_nhds hz)).mdifferentiableAt (by simp)))
  have hCb : Function.Injective (chartD (U b)) :=
    (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E))
      (show U b ∈ (extChartAt 𝓘(ℝ, E) p).source by
        simpa only [extChartAt_source] using hchart b hb)).injective
  have hDXb : Function.Injective (fderiv ℝ X b) := by
    rw [hDX b hb]
    exact hCb.comp hDb
  have hrangeX : LinearMap.range (fderiv ℝ X b).toLinearMap ≤
      LinearMap.range (fderiv ℝ X a).toLinearMap := by
    rintro v ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := hrange (LinearMap.mem_range_self
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b).toLinearMap w)
    let Da : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a
    let Db : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b
    change Da t = Db w at ht
    refine ⟨t, ?_⟩
    rw [hDX a ha, hDX b hb]
    change chartD (U a) (Da t) = chartD (U b) (Db w)
    calc
      chartD (U a) (Da t) = chartD (U a) (Db w) := congrArg (chartD (U a)) ht
      _ = chartD (U b) (Db w) :=
        congrArg (fun L : E →L[ℝ] E => L (Db w)) (congrArg chartD hvalue)
  obtain ⟨e₁, e₂, hae₁, hbe₂, he₁s, he₂s, hdisj, he₁, he₂, hei₁, hei₂, htargets⟩ :=
    Analysis.exists_disjoint_common_projection_inverse_germs hs hX proj ha hb hab
      (congrArg (extChartAt 𝓘(ℝ, E) p) hvalue) hPa hDXb hrangeX
  change (e₁ : ℂ → ℂ) = F at he₁
  change (e₂ : ℂ → ℂ) = F at he₂
  have hnear : ∀ᶠ z in 𝓝 a, z ∈ s ∧ (fderiv ℝ F z).IsInvertible := by
    have hcont := (hF.continuousOn_fderiv_of_isOpen hs (by simp) a ha).continuousAt
      (hs.mem_nhds ha)
    have hset : {L : ℂ →L[ℝ] ℂ | L.IsInvertible} ∈ 𝓝 (fderiv ℝ F a) := by
      rw [hFa]
      exact (ContinuousLinearEquiv.refl ℝ ℂ).nhds
    filter_upwards [hs.mem_nhds ha, hcont hset] with z hzs hzinv
    exact ⟨hzs, hzinv⟩
  obtain ⟨V, hVsub, hVo, haV⟩ := mem_nhds_iff.mp hnear
  have hVs : V ⊆ s := fun z hz => (hVsub hz).1
  have hnull := chartComplexGradient_isotropic g (hUa.of_le (by simp))
    (hchart a ha) (hconformal a ha)
  obtain ⟨N, hNN, hPN, hsplit, _⟩ :=
    chartLeadingPlaneProjection_exists_graph_germs g hd3 hVo (hU.mono hVs) haV
      (fun z hz => hchart z (hVs hz)) hBne hnull
      (fun z hz _ => (hVsub hz).2)
  have haChart : X a ∈ (extChartAt 𝓘(ℝ, E) p).target :=
    (extChartAt 𝓘(ℝ, E) p).map_source (by
      simpa only [extChartAt_source] using hchart a ha)
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p) (X a) haChart
  let O : Set ℂ := (e₁.target ∩ e₂.target) ∩
    ((fun y => X (e₁.symm y)) ⁻¹' Metric.ball (X a) ε ∩
      (fun y => X (e₂.symm y)) ⁻¹' Metric.ball (X a) ε)
  have hXe₁ : ContDiffOn ℝ ∞ (fun y => X (e₁.symm y)) e₁.target :=
    hX.comp hei₁ (fun y hy => he₁s (e₁.map_target hy))
  have hXe₂ : ContDiffOn ℝ ∞ (fun y => X (e₂.symm y)) e₂.target :=
    hX.comp hei₂ (fun y hy => he₂s (e₂.map_target hy))
  have hOo : IsOpen O := by
    have ho₁ := hXe₁.continuousOn.isOpen_inter_preimage
      (t := Metric.ball (X a) ε) e₁.open_target Metric.isOpen_ball
    have ho₂ := hXe₂.continuousOn.isOpen_inter_preimage
      (t := Metric.ball (X a) ε) e₂.open_target Metric.isOpen_ball
    convert ho₁.inter ho₂ using 1
    ext y
    simp only [O, mem_inter_iff, mem_preimage]
    tauto
  have hXvalue : X a = X b := congrArg (extChartAt 𝓘(ℝ, E) p) hvalue
  have hFvalue : F a = F b := congrArg proj hXvalue
  have he₁a : e₁.symm (F a) = a := by rw [← he₁]; exact e₁.left_inv hae₁
  have he₂b : e₂.symm (F a) = b := by rw [hFvalue, ← he₂]; exact e₂.left_inv hbe₂
  refine ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
    hdisj, he₁, he₂, hei₁, hei₂, hOo, ?_, inter_subset_left, ?_⟩
  · refine ⟨htargets, ?_, ?_⟩
    · change X (e₁.symm (F a)) ∈ Metric.ball (X a) ε
      rw [he₁a]
      exact Metric.mem_ball_self hε
    · change X (e₂.symm (F a)) ∈ Metric.ball (X a) ε
      rw [he₂b, ← hXvalue]
      exact Metric.mem_ball_self hε
  · intro y hy t ht
    exact hεsub ((convex_ball (X a) ε) hy.2.2 hy.2.1
      (sub_nonneg.mpr ht.2) ht.1 (by ring))

end DifferentialGeometry.Geometry
