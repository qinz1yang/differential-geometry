import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Paths.Flat
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.ExponentialBallPartialDiffeomorph
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MeasureZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Monotonicity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def redDensity
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x y : M)
    (tau : Real) : Real :=
  Real.exp
    (-redLength S T x y tau -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))

noncomputable def redVolume
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) : ENNReal :=
  ∫⁻ y, ENNReal.ofReal (redDensity S T x y tau)
    ∂riemannianVolumeMeasure (I := I) (M := M)
      (S.base.metric (T - tau))

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
theorem redDensity_pos
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x y : M)
    (tau : Real) : 0 < redDensity S T x y tau :=
  Real.exp_pos _

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_lExpPartial
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) :
    ∃ Φ : PartialDiffeomorph (modelWithCornersSelf Real E) I E M 1,
      Φ.source = lInjDomain S T x tau ∧
      Φ.target =
        (fun Z : E ↦ lExp S T x Z tau) '' lInjDomain S T x tau ∧
      Set.EqOn Φ (fun Z : E ↦ lExp S T x Z tau)
        (lInjDomain S T x tau) := by
  let f : E → M := fun Z ↦ lExp S T x Z tau
  let U : Set E := lInjDomain S T x tau
  have hlocal : IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞ f U := by
    rintro ⟨Z, hZ⟩
    exact lInj_local S hS T x tau htau hZ
  obtain ⟨Φ, hsource, htarget, hEq⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_partial_diffeomorph_of_is_local_diffeomorph_on_inj_on
      hlocal (lInj_isOpen S hS T x tau) (lInj_inj S hS T x tau htau)
  let Ψ : PartialDiffeomorph (modelWithCornersSelf Real E) I E M 1 :=
    { toPartialEquiv := Φ.toPartialEquiv
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · simpa only [Ψ, U] using hsource
  · simpa only [Ψ, f, U] using htarget
  · simpa only [Ψ, f, U] using hEq

noncomputable def lExpPartial
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) :
    PartialDiffeomorph (modelWithCornersSelf Real E) I E M 1 :=
  Classical.choose (exists_lExpPartial S hS T x tau htau)

theorem lExpPartial_source
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) :
    (lExpPartial S hS T x tau htau).source = lInjDomain S T x tau :=
  (Classical.choose_spec (exists_lExpPartial S hS T x tau htau)).1

theorem lExpPartial_target
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) :
    (lExpPartial S hS T x tau htau).target =
      (fun Z : E ↦ lExp S T x Z tau) '' lInjDomain S T x tau :=
  (Classical.choose_spec (exists_lExpPartial S hS T x tau htau)).2.1

theorem lExpPartial_apply
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    lExpPartial S hS T x tau htau Z = lExp S T x Z tau :=
  (Classical.choose_spec (exists_lExpPartial S hS T x tau htau)).2.2 hZ

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExpPartial_density
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    paramDensity (S.base.metric (T - tau))
        (lExpPartial S hS T x tau htau) Z =
      lExpDensity S T x Z tau := by
  have hsource : Z ∈ (lExpPartial S hS T x tau htau).source := by
    rw [lExpPartial_source S hS T x tau htau]
    exact hZ
  have hev :
      (lExpPartial S hS T x tau htau : E → M) =ᶠ[nhds Z]
        (fun W : E ↦ lExp S T x W tau) := by
    refine Filter.eventuallyEq_of_mem
      ((lExpPartial S hS T x tau htau).open_source.mem_nhds hsource) ?_
    intro W hW
    apply lExpPartial_apply S hS T x tau htau
    rw [← lExpPartial_source S hS T x tau htau]
    exact hW
  unfold paramDensity paramGramMatrix lExpDensity lExpGram lGram lExpField
  rw [hev.eq_of_nhds,
    hev.mfderiv_eq (I := modelWithCornersSelf Real E) (I' := I)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRedJac_eq
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    lRedJac S T x Z tau =
      lExpJac S T x Z tau *
        redDensity S T x (lExp S T x Z tau) tau := by
  have hJ : 0 < lExpJac S T x Z tau :=
    lExpJac_pos S hS T x htau hZ
  rw [lRedJac, lRedLog, redDensity]
  have hexp :
      Real.log (lExpJac S T x Z tau) -
          redLength S T x (lExp S T x Z tau) tau -
          ((Module.finrank Real E : Real) / 2) * Real.log tau -
          ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi) =
        Real.log (lExpJac S T x Z tau) +
          (-redLength S T x (lExp S T x Z tau) tau -
            ((Module.finrank Real E : Real) / 2) * Real.log tau -
            ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi)) := by
    ring
  rw [hexp, Real.exp_add, Real.exp_log hJ]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRedJac_mul_src
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    lRedJac S T x Z tau * lSrcDensity S T x =
      lExpDensity S T x Z tau *
        redDensity S T x (lExp S T x Z tau) tau := by
  rw [lRedJac_eq S hS T x htau hZ, lExpJac]
  field_simp [ne_of_gt (lSrcDensity_pos S T x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_lMin_slab
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x y : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Set.Icc (T - tau) T ⊆ D.regular) :
    ∃ Z : TangentSpace I x,
      (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau = y := by
  let g := S.base.metric T
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  have hxy : Manifold.riemannianEDist I x y < (⊤ : ENNReal) :=
    lt_of_le_of_ne le_top
      (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
        (I := I) x y)
  obtain ⟨p, hp, _hlen⟩ :=
    DifferentialGeometry.Geometry.Riemannian.CGT.exists_flat_path
      (I := I) hxy
  let b : Real := Real.sqrt tau
  have hb : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 htau
  let alpha : Real → M := fun s ↦ p.extend (s / b)
  have halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha := by
    apply hp.c1.comp
    rw [contMDiff_iff_contDiff]
    fun_prop
  have ha0 : alpha 0 = x := by
    simp only [alpha, zero_div, Path.extend_zero]
  have hab : alpha b = y := by
    simp only [alpha, div_self hb.ne', Path.extend_one]
  have hback : ∀ s ∈ Set.Icc (0 : Real) b,
      T - s ^ 2 ∈ Set.Icc (T - tau) T := by
    intro s hs
    have hsSq : s ^ 2 ≤ tau := by
      calc
        s ^ 2 ≤ (Real.sqrt tau) ^ 2 :=
          (sq_le_sq₀ hs.1 (Real.sqrt_nonneg tau)).2 (by
            simpa only [b] using hs.2)
        _ = tau := Real.sq_sqrt htau.le
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  exact exists_lMinVec (I := I) S hS T (T - tau) T tau htau
    (fun r hr ↦ D.regular_subset (hslab hr))
    hback x y alpha halpha ha0 hab (fun s hs ↦ hslab (hback s hs))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lExp_inj_cover
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Set.Icc (T - tau) T ⊆ D.regular) :
    ((fun Z : E ↦ lExp S T x Z tau) '' lInjDomain S T x tau)ᶜ ⊆
      lCutImage S T x tau := by
  intro y hy
  obtain ⟨Z, hmin, hend⟩ :=
    exists_lMin_slab S hS T x y tau htau hslab
  have hnot : (Z : E) ∉ lInjDomain S T x tau := by
    intro hZ
    exact hy ⟨(Z : E), hZ, hend⟩
  exact ⟨(Z : E),
    (mem_lCutDomain S T x tau (Z : E)).2 ⟨hmin, hnot⟩, hend⟩

theorem lExp_inj_ae
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Set.Icc (T - tau) T ⊆ D.regular) :
    (fun Z : E ↦ lExp S T x Z tau) '' lInjDomain S T x tau ∈
      ae (riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric (T - tau))) := by
  apply mem_ae_iff.mpr
  exact measure_mono_null (lExp_inj_cover S hS T x tau htau hslab)
    (lCut_null S hS T x tau (S.base.metric (T - tau)))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redVolume_lint
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (tau : Real) (htau : 0 < tau)
    (hslab : Set.Icc (T - tau) T ⊆ D.regular) :
    redVolume S T x tau =
      ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lRedJac S T x Z tau * lSrcDensity S T x)
        ∂modelHaar (E := E) := by
  let U : Set E := lInjDomain S T x tau
  let Ψ := lExpPartial S hS T x tau htau
  have hUmeas : MeasurableSet U :=
    (lInj_isOpen S hS T x tau).measurableSet
  have hUsource : U ⊆ Ψ.source := by
    rw [lExpPartial_source S hS T x tau htau]
  have himage :
      Ψ '' U = (fun Z : E ↦ lExp S T x Z tau) '' U := by
    exact Set.image_congr fun Z hZ ↦
      lExpPartial_apply S hS T x tau htau hZ
  calc
    redVolume S T x tau =
        ∫⁻ y in (fun Z : E ↦ lExp S T x Z tau) '' U,
          ENNReal.ofReal (redDensity S T x y tau)
          ∂riemannianVolumeMeasure (I := I) (M := M)
            (S.base.metric (T - tau)) := by
      unfold redVolume
      exact congrArg
        (fun μ : Measure M ↦
          ∫⁻ y, ENNReal.ofReal (redDensity S T x y tau) ∂μ)
        (Measure.restrict_eq_self_of_ae_mem
          (lExp_inj_ae S hS T x tau htau hslab)).symm
    _ = ∫⁻ Z in U,
        ENNReal.ofReal
            (paramDensity (S.base.metric (T - tau)) Ψ Z) *
          ENNReal.ofReal (redDensity S T x (Ψ Z) tau)
        ∂modelHaar (E := E) := by
      rw [← himage]
      exact riemVol_param_lint (I := I) (S.base.metric (T - tau)) Ψ
        (fun y ↦ ENNReal.ofReal (redDensity S T x y tau))
        hUmeas hUsource
    _ = ∫⁻ Z in U,
        ENNReal.ofReal (lRedJac S T x Z tau * lSrcDensity S T x)
        ∂modelHaar (E := E) := by
      refine MeasureTheory.setLIntegral_congr_fun hUmeas ?_
      intro Z hZ
      dsimp only [Ψ, U] at hZ ⊢
      rw [lExpPartial_density S hS T x tau htau hZ,
        lExpPartial_apply S hS T x tau htau hZ]
      rw [← ENNReal.ofReal_mul (lExpDensity_pos S hS T x htau hZ).le]
      exact congrArg ENNReal.ofReal
        (lRedJac_mul_src S hS T x htau hZ).symm
    _ = ∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lRedJac S T x Z tau * lSrcDensity S T x)
        ∂modelHaar (E := E) := by
      rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redVolume_anti
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {tau₁ tau₂ : Real} (htau₁ : 0 < tau₁) (h12 : tau₁ ≤ tau₂)
    (hslab : Set.Icc (T - tau₂) T ⊆ D.regular) :
    redVolume S T x tau₂ ≤ redVolume S T x tau₁ := by
  have htau₂ : 0 < tau₂ := htau₁.trans_le h12
  have hslab₁ : Set.Icc (T - tau₁) T ⊆ D.regular := by
    intro r hr
    exact hslab ⟨(sub_le_sub_left h12 T).trans hr.1, hr.2⟩
  have hdomain :
      lInjDomain S T x tau₂ ⊆ lInjDomain S T x tau₁ := by
    rintro Z ⟨sigma, hsigma, hmin⟩
    exact ⟨sigma, lt_of_le_of_lt h12 hsigma, hmin⟩
  rw [redVolume_lint S hS T x tau₂ htau₂ hslab,
    redVolume_lint S hS T x tau₁ htau₁ hslab₁]
  calc
    (∫⁻ Z in lInjDomain S T x tau₂,
        ENNReal.ofReal (lRedJac S T x Z tau₂ * lSrcDensity S T x)
        ∂modelHaar (E := E)) ≤
        ∫⁻ Z in lInjDomain S T x tau₂,
          ENNReal.ofReal (lRedJac S T x Z tau₁ * lSrcDensity S T x)
          ∂modelHaar (E := E) := by
      refine MeasureTheory.setLIntegral_mono'
        (lInj_isOpen S hS T x tau₂).measurableSet ?_
      intro Z hZ
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right
          (lRedJac_anti S hS T x htau₁ h12 hZ)
          (lSrcDensity_pos S T x).le)
    _ ≤ ∫⁻ Z in lInjDomain S T x tau₁,
        ENNReal.ofReal (lRedJac S T x Z tau₁ * lSrcDensity S T x)
        ∂modelHaar (E := E) :=
      MeasureTheory.lintegral_mono_set hdomain

end DifferentialGeometry.PDE.RicciFlow.Perelman
