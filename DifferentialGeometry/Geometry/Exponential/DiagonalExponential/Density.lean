import DifferentialGeometry.Analysis.Integration.Measure.ParamDensityComposition
import DifferentialGeometry.Analysis.Integration.Measure.ParamDensityJointSmoothness
import DifferentialGeometry.Geometry.Exponential.Trivialization
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem paramDensity_expMapIntrinsic_trivialization_pos_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    {p : M} (hp : p ∈ e.baseSet) :
    0 < paramDensity g (fun v : E => expMapIntrinsic g hEnorm p (e.symmL ℝ p v)) 0 := by
  let Φ : E → M := fun v => expMapIntrinsic g hEnorm p (show TangentSpace I p from v)
  let D := ((standardDiagonalInverseBranch g hEnorm p).fixed p).hom
  let D₁ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
    { toPartialEquiv := D.toPartialEquiv
      open_source := D.open_source
      open_target := D.open_target
      contMDiffOn_toFun := D.contMDiffOn_toFun.of_le (by simp)
      contMDiffOn_invFun := D.contMDiffOn_invFun.of_le (by simp) }
  have hDzero : (0 : E) ∈ D₁.source := (standardDiagonalInverseBranch g hEnorm p).zero_mem
  have hΦpos : 0 < paramDensity g Φ 0 := paramDensity_pos g D₁ hDzero
  let L : E ≃L[ℝ] E := (e.continuousLinearEquivAt ℝ p hp).symm
  have hΦdiff : MDifferentiableAt 𝓘(ℝ, E) I Φ 0 :=
    (intrinsicFiber_smooth g hEnorm p).contMDiffAt.mdifferentiableAt (by simp)
  have heq : (fun v : E => expMapIntrinsic g hEnorm p (e.symmL ℝ p v)) = Φ ∘ L := by
    funext v
    exact congrArg (expMapIntrinsic g hEnorm p)
      ((congrFun (e.symm_continuousLinearEquivAt_eq (R := ℝ) hp) v).symm)
  rw [heq, paramDensity_comp g (by simpa only [map_zero] using hΦdiff) L.differentiableAt]
  simp only [L.fderiv, map_zero]
  exact mul_pos (abs_pos.mpr L.toLinearEquiv.isUnit_det'.ne_zero) hΦpos

theorem exists_contMDiffOn_paramDensity_expMapIntrinsic_trivialization
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    : ∃ U : Set (M × E), IsOpen U ∧ U ⊆ e.target ∧
      (∀ p ∈ e.baseSet, (p, (0 : E)) ∈ U) ∧
      (∀ z ∈ U, 0 < paramDensity g
        (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) z.2) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun z : M × E => paramDensity g
          (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) z.2) U := by
  let Φ : M → E → M := fun q v => expMapIntrinsic g hEnorm q (e.symmL ℝ q v)
  let d : M × E → ℝ := fun z => paramDensity g (Φ z.1) z.2
  have hΦ : ContMDiffOn (I.prod 𝓘(ℝ, E)) I ∞ (Function.uncurry Φ) e.target :=
    contMDiffOn_expMapIntrinsic_trivialization g hEnorm e
  have hd : ContinuousOn d e.target := by
    intro z hz
    exact (continuousAt_paramDensity_joint (IP := I) g
      ((hΦ.contMDiffAt (e.open_target.mem_nhds hz)).of_le (by simp))).continuousWithinAt
  let U : Set (M × E) := e.target ∩ d ⁻¹' Ioi 0
  have hUopen : IsOpen U := hd.isOpen_inter_preimage e.open_target isOpen_Ioi
  have hzero : ∀ p ∈ e.baseSet, (p, (0 : E)) ∈ U := fun p hp =>
    ⟨e.mk_mem_target.mpr hp, paramDensity_expMapIntrinsic_trivialization_pos_zero g hEnorm e hp⟩
  refine ⟨U, hUopen, inter_subset_left, hzero, fun z hz => hz.2, ?_⟩
  intro z hz
  have hdet : 0 < (paramGramMatrix g (Φ z.1) z.2).det :=
    Real.sqrt_pos.mp (show 0 < Real.sqrt (paramGramMatrix g (Φ z.1) z.2).det from hz.2)
  have hΦat := hΦ.contMDiffAt (e.open_target.mem_nhds hz.1)
  exact (contMDiffAt_paramDensity_joint (IP := I) g (n := ⊤)
    (by simpa using hΦat) hdet.ne').contMDiffWithinAt

theorem exists_contMDiffOn_paramDensity_ratio_expMapIntrinsic_trivialization
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e] :
    ∃ U : Set (M × E), IsOpen U ∧ U ⊆ e.target ∧
      (∀ p ∈ e.baseSet, (p, (0 : E)) ∈ U) ∧
      (∀ z ∈ U, 0 <
        paramDensity g (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) z.2 /
          paramDensity g (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) 0) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun z : M × E =>
          paramDensity g (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) z.2 /
            paramDensity g (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) 0) U := by
  obtain ⟨U, hUopen, hUtarget, hUzero, hpos, hd⟩ :=
    exists_contMDiffOn_paramDensity_expMapIntrinsic_trivialization g hEnorm e
  have harg : ContMDiffOn (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E)) ∞
      (fun z : M × E => (z.1, (0 : E))) U :=
    (contMDiff_fst.prodMk contMDiff_const).contMDiffOn
  have hmaps : MapsTo (fun z : M × E => (z.1, (0 : E))) U U :=
    fun z hz => hUzero z.1 (e.mem_target.mp (hUtarget hz))
  refine ⟨U, hUopen, hUtarget, hUzero, ?_, ?_⟩
  · intro z hz
    exact div_pos (hpos z hz) (hpos (z.1, (0 : E)) (hmaps hz))
  · let d : M × E → ℝ := fun z => paramDensity g
      (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) z.2
    change ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ (fun z => d z / d (z.1, 0)) U
    change ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ d U at hd
    have hden : ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun z : M × E => d (z.1, 0)) U := hd.comp harg hmaps
    exact hd.div₀ hden (fun z hz => (hpos (z.1, (0 : E)) (hmaps hz)).ne')

end DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.DiagonalInverseBranch

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem exists_contMDiffOn_paramDensity_ratio_inv
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    (hc : c ∈ e.baseSet) :
    ∃ D : Set (M × M), IsOpen D ∧ (c, c) ∈ D ∧ D ⊆ B.dom ∧
      (∀ z ∈ D, B.inv z ∈ e.source) ∧
      (∀ z ∈ D, 0 < paramDensity g
        (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v))
          (e (B.inv z)).2 /
        paramDensity g (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) 0) ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : M × M => paramDensity g
          (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v))
            (e (B.inv z)).2 /
          paramDensity g (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) 0) D := by
  obtain ⟨U, hU, _, hUzero, hpos, hd⟩ :=
    exists_contMDiffOn_paramDensity_ratio_expMapIntrinsic_trivialization g hEnorm e
  let V := B.dom ∩ B.inv ⁻¹' e.source
  have hV : IsOpen V :=
    B.inv_contMDiffOn.continuousOn.isOpen_inter_preimage B.hom.open_target e.open_source
  have hinv : ContMDiffOn (I.prod I) I.tangent ∞ B.inv V :=
    B.inv_contMDiffOn.mono inter_subset_left
  have hmap : MapsTo B.inv V e.source := fun _ hz => hz.2
  have he : ContMDiffOn (I.prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun z => e (B.inv z)) V := e.contMDiffOn.comp hinv hmap
  let G : M × M → M × E := fun z => (z.1, (e (B.inv z)).2)
  have hG : ContMDiffOn (I.prod I) (I.prod 𝓘(ℝ, E)) ∞ G V :=
    contMDiffOn_fst.prodMk (contMDiff_snd.comp_contMDiffOn he)
  let D := V ∩ G ⁻¹' U
  have hD : IsOpen D := hG.continuousOn.isOpen_inter_preimage hV hU
  have hzero : e (B.inv (c, c)) = (c, (0 : E)) := by
    rw [B.center_inv, e.apply_eq_prod_continuousLinearEquivAt ℝ c hc, map_zero]
  have hcV : (c, c) ∈ V := by
    refine ⟨B.center_mem, ?_⟩
    change B.inv (c, c) ∈ e.source
    rw [B.center_inv, e.mem_source]
    exact hc
  have hcD : (c, c) ∈ D := by
    refine ⟨hcV, ?_⟩
    change (c, (e (B.inv (c, c))).2) ∈ U
    rw [hzero]
    exact hUzero c hc
  refine ⟨D, hD, hcD, fun z hz => hz.1.1, fun z hz => hz.1.2, ?_, ?_⟩
  · intro z hz
    exact hpos (G z) hz.2
  · change ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
      ((fun z : M × E => paramDensity g
        (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) z.2 /
        paramDensity g (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) 0) ∘ G) D
    exact hd.comp (hG.mono inter_subset_left) (fun _ hz => hz.2)

private theorem paramDensity_ratio_inv_eq_fixed
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c)
    (e : Bundle.Trivialization E (π E (TangentSpace I : M → Type _))) [MemTrivializationAtlas e]
    {z : M × M} (hz : z ∈ B.dom) (he : B.inv z ∈ e.source) :
    paramDensity g (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v))
        (e (B.inv z)).2 /
      paramDensity g (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) 0 =
    paramDensity g (B.fixed z.1).hom ((B.fixed z.1).inv z.2) /
      paramDensity g (B.fixed z.1).hom 0 := by
  have hp : z.1 ∈ e.baseSet := by
    have hp := e.mem_source.mp he
    rwa [B.proj_eq hz] at hp
  let L : E ≃L[ℝ] E := (e.continuousLinearEquivAt ℝ z.1 hp).symm
  have hexp : (fun v : E => expMapIntrinsic g hEnorm z.1 (e.symmL ℝ z.1 v)) =
      (B.fixed z.1).hom ∘ L := by
    funext v
    exact congrArg (expMapIntrinsic g hEnorm z.1)
      ((congrFun (e.symm_continuousLinearEquivAt_eq (R := ℝ) hp) v).symm)
  have htotal : B.inv z = (⟨z.1, show TangentSpace I z.1 from (B.inv z).snd⟩ :
      TangentBundle I M) := by
    apply TotalSpace.ext (B.proj_eq hz)
    exact heq_of_eq rfl
  have hL : L (e (B.inv z)).2 = (B.fixed z.1).inv z.2 := by
    rw [htotal, e.apply_eq_prod_continuousLinearEquivAt ℝ z.1 hp]
    exact (e.continuousLinearEquivAt ℝ z.1 hp).symm_apply_apply _
  have hΦ (v : E) : MDifferentiableAt 𝓘(ℝ, E) I (B.fixed z.1).hom v :=
    ((intrinsicFiber_smooth g hEnorm z.1).contMDiffAt).mdifferentiableAt (by simp)
  rw [hexp, paramDensity_ratio_comp_continuousLinearEquiv g L (hΦ _) (hΦ 0), hL]

theorem exists_contMDiffOn_paramDensity_ratio_fixed
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c) :
    ∃ D : Set (M × M), IsOpen D ∧ (c, c) ∈ D ∧ D ⊆ B.dom ∧
      (∀ z ∈ D, 0 < paramDensity g (B.fixed z.1).hom ((B.fixed z.1).inv z.2) /
        paramDensity g (B.fixed z.1).hom 0) ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : M × M => paramDensity g (B.fixed z.1).hom ((B.fixed z.1).inv z.2) /
          paramDensity g (B.fixed z.1).hom 0) D := by
  let e := trivializationAt E (TangentSpace I) c
  have hc : c ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H c
  obtain ⟨D, hD, hcD, hBD, heD, hpos, hd⟩ := B.exists_contMDiffOn_paramDensity_ratio_inv e hc
  refine ⟨D, hD, hcD, hBD, ?_, ?_⟩
  · intro z hz
    rw [← B.paramDensity_ratio_inv_eq_fixed e (hBD hz) (heD z hz)]
    exact hpos z hz
  · exact hd.congr fun z hz => (B.paramDensity_ratio_inv_eq_fixed e (hBD hz) (heD z hz)).symm

theorem exists_contMDiffOn_paramDensity_ratio_fixed_inv_sqrt
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c) :
    ∃ D : Set (M × M), IsOpen D ∧ (c, c) ∈ D ∧ D ⊆ B.dom ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : M × M => (Real.sqrt (paramDensity g (B.fixed z.1).hom
          ((B.fixed z.1).inv z.2) / paramDensity g (B.fixed z.1).hom 0))⁻¹) D := by
  obtain ⟨D, hD, hcD, hBD, hpos, hd⟩ := B.exists_contMDiffOn_paramDensity_ratio_fixed
  refine ⟨D, hD, hcD, hBD, ?_⟩
  intro z hz
  have hsqrt := (Real.contDiffAt_sqrt (hpos z hz).ne').contMDiffAt.comp z
    (hd.contMDiffAt (hD.mem_nhds hz))
  exact (hsqrt.inv₀ (Real.sqrt_pos.mpr (hpos z hz)).ne').contMDiffWithinAt

end DifferentialGeometry.Geometry.Riemannian.Exponential.DiagonalInverseBranch
