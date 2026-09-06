import DifferentialGeometry.Analysis.Integration.Measure.ParamDensityComposition
import DifferentialGeometry.Analysis.Integration.Measure.ParamDensityJointSmoothness
import DifferentialGeometry.Geometry.Exponential.Trivialization
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative

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
  let D := ((stdBranch g hEnorm p).fixed p).hom
  let D₁ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
    { toPartialEquiv := D.toPartialEquiv
      open_source := D.open_source
      open_target := D.open_target
      contMDiffOn_toFun := D.contMDiffOn_toFun.of_le (by simp)
      contMDiffOn_invFun := D.contMDiffOn_invFun.of_le (by simp) }
  have hDzero : (0 : E) ∈ D₁.source := (stdBranch g hEnorm p).zero_mem
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
