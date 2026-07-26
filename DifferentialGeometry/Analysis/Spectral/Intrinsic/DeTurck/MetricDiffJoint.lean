import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricFamilyConnDiff
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyPair
import DifferentialGeometry.Tensor.RSTensor.Metric

/-!
# Joint regularity of a metric-difference tensor

This file exports the generic joint-smoothness fact previously used only
privately by scalar-flux estimates: a smooth realized metric family, measured
against one fixed background metric, gives a jointly smooth family of
`metricDifferenceCcTensor`s.
-/

noncomputable section

open Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma metricDiff_apply (q h : SmoothRiemannianMetric I M)
    (x : M) (c : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
      (metricDifferenceCcTensor (I := I) (M := M) q h).toSection x) c =
      tensor0SSpace_evalScalar x c •
        (metricCcTensorFib (I := I) h x - metricCcTensorFib (I := I) q x) := by
  rw [metricDifferenceCcTensor, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply]
  change
    (MixedSection.eval₀ (F := E) (E := TangentSpace I) x c) •
          metricCcTensorFib (I := I) h x -
        (MixedSection.eval₀ (F := E) (E := TangentSpace I) x c) •
          metricCcTensorFib (I := I) q x =
      tensor0SSpace_evalScalar x c •
        (metricCcTensorFib (I := I) h x - metricCcTensorFib (I := I) q x)
  rw [Tensor0SSpace.evalScalar_apply, MixedSection.eval₀_apply, smul_sub]

/-- The unsymmetrized tensor extracted from the fixed-background metric
difference is already the pointwise metric bilinear-form difference. -/
theorem metricDiff_raw (q h : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q h) x v w =
      h.inner x v w - q.inner x v w := by
  unfold metricDifferenceCcTensor
  have hvw : ccTensorBilin (I := I) q
      (metricCcTensor (I := I) (M := M) q h -
        metricCcTensor (I := I) (M := M) q q) x v w =
      ccTensorBilin (I := I) q
          (metricCcTensor (I := I) (M := M) q h) x v w -
        ccTensorBilin (I := I) q
          (metricCcTensor (I := I) (M := M) q q) x v w := by
    rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply,
      ccTensorModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [hvw, metricCcTensor_apply, metricCcTensor_apply]

/-- Unit-model evaluation of a metric-difference tensor is the moving metric
component minus the fixed background component. -/
theorem metricDiff_unit (q h : SmoothRiemannianMetric I M)
    (x : M) (slots : Fin 2 → E) :
    unitModel (I := I) (M := M) q 2
        (metricDifferenceCcTensor (I := I) (M := M) q h) x slots =
      h.inner x (slots 0) (slots 1) - q.inner x (slots 0) (slots 1) := by
  have hslots : slots = ![slots 0, slots 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hslots, unitModel_eq_ccTensorBilin_local, metricDiff_raw]

/-- A metric-difference tensor is symmetric before applying the realization
symmetrizer. -/
theorem metricDiff_symm (q h : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q h) x v w =
      ccTensorBilin (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q h) x w v := by
  rw [metricDiff_raw, metricDiff_raw, h.symm x v w, q.symm x v w]

/-- The symmetrized fixed-background metric difference is exactly the
pointwise metric bilinear-form difference. -/
theorem metricDiff_symVal (q h : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q h) x v w =
      h.inner x v w - q.inner x v w := by
  rw [ccTensorBilinSymm_apply, metricDiff_raw, metricDiff_raw,
    h.symm x v w, q.symm x v w]
  ring

private theorem metric_ext_inner
    {g h : SmoothRiemannianMetric I M}
    (heq : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner x v w) :
    g = h := by
  have hinner : g.inner = h.inner := by
    funext x
    ext v w
    exact heq x v w
  cases g with
  | mk gi gsymm gpos gvon gcont =>
    cases h with
    | mk hi hsymm hpos hvon hcont =>
      cases hinner
      rfl

/-- Realizing the fixed-background tensor difference recovers the target
metric exactly; no separate realization-identification hypothesis is needed. -/
theorem realize_metricDiff (q h : SmoothRiemannianMetric I M)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) q
      (ccTensorBilinSymm (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q h)) δ) :
    tensorSectionRealizeMetric (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q h) hδ_lt hδ = h := by
  apply metric_ext_inner
  intro x v w
  rw [tensorSectionRealizeMetric_inner, metricDiff_symVal]
  ring

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private theorem metricDiff_eval
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M)
    (Y Z : Cₘ^∞⟮I; E, fun x : M => TangentSpace I x⟯) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        (G.metric p.2).inner p.1 (Y p.1) (Z p.1) -
          q.inner p.1 (Y p.1) (Z p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  intro p hp
  have hpair := hG.pairSmoothAt (t := p.2) (x := p.1)
    (D.regular_isOpen.mem_nhds hp.2) (![Y, Z])
  have hswap : ContMDiffAt (I.prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod I) ∞ (fun r : M × ℝ => (r.2, r.1)) p :=
    contMDiffAt_snd.prodMk contMDiffAt_fst
  have hmove : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun r : M × ℝ =>
        (G.metric r.2).inner r.1 (Y r.1) (Z r.1)) p :=
    hpair.comp p hswap
  have hfixedM :=
    DifferentialGeometry.Integral.DivergenceTheorem.contMDiff_g_inner_of_smooth_sections
      (I := I) (M := M) q Y Z
  have hfixed : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun r : M × ℝ => q.inner r.1 (Y r.1) (Z r.1)) p :=
    hfixedM.contMDiffAt.comp p contMDiffAt_fst
  have hscalar := hmove.sub hfixed
  refine hscalar.contMDiffWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards with r
    rfl
  · rfl

/-- A `MetricFamilySmoothOn` family gives a jointly smooth path of fixed-base
metric-difference tensors on its regular time set. -/
theorem metricDiff_joint
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1
        ((metricDifferenceCcTensor (I := I) (M := M) q
          (G.metric p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 0 ℝ E) (V₁ := fun x : M => Tensor0SSpace 0 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace 0 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
        (metricDifferenceCcTensor (I := I) (M := M) q
          (G.metric p.2)).toSection p.1))
  intro Y
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (Tensor0SNabla.scalarFn I M (fun x : M => Y x)) :=
    (Tensor0SNabla.contMDiff_scalarFn_iff_section I M
      (fun x : M => Y x)).mpr Y.contMDiff
  have hscalar' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        Tensor0SNabla.scalarFn I M (fun x : M => Y x) p.1)
      ((Set.univ : Set M) ×ˢ D.regular) :=
    hscalar.comp_contMDiffOn contMDiffOn_fst
  have hbilin : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.1 ((Tensor0SNabla.scalarFn I M (fun x : M => Y x) p.1) •
          ((G.metric p.2).inner p.1 - q.inner p.1)))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := E →L[ℝ] ℝ) (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (φ := fun p : M × ℝ =>
        (Tensor0SNabla.scalarFn I M (fun x : M => Y x) p.1) •
          ((G.metric p.2).inner p.1 - q.inner p.1))
    intro Z
    apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
      (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
      (F₂ := ℝ) (V₂ := fun _ : M => ℝ)
      (φ := fun p : M × ℝ =>
        ((Tensor0SNabla.scalarFn I M (fun x : M => Y x) p.1) •
          ((G.metric p.2).inner p.1 - q.inner p.1)) (Z p.1))
    intro W p hp
    rw [Bundle.contMDiffWithinAt_totalSpace]
    refine ⟨contMDiffWithinAt_fst, ?_⟩
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      smul_eq_mul] using
        (hscalar' p hp).mul
          (metricDiff_eval (I := I) (M := M) (D := D) G hG q Z W p hp)
  have hscaled : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SSpace 2 I x) p.1
        ((Tensor0SNabla.scalarFn I M (fun x : M => Y x) p.1) •
          (metricCcTensorFib (I := I) (G.metric p.2) p.1 -
            metricCcTensorFib (I := I) q p.1)))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    refine (joint_to02 (I := I) (M := M)
      (fun p : M × ℝ =>
        (Tensor0SNabla.scalarFn I M (fun x : M => Y x) p.1) •
          ((G.metric p.2).inner p.1 - q.inner p.1)) hbilin).congr (fun p _ => ?_)
    congr 1
  refine hscaled.congr (fun p _ => ?_)
  refine congrArg (fun z : Tensor0SSpace 2 I p.1 =>
    TotalSpace.mk' (Tensor0SModel 2 ℝ E)
      (E := fun x : M => Tensor0SSpace 2 I x) p.1 z) ?_
  rw [metricDiff_apply (I := I) (M := M)]
  congr 1
  rw [Tensor0SNabla.scalarFn_eq_apply_zero, Tensor0SSpace.evalScalar_apply]
  exact congrArg (Y p.1) (Subsingleton.elim _ _)

/-- Joint smoothness is stable under translating a regular-time window.  The
explicit image hypothesis records that this is an interior restart and makes
no assertion at a merely continuous endpoint of the original family. -/
theorem metricDiff_shift
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M) (c : ℝ) {S : Set ℝ}
    (hmap : ∀ t ∈ S, c + t ∈ D.regular) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun x : M => TensorRSSpace 0 2 I x) p.1
        ((metricDifferenceCcTensor (I := I) (M := M) q
          (G.metric (c + p.2))).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  have hshift : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : M × ℝ => (p.1, c + p.2)) ((Set.univ : Set M) ×ˢ S) :=
    (contMDiff_fst.prodMk (contMDiff_const.add contMDiff_snd)).contMDiffOn
  exact (metricDiff_joint (I := I) (M := M) G hG q).comp hshift
    (fun p hp => ⟨Set.mem_univ p.1, hmap p.2 hp.2⟩)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
