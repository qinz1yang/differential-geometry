import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.MetricExistence
import DifferentialGeometry.Bundle.ClmSectionSmooth

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [T2Space N]

private noncomputable def sliceFstInner
    (g : SmoothRiemannianMetric (I.prod J) (M × N)) (y : N) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let L : TangentSpace I x →L[ℝ] TangentSpace (I.prod J) (x, y) :=
    ContinuousLinearMap.inl ℝ (TangentSpace I x) (TangentSpace J y)
  (ContinuousLinearMap.precomp ℝ L).comp ((g.inner (x, y)).comp L)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N] in
private theorem sliceFstInner_apply
    (g : SmoothRiemannianMetric (I.prod J) (M × N)) (y : N)
    (x : M) (u v : TangentSpace I x) :
    sliceFstInner g y x u v = g.inner (x, y) (u, 0) (v, 0) := by
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N] in
private theorem sliceFstInner_pos
    (g : SmoothRiemannianMetric (I.prod J) (M × N)) (y : N)
    (x : M) (u : TangentSpace I x) (hu : u ≠ 0) :
    0 < sliceFstInner g y x u u := by
  rw [sliceFstInner_apply]
  apply g.pos
  intro h
  exact hu (congrArg Prod.fst h)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N] in
private theorem push_smooth_slice
    (f : M → M × N) (hf : ContMDiff I (I.prod J) ∞ f)
    (Y : ∀ x : M, TangentSpace I x)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I ((I.prod J).prod 𝓘(ℝ, E × F)) ∞
      (fun x : M => TotalSpace.mk' (E × F)
        (E := (TangentSpace (I.prod J) : M × N → Type _))
        (f x) (mfderiv I (I.prod J) f x (Y x))) := by
  exact (hf.contMDiff_tangentMap (le_refl _)).comp hY

noncomputable def SmoothRiemannianMetric.sliceFst
    (g : SmoothRiemannianMetric (I.prod J) (M × N)) (y : N) :
    SmoothRiemannianMetric I M where
  inner x := sliceFstInner g y x
  symm x u v := by
    rw [sliceFstInner_apply, sliceFstInner_apply]
    exact g.symm (x, y) _ _
  pos x u hu := sliceFstInner_pos g y x u hu
  isVonNBounded x := Geometry.posDef_isVonNBounded
    (sliceFstInner g y x) (sliceFstInner_pos g y x)
  contMDiff := by
    classical
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (φ := fun x : M => sliceFstInner g y x)
    intro Y
    apply cotangentCov_clmSection_smooth_aux
      (V₂ := fun _ : M => ℝ)
      (φ := fun x : M => sliceFstInner g y x (Y x))
    intro W
    let f : M → M × N := fun x => (x, y)
    have hf : ContMDiff I (I.prod J) ∞ f :=
      contMDiff_id.prodMk contMDiff_const
    have hY := push_smooth_slice f hf (fun x => Y x) Y.contMDiff
    have hW := push_smooth_slice f hf (fun x => W x) W.contMDiff
    have hg : ContMDiff I
        ((I.prod J).prod 𝓘(ℝ, (E × F) →L[ℝ] (E × F) →L[ℝ] ℝ)) ∞
        (fun x : M => TotalSpace.mk'
          ((E × F) →L[ℝ] (E × F) →L[ℝ] ℝ)
          (E := fun p : M × N => TangentSpace (I.prod J) p →L[ℝ]
            TangentSpace (I.prod J) p →L[ℝ] ℝ)
          (f x) (g.inner (f x))) := g.contMDiff.comp hf
    have htotal : ContMDiff I ((I.prod J).prod 𝓘(ℝ, ℝ)) ∞
        (fun x : M => TotalSpace.mk' ℝ
          (E := Bundle.Trivial (M × N) ℝ) (f x)
          (g.inner (f x) (mfderiv I (I.prod J) f x (Y x))
            (mfderiv I (I.prod J) f x (W x)))) :=
      ContMDiff.clm_bundle_apply₂ hg hY hW
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => g.inner (f x)
          (mfderiv I (I.prod J) f x (Y x))
          (mfderiv I (I.prod J) f x (W x))) := by
      intro x
      have hx := htotal x
      rw [contMDiffAt_totalSpace] at hx
      simpa using hx.2
    have hderiv (x : M) (u : TangentSpace I x) :
        mfderiv I (I.prod J) f x u = (u, 0) := by
      rw [show mfderiv I (I.prod J) f x =
          (mfderiv I I id x).prod
            (mfderiv I J (fun _ : M => y) x) from
        mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const]
      rw [mfderiv_id, mfderiv_const]
      rfl
    have hsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => sliceFstInner g y x (Y x) (W x)) := by
      convert hscalar using 1
      funext x
      rw [sliceFstInner_apply, hderiv, hderiv]
      rfl
    intro x
    rw [contMDiffAt_section]
    refine hsmooth.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards with z
    rfl

omit [FiniteDimensional ℝ F] [T2Space N] in
theorem SmoothRiemannianMetric.sliceFst_inner
    (g : SmoothRiemannianMetric (I.prod J) (M × N)) (y : N)
    (x : M) (u v : TangentSpace I x) :
    (g.sliceFst y).inner x u v = g.inner (x, y) (u, 0) (v, 0) :=
  sliceFstInner_apply g y x u v

omit [FiniteDimensional ℝ F] [T2Space N] in
theorem riemannianEDistOf_sliceFst_le
    (g : SmoothRiemannianMetric (I.prod J) (M × N)) (y : N) (x z : M) :
    riemannianEDistOf (I := I.prod J) g (x, y) (z, y) ≤
      riemannianEDistOf (I := I) (g.sliceFst y) x z := by
  rw [edistOf_iInf, edistOf_iInf]
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  let f : M → M × N := fun w => (w, y)
  let δ : Path (x, y) (z, y) := Path.map γ
    (continuous_id.prodMk continuous_const)
  have hf : ContMDiff I (I.prod J) ∞ f :=
    contMDiff_id.prodMk contMDiff_const
  have hfOne : ContMDiff I (I.prod J) 1 f := hf.of_le (by norm_num)
  have hδ : CMDiff 1 δ := hfOne.comp hγ
  refine iInf_le_of_le δ (iInf_le_of_le hδ ?_)
  apply le_of_eq
  apply lintegral_congr
  intro t
  rw [SmoothRiemannianMetric.sliceFst_inner]
  have hγMD : MDifferentiableAt _ I (γ : unitInterval → M) t :=
    (hγ t).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp t
    ((hf (γ t)).mdifferentiableAt (by simp)) hγMD
  have hfderiv (w : M) (u : TangentSpace I w) :
      mfderiv I (I.prod J) f w u = (u, 0) := by
    rw [show mfderiv I (I.prod J) f w =
        (mfderiv I I id w).prod
          (mfderiv I J (fun _ : M => y) w) from
      mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const]
    rw [mfderiv_id, mfderiv_const]
    rfl
  change ENNReal.ofReal (Real.sqrt
      (g.inner ((δ : unitInterval → M × N) t)
        ((mfderiv% (δ : unitInterval → M × N) t) 1)
        ((mfderiv% (δ : unitInterval → M × N) t) 1))) = _
  change ENNReal.ofReal (Real.sqrt
      (g.inner (f (γ t))
        ((mfderiv _ (I.prod J) (f ∘ (γ : unitInterval → M)) t) 1)
        ((mfderiv _ (I.prod J) (f ∘ (γ : unitInterval → M)) t) 1))) = _
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply, hfderiv]
  rfl

namespace RiemannianMetricComplete

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem sliceFst
    [SigmaCompactSpace M] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric (I.prod J) (M × N)) (y : N)
    (hg : RiemannianMetricComplete (I := I.prod J) g) :
    RiemannianMetricComplete (I := I) (g.sliceFst y) := by
  let : IsManifold I 1 M := IsManifold.of_le
    (I := I) (M := M) (n := ∞) (by norm_num)
  let : IsManifold (I.prod J) 1 (M × N) := IsManifold.of_le
    (I := I.prod J) (M := M × N) (n := ∞) (by norm_num)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : TopologicalSpace.MetrizableSpace (M × N) :=
    Manifold.metrizableSpace (I.prod J) (M × N)
  let : T3Space M := inferInstance
  let : T3Space (M × N) := inferInstance
  refine ⟨?_⟩
  let h := g.sliceFst y
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨h.inner, h.contMDiff.continuous, by intro x u v; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : RiemannianBundle
      (fun p : M × N => TangentSpace (I.prod J) p) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (E × F)
      (fun p : M × N => TangentSpace (I.prod J) p) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro p u v; rfl⟩⟩
  let : EMetricSpace (M × N) :=
    EMetricSpace.ofRiemannianMetric (I.prod J) (M × N)
  let : CompleteSpace (M × N) := hg.complete
  apply EMetric.complete_of_cauchySeq_tendsto
  intro s hs
  have hsprod : CauchySeq (fun n => (s n, y)) := by
    rw [EMetric.cauchySeq_iff] at hs ⊢
    intro ε hε
    obtain ⟨n, hn⟩ := hs ε hε
    refine ⟨n, fun a ha b hb => ?_⟩
    change riemannianEDistOf (I := I.prod J) g (s a, y) (s b, y) < ε
    exact (riemannianEDistOf_sliceFst_le g y (s a) (s b)).trans_lt
      (hn a ha b hb)
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hsprod
  refine ⟨p.1, ?_⟩
  exact (continuous_fst.tendsto p).comp hp

end RiemannianMetricComplete

end DifferentialGeometry
