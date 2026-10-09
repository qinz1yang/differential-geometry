import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.PartialDiffeomorph
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Locality
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Restriction
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Restriction
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

/-!
# `σ`-compactness-free derivative-norm locality (S-HG-INTAKE, suffix `_HGI`)

The donor branch `codex/della-mostow-smooth-adapter-20261004` (467465bc6c) removes the
`[SigmaCompactSpace U]` hypotheses from `metricDerivNorm_restrictOpen`, `metricDerivNorm_flat`
and `metricDerivNorm_eq_of_partialDiffeomorph_inner` (files
`DerivativeNorm/{Restriction,Flat,PartialDiffeomorph}.lean`). The tracked files still carry
them.  Here the three donor proofs (and the donor's helpers of `Flat`) are copied verbatim into
the namespace `DifferentialGeometry.CheegerGromovCompactness.HGI`, so that the donor users can
be pointed at `HGI.metricDerivNorm_restrictOpen` etc.
-/

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness.HGI

open scoped Manifold ContDiff Topology

section RestrictionGeneralHGI
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem metricDerivNorm_restrictOpen
    (gk gInf gRef : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [T2Space U] (a : Nat) (x : U) :
    metricDerivNorm (I := I) a (gk.restrictOpen (I := I) U)
        (gInf.restrictOpen (I := I) U) (gRef.restrictOpen (I := I) U) x =
      metricDerivNorm (I := I) a gk gInf gRef (x : M) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : IsManifold I 2 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let _ : IsManifold I 1 U := IsManifold.of_le (I := I) (M := U) (n := ∞) (by decide)
  let _ : IsManifold I 2 U := IsManifold.of_le (I := I) (M := U) (n := ∞) (by decide)
  have hcov (g : SmoothRiemannianMetric I M) :
      metricCovDeriv (I := I) (g.restrictOpen U) (gRef.restrictOpen U) a x =
        metricCovDeriv (I := I) g gRef a (x : M) := by
    ext slots
    rw [metricCovDeriv_eq_covDerivOfField, metricCovDeriv_eq_covDerivOfField]
    exact covDerivOfField_restrictOpen (I := I) gRef U
      (Tensor0SBundle.metricTensorField (I := I) (g.restrictOpen U))
      (Tensor0SBundle.metricTensorField (I := I) g)
      (by intro y v; rfl) a x slots
  have hdiff : metricDiffCovDerivAt (I := I) a (gk.restrictOpen U) (gInf.restrictOpen U)
      (gRef.restrictOpen U) x = metricDiffCovDerivAt (I := I) a gk gInf gRef (x : M) := by
    unfold metricDiffCovDerivAt
    rw [hcov gk, hcov gInf]
    rfl
  unfold metricDerivNorm
  rw [hdiff]
  exact congrArg Real.sqrt
    (Tensor0SBundle.normSq0S_restrictOpen_apply (I := I) gRef U (a + 2) x _)

end RestrictionGeneralHGI

section FlatGeneralHGI
open scoped Manifold ContDiff Topology
open TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private theorem codRestr_mdiffAt
    {A B : Type*} [TopologicalSpace A] [ChartedSpace H A]
    [TopologicalSpace B] [ChartedSpace H B]
    {W : Opens B} {f : A → B} (hmem : ∀ y, f y ∈ W) {x : A}
    (hf : ContMDiffAt I I (∞ : WithTop ℕ∞) f x) :
    ContMDiffAt I I (∞ : WithTop ℕ∞) (fun y => (⟨f y, hmem y⟩ : W)) x := by
  rw [contMDiffAt_iff] at hf ⊢
  obtain ⟨hcont, hdiff⟩ := hf
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    (by simpa [Function.comp_def] using hcont), ?_⟩
  convert hdiff using 2
  funext y
  rfl

def nestedOpen {U V : Opens M} : Opens U :=
  ⟨Subtype.val ⁻¹' (V : Set M), V.isOpen.preimage continuous_subtype_val⟩

private def flatNestedEquiv {U V : Opens M} (hVU : V ≤ U) :
    V ≃ nestedOpen (M := M) (U := U) (V := V) where
  toFun x := ⟨⟨x.1, hVU x.2⟩, x.2⟩
  invFun y := ⟨y.1.1, y.2⟩
  left_inv _ := rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def flatNestedDiffeo {U V : Opens M} (hVU : V ≤ U) :
    V ≃ₘ⟮I, I⟯ nestedOpen (M := M) (U := U) (V := V) where
  toEquiv := flatNestedEquiv (M := M) hVU
  contMDiff_toFun := by
    intro x
    exact codRestr_mdiffAt (fun y => y.2) (contMDiff_inclusion hVU).contMDiffAt
  contMDiff_invFun := by
    intro x
    apply codRestr_mdiffAt (fun y => y.2)
    exact ((contMDiff_subtype_val (I := I) (U := U)).comp
      (contMDiff_subtype_val (I := I)
        (U := nestedOpen (M := M) (U := U) (V := V)))).contMDiffAt

omit [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem flatNested_mfderiv {U V : Opens M} (hVU : V ≤ U) (x : V) :
    mfderiv I I (flatNestedDiffeo (H := H) (I := I) (M := M) hVU :
      V → nestedOpen (M := M) (U := U) (V := V)) x =
      ContinuousLinearMap.id Real E := by
  let F := flatNestedDiffeo (H := H) (I := I) (M := M) hVU
  have hF : MDifferentiableAt I I
      (F : V → nestedOpen (M := M) (U := U) (V := V)) x :=
    F.contMDiff.contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hval : MDifferentiableAt I I
      (Subtype.val : nestedOpen (M := M) (U := U) (V := V) → U) (F x) :=
    (contMDiff_subtype_val (I := I)
      (U := nestedOpen (M := M) (U := U) (V := V))).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp x hval hF
  change mfderiv I I (Opens.inclusion hVU : V → U) x =
    (mfderiv I I (Subtype.val : nestedOpen (M := M) (U := U) (V := V) → U) (F x)).comp
      (mfderiv I I (F : V → nestedOpen (M := M) (U := U) (V := V)) x) at hcomp
  rw [mfderiv_opens_incl (I := I) hVU x,
    mfderiv_subtype_val (I := I) (nestedOpen (M := M) (U := U) (V := V)) (F x)] at hcomp
  ext v
  have hv := DFunLike.congr_fun hcomp v
  change v = mfderiv I I (F : V → nestedOpen (M := M) (U := U) (V := V)) x v at hv
  exact hv.symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [SigmaCompactSpace M] in
private theorem metric_ext
    {U : Opens M} {g g' : SmoothRiemannianMetric I U}
    (h : ∀ (x : U) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) :
    g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl

omit [T2Space M] [SigmaCompactSpace M] [CompleteSpace E]
    [NeZero (Module.finrank ℝ E)] in
theorem restrictSubset_pull
    {U V : Opens M} (hVU : V ≤ U)
    [T2Space U]
    [T2Space V]
    (g : SmoothRiemannianMetric I U) :
    g.restrictOpenOfSubset (I := I) hVU =
      Diffeomorph.pullbackMetric (I := I)
        (g.restrictOpen (I := I) (nestedOpen (M := M) (U := U) (V := V)))
        (flatNestedDiffeo (H := H) (I := I) (M := M) hVU) := by
  apply metric_ext
  intro x v w
  rw [SmoothRiemannianMetric.restrictSubset_inner,
    Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner,
    flatNested_mfderiv (I := I)]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private theorem norm_eq_of_pull
    {P Q : Type*} [TopologicalSpace P] [ChartedSpace H P]
    [TopologicalSpace Q] [ChartedSpace H Q]
    [IsManifold I ∞ P] [IsManifold I ∞ Q]
    [T2Space P]
    [T2Space Q]
    [IsManifold I 1 P] [IsManifold I 2 P]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) P]
    [IsManifold I 1 Q] [IsManifold I 2 Q]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) Q]
    (A B C : SmoothRiemannianMetric I P)
    (gk gInf gRef : SmoothRiemannianMetric I Q)
    (F : P ≃ₘ⟮I, I⟯ Q)
    (hA : A = Diffeomorph.pullbackMetric (I := I) gk F)
    (hB : B = Diffeomorph.pullbackMetric (I := I) gInf F)
    (hC : C = Diffeomorph.pullbackMetric (I := I) gRef F)
    (a : Nat) (x : P) :
    metricDerivNorm (I := I) a A B C x =
      metricDerivNorm (I := I) a gk gInf gRef (F x) := by
  subst A
  subst B
  subst C
  exact metricDerivNorm_pullback (E := E) (H := H) (I := I)
    (M := P) (N := Q) gk gInf gRef F a x

omit [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricDerivNorm_flat
    {U V : Opens M} (hVU : V ≤ U)
    [T2Space U]
    [T2Space V]
    (gk gInf gRef : SmoothRiemannianMetric I U) (a : Nat) (x : V) :
    metricDerivNorm (I := I) a
        (gk.restrictOpenOfSubset (I := I) hVU)
        (gInf.restrictOpenOfSubset (I := I) hVU)
        (gRef.restrictOpenOfSubset (I := I) hVU) x =
      metricDerivNorm (I := I) a gk gInf gRef (Opens.inclusion hVU x) := by
  let W := nestedOpen (M := M) (U := U) (V := V)
  let : IsManifold I 1 V :=
    IsManifold.of_le (I := I) (M := V) (n := ∞) (by decide)
  let : IsManifold I 2 V :=
    IsManifold.of_le (I := I) (M := V) (n := ∞) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) V := by
    change IsManifold I ∞ V
    infer_instance
  let : IsManifold I 1 W :=
    IsManifold.of_le (I := I) (M := W) (n := ∞) (by decide)
  let : IsManifold I 2 W :=
    IsManifold.of_le (I := I) (M := W) (n := ∞) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) W := by
    change IsManifold I ∞ W
    infer_instance
  let F := flatNestedDiffeo (H := H) (I := I) (M := M) hVU
  calc
    metricDerivNorm (I := I) a
        (gk.restrictOpenOfSubset (I := I) hVU)
        (gInf.restrictOpenOfSubset (I := I) hVU)
        (gRef.restrictOpenOfSubset (I := I) hVU) x =
      metricDerivNorm (I := I) a (gk.restrictOpen (I := I) W)
        (gInf.restrictOpen (I := I) W)
        (gRef.restrictOpen (I := I) W) (F x) :=
      norm_eq_of_pull (E := E) (H := H) (I := I)
        (gk.restrictOpenOfSubset (I := I) hVU)
        (gInf.restrictOpenOfSubset (I := I) hVU)
        (gRef.restrictOpenOfSubset (I := I) hVU)
        (gk.restrictOpen (I := I) W)
        (gInf.restrictOpen (I := I) W)
        (gRef.restrictOpen (I := I) W) F
        (restrictSubset_pull (I := I) hVU gk)
        (restrictSubset_pull (I := I) hVU gInf)
        (restrictSubset_pull (I := I) hVU gRef) a x
    _ = metricDerivNorm (I := I) a gk gInf gRef ((F x : W) : U) :=
      metricDerivNorm_restrictOpen (I := I) gk gInf gRef W a (F x)
    _ = metricDerivNorm (I := I) a gk gInf gRef (Opens.inclusion hVU x) := by
      rfl

end FlatGeneralHGI

section PartialDiffeomorphGeneralHGI

open scoped Manifold ContDiff Topology

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private theorem metricDerivNorm_eq_of_partialDiffeomorph_inner_of_sigmaCompact
    (Phi : PartialDiffeomorph I J M N ∞) {U : TopologicalSpace.Opens M}
    [SigmaCompactSpace U] (hU : (U : Set M) ⊆ Phi.source)
    (gk gInf gRef : SmoothRiemannianMetric J N)
    (Gk GInf GRef : SmoothRiemannianMetric I U)
    (hk : ∀ (y : U) (v w : TangentSpace I y),
      Gk.inner y v w = gk.inner (Phi (y : M))
        (mfderiv I J Phi (y : M) v) (mfderiv I J Phi (y : M) w))
    (hInf : ∀ (y : U) (v w : TangentSpace I y),
      GInf.inner y v w = gInf.inner (Phi (y : M))
        (mfderiv I J Phi (y : M) v) (mfderiv I J Phi (y : M) w))
    (hRef : ∀ (y : U) (v w : TangentSpace I y),
      GRef.inner y v w = gRef.inner (Phi (y : M))
        (mfderiv I J Phi (y : M) v) (mfderiv I J Phi (y : M) w))
    (a : ℕ) (x : U) :
    metricDerivNorm (I := I) a Gk GInf GRef x =
      metricDerivNorm (I := J) a gk gInf gRef (Phi (x : M)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let V : TopologicalSpace.Opens N :=
    ⟨(Phi : M → N) '' (U : Set M), image_opens_isOpen Phi hU⟩
  let D : U ≃ₘ⟮I, J⟯ V := PartialDiffeomorph.toOpensDiffeo Phi hU
  let _ : IsManifold I 1 U := IsManifold.of_le (I := I) (M := U) (n := ∞) (by decide)
  let _ : IsManifold I 2 U := IsManifold.of_le (I := I) (M := U) (n := ∞) (by decide)
  let _ : IsManifold J 1 V := IsManifold.of_le (I := J) (M := V) (n := ∞) (by decide)
  let _ : IsManifold J 2 V := IsManifold.of_le (I := J) (M := V) (n := ∞) (by decide)
  have hmetric (A : SmoothRiemannianMetric I U) (g : SmoothRiemannianMetric J N)
      (h : ∀ (y : U) (v w : TangentSpace I y),
        A.inner y v w = g.inner (Phi (y : M))
          (mfderiv I J Phi (y : M) v) (mfderiv I J Phi (y : M) w)) :
      A = Diffeomorph.pullbackMetricCross (g.restrictOpen V) D := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner]
    change A.inner y v w = g.inner (Phi (y : M))
      (mfderiv I J (PartialDiffeomorph.toOpensDiffeo Phi hU) y v)
      (mfderiv I J (PartialDiffeomorph.toOpensDiffeo Phi hU) y w)
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo, PartialDiffeomorph.mfderiv_toOpensDiffeo]
    exact h y v w
  rw [hmetric Gk gk hk, hmetric GInf gInf hInf, hmetric GRef gRef hRef]
  exact (metricDerivNorm_pullbackCross (I := I) (J := J)
    (gk.restrictOpen V) (gInf.restrictOpen V) (gRef.restrictOpen V) D a x).trans
      (metricDerivNorm_restrictOpen (I := J) gk gInf gRef V a (D x))

theorem metricDerivNorm_eq_of_partialDiffeomorph_inner
    (Phi : PartialDiffeomorph I J M N ∞) {U : TopologicalSpace.Opens M}
    (hU : (U : Set M) ⊆ Phi.source)
    (gk gInf gRef : SmoothRiemannianMetric J N)
    (Gk GInf GRef : SmoothRiemannianMetric I U)
    (hk : ∀ (y : U) (v w : TangentSpace I y),
      Gk.inner y v w = gk.inner (Phi (y : M))
        (mfderiv I J Phi (y : M) v) (mfderiv I J Phi (y : M) w))
    (hInf : ∀ (y : U) (v w : TangentSpace I y),
      GInf.inner y v w = gInf.inner (Phi (y : M))
        (mfderiv I J Phi (y : M) v) (mfderiv I J Phi (y : M) w))
    (hRef : ∀ (y : U) (v w : TangentSpace I y),
      GRef.inner y v w = gRef.inner (Phi (y : M))
        (mfderiv I J Phi (y : M) v) (mfderiv I J Phi (y : M) w))
    (a : ℕ) (x : U) :
    metricDerivNorm (I := I) a Gk GInf GRef x =
      metricDerivNorm (I := J) a gk gInf gRef (Phi (x : M)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let V : TopologicalSpace.Opens M :=
    ⟨(U : Set M) ∩ (chartAt H (x : M)).source, U.isOpen.inter (chartAt H (x : M)).open_source⟩
  have hVU : V ≤ U := fun _ hy => hy.1
  let y : V := ⟨x, x.property, mem_chart_source H (x : M)⟩
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : SecondCountableTopology H := I.secondCountableTopology
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let _ : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  let e : V ≃ₜ ((chartAt H (x : M)) '' (V : Set M)) :=
    (chartAt H (x : M)).homeomorphOfImageSubsetSource (fun _ hy => hy.2) rfl
  let _ : SecondCountableTopology V := e.secondCountableTopology
  let _ : SigmaCompactSpace V := inferInstance
  have hsmall := metricDerivNorm_eq_of_partialDiffeomorph_inner_of_sigmaCompact
    Phi (U := V) (fun _ hz => hU hz.1) gk gInf gRef
    (Gk.restrictOpenOfSubset hVU) (GInf.restrictOpenOfSubset hVU)
    (GRef.restrictOpenOfSubset hVU)
    (fun z v w => hk (TopologicalSpace.Opens.inclusion hVU z) v w)
    (fun z v w => hInf (TopologicalSpace.Opens.inclusion hVU z) v w)
    (fun z v w => hRef (TopologicalSpace.Opens.inclusion hVU z) v w) a y
  exact (metricDerivNorm_flat hVU Gk GInf GRef a y).symm.trans hsmall

end PartialDiffeomorphGeneralHGI

end DifferentialGeometry.CheegerGromovCompactness.HGI
