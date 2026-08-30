import DifferentialGeometry.Geometry.Metric.SmoothMetricFromCoeff
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import DifferentialGeometry.Geometry.Connection.LeviCivita.KoszulFormula
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Operator.HessianAlgebra
import DifferentialGeometry.Bundle.SmoothScalarGerm

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

private abbrev productTangentFst (x : M × N) :
    TangentSpace (I.prod J) x →L[Real] TangentSpace I x.1 :=
  ContinuousLinearMap.fst Real (TangentSpace I x.1) (TangentSpace J x.2)

private abbrev productTangentSnd (x : M × N) :
    TangentSpace (I.prod J) x →L[Real] TangentSpace J x.2 :=
  ContinuousLinearMap.snd Real (TangentSpace I x.1) (TangentSpace J x.2)

private def productMetricForm
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (x : M × N) :
    TangentSpace (I.prod J) x →L[Real] TangentSpace (I.prod J) x →L[Real] Real :=
  (g.inner x.1).bilinearComp
      (productTangentFst (I := I) (J := J) x)
      (productTangentFst (I := I) (J := J) x) +
    (h.inner x.2).bilinearComp
      (productTangentSnd (I := I) (J := J) x)
      (productTangentSnd (I := I) (J := J) x)

omit [FiniteDimensional Real E] [FiniteDimensional Real F] in
private theorem productMetricForm_apply
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (x : M × N)
    (v w : TangentSpace (I.prod J) x) :
    productMetricForm (I := I) (J := J) g h x v w =
      g.inner x.1 (productTangentFst (I := I) (J := J) x v)
          (productTangentFst (I := I) (J := J) x w) +
        h.inner x.2 (productTangentSnd (I := I) (J := J) x v)
          (productTangentSnd (I := I) (J := J) x w) := by
  rfl

omit [FiniteDimensional Real E] [FiniteDimensional Real F] in
private theorem productMetricForm_symm
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (x : M × N)
    (v w : TangentSpace (I.prod J) x) :
    productMetricForm (I := I) (J := J) g h x v w =
      productMetricForm (I := I) (J := J) g h x w v := by
  rw [productMetricForm_apply, productMetricForm_apply,
    g.symm x.1 (productTangentFst (I := I) (J := J) x v)
      (productTangentFst (I := I) (J := J) x w),
    h.symm x.2 (productTangentSnd (I := I) (J := J) x v)
      (productTangentSnd (I := I) (J := J) x w)]

omit [FiniteDimensional Real E] [FiniteDimensional Real F] in
private theorem productMetricForm_pos
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) (x : M × N)
    (v : TangentSpace (I.prod J) x) (hv : v ≠ 0) :
    0 < productMetricForm (I := I) (J := J) g h x v v := by
  rw [productMetricForm_apply]
  by_cases hv₁ : productTangentFst (I := I) (J := J) x v = 0
  · have hv₂ : productTangentSnd (I := I) (J := J) x v ≠ 0 := by
      intro hv₂
      apply hv
      exact Prod.ext hv₁ hv₂
    rw [hv₁]
    simp only [map_zero, zero_add]
    exact h.pos x.2 (productTangentSnd (I := I) (J := J) x v) hv₂
  · have hg := g.pos x.1 (productTangentFst (I := I) (J := J) x v) hv₁
    have hh : 0 ≤ h.inner x.2 (productTangentSnd (I := I) (J := J) x v)
        (productTangentSnd (I := I) (J := J) x v) := by
      by_cases hv₂ : productTangentSnd (I := I) (J := J) x v = 0
      · rw [hv₂]
        simp only [map_zero, le_rfl]
      · exact (h.pos x.2 (productTangentSnd (I := I) (J := J) x v) hv₂).le
    linarith

private theorem productFrame_contMDiffAt
    (x₀ : M × N) (i : Fin (Module.finrank Real (E × F))) {x : M × N}
    (hx : x ∈ (trivializationAt (E × F) (TangentSpace (I.prod J)) x₀).baseSet) :
    ContMDiffAt (I.prod J) ((I.prod J).prod 𝓘(Real, E × F)) ∞
      (fun y : M × N =>
        TotalSpace.mk' (E × F) y (frameVec (I := I.prod J) x₀ i y)) x := by
  set e := trivializationAt (E × F) (TangentSpace (I.prod J)) x₀
  set b := Module.finBasis Real (E × F)
  have hfr : frameVec (I := I.prod J) x₀ i =ᶠ[nhds x] e.localFrame b i := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    change (e.symmL Real y) (b i) = e.localFrame b i y
    rw [Bundle.Trivialization.localFrame, dif_pos hy]
    rw [Bundle.Trivialization.basisAt, Module.Basis.map_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply]
    exact e.symmL_apply hy (b i)
  refine (contMDiffAt_localFrame_of_mem (I := I.prod J) (n := (∞ : WithTop ℕ∞))
    (e := e) (b := b) (i := i) hx).congr_of_eventuallyEq ?_
  exact hfr.mono (fun y hy => congrArg (TotalSpace.mk' (E × F) y) hy)

private theorem productMetricForm_coeff_contMDiffOn
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x₀ : M × N) (i j : Fin (Module.finrank Real (E × F))) :
    ContMDiffOn (I.prod J) 𝓘(Real) ∞
      (fun x => productMetricForm (I := I) (J := J) g h x
        (frameVec (I := I.prod J) x₀ i x) (frameVec (I := I.prod J) x₀ j x))
      (trivializationAt (E × F) (TangentSpace (I.prod J)) x₀).baseSet := by
  rw [show (fun x => productMetricForm (I := I) (J := J) g h x
        (frameVec (I := I.prod J) x₀ i x) (frameVec (I := I.prod J) x₀ j x)) =
      (fun x =>
        g.inner x.1
            (productTangentFst (I := I) (J := J) x
              (frameVec (I := I.prod J) x₀ i x))
            (productTangentFst (I := I) (J := J) x
              (frameVec (I := I.prod J) x₀ j x)) +
          h.inner x.2
            (productTangentSnd (I := I) (J := J) x
              (frameVec (I := I.prod J) x₀ i x))
            (productTangentSnd (I := I) (J := J) x
              (frameVec (I := I.prod J) x₀ j x))) by
    funext x
    exact productMetricForm_apply (I := I) (J := J) g h x _ _]
  intro x hx
  have hfi := productFrame_contMDiffAt (I := I) (J := J) x₀ i hx
  have hfj := productFrame_contMDiffAt (I := I) (J := J) x₀ j hx
  have hfi₁ :=
    (contMDiff_fst.contMDiff_tangentMap (m := (∞ : WithTop ℕ∞)) le_rfl).contMDiffAt.comp x hfi
  have hfj₁ :=
    (contMDiff_fst.contMDiff_tangentMap (m := (∞ : WithTop ℕ∞)) le_rfl).contMDiffAt.comp x hfj
  have hfi₂ :=
    (contMDiff_snd.contMDiff_tangentMap (m := (∞ : WithTop ℕ∞)) le_rfl).contMDiffAt.comp x hfi
  have hfj₂ :=
    (contMDiff_snd.contMDiff_tangentMap (m := (∞ : WithTop ℕ∞)) le_rfl).contMDiffAt.comp x hfj
  have hgField : ContMDiffAt (I.prod J)
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun y : M × N =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun z : M => TangentSpace I z →L[Real] TangentSpace I z →L[Real] Real)
          y.1 (g.inner y.1)) x := by
    exact g.contMDiff.contMDiffAt.comp x contMDiffAt_fst
  have hhField : ContMDiffAt (I.prod J)
      (J.prod 𝓘(Real, F →L[Real] F →L[Real] Real)) ∞
      (fun y : M × N =>
        TotalSpace.mk' (F →L[Real] F →L[Real] Real)
          (E := fun z : N => TangentSpace J z →L[Real] TangentSpace J z →L[Real] Real)
          y.2 (h.inner y.2)) x := by
    exact h.contMDiff.contMDiffAt.comp x contMDiffAt_snd
  have hgTotal := ContMDiffAt.clm_bundle_apply₂
    (F₁ := E) (F₂ := E) (F₃ := Real)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M Real)
    (b := fun y : M × N => y.1) hgField hfi₁ hfj₁
  have hhTotal := ContMDiffAt.clm_bundle_apply₂
    (F₁ := F) (F₂ := F) (F₃ := Real)
    (E₁ := TangentSpace J) (E₂ := TangentSpace J) (E₃ := Bundle.Trivial N Real)
    (b := fun y : M × N => y.2) hhField hfi₂ hfj₂
  simp only [contMDiffAt_totalSpace] at hgTotal hhTotal
  have hg : ContMDiffAt (I.prod J) 𝓘(Real) ∞
      (fun y : M × N =>
        g.inner y.1
          (productTangentFst (I := I) (J := J) y
            (frameVec (I := I.prod J) x₀ i y))
          (productTangentFst (I := I) (J := J) y
            (frameVec (I := I.prod J) x₀ j y))) x := by
    have hs := hgTotal.2
    change ContMDiffAt (I.prod J) 𝓘(Real) ∞
      (fun y : M × N =>
        g.inner y.1
          (mfderiv (I.prod J) I Prod.fst y (frameVec (I := I.prod J) x₀ i y))
          (mfderiv (I.prod J) I Prod.fst y (frameVec (I := I.prod J) x₀ j y))) x at hs
    simpa only [mfderiv_fst] using hs
  have hh : ContMDiffAt (I.prod J) 𝓘(Real) ∞
      (fun y : M × N =>
        h.inner y.2
          (productTangentSnd (I := I) (J := J) y
            (frameVec (I := I.prod J) x₀ i y))
          (productTangentSnd (I := I) (J := J) y
            (frameVec (I := I.prod J) x₀ j y))) x := by
    have hs := hhTotal.2
    change ContMDiffAt (I.prod J) 𝓘(Real) ∞
      (fun y : M × N =>
        h.inner y.2
          (mfderiv (I.prod J) J Prod.snd y (frameVec (I := I.prod J) x₀ i y))
          (mfderiv (I.prod J) J Prod.snd y (frameVec (I := I.prod J) x₀ j y))) x at hs
    simpa only [mfderiv_snd] using hs
  exact (hg.add hh).contMDiffWithinAt

end DifferentialGeometry.Geometry

namespace DifferentialGeometry

open Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

noncomputable def SmoothRiemannianMetric.prod
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N) :
    SmoothRiemannianMetric (I.prod J) (M × N) :=
  (smoothMetric_of_localCoeff (I := I.prod J)
    (productMetricForm (I := I) (J := J) g h)
    (productMetricForm_symm (I := I) (J := J) g h)
    (productMetricForm_pos (I := I) (J := J) g h)
    (productMetricForm_coeff_contMDiffOn (I := I) (J := J) g h)).choose

@[simp]
theorem SmoothRiemannianMetric.prod_inner
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    (g.prod h).inner x v w =
      g.inner x.1 (mfderiv (I.prod J) I Prod.fst x v)
          (mfderiv (I.prod J) I Prod.fst x w) +
        h.inner x.2 (mfderiv (I.prod J) J Prod.snd x v)
          (mfderiv (I.prod J) J Prod.snd x w) := by
  rw [show (g.prod h).inner x v w =
      productMetricForm (I := I) (J := J) g h x v w from
    (smoothMetric_of_localCoeff (I := I.prod J)
      (productMetricForm (I := I) (J := J) g h)
      (productMetricForm_symm (I := I) (J := J) g h)
      (productMetricForm_pos (I := I) (J := J) g h)
      (productMetricForm_coeff_contMDiffOn (I := I) (J := J) g h)).choose_spec x v w]
  rw [productMetricForm_apply, mfderiv_fst, mfderiv_snd]

end DifferentialGeometry

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

private def horizontalLift (X : (x : M) → TangentSpace I x) (x : M × N) :
    TangentSpace (I.prod J) x :=
  (X x.1, 0)

private def verticalLift (Y : (y : N) → TangentSpace J y) (x : M × N) :
    TangentSpace (I.prod J) x :=
  (0, Y x.2)

omit [FiniteDimensional Real E] [FiniteDimensional Real F] in
private lemma horizontalLift_contMDiff {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X)) :
    ContMDiff (I.prod J) ((I.prod J).prod (modelWithCornersSelf Real (E × F))) ∞
      (T% (horizontalLift (I := I) (J := J) (N := N) X)) := by
  have hpair : ContMDiff (I.prod J)
      ((I.prod (modelWithCornersSelf Real E)).prod
        (J.prod (modelWithCornersSelf Real F))) ∞
      (fun x : M × N =>
        (TotalSpace.mk' E x.1 (X x.1),
          TotalSpace.mk' F x.2 (0 : TangentSpace J x.2))) := by
    exact (hX.comp contMDiff_fst).prodMk
      ((contMDiff_zeroSection Real (TangentSpace J)).comp contMDiff_snd)
  exact contMDiff_equivTangentBundleProd_symm.comp hpair

omit [FiniteDimensional Real E] [FiniteDimensional Real F] in
private lemma verticalLift_contMDiff {Y : (y : N) → TangentSpace J y}
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y)) :
    ContMDiff (I.prod J) ((I.prod J).prod (modelWithCornersSelf Real (E × F))) ∞
      (T% (verticalLift (I := I) (J := J) (M := M) Y)) := by
  have hpair : ContMDiff (I.prod J)
      ((I.prod (modelWithCornersSelf Real E)).prod
        (J.prod (modelWithCornersSelf Real F))) ∞
      (fun x : M × N =>
        (TotalSpace.mk' E x.1 (0 : TangentSpace I x.1),
          TotalSpace.mk' F x.2 (Y x.2))) := by
    exact ((contMDiff_zeroSection Real (TangentSpace I)).comp contMDiff_fst).prodMk
      (hY.comp contMDiff_snd)
  exact contMDiff_equivTangentBundleProd_symm.comp hpair

omit [FiniteDimensional Real E] [FiniteDimensional Real F]
    [IsManifold I ∞ M] [IsManifold J ∞ N] in
private lemma mvfderiv_fst_horizontal
    {f : M → Real} {x : M × N} (hf : MDifferentiableAt I (modelWithCornersSelf Real Real) f x.1)
    (X : (x : M) → TangentSpace I x) :
    mvfderiv (I := I.prod J) (f ∘ Prod.fst) x
        (horizontalLift (I := I) (J := J) (N := N) X x) =
      mvfderiv (I := I) f x.1 (X x.1) := by
  unfold mvfderiv horizontalLift
  rw [mfderiv_comp x hf mdifferentiableAt_fst, mfderiv_fst]
  rfl

omit [FiniteDimensional Real E] [FiniteDimensional Real F]
    [IsManifold I ∞ M] [IsManifold J ∞ N] in
private lemma mvfderiv_fst
    {f : M → Real} {x : M × N} (hf : MDifferentiableAt I (modelWithCornersSelf Real Real) f x.1)
    (v : TangentSpace (I.prod J) x) :
    mvfderiv (I := I.prod J) (f ∘ Prod.fst) x v =
      mvfderiv (I := I) f x.1 v.1 := by
  unfold mvfderiv
  rw [mfderiv_comp x hf mdifferentiableAt_fst, mfderiv_fst]
  rfl

omit [FiniteDimensional Real E] [FiniteDimensional Real F]
    [IsManifold I ∞ M] [IsManifold J ∞ N] in
private lemma mvfderiv_fst_vertical
    {f : M → Real} {x : M × N} (hf : MDifferentiableAt I (modelWithCornersSelf Real Real) f x.1)
    (Y : (y : N) → TangentSpace J y) :
    mvfderiv (I := I.prod J) (f ∘ Prod.fst) x
        (verticalLift (I := I) (J := J) (M := M) Y x) = 0 := by
  unfold mvfderiv verticalLift
  rw [mfderiv_comp x hf mdifferentiableAt_fst, mfderiv_fst]
  change (NormedSpace.fromTangentSpace (f x.1)) ((mfderiv I (modelWithCornersSelf Real Real) f x.1) 0) = 0
  simp

omit [FiniteDimensional Real E] [FiniteDimensional Real F]
    [IsManifold I ∞ M] [IsManifold J ∞ N] in
private lemma mvfderiv_snd
    {f : N → Real} {x : M × N} (hf : MDifferentiableAt J (modelWithCornersSelf Real Real) f x.2)
    (v : TangentSpace (I.prod J) x) :
    mvfderiv (I := I.prod J) (f ∘ Prod.snd) x v =
      mvfderiv (I := J) f x.2 v.2 := by
  unfold mvfderiv
  rw [mfderiv_comp x hf mdifferentiableAt_snd, mfderiv_snd]
  rfl

omit [FiniteDimensional Real E] [FiniteDimensional Real F]
    [IsManifold I ∞ M] [IsManifold J ∞ N] in
private lemma mvfderiv_snd_horizontal
    {f : N → Real} {x : M × N} (hf : MDifferentiableAt J (modelWithCornersSelf Real Real) f x.2)
    (X : (x : M) → TangentSpace I x) :
    mvfderiv (I := I.prod J) (f ∘ Prod.snd) x
        (horizontalLift (I := I) (J := J) (N := N) X x) = 0 := by
  rw [mvfderiv_snd (I := I) (J := J) hf]
  unfold horizontalLift
  exact map_zero _

omit [FiniteDimensional Real E] [FiniteDimensional Real F]
    [IsManifold I ∞ M] [IsManifold J ∞ N] in
private lemma mvfderiv_snd_vertical
    {f : N → Real} {x : M × N} (hf : MDifferentiableAt J (modelWithCornersSelf Real Real) f x.2)
    (Y : (y : N) → TangentSpace J y) :
    mvfderiv (I := I.prod J) (f ∘ Prod.snd) x
        (verticalLift (I := I) (J := J) (M := M) Y x) =
      mvfderiv (I := J) f x.2 (Y x.2) := by
  rw [mvfderiv_snd (I := I) (J := J) hf]
  rfl

private lemma mvfderiv_fst_mlieBracket_horizontal
    (f : M → Real)
    (hf : ContMDiff I (modelWithCornersSelf Real Real) ∞ f)
    (X Y : (x : M) → TangentSpace I x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Y))
    (x : M × N) :
    mvfderiv (I := I.prod J) (f ∘ Prod.fst) x
        (VectorField.mlieBracket (I.prod J)
          (horizontalLift (I := I) (J := J) (N := N) X)
          (horizontalLift (I := I) (J := J) (N := N) Y) x) =
      mvfderiv (I := I) f x.1 (VectorField.mlieBracket I X Y x.1) := by
  let Xsec : ContMDiffSection I E ∞ (TangentSpace I) := ⟨X, hX⟩
  let Ysec : ContMDiffSection I E ∞ (TangentSpace I) := ⟨Y, hY⟩
  have hYf : ContMDiff I (modelWithCornersSelf Real Real) ∞
      (fun p : M => mvfderiv (I := I) f p (Y p)) :=
    DifferentialGeometry.mvfderiv_apply_contMDiff I f hf Ysec
  have hXf : ContMDiff I (modelWithCornersSelf Real Real) ∞
      (fun p : M => mvfderiv (I := I) f p (X p)) :=
    DifferentialGeometry.mvfderiv_apply_contMDiff I f hf Xsec
  have htwo : minSmoothness Real 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_cast
  have hleft := DifferentialGeometry.mvfderiv_apply_mlieBracket
    (I := I.prod J)
    (horizontalLift (I := I) (J := J) (N := N) X)
    (horizontalLift (I := I) (J := J) (N := N) Y)
    (f ∘ Prod.fst) x
    ((horizontalLift_contMDiff (I := I) (J := J) (N := N) hX).contMDiffAt.of_le htwo)
    ((horizontalLift_contMDiff (I := I) (J := J) (N := N) hY).contMDiffAt.of_le htwo)
    ((hf.comp contMDiff_fst).contMDiffAt.of_le htwo)
  have hright := DifferentialGeometry.mvfderiv_apply_mlieBracket
    (I := I) X Y f x.1
    (hX.contMDiffAt.of_le htwo) (hY.contMDiffAt.of_le htwo)
    (hf.contMDiffAt.of_le htwo)
  have hYeq : (fun z : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.fst) z
        (horizontalLift (I := I) (J := J) (N := N) Y z)) =
      (fun z : M × N => mvfderiv (I := I) f z.1 (Y z.1)) := by
    funext z
    exact mvfderiv_fst_horizontal (I := I) (J := J) (N := N)
      (hf.mdifferentiableAt (by simp)) Y
  have hXeq : (fun z : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.fst) z
        (horizontalLift (I := I) (J := J) (N := N) X z)) =
      (fun z : M × N => mvfderiv (I := I) f z.1 (X z.1)) := by
    funext z
    exact mvfderiv_fst_horizontal (I := I) (J := J) (N := N)
      (hf.mdifferentiableAt (by simp)) X
  rw [hYeq, hXeq] at hleft
  have hYouter : mvfderiv (I := I.prod J)
      (fun z : M × N => mvfderiv (I := I) f z.1 (Y z.1)) x
        (horizontalLift (I := I) (J := J) (N := N) X x) =
      mvfderiv (I := I) (fun p : M => mvfderiv (I := I) f p (Y p)) x.1 (X x.1) := by
    simpa only [Function.comp_def] using
      (mvfderiv_fst_horizontal (I := I) (J := J) (N := N)
        (hYf.mdifferentiableAt (by simp)) X)
  have hXouter : mvfderiv (I := I.prod J)
      (fun z : M × N => mvfderiv (I := I) f z.1 (X z.1)) x
        (horizontalLift (I := I) (J := J) (N := N) Y x) =
      mvfderiv (I := I) (fun p : M => mvfderiv (I := I) f p (X p)) x.1 (Y x.1) := by
    simpa only [Function.comp_def] using
      (mvfderiv_fst_horizontal (I := I) (J := J) (N := N)
        (hXf.mdifferentiableAt (by simp)) Y)
  rw [hYouter, hXouter] at hleft
  exact hleft.trans hright.symm

private lemma mvfderiv_snd_mlieBracket_horizontal
    (f : N → Real)
    (hf : ContMDiff J (modelWithCornersSelf Real Real) ∞ f)
    (X Y : (x : M) → TangentSpace I x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Y))
    (x : M × N) :
    mvfderiv (I := I.prod J) (f ∘ Prod.snd) x
        (VectorField.mlieBracket (I.prod J)
          (horizontalLift (I := I) (J := J) (N := N) X)
          (horizontalLift (I := I) (J := J) (N := N) Y) x) = 0 := by
  have htwo : minSmoothness Real 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_cast
  have hleft := DifferentialGeometry.mvfderiv_apply_mlieBracket
    (I := I.prod J)
    (horizontalLift (I := I) (J := J) (N := N) X)
    (horizontalLift (I := I) (J := J) (N := N) Y)
    (f ∘ Prod.snd) x
    ((horizontalLift_contMDiff (I := I) (J := J) (N := N) hX).contMDiffAt.of_le htwo)
    ((horizontalLift_contMDiff (I := I) (J := J) (N := N) hY).contMDiffAt.of_le htwo)
    ((hf.comp contMDiff_snd).contMDiffAt.of_le htwo)
  have hYeq : (fun z : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.snd) z
        (horizontalLift (I := I) (J := J) (N := N) Y z)) = 0 := by
    funext z
    exact mvfderiv_snd_horizontal (I := I) (J := J)
      (hf.mdifferentiableAt (by simp)) Y
  have hXeq : (fun z : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.snd) z
        (horizontalLift (I := I) (J := J) (N := N) X z)) = 0 := by
    funext z
    exact mvfderiv_snd_horizontal (I := I) (J := J)
      (hf.mdifferentiableAt (by simp)) X
  rw [hYeq, hXeq] at hleft
  have hzero (v : TangentSpace (I.prod J) x) :
      mvfderiv (I := I.prod J) (0 : M × N → Real) x v = 0 := by
    have hz := mvfderiv_const (I := I.prod J) (M := M × N) (0 : Real) (x := x)
    exact congrArg (fun A => A v) hz
  rw [hzero, hzero, sub_zero] at hleft
  exact hleft

private lemma mvfderiv_chart_coord
    (b : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (i : Fin (Module.finrank Real E)) (x : M) (v : TangentSpace I x) :
    mvfderiv (I := I) (fun y : M => b.coord i (extChartAt I x y)) x v =
      b.coord i v := by
  let L : E →L[Real] Real := LinearMap.toContinuousLinearMap (b.coord i)
  have hchart : MDifferentiableAt I (modelWithCornersSelf Real E) (extChartAt I x) x :=
    (contMDiffAt_extChartAt (I := I) (n := (∞ : WithTop ℕ∞))).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp x L.mdifferentiableAt hchart
  have hL : mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real Real)
      L (extChartAt I x x) = L := by
    rw [mfderiv_eq_fderiv, L.fderiv]
  rw [hL, mfderiv_extChartAt_self] at hcomp
  unfold mvfderiv
  rw [show mfderiv I (modelWithCornersSelf Real Real)
      (fun y : M => b.coord i (extChartAt I x y)) x =
      mfderiv I (modelWithCornersSelf Real Real) (L ∘ extChartAt I x) x by rfl]
  rw [hcomp]
  rfl

private lemma mlieBracket_horizontal_fst
    [T2Space M]
    (X Y : (x : M) → TangentSpace I x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Y))
    (x : M × N) :
    (VectorField.mlieBracket (I.prod J)
      (horizontalLift (I := I) (J := J) (N := N) X)
      (horizontalLift (I := I) (J := J) (N := N) Y) x).1 =
      VectorField.mlieBracket I X Y x.1 := by
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E := Module.finBasis Real E
  apply b.ext_elem
  intro i
  let L : E →L[Real] Real := LinearMap.toContinuousLinearMap (b.coord i)
  let coordFun : M → Real := fun y => L (extChartAt I x.1 y)
  have hlocal : ContMDiffOn I (modelWithCornersSelf Real Real) ∞ coordFun
      (chartAt H x.1).source := by
    exact L.contMDiff.contMDiffOn.comp (t := Set.univ)
      (contMDiffOn_extChartAt (I := I) (n := (∞ : WithTop ℕ∞)) (x := x.1))
      (fun y hy => Set.mem_univ (extChartAt I x.1 y))
  obtain ⟨f, hf, hfgerm⟩ := DifferentialGeometry.exists_smooth_germ
    (chartAt H x.1).open_source (mem_chart_source H x.1) hlocal
  have hcoord (v : TangentSpace I x.1) :
      mvfderiv (I := I) f x.1 v = b.coord i v := by
    unfold mvfderiv
    rw [hfgerm.mfderiv_eq (I := I) (I' := modelWithCornersSelf Real Real)]
    exact mvfderiv_chart_coord (I := I) b i x.1 v
  calc
    b.coord i
        (VectorField.mlieBracket (I.prod J)
          (horizontalLift (I := I) (J := J) (N := N) X)
          (horizontalLift (I := I) (J := J) (N := N) Y) x).1 =
      mvfderiv (I := I) f x.1
        (VectorField.mlieBracket (I.prod J)
          (horizontalLift (I := I) (J := J) (N := N) X)
          (horizontalLift (I := I) (J := J) (N := N) Y) x).1 := by
        exact (hcoord _).symm
    _ = mvfderiv (I := I.prod J) (f ∘ Prod.fst) x
        (VectorField.mlieBracket (I.prod J)
          (horizontalLift (I := I) (J := J) (N := N) X)
          (horizontalLift (I := I) (J := J) (N := N) Y) x) := by
        rw [mvfderiv_fst (I := I) (J := J)
          (hf.mdifferentiableAt (by simp))]
    _ = mvfderiv (I := I) f x.1 (VectorField.mlieBracket I X Y x.1) :=
      mvfderiv_fst_mlieBracket_horizontal (I := I) (J := J) (N := N)
        f hf X Y hX hY x
    _ = b.coord i (VectorField.mlieBracket I X Y x.1) := hcoord _

private lemma tangent_eq_zero_of_mvfderiv_eq_zero
    [T2Space N] (x : N) (v : TangentSpace J x)
    (hv : ∀ f : N → Real, ContMDiff J (modelWithCornersSelf Real Real) ∞ f →
      mvfderiv (I := J) f x v = 0) :
    v = 0 := by
  change v = (0 : F)
  let b : Module.Basis (Fin (Module.finrank Real F)) Real F := Module.finBasis Real F
  apply b.ext_elem
  intro i
  let L : F →L[Real] Real := LinearMap.toContinuousLinearMap (b.coord i)
  let coordFun : N → Real := fun y => L (extChartAt J x y)
  have hcoordFun : ContMDiffOn J (modelWithCornersSelf Real Real) ∞ coordFun
      (chartAt G x).source := by
    exact L.contMDiff.contMDiffOn.comp (t := Set.univ)
      (contMDiffOn_extChartAt (I := J) (n := (∞ : WithTop ℕ∞)) (x := x))
      (fun y hy => Set.mem_univ (extChartAt J x y))
  obtain ⟨f, hf, hfgerm⟩ := DifferentialGeometry.exists_smooth_germ
    (chartAt G x).open_source (mem_chart_source G x) hcoordFun
  have hcoord : mvfderiv (I := J) f x v = b.coord i v := by
    unfold mvfderiv
    rw [hfgerm.mfderiv_eq (I := J) (I' := modelWithCornersSelf Real Real)]
    exact mvfderiv_chart_coord (I := J) b i x v
  change b.coord i (show F from v) = b.coord i (0 : F)
  rw [← hcoord, hv f hf]
  exact (map_zero (b.coord i)).symm

private lemma mlieBracket_horizontal
    [T2Space M] [T2Space N]
    (X Y : (x : M) → TangentSpace I x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Y))
    (x : M × N) :
    VectorField.mlieBracket (I.prod J)
      (horizontalLift (I := I) (J := J) (N := N) X)
      (horizontalLift (I := I) (J := J) (N := N) Y) x =
      horizontalLift (I := I) (J := J) (N := N)
        (VectorField.mlieBracket I X Y) x := by
  apply Prod.ext
  · exact mlieBracket_horizontal_fst (I := I) (J := J) X Y hX hY x
  · apply tangent_eq_zero_of_mvfderiv_eq_zero (J := J) (N := N) (x := x.2)
    intro f hf
    rw [← mvfderiv_snd (I := I) (J := J)
      (hf.mdifferentiableAt (by simp))]
    exact mvfderiv_snd_mlieBracket_horizontal (I := I) (J := J)
      f hf X Y hX hY x

private lemma mvfderiv_snd_mlieBracket_vertical
    (f : N → Real)
    (hf : ContMDiff J (modelWithCornersSelf Real Real) ∞ f)
    (Y Z : (x : N) → TangentSpace J x)
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (hZ : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Z))
    (x : M × N) :
    mvfderiv (I := I.prod J) (f ∘ Prod.snd) x
        (VectorField.mlieBracket (I.prod J)
          (verticalLift (I := I) (J := J) (M := M) Y)
          (verticalLift (I := I) (J := J) (M := M) Z) x) =
      mvfderiv (I := J) f x.2 (VectorField.mlieBracket J Y Z x.2) := by
  let Ysec : ContMDiffSection J F ∞ (TangentSpace J) := ⟨Y, hY⟩
  let Zsec : ContMDiffSection J F ∞ (TangentSpace J) := ⟨Z, hZ⟩
  have hZf : ContMDiff J (modelWithCornersSelf Real Real) ∞
      (fun p : N => mvfderiv (I := J) f p (Z p)) :=
    DifferentialGeometry.mvfderiv_apply_contMDiff J f hf Zsec
  have hYf : ContMDiff J (modelWithCornersSelf Real Real) ∞
      (fun p : N => mvfderiv (I := J) f p (Y p)) :=
    DifferentialGeometry.mvfderiv_apply_contMDiff J f hf Ysec
  have htwo : minSmoothness Real 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_cast
  have hleft := DifferentialGeometry.mvfderiv_apply_mlieBracket
    (I := I.prod J)
    (verticalLift (I := I) (J := J) (M := M) Y)
    (verticalLift (I := I) (J := J) (M := M) Z)
    (f ∘ Prod.snd) x
    ((verticalLift_contMDiff (I := I) (J := J) (M := M) hY).contMDiffAt.of_le htwo)
    ((verticalLift_contMDiff (I := I) (J := J) (M := M) hZ).contMDiffAt.of_le htwo)
    ((hf.comp contMDiff_snd).contMDiffAt.of_le htwo)
  have hright := DifferentialGeometry.mvfderiv_apply_mlieBracket
    (I := J) Y Z f x.2
    (hY.contMDiffAt.of_le htwo) (hZ.contMDiffAt.of_le htwo)
    (hf.contMDiffAt.of_le htwo)
  have hZeq : (fun p : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.snd) p
        (verticalLift (I := I) (J := J) (M := M) Z p)) =
      (fun p : M × N => mvfderiv (I := J) f p.2 (Z p.2)) := by
    funext p
    exact mvfderiv_snd_vertical (I := I) (J := J) (M := M)
      (hf.mdifferentiableAt (by simp)) Z
  have hYeq : (fun p : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.snd) p
        (verticalLift (I := I) (J := J) (M := M) Y p)) =
      (fun p : M × N => mvfderiv (I := J) f p.2 (Y p.2)) := by
    funext p
    exact mvfderiv_snd_vertical (I := I) (J := J) (M := M)
      (hf.mdifferentiableAt (by simp)) Y
  rw [hZeq, hYeq] at hleft
  have hZouter : mvfderiv (I := I.prod J)
      (fun p : M × N => mvfderiv (I := J) f p.2 (Z p.2)) x
        (verticalLift (I := I) (J := J) (M := M) Y x) =
      mvfderiv (I := J) (fun q : N => mvfderiv (I := J) f q (Z q))
        x.2 (Y x.2) := by
    simpa only [Function.comp_def] using
      (mvfderiv_snd_vertical (I := I) (J := J) (M := M)
        (hZf.mdifferentiableAt (by simp)) Y)
  have hYouter : mvfderiv (I := I.prod J)
      (fun p : M × N => mvfderiv (I := J) f p.2 (Y p.2)) x
        (verticalLift (I := I) (J := J) (M := M) Z x) =
      mvfderiv (I := J) (fun q : N => mvfderiv (I := J) f q (Y q))
        x.2 (Z x.2) := by
    simpa only [Function.comp_def] using
      (mvfderiv_snd_vertical (I := I) (J := J) (M := M)
        (hYf.mdifferentiableAt (by simp)) Z)
  rw [hZouter, hYouter] at hleft
  exact hleft.trans hright.symm

private lemma mvfderiv_fst_mlieBracket_vertical
    (f : M → Real)
    (hf : ContMDiff I (modelWithCornersSelf Real Real) ∞ f)
    (Y Z : (x : N) → TangentSpace J x)
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (hZ : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Z))
    (x : M × N) :
    mvfderiv (I := I.prod J) (f ∘ Prod.fst) x
        (VectorField.mlieBracket (I.prod J)
          (verticalLift (I := I) (J := J) (M := M) Y)
          (verticalLift (I := I) (J := J) (M := M) Z) x) = 0 := by
  have htwo : minSmoothness Real 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_cast
  have hleft := DifferentialGeometry.mvfderiv_apply_mlieBracket
    (I := I.prod J)
    (verticalLift (I := I) (J := J) (M := M) Y)
    (verticalLift (I := I) (J := J) (M := M) Z)
    (f ∘ Prod.fst) x
    ((verticalLift_contMDiff (I := I) (J := J) (M := M) hY).contMDiffAt.of_le htwo)
    ((verticalLift_contMDiff (I := I) (J := J) (M := M) hZ).contMDiffAt.of_le htwo)
    ((hf.comp contMDiff_fst).contMDiffAt.of_le htwo)
  have hZeq : (fun p : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.fst) p
        (verticalLift (I := I) (J := J) (M := M) Z p)) = 0 := by
    funext p
    exact mvfderiv_fst_vertical (I := I) (J := J)
      (hf.mdifferentiableAt (by simp)) Z
  have hYeq : (fun p : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.fst) p
        (verticalLift (I := I) (J := J) (M := M) Y p)) = 0 := by
    funext p
    exact mvfderiv_fst_vertical (I := I) (J := J)
      (hf.mdifferentiableAt (by simp)) Y
  rw [hZeq, hYeq] at hleft
  have hzero (v : TangentSpace (I.prod J) x) :
      mvfderiv (I := I.prod J) (0 : M × N → Real) x v = 0 := by
    have hz := mvfderiv_const (I := I.prod J) (M := M × N) (0 : Real) (x := x)
    exact congrArg (fun A => A v) hz
  rw [hzero, hzero, sub_zero] at hleft
  exact hleft

private lemma mlieBracket_vertical_snd
    [T2Space N]
    (Y Z : (x : N) → TangentSpace J x)
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (hZ : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Z))
    (x : M × N) :
    (VectorField.mlieBracket (I.prod J)
      (verticalLift (I := I) (J := J) (M := M) Y)
      (verticalLift (I := I) (J := J) (M := M) Z) x).2 =
      VectorField.mlieBracket J Y Z x.2 := by
  let b : Module.Basis (Fin (Module.finrank Real F)) Real F := Module.finBasis Real F
  apply b.ext_elem
  intro i
  let L : F →L[Real] Real := LinearMap.toContinuousLinearMap (b.coord i)
  let coordFun : N → Real := fun y => L (extChartAt J x.2 y)
  have hlocal : ContMDiffOn J (modelWithCornersSelf Real Real) ∞ coordFun
      (chartAt G x.2).source := by
    exact L.contMDiff.contMDiffOn.comp (t := Set.univ)
      (contMDiffOn_extChartAt (I := J) (n := (∞ : WithTop ℕ∞)) (x := x.2))
      (fun y hy => Set.mem_univ (extChartAt J x.2 y))
  obtain ⟨f, hf, hfgerm⟩ := DifferentialGeometry.exists_smooth_germ
    (chartAt G x.2).open_source (mem_chart_source G x.2) hlocal
  have hcoord (v : TangentSpace J x.2) :
      mvfderiv (I := J) f x.2 v = b.coord i v := by
    unfold mvfderiv
    rw [hfgerm.mfderiv_eq (I := J) (I' := modelWithCornersSelf Real Real)]
    exact mvfderiv_chart_coord (I := J) b i x.2 v
  calc
    b.coord i
        (VectorField.mlieBracket (I.prod J)
          (verticalLift (I := I) (J := J) (M := M) Y)
          (verticalLift (I := I) (J := J) (M := M) Z) x).2 =
      mvfderiv (I := J) f x.2
        (VectorField.mlieBracket (I.prod J)
          (verticalLift (I := I) (J := J) (M := M) Y)
          (verticalLift (I := I) (J := J) (M := M) Z) x).2 := by
        exact (hcoord _).symm
    _ = mvfderiv (I := I.prod J) (f ∘ Prod.snd) x
        (VectorField.mlieBracket (I.prod J)
          (verticalLift (I := I) (J := J) (M := M) Y)
          (verticalLift (I := I) (J := J) (M := M) Z) x) := by
        rw [mvfderiv_snd (I := I) (J := J)
          (hf.mdifferentiableAt (by simp))]
    _ = mvfderiv (I := J) f x.2 (VectorField.mlieBracket J Y Z x.2) :=
      mvfderiv_snd_mlieBracket_vertical (I := I) (J := J) (M := M)
        f hf Y Z hY hZ x
    _ = b.coord i (VectorField.mlieBracket J Y Z x.2) := hcoord _

private lemma mlieBracket_vertical
    [T2Space M] [T2Space N]
    (Y Z : (x : N) → TangentSpace J x)
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (hZ : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Z))
    (x : M × N) :
    VectorField.mlieBracket (I.prod J)
      (verticalLift (I := I) (J := J) (M := M) Y)
      (verticalLift (I := I) (J := J) (M := M) Z) x =
      verticalLift (I := I) (J := J) (M := M)
        (VectorField.mlieBracket J Y Z) x := by
  apply Prod.ext
  · apply tangent_eq_zero_of_mvfderiv_eq_zero (J := I) (N := M) (x := x.1)
    intro f hf
    rw [← mvfderiv_fst (I := I) (J := J)
      (hf.mdifferentiableAt (by simp))]
    exact mvfderiv_fst_mlieBracket_vertical (I := I) (J := J)
      f hf Y Z hY hZ x
  · exact mlieBracket_vertical_snd (I := I) (J := J) Y Z hY hZ x

private lemma mvfderiv_fst_mlieBracket_mixed
    (f : M → Real)
    (hf : ContMDiff I (modelWithCornersSelf Real Real) ∞ f)
    (X : (x : M) → TangentSpace I x)
    (Y : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (x : M × N) :
    mvfderiv (I := I.prod J) (f ∘ Prod.fst) x
        (VectorField.mlieBracket (I.prod J)
          (horizontalLift (I := I) (J := J) (N := N) X)
          (verticalLift (I := I) (J := J) (M := M) Y) x) = 0 := by
  let Xsec : ContMDiffSection I E ∞ (TangentSpace I) := ⟨X, hX⟩
  have hXf : ContMDiff I (modelWithCornersSelf Real Real) ∞
      (fun p : M => mvfderiv (I := I) f p (X p)) :=
    DifferentialGeometry.mvfderiv_apply_contMDiff I f hf Xsec
  have htwo : minSmoothness Real 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_cast
  have hleft := DifferentialGeometry.mvfderiv_apply_mlieBracket
    (I := I.prod J)
    (horizontalLift (I := I) (J := J) (N := N) X)
    (verticalLift (I := I) (J := J) (M := M) Y)
    (f ∘ Prod.fst) x
    ((horizontalLift_contMDiff (I := I) (J := J) (N := N) hX).contMDiffAt.of_le htwo)
    ((verticalLift_contMDiff (I := I) (J := J) (M := M) hY).contMDiffAt.of_le htwo)
    ((hf.comp contMDiff_fst).contMDiffAt.of_le htwo)
  have hYeq : (fun p : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.fst) p
        (verticalLift (I := I) (J := J) (M := M) Y p)) = 0 := by
    funext p
    exact mvfderiv_fst_vertical (I := I) (J := J)
      (hf.mdifferentiableAt (by simp)) Y
  have hXeq : (fun p : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.fst) p
        (horizontalLift (I := I) (J := J) (N := N) X p)) =
      (fun p : M × N => mvfderiv (I := I) f p.1 (X p.1)) := by
    funext p
    exact mvfderiv_fst_horizontal (I := I) (J := J) (N := N)
      (hf.mdifferentiableAt (by simp)) X
  rw [hYeq, hXeq] at hleft
  have hzero (v : TangentSpace (I.prod J) x) :
      mvfderiv (I := I.prod J) (0 : M × N → Real) x v = 0 := by
    have hz := mvfderiv_const (I := I.prod J) (M := M × N) (0 : Real) (x := x)
    exact congrArg (fun A => A v) hz
  have hXouter : mvfderiv (I := I.prod J)
      (fun p : M × N => mvfderiv (I := I) f p.1 (X p.1)) x
        (verticalLift (I := I) (J := J) (M := M) Y x) = 0 := by
    simpa only [Function.comp_def] using
      (mvfderiv_fst_vertical (I := I) (J := J)
        (hXf.mdifferentiableAt (by simp)) Y)
  rw [hzero, hXouter, sub_zero] at hleft
  exact hleft

private lemma mvfderiv_snd_mlieBracket_mixed
    (f : N → Real)
    (hf : ContMDiff J (modelWithCornersSelf Real Real) ∞ f)
    (X : (x : M) → TangentSpace I x)
    (Y : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (x : M × N) :
    mvfderiv (I := I.prod J) (f ∘ Prod.snd) x
        (VectorField.mlieBracket (I.prod J)
          (horizontalLift (I := I) (J := J) (N := N) X)
          (verticalLift (I := I) (J := J) (M := M) Y) x) = 0 := by
  let Ysec : ContMDiffSection J F ∞ (TangentSpace J) := ⟨Y, hY⟩
  have hYf : ContMDiff J (modelWithCornersSelf Real Real) ∞
      (fun p : N => mvfderiv (I := J) f p (Y p)) :=
    DifferentialGeometry.mvfderiv_apply_contMDiff J f hf Ysec
  have htwo : minSmoothness Real 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    norm_cast
  have hleft := DifferentialGeometry.mvfderiv_apply_mlieBracket
    (I := I.prod J)
    (horizontalLift (I := I) (J := J) (N := N) X)
    (verticalLift (I := I) (J := J) (M := M) Y)
    (f ∘ Prod.snd) x
    ((horizontalLift_contMDiff (I := I) (J := J) (N := N) hX).contMDiffAt.of_le htwo)
    ((verticalLift_contMDiff (I := I) (J := J) (M := M) hY).contMDiffAt.of_le htwo)
    ((hf.comp contMDiff_snd).contMDiffAt.of_le htwo)
  have hYeq : (fun p : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.snd) p
        (verticalLift (I := I) (J := J) (M := M) Y p)) =
      (fun p : M × N => mvfderiv (I := J) f p.2 (Y p.2)) := by
    funext p
    exact mvfderiv_snd_vertical (I := I) (J := J) (M := M)
      (hf.mdifferentiableAt (by simp)) Y
  have hXeq : (fun p : M × N =>
      mvfderiv (I := I.prod J) (f ∘ Prod.snd) p
        (horizontalLift (I := I) (J := J) (N := N) X p)) = 0 := by
    funext p
    exact mvfderiv_snd_horizontal (I := I) (J := J)
      (hf.mdifferentiableAt (by simp)) X
  rw [hYeq, hXeq] at hleft
  have hYouter : mvfderiv (I := I.prod J)
      (fun p : M × N => mvfderiv (I := J) f p.2 (Y p.2)) x
        (horizontalLift (I := I) (J := J) (N := N) X x) = 0 := by
    simpa only [Function.comp_def] using
      (mvfderiv_snd_horizontal (I := I) (J := J)
        (hYf.mdifferentiableAt (by simp)) X)
  have hzero (v : TangentSpace (I.prod J) x) :
      mvfderiv (I := I.prod J) (0 : M × N → Real) x v = 0 := by
    have hz := mvfderiv_const (I := I.prod J) (M := M × N) (0 : Real) (x := x)
    exact congrArg (fun A => A v) hz
  rw [hYouter, hzero, sub_zero] at hleft
  exact hleft

private lemma mlieBracket_mixed
    [T2Space M] [T2Space N]
    (X : (x : M) → TangentSpace I x)
    (Y : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (x : M × N) :
    VectorField.mlieBracket (I.prod J)
      (horizontalLift (I := I) (J := J) (N := N) X)
      (verticalLift (I := I) (J := J) (M := M) Y) x = 0 := by
  apply Prod.ext
  · apply tangent_eq_zero_of_mvfderiv_eq_zero (J := I) (N := M) (x := x.1)
    intro f hf
    rw [← mvfderiv_fst (I := I) (J := J)
      (hf.mdifferentiableAt (by simp))]
    exact mvfderiv_fst_mlieBracket_mixed (I := I) (J := J)
      f hf X Y hX hY x
  · apply tangent_eq_zero_of_mvfderiv_eq_zero (J := J) (N := N) (x := x.2)
    intro f hf
    rw [← mvfderiv_snd (I := I) (J := J)
      (hf.mdifferentiableAt (by simp))]
    exact mvfderiv_snd_mlieBracket_mixed (I := I) (J := J)
      f hf X Y hX hY x

private lemma prod_inner_horizontal_horizontal
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Y : (x : M) → TangentSpace I x) (x : M × N) :
    (g.prod h).inner x
        (horizontalLift (I := I) (J := J) (N := N) X x)
        (horizontalLift (I := I) (J := J) (N := N) Y x) =
      g.inner x.1 (X x.1) (Y x.1) := by
  have hfstX : mfderiv (I.prod J) I Prod.fst x
      (horizontalLift (I := I) (J := J) (N := N) X x) = X x.1 := by
    rw [mfderiv_fst]
    rfl
  have hfstY : mfderiv (I.prod J) I Prod.fst x
      (horizontalLift (I := I) (J := J) (N := N) Y x) = Y x.1 := by
    rw [mfderiv_fst]
    rfl
  have hsndX : mfderiv (I.prod J) J Prod.snd x
      (horizontalLift (I := I) (J := J) (N := N) X x) = 0 := by
    rw [mfderiv_snd]
    rfl
  have hsndY : mfderiv (I.prod J) J Prod.snd x
      (horizontalLift (I := I) (J := J) (N := N) Y x) = 0 := by
    rw [mfderiv_snd]
    rfl
  rw [SmoothRiemannianMetric.prod_inner]
  rw [hfstX, hfstY, hsndX, hsndY]
  simp

private lemma prod_inner_vertical_vertical
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Y Z : (x : N) → TangentSpace J x) (x : M × N) :
    (g.prod h).inner x
        (verticalLift (I := I) (J := J) (M := M) Y x)
        (verticalLift (I := I) (J := J) (M := M) Z x) =
      h.inner x.2 (Y x.2) (Z x.2) := by
  have hfstY : mfderiv (I.prod J) I Prod.fst x
      (verticalLift (I := I) (J := J) (M := M) Y x) = 0 := by
    rw [mfderiv_fst]
    rfl
  have hfstZ : mfderiv (I.prod J) I Prod.fst x
      (verticalLift (I := I) (J := J) (M := M) Z x) = 0 := by
    rw [mfderiv_fst]
    rfl
  have hsndY : mfderiv (I.prod J) J Prod.snd x
      (verticalLift (I := I) (J := J) (M := M) Y x) = Y x.2 := by
    rw [mfderiv_snd]
    rfl
  have hsndZ : mfderiv (I.prod J) J Prod.snd x
      (verticalLift (I := I) (J := J) (M := M) Z x) = Z x.2 := by
    rw [mfderiv_snd]
    rfl
  rw [SmoothRiemannianMetric.prod_inner]
  rw [hfstY, hfstZ, hsndY, hsndZ]
  simp

private lemma prod_inner_horizontal_vertical
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X : (x : M) → TangentSpace I x) (Y : (x : N) → TangentSpace J x)
    (x : M × N) :
    (g.prod h).inner x
        (horizontalLift (I := I) (J := J) (N := N) X x)
      (verticalLift (I := I) (J := J) (M := M) Y x) = 0 := by
  have hfstX : mfderiv (I.prod J) I Prod.fst x
      (horizontalLift (I := I) (J := J) (N := N) X x) = X x.1 := by
    rw [mfderiv_fst]
    rfl
  have hfstY : mfderiv (I.prod J) I Prod.fst x
      (verticalLift (I := I) (J := J) (M := M) Y x) = 0 := by
    rw [mfderiv_fst]
    rfl
  have hsndX : mfderiv (I.prod J) J Prod.snd x
      (horizontalLift (I := I) (J := J) (N := N) X x) = 0 := by
    rw [mfderiv_snd]
    rfl
  have hsndY : mfderiv (I.prod J) J Prod.snd x
      (verticalLift (I := I) (J := J) (M := M) Y x) = Y x.2 := by
    rw [mfderiv_snd]
    rfl
  rw [SmoothRiemannianMetric.prod_inner]
  rw [hfstX, hfstY, hsndX, hsndY]
  simp

private lemma prod_inner_vertical_horizontal
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X : (x : M) → TangentSpace I x) (Y : (x : N) → TangentSpace J x)
    (x : M × N) :
    (g.prod h).inner x
        (verticalLift (I := I) (J := J) (M := M) Y x)
        (horizontalLift (I := I) (J := J) (N := N) X x) = 0 := by
  rw [(g.prod h).symm]
  exact prod_inner_horizontal_vertical (I := I) (J := J) g h X Y x

omit [FiniteDimensional Real E] in
private lemma metric_inner_contMDiff
    (g : SmoothRiemannianMetric I M)
    {X Y : (x : M) → TangentSpace I x}
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Y)) :
    ContMDiff I (modelWithCornersSelf Real Real) ∞
      (fun x : M => g.inner x (X x) (Y x)) := by
  have happ : ContMDiff I (I.prod (modelWithCornersSelf Real Real)) ∞
      (fun x : M => (⟨x, g.inner x (X x) (Y x)⟩ :
        TotalSpace Real (Bundle.Trivial M Real))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := Real)
      (b := id) g.contMDiff hX hY
  intro x
  have hx := happ x
  rw [Bundle.contMDiffAt_totalSpace] at hx
  exact hx.2

private lemma koszulScalar_horizontal
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Y Z : (x : M) → TangentSpace I x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Z))
    (x : M × N) :
    Connection.koszulScalar (I := I.prod J) (g.prod h)
        (horizontalLift (I := I) (J := J) (N := N) X)
        (horizontalLift (I := I) (J := J) (N := N) Y)
        (horizontalLift (I := I) (J := J) (N := N) Z) x =
      Connection.koszulScalar (I := I) g X Y Z x.1 := by
  have hYZ := metric_inner_contMDiff (I := I) g hY hZ
  have hZX := metric_inner_contMDiff (I := I) g hZ hX
  have hXY := metric_inner_contMDiff (I := I) g hX hY
  unfold Connection.koszulScalar Connection.directionalDerivAlong
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (horizontalLift (I := I) (J := J) (N := N) Y p)
        (horizontalLift (I := I) (J := J) (N := N) Z p)) =
      (fun q : M => g.inner q (Y q) (Z q)) ∘ Prod.fst by
        funext p
        exact prod_inner_horizontal_horizontal (I := I) (J := J) g h Y Z p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (horizontalLift (I := I) (J := J) (N := N) Z p)
        (horizontalLift (I := I) (J := J) (N := N) X p)) =
      (fun q : M => g.inner q (Z q) (X q)) ∘ Prod.fst by
        funext p
        exact prod_inner_horizontal_horizontal (I := I) (J := J) g h Z X p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (horizontalLift (I := I) (J := J) (N := N) X p)
        (horizontalLift (I := I) (J := J) (N := N) Y p)) =
      (fun q : M => g.inner q (X q) (Y q)) ∘ Prod.fst by
        funext p
        exact prod_inner_horizontal_horizontal (I := I) (J := J) g h X Y p]
  rw [mvfderiv_fst_horizontal (I := I) (J := J) (N := N)
    (hYZ.mdifferentiableAt (by simp)) X]
  rw [mvfderiv_fst_horizontal (I := I) (J := J) (N := N)
    (hZX.mdifferentiableAt (by simp)) Y]
  rw [mvfderiv_fst_horizontal (I := I) (J := J) (N := N)
    (hXY.mdifferentiableAt (by simp)) Z]
  rw [mlieBracket_horizontal (I := I) (J := J) Y Z hY hZ x]
  rw [mlieBracket_horizontal (I := I) (J := J) Z X hZ hX x]
  rw [mlieBracket_horizontal (I := I) (J := J) X Y hX hY x]
  rw [prod_inner_horizontal_horizontal, prod_inner_horizontal_horizontal,
    prod_inner_horizontal_horizontal]

private lemma koszulScalar_horizontal_horizontal_vertical
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Y : (x : M) → TangentSpace I x) (Z : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Y))
    (hZ : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Z))
    (x : M × N) :
    Connection.koszulScalar (I := I.prod J) (g.prod h)
        (horizontalLift (I := I) (J := J) (N := N) X)
        (horizontalLift (I := I) (J := J) (N := N) Y)
        (verticalLift (I := I) (J := J) (M := M) Z) x = 0 := by
  have hXY := metric_inner_contMDiff (I := I) g hX hY
  have hzero (v : TangentSpace (I.prod J) x) :
      mvfderiv (I := I.prod J) (0 : M × N → Real) x v = 0 := by
    have hz := mvfderiv_const (I := I.prod J) (M := M × N) (0 : Real) (x := x)
    exact congrArg (fun A => A v) hz
  unfold Connection.koszulScalar Connection.directionalDerivAlong
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (horizontalLift (I := I) (J := J) (N := N) Y p)
        (verticalLift (I := I) (J := J) (M := M) Z p)) = 0 by
        funext p
        exact prod_inner_horizontal_vertical (I := I) (J := J) g h Y Z p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (verticalLift (I := I) (J := J) (M := M) Z p)
        (horizontalLift (I := I) (J := J) (N := N) X p)) = 0 by
        funext p
        exact prod_inner_vertical_horizontal (I := I) (J := J) g h X Z p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (horizontalLift (I := I) (J := J) (N := N) X p)
        (horizontalLift (I := I) (J := J) (N := N) Y p)) =
      (fun q : M => g.inner q (X q) (Y q)) ∘ Prod.fst by
        funext p
        exact prod_inner_horizontal_horizontal (I := I) (J := J) g h X Y p]
  rw [hzero, hzero]
  rw [mvfderiv_fst_vertical (I := I) (J := J)
    (hXY.mdifferentiableAt (by simp)) Z]
  rw [mlieBracket_mixed (I := I) (J := J) Y Z hY hZ x]
  rw [VectorField.mlieBracket_swap_apply]
  rw [mlieBracket_mixed (I := I) (J := J) X Z hX hZ x]
  rw [mlieBracket_horizontal (I := I) (J := J) X Y hX hY x]
  rw [prod_inner_vertical_horizontal (I := I) (J := J) g h
    (VectorField.mlieBracket I X Y) Z x]
  simp only [map_zero, neg_zero, sub_zero, add_zero]

private lemma koszulScalar_horizontal_vertical_horizontal
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Z : (x : M) → TangentSpace I x) (Y : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Z))
    (x : M × N) :
    Connection.koszulScalar (I := I.prod J) (g.prod h)
        (horizontalLift (I := I) (J := J) (N := N) X)
        (verticalLift (I := I) (J := J) (M := M) Y)
        (horizontalLift (I := I) (J := J) (N := N) Z) x = 0 := by
  have hZX := metric_inner_contMDiff (I := I) g hZ hX
  have hzero (v : TangentSpace (I.prod J) x) :
      mvfderiv (I := I.prod J) (0 : M × N → Real) x v = 0 := by
    have hz := mvfderiv_const (I := I.prod J) (M := M × N) (0 : Real) (x := x)
    exact congrArg (fun A => A v) hz
  unfold Connection.koszulScalar Connection.directionalDerivAlong
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (verticalLift (I := I) (J := J) (M := M) Y p)
        (horizontalLift (I := I) (J := J) (N := N) Z p)) = 0 by
        funext p
        exact prod_inner_vertical_horizontal (I := I) (J := J) g h Z Y p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (horizontalLift (I := I) (J := J) (N := N) Z p)
        (horizontalLift (I := I) (J := J) (N := N) X p)) =
      (fun q : M => g.inner q (Z q) (X q)) ∘ Prod.fst by
        funext p
        exact prod_inner_horizontal_horizontal (I := I) (J := J) g h Z X p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (horizontalLift (I := I) (J := J) (N := N) X p)
        (verticalLift (I := I) (J := J) (M := M) Y p)) = 0 by
        funext p
        exact prod_inner_horizontal_vertical (I := I) (J := J) g h X Y p]
  rw [hzero]
  rw [mvfderiv_fst_vertical (I := I) (J := J)
    (hZX.mdifferentiableAt (by simp)) Y]
  rw [hzero]
  rw [VectorField.mlieBracket_swap_apply]
  rw [mlieBracket_mixed (I := I) (J := J) Z Y hZ hY x]
  rw [mlieBracket_horizontal (I := I) (J := J) Z X hZ hX x]
  rw [mlieBracket_mixed (I := I) (J := J) X Y hX hY x]
  rw [prod_inner_vertical_horizontal (I := I) (J := J) g h
    (VectorField.mlieBracket I Z X) Y x]
  simp only [map_zero, neg_zero, sub_zero, add_zero]

private lemma koszulScalar_horizontal_vertical_vertical
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X : (x : M) → TangentSpace I x) (Y Z : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (hZ : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Z))
    (x : M × N) :
    Connection.koszulScalar (I := I.prod J) (g.prod h)
        (horizontalLift (I := I) (J := J) (N := N) X)
        (verticalLift (I := I) (J := J) (M := M) Y)
        (verticalLift (I := I) (J := J) (M := M) Z) x = 0 := by
  have hYZ := metric_inner_contMDiff (I := J) h hY hZ
  have hzero (v : TangentSpace (I.prod J) x) :
      mvfderiv (I := I.prod J) (0 : M × N → Real) x v = 0 := by
    have hz := mvfderiv_const (I := I.prod J) (M := M × N) (0 : Real) (x := x)
    exact congrArg (fun A => A v) hz
  unfold Connection.koszulScalar Connection.directionalDerivAlong
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (verticalLift (I := I) (J := J) (M := M) Y p)
        (verticalLift (I := I) (J := J) (M := M) Z p)) =
      (fun q : N => h.inner q (Y q) (Z q)) ∘ Prod.snd by
        funext p
        exact prod_inner_vertical_vertical (I := I) (J := J) g h Y Z p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (verticalLift (I := I) (J := J) (M := M) Z p)
        (horizontalLift (I := I) (J := J) (N := N) X p)) = 0 by
        funext p
        exact prod_inner_vertical_horizontal (I := I) (J := J) g h X Z p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (horizontalLift (I := I) (J := J) (N := N) X p)
        (verticalLift (I := I) (J := J) (M := M) Y p)) = 0 by
        funext p
        exact prod_inner_horizontal_vertical (I := I) (J := J) g h X Y p]
  rw [mvfderiv_snd_horizontal (I := I) (J := J)
    (hYZ.mdifferentiableAt (by simp)) X]
  rw [hzero, hzero]
  rw [mlieBracket_vertical (I := I) (J := J) Y Z hY hZ x]
  rw [VectorField.mlieBracket_swap_apply]
  rw [mlieBracket_mixed (I := I) (J := J) X Z hX hZ x]
  rw [mlieBracket_mixed (I := I) (J := J) X Y hX hY x]
  rw [prod_inner_horizontal_vertical (I := I) (J := J) g h X
    (VectorField.mlieBracket J Y Z) x]
  simp only [map_zero, neg_zero, sub_zero, add_zero]

private lemma koszulScalar_vertical
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Y Z : (x : N) → TangentSpace J x)
    (hX : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% X))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (hZ : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Z))
    (x : M × N) :
    Connection.koszulScalar (I := I.prod J) (g.prod h)
        (verticalLift (I := I) (J := J) (M := M) X)
        (verticalLift (I := I) (J := J) (M := M) Y)
        (verticalLift (I := I) (J := J) (M := M) Z) x =
      Connection.koszulScalar (I := J) h X Y Z x.2 := by
  have hYZ := metric_inner_contMDiff (I := J) h hY hZ
  have hZX := metric_inner_contMDiff (I := J) h hZ hX
  have hXY := metric_inner_contMDiff (I := J) h hX hY
  unfold Connection.koszulScalar Connection.directionalDerivAlong
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (verticalLift (I := I) (J := J) (M := M) Y p)
        (verticalLift (I := I) (J := J) (M := M) Z p)) =
      (fun q : N => h.inner q (Y q) (Z q)) ∘ Prod.snd by
        funext p
        exact prod_inner_vertical_vertical (I := I) (J := J) g h Y Z p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (verticalLift (I := I) (J := J) (M := M) Z p)
        (verticalLift (I := I) (J := J) (M := M) X p)) =
      (fun q : N => h.inner q (Z q) (X q)) ∘ Prod.snd by
        funext p
        exact prod_inner_vertical_vertical (I := I) (J := J) g h Z X p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (verticalLift (I := I) (J := J) (M := M) X p)
        (verticalLift (I := I) (J := J) (M := M) Y p)) =
      (fun q : N => h.inner q (X q) (Y q)) ∘ Prod.snd by
        funext p
        exact prod_inner_vertical_vertical (I := I) (J := J) g h X Y p]
  rw [mvfderiv_snd_vertical (I := I) (J := J) (M := M)
    (hYZ.mdifferentiableAt (by simp)) X]
  rw [mvfderiv_snd_vertical (I := I) (J := J) (M := M)
    (hZX.mdifferentiableAt (by simp)) Y]
  rw [mvfderiv_snd_vertical (I := I) (J := J) (M := M)
    (hXY.mdifferentiableAt (by simp)) Z]
  rw [mlieBracket_vertical (I := I) (J := J) Y Z hY hZ x]
  rw [mlieBracket_vertical (I := I) (J := J) Z X hZ hX x]
  rw [mlieBracket_vertical (I := I) (J := J) X Y hX hY x]
  rw [prod_inner_vertical_vertical, prod_inner_vertical_vertical,
    prod_inner_vertical_vertical]

private lemma koszulScalar_vertical_vertical_horizontal
    [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X : (x : M) → TangentSpace I x) (Y Z : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (hZ : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Z))
    (x : M × N) :
    Connection.koszulScalar (I := I.prod J) (g.prod h)
        (verticalLift (I := I) (J := J) (M := M) Y)
        (verticalLift (I := I) (J := J) (M := M) Z)
        (horizontalLift (I := I) (J := J) (N := N) X) x = 0 := by
  have hYZ := metric_inner_contMDiff (I := J) h hY hZ
  have hzero (v : TangentSpace (I.prod J) x) :
      mvfderiv (I := I.prod J) (0 : M × N → Real) x v = 0 := by
    have hz := mvfderiv_const (I := I.prod J) (M := M × N) (0 : Real) (x := x)
    exact congrArg (fun A => A v) hz
  unfold Connection.koszulScalar Connection.directionalDerivAlong
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (verticalLift (I := I) (J := J) (M := M) Z p)
        (horizontalLift (I := I) (J := J) (N := N) X p)) = 0 by
        funext p
        exact prod_inner_vertical_horizontal (I := I) (J := J) g h X Z p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (horizontalLift (I := I) (J := J) (N := N) X p)
        (verticalLift (I := I) (J := J) (M := M) Y p)) = 0 by
        funext p
        exact prod_inner_horizontal_vertical (I := I) (J := J) g h X Y p]
  rw [show (fun p : M × N =>
      (g.prod h).inner p
        (verticalLift (I := I) (J := J) (M := M) Y p)
        (verticalLift (I := I) (J := J) (M := M) Z p)) =
      (fun q : N => h.inner q (Y q) (Z q)) ∘ Prod.snd by
        funext p
        exact prod_inner_vertical_vertical (I := I) (J := J) g h Y Z p]
  rw [hzero, hzero]
  rw [mvfderiv_snd_horizontal (I := I) (J := J)
    (hYZ.mdifferentiableAt (by simp)) X]
  rw [VectorField.mlieBracket_swap_apply]
  rw [mlieBracket_mixed (I := I) (J := J) X Z hX hZ x]
  rw [mlieBracket_mixed (I := I) (J := J) X Y hX hY x]
  rw [mlieBracket_vertical (I := I) (J := J) Y Z hY hZ x]
  rw [prod_inner_horizontal_vertical (I := I) (J := J) g h X
    (VectorField.mlieBracket J Y Z) x]
  simp only [map_zero, neg_zero, sub_zero, add_zero]

private lemma prod_inner_right_horizontal
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {x : M × N}
    (v : TangentSpace (I.prod J) x)
    (Z : (x : M) → TangentSpace I x) :
    (g.prod h).inner x v
        (horizontalLift (I := I) (J := J) (N := N) Z x) =
      g.inner x.1 v.1 (Z x.1) := by
  have hfstV : mfderiv (I.prod J) I Prod.fst x v = v.1 := by
    rw [mfderiv_fst]
    rfl
  have hsndV : mfderiv (I.prod J) J Prod.snd x v = v.2 := by
    rw [mfderiv_snd]
    rfl
  have hfstZ : mfderiv (I.prod J) I Prod.fst x
      (horizontalLift (I := I) (J := J) (N := N) Z x) = Z x.1 := by
    rw [mfderiv_fst]
    rfl
  have hsndZ : mfderiv (I.prod J) J Prod.snd x
      (horizontalLift (I := I) (J := J) (N := N) Z x) = 0 := by
    rw [mfderiv_snd]
    rfl
  rw [SmoothRiemannianMetric.prod_inner, hfstV, hsndV, hfstZ, hsndZ]
  simp

private lemma prod_inner_right_vertical
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {x : M × N}
    (v : TangentSpace (I.prod J) x)
    (Z : (x : N) → TangentSpace J x) :
    (g.prod h).inner x v
        (verticalLift (I := I) (J := J) (M := M) Z x) =
      h.inner x.2 v.2 (Z x.2) := by
  have hfstV : mfderiv (I.prod J) I Prod.fst x v = v.1 := by
    rw [mfderiv_fst]
    rfl
  have hsndV : mfderiv (I.prod J) J Prod.snd x v = v.2 := by
    rw [mfderiv_snd]
    rfl
  have hfstZ : mfderiv (I.prod J) I Prod.fst x
      (verticalLift (I := I) (J := J) (M := M) Z x) = 0 := by
    rw [mfderiv_fst]
    rfl
  have hsndZ : mfderiv (I.prod J) J Prod.snd x
      (verticalLift (I := I) (J := J) (M := M) Z x) = Z x.2 := by
    rw [mfderiv_snd]
    rfl
  rw [SmoothRiemannianMetric.prod_inner, hfstV, hsndV, hfstZ, hsndZ]
  simp

private lemma leviCivita_horizontal
    [CompleteSpace E] [CompleteSpace F] [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Y : (x : M) → TangentSpace I x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Y))
    (x : M × N) :
    (Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).toFun
        (horizontalLift (I := I) (J := J) (N := N) Y) x
        (horizontalLift (I := I) (J := J) (N := N) X x) =
      horizontalLift (I := I) (J := J) (N := N)
        (fun q : M =>
          (Connection.leviCivitaConnectionOfMetric (I := I) g).toFun Y q (X q)) x := by
  have hXprod := horizontalLift_contMDiff (I := I) (J := J) (N := N) hX
  have hYprod := horizontalLift_contMDiff (I := I) (J := J) (N := N) hY
  apply Prod.ext
  · apply DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_injective (I := I) g x.1
    ext z
    obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x.1 z
    have hZprod := horizontalLift_contMDiff (I := I) (J := J) (N := N) Z.contMDiff
    have hprod :=
      Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
        (I := I.prod J) (g.prod h)
        (horizontalLift (I := I) (J := J) (N := N) X)
        (horizontalLift (I := I) (J := J) (N := N) Y)
        (horizontalLift (I := I) (J := J) (N := N) Z) x
        (hXprod.contMDiffAt.mdifferentiableAt (by simp))
        (hYprod.contMDiffAt.mdifferentiableAt (by simp))
        (hZprod.contMDiffAt.mdifferentiableAt (by simp))
    rw [prod_inner_right_horizontal (I := I) (J := J)] at hprod
    rw [koszulScalar_horizontal (I := I) (J := J) g h X Y Z
      hX hY Z.contMDiff x] at hprod
    rw [hZx] at hprod
    have hfactor :=
      Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
        (I := I) g X Y Z x.1
        (hX.contMDiffAt.mdifferentiableAt (by simp))
        (hY.contMDiffAt.mdifferentiableAt (by simp))
        (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    rw [hZx] at hfactor
    exact hprod.trans hfactor.symm
  · change
      ((Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).toFun
        (horizontalLift (I := I) (J := J) (N := N) Y) x
        (horizontalLift (I := I) (J := J) (N := N) X x)).2 = 0
    apply DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_injective (I := J) h x.2
    ext z
    change h.inner x.2
      ((Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).toFun
        (horizontalLift (I := I) (J := J) (N := N) Y) x
        (horizontalLift (I := I) (J := J) (N := N) X x)).2 z =
      h.inner x.2 0 z
    obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at
      (I := J) (F := F) (V := TangentSpace J) (n := (⊤ : ℕ∞)) x.2 z
    have hZprod := verticalLift_contMDiff (I := I) (J := J) (M := M) Z.contMDiff
    have hprod :=
      Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
        (I := I.prod J) (g.prod h)
        (horizontalLift (I := I) (J := J) (N := N) X)
        (horizontalLift (I := I) (J := J) (N := N) Y)
        (verticalLift (I := I) (J := J) (M := M) Z) x
        (hXprod.contMDiffAt.mdifferentiableAt (by simp))
        (hYprod.contMDiffAt.mdifferentiableAt (by simp))
        (hZprod.contMDiffAt.mdifferentiableAt (by simp))
    rw [prod_inner_right_vertical (I := I) (J := J)] at hprod
    rw [koszulScalar_horizontal_horizontal_vertical (I := I) (J := J)
      g h X Y Z hX hY Z.contMDiff x] at hprod
    rw [hZx] at hprod
    simpa using hprod

private lemma leviCivita_vertical
    [CompleteSpace E] [CompleteSpace F] [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Y : (x : N) → TangentSpace J x)
    (hX : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% X))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (x : M × N) :
    (Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).toFun
        (verticalLift (I := I) (J := J) (M := M) Y) x
        (verticalLift (I := I) (J := J) (M := M) X x) =
      verticalLift (I := I) (J := J) (M := M)
        (fun q : N =>
          (Connection.leviCivitaConnectionOfMetric (I := J) h).toFun Y q (X q)) x := by
  have hXprod := verticalLift_contMDiff (I := I) (J := J) (M := M) hX
  have hYprod := verticalLift_contMDiff (I := I) (J := J) (M := M) hY
  apply Prod.ext
  · change
      ((Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).toFun
        (verticalLift (I := I) (J := J) (M := M) Y) x
        (verticalLift (I := I) (J := J) (M := M) X x)).1 = 0
    apply DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_injective (I := I) g x.1
    ext z
    change g.inner x.1
      ((Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).toFun
        (verticalLift (I := I) (J := J) (M := M) Y) x
        (verticalLift (I := I) (J := J) (M := M) X x)).1 z =
      g.inner x.1 0 z
    obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x.1 z
    have hZprod := horizontalLift_contMDiff (I := I) (J := J) (N := N) Z.contMDiff
    have hprod :=
      Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
        (I := I.prod J) (g.prod h)
        (verticalLift (I := I) (J := J) (M := M) X)
        (verticalLift (I := I) (J := J) (M := M) Y)
        (horizontalLift (I := I) (J := J) (N := N) Z) x
        (hXprod.contMDiffAt.mdifferentiableAt (by simp))
        (hYprod.contMDiffAt.mdifferentiableAt (by simp))
        (hZprod.contMDiffAt.mdifferentiableAt (by simp))
    rw [prod_inner_right_horizontal (I := I) (J := J)] at hprod
    rw [koszulScalar_vertical_vertical_horizontal (I := I) (J := J)
      g h Z X Y Z.contMDiff hX hY x] at hprod
    rw [hZx] at hprod
    simpa using hprod
  · apply DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_injective (I := J) h x.2
    ext z
    obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at
      (I := J) (F := F) (V := TangentSpace J) (n := (⊤ : ℕ∞)) x.2 z
    have hZprod := verticalLift_contMDiff (I := I) (J := J) (M := M) Z.contMDiff
    have hprod :=
      Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
        (I := I.prod J) (g.prod h)
        (verticalLift (I := I) (J := J) (M := M) X)
        (verticalLift (I := I) (J := J) (M := M) Y)
        (verticalLift (I := I) (J := J) (M := M) Z) x
        (hXprod.contMDiffAt.mdifferentiableAt (by simp))
        (hYprod.contMDiffAt.mdifferentiableAt (by simp))
        (hZprod.contMDiffAt.mdifferentiableAt (by simp))
    rw [prod_inner_right_vertical (I := I) (J := J)] at hprod
    rw [koszulScalar_vertical (I := I) (J := J) g h X Y Z
      hX hY Z.contMDiff x] at hprod
    rw [hZx] at hprod
    have hfactor :=
      Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
        (I := J) h X Y Z x.2
        (hX.contMDiffAt.mdifferentiableAt (by simp))
        (hY.contMDiffAt.mdifferentiableAt (by simp))
        (Z.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    rw [hZx] at hfactor
    exact hprod.trans hfactor.symm

private lemma leviCivita_horizontal_vertical
    [CompleteSpace E] [CompleteSpace F] [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X : (x : M) → TangentSpace I x) (Y : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (x : M × N) :
    (Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).toFun
        (verticalLift (I := I) (J := J) (M := M) Y) x
        (horizontalLift (I := I) (J := J) (N := N) X x) = 0 := by
  have hXprod := horizontalLift_contMDiff (I := I) (J := J) (N := N) hX
  have hYprod := verticalLift_contMDiff (I := I) (J := J) (M := M) hY
  apply Prod.ext
  · apply DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_injective (I := I) g x.1
    ext z
    change g.inner x.1
      ((Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).toFun
        (verticalLift (I := I) (J := J) (M := M) Y) x
        (horizontalLift (I := I) (J := J) (N := N) X x)).1 z =
      g.inner x.1 0 z
    obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x.1 z
    have hZprod := horizontalLift_contMDiff (I := I) (J := J) (N := N) Z.contMDiff
    have hprod :=
      Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
        (I := I.prod J) (g.prod h)
        (horizontalLift (I := I) (J := J) (N := N) X)
        (verticalLift (I := I) (J := J) (M := M) Y)
        (horizontalLift (I := I) (J := J) (N := N) Z) x
        (hXprod.contMDiffAt.mdifferentiableAt (by simp))
        (hYprod.contMDiffAt.mdifferentiableAt (by simp))
        (hZprod.contMDiffAt.mdifferentiableAt (by simp))
    rw [prod_inner_right_horizontal (I := I) (J := J)] at hprod
    rw [koszulScalar_horizontal_vertical_horizontal (I := I) (J := J)
      g h X Z Y hX hY Z.contMDiff x] at hprod
    rw [hZx] at hprod
    simpa using hprod
  · apply DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_injective (I := J) h x.2
    ext z
    change h.inner x.2
      ((Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).toFun
        (verticalLift (I := I) (J := J) (M := M) Y) x
        (horizontalLift (I := I) (J := J) (N := N) X x)).2 z =
      h.inner x.2 0 z
    obtain ⟨Z, hZx⟩ := ContMDiffSection.exists_eq_at
      (I := J) (F := F) (V := TangentSpace J) (n := (⊤ : ℕ∞)) x.2 z
    have hZprod := verticalLift_contMDiff (I := I) (J := J) (M := M) Z.contMDiff
    have hprod :=
      Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
        (I := I.prod J) (g.prod h)
        (horizontalLift (I := I) (J := J) (N := N) X)
        (verticalLift (I := I) (J := J) (M := M) Y)
        (verticalLift (I := I) (J := J) (M := M) Z) x
        (hXprod.contMDiffAt.mdifferentiableAt (by simp))
        (hYprod.contMDiffAt.mdifferentiableAt (by simp))
        (hZprod.contMDiffAt.mdifferentiableAt (by simp))
    rw [prod_inner_right_vertical (I := I) (J := J)] at hprod
    rw [koszulScalar_horizontal_vertical_vertical (I := I) (J := J)
      g h X Y Z hX hY Z.contMDiff x] at hprod
    rw [hZx] at hprod
    simpa using hprod

private lemma leviCivita_vertical_horizontal
    [CompleteSpace E] [CompleteSpace F] [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X : (x : M) → TangentSpace I x) (Y : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (x : M × N) :
    (Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).toFun
        (horizontalLift (I := I) (J := J) (N := N) X) x
        (verticalLift (I := I) (J := J) (M := M) Y x) = 0 := by
  have hXprod := horizontalLift_contMDiff (I := I) (J := J) (N := N) hX
  have hYprod := verticalLift_contMDiff (I := I) (J := J) (M := M) hY
  have htor :
      (Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).torsion = 0 := by
    funext p
    exact Connection.leviCivitaConnectionOfMetric_isTorsionFree
      (I := I.prod J) (g.prod h) p
  have ht :=
    (CovariantDerivative.torsion_eq_zero_iff
      (cov := Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h))).mp
      htor
      (X := verticalLift (I := I) (J := J) (M := M) Y)
      (Y := horizontalLift (I := I) (J := J) (N := N) X)
      (x := x)
      (hYprod.contMDiffAt.mdifferentiableAt (by simp))
      (hXprod.contMDiffAt.mdifferentiableAt (by simp))
  rw [leviCivita_horizontal_vertical (I := I) (J := J) g h X Y hX hY x] at ht
  rw [VectorField.mlieBracket_swap_apply] at ht
  rw [mlieBracket_mixed (I := I) (J := J) X Y hX hY x] at ht
  simpa using ht

private lemma leviCivita_covApply_contMDiff
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M)
    {X Y : (x : M) → TangentSpace I x}
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Y)) :
    ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞
      (T% (Curvature.covApply
        (Connection.leviCivitaConnectionOfMetric (I := I) g) X Y)) := by
  rw [← contMDiffOn_univ]
  refine Curvature.covApply_contMDiffOn
    (cov := Connection.leviCivitaConnectionOfMetric (I := I) g)
    (hcov := Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivative
      (I := I) g) hX ?_
  simpa only [ENat.coe_top_add_one] using hY

private lemma riemannSec_horizontal
    [CompleteSpace E] [CompleteSpace F] [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Y Z : (x : M) → TangentSpace I x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Z))
    (x : M × N) :
    Curvature.riemannSec
        (Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h))
        (horizontalLift (I := I) (J := J) (N := N) X)
        (horizontalLift (I := I) (J := J) (N := N) Y)
        (horizontalLift (I := I) (J := J) (N := N) Z) x =
      horizontalLift (I := I) (J := J) (N := N)
        (fun q : M => Curvature.riemannSec
          (Connection.leviCivitaConnectionOfMetric (I := I) g) X Y Z q) x := by
  let covProd := Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)
  let covFactor := Connection.leviCivitaConnectionOfMetric (I := I) g
  have hYZ := leviCivita_covApply_contMDiff (I := I) g hY hZ
  have hXZ := leviCivita_covApply_contMDiff (I := I) g hX hZ
  have hcovYZ : Curvature.covApply covProd
      (horizontalLift (I := I) (J := J) (N := N) Y)
      (horizontalLift (I := I) (J := J) (N := N) Z) =
      horizontalLift (I := I) (J := J) (N := N)
        (Curvature.covApply covFactor Y Z) := by
    funext p
    exact leviCivita_horizontal (I := I) (J := J) g h Y Z hY hZ p
  have hcovXZ : Curvature.covApply covProd
      (horizontalLift (I := I) (J := J) (N := N) X)
      (horizontalLift (I := I) (J := J) (N := N) Z) =
      horizontalLift (I := I) (J := J) (N := N)
        (Curvature.covApply covFactor X Z) := by
    funext p
    exact leviCivita_horizontal (I := I) (J := J) g h X Z hX hZ p
  have hfirst : covProd.toFun
      (Curvature.covApply covProd
        (horizontalLift (I := I) (J := J) (N := N) Y)
        (horizontalLift (I := I) (J := J) (N := N) Z)) x
      (horizontalLift (I := I) (J := J) (N := N) X x) =
      horizontalLift (I := I) (J := J) (N := N)
        (fun q : M => covFactor.toFun
          (Curvature.covApply covFactor Y Z) q (X q)) x := by
    rw [hcovYZ]
    exact leviCivita_horizontal (I := I) (J := J) g h X
      (Curvature.covApply covFactor Y Z) hX hYZ x
  have hsecond : covProd.toFun
      (Curvature.covApply covProd
        (horizontalLift (I := I) (J := J) (N := N) X)
        (horizontalLift (I := I) (J := J) (N := N) Z)) x
      (horizontalLift (I := I) (J := J) (N := N) Y x) =
      horizontalLift (I := I) (J := J) (N := N)
        (fun q : M => covFactor.toFun
          (Curvature.covApply covFactor X Z) q (Y q)) x := by
    rw [hcovXZ]
    exact leviCivita_horizontal (I := I) (J := J) g h Y
      (Curvature.covApply covFactor X Z) hY hXZ x
  obtain ⟨W, hWx⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x.1
      (VectorField.mlieBracket I X Y x.1)
  have hthird : covProd.toFun
      (horizontalLift (I := I) (J := J) (N := N) Z) x
      (VectorField.mlieBracket (I.prod J)
        (horizontalLift (I := I) (J := J) (N := N) X)
        (horizontalLift (I := I) (J := J) (N := N) Y) x) =
      horizontalLift (I := I) (J := J) (N := N)
        (fun q : M => covFactor.toFun Z q (W q)) x := by
    rw [mlieBracket_horizontal (I := I) (J := J) X Y hX hY x]
    have hLift : horizontalLift (I := I) (J := J) (N := N) W x =
        horizontalLift (I := I) (J := J) (N := N)
          (VectorField.mlieBracket I X Y) x := by
      unfold horizontalLift
      rw [hWx]
    rw [← hLift]
    exact leviCivita_horizontal (I := I) (J := J) g h W Z W.contMDiff hZ x
  rw [Curvature.riemannSec_def, hfirst, hsecond, hthird]
  unfold Curvature.riemannSec
  have hthirdFactor : covFactor.toFun Z x.1 (W x.1) =
      covFactor.toFun Z x.1 (VectorField.mlieBracket I X Y x.1) := by
    rw [hWx]
  have hthirdLift : horizontalLift (I := I) (J := J) (N := N)
      (fun q : M => covFactor.toFun Z q (W q)) x =
      horizontalLift (I := I) (J := J) (N := N)
        (fun q : M => covFactor.toFun Z q (VectorField.mlieBracket I X Y q)) x := by
    apply Prod.ext
    · exact hthirdFactor
    · rfl
  rw [hthirdLift]
  apply Prod.ext
  · change
      covFactor.toFun (Curvature.covApply covFactor Y Z) x.1 (X x.1) -
          covFactor.toFun (Curvature.covApply covFactor X Z) x.1 (Y x.1) -
        covFactor.toFun Z x.1 (VectorField.mlieBracket I X Y x.1) =
        (Connection.leviCivitaConnectionOfMetric (I := I) g).toFun
            (Curvature.covApply
              (Connection.leviCivitaConnectionOfMetric (I := I) g) Y Z) x.1 (X x.1) -
          (Connection.leviCivitaConnectionOfMetric (I := I) g).toFun
              (Curvature.covApply
                (Connection.leviCivitaConnectionOfMetric (I := I) g) X Z) x.1 (Y x.1) -
            (Connection.leviCivitaConnectionOfMetric (I := I) g).toFun Z x.1
              (VectorField.mlieBracket I X Y x.1)
    rfl
  · change (0 : F) - 0 - 0 = 0
    simp

private def productLift
    (X : (x : M) → TangentSpace I x) (Y : (x : N) → TangentSpace J x)
    (x : M × N) : TangentSpace (I.prod J) x :=
  horizontalLift (I := I) (J := J) (N := N) X x +
    verticalLift (I := I) (J := J) (M := M) Y x

omit [FiniteDimensional Real E] [FiniteDimensional Real F]
    [IsManifold I ∞ M] [IsManifold J ∞ N] in
@[simp] private lemma productLift_apply
    (X : (x : M) → TangentSpace I x) (Y : (x : N) → TangentSpace J x)
    (x : M × N) :
    productLift (I := I) (J := J) X Y x = (X x.1, Y x.2) := by
  unfold productLift horizontalLift verticalLift
  apply Prod.ext
  · change (ContinuousLinearMap.fst Real (TangentSpace I x.1) (TangentSpace J x.2))
      ((X x.1, 0) + (0, Y x.2)) = X x.1
    rw [map_add]
    change X x.1 + 0 = X x.1
    rw [add_zero]
  · change (ContinuousLinearMap.snd Real (TangentSpace I x.1) (TangentSpace J x.2))
      ((X x.1, 0) + (0, Y x.2)) = Y x.2
    rw [map_add]
    change 0 + Y x.2 = Y x.2
    rw [zero_add]

omit [FiniteDimensional Real E] [FiniteDimensional Real F] in
private lemma productLift_contMDiff
    {X : (x : M) → TangentSpace I x} {Y : (x : N) → TangentSpace J x}
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y)) :
    ContMDiff (I.prod J) ((I.prod J).prod (modelWithCornersSelf Real (E × F))) ∞
      (T% (productLift (I := I) (J := J) X Y)) := by
  exact (horizontalLift_contMDiff (I := I) (J := J) (N := N) hX).add_section
    (verticalLift_contMDiff (I := I) (J := J) (M := M) hY)

private lemma mlieBracket_productLift
    [T2Space M] [T2Space N]
    (X Z : (x : M) → TangentSpace I x) (Y W : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Z))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (hW : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% W))
    (x : M × N) :
    VectorField.mlieBracket (I.prod J)
        (productLift (I := I) (J := J) X Y)
        (productLift (I := I) (J := J) Z W) x =
      productLift (I := I) (J := J)
        (VectorField.mlieBracket I X Z) (VectorField.mlieBracket J Y W) x := by
  have hHX := horizontalLift_contMDiff (I := I) (J := J) (N := N) hX
  have hHZ := horizontalLift_contMDiff (I := I) (J := J) (N := N) hZ
  have hVY := verticalLift_contMDiff (I := I) (J := J) (M := M) hY
  have hVW := verticalLift_contMDiff (I := I) (J := J) (M := M) hW
  unfold productLift
  change VectorField.mlieBracket (I.prod J)
      (horizontalLift (I := I) (J := J) (N := N) X +
        verticalLift (I := I) (J := J) (M := M) Y)
      (horizontalLift (I := I) (J := J) (N := N) Z +
        verticalLift (I := I) (J := J) (M := M) W) x = _
  rw [VectorField.mlieBracket_add_left
    (hHX.contMDiffAt.mdifferentiableAt (by simp))
    (hVY.contMDiffAt.mdifferentiableAt (by simp))]
  rw [VectorField.mlieBracket_add_right
    (hHZ.contMDiffAt.mdifferentiableAt (by simp))
    (hVW.contMDiffAt.mdifferentiableAt (by simp))]
  rw [VectorField.mlieBracket_add_right
    (hHZ.contMDiffAt.mdifferentiableAt (by simp))
    (hVW.contMDiffAt.mdifferentiableAt (by simp))]
  rw [mlieBracket_horizontal (I := I) (J := J) X Z hX hZ x]
  rw [mlieBracket_mixed (I := I) (J := J) X W hX hW x]
  rw [VectorField.mlieBracket_swap_apply]
  rw [mlieBracket_mixed (I := I) (J := J) Z Y hZ hY x]
  rw [mlieBracket_vertical (I := I) (J := J) Y W hY hW x]
  simp only [add_zero, zero_add, neg_zero]

private lemma leviCivita_productLift
    [CompleteSpace E] [CompleteSpace F] [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Z : (x : M) → TangentSpace I x) (Y W : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Z))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (hW : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% W))
    (x : M × N) :
    (Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)).toFun
        (productLift (I := I) (J := J) Z W) x
        (productLift (I := I) (J := J) X Y x) =
      productLift (I := I) (J := J)
        (fun q : M =>
          (Connection.leviCivitaConnectionOfMetric (I := I) g).toFun Z q (X q))
        (fun q : N =>
          (Connection.leviCivitaConnectionOfMetric (I := J) h).toFun W q (Y q)) x := by
  let covProd := Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)
  have hHZ := horizontalLift_contMDiff (I := I) (J := J) (N := N) hZ
  have hVW := verticalLift_contMDiff (I := I) (J := J) (M := M) hW
  have hadd := covProd.isCovariantDerivativeOnUniv.add
    (σ := horizontalLift (I := I) (J := J) (N := N) Z)
    (σ' := verticalLift (I := I) (J := J) (M := M) W)
    (hHZ.contMDiffAt.mdifferentiableAt (by simp))
    (hVW.contMDiffAt.mdifferentiableAt (by simp)) (Set.mem_univ x)
  unfold productLift
  change covProd.toFun
      (horizontalLift (I := I) (J := J) (N := N) Z +
        verticalLift (I := I) (J := J) (M := M) W) x
      ((horizontalLift (I := I) (J := J) (N := N) X +
        verticalLift (I := I) (J := J) (M := M) Y) x) = _
  rw [hadd]
  simp only [add_apply]
  change covProd.toFun
      (horizontalLift (I := I) (J := J) (N := N) Z) x
        (horizontalLift (I := I) (J := J) (N := N) X x +
          verticalLift (I := I) (J := J) (M := M) Y x) +
    covProd.toFun
      (verticalLift (I := I) (J := J) (M := M) W) x
        (horizontalLift (I := I) (J := J) (N := N) X x +
          verticalLift (I := I) (J := J) (M := M) Y x) = _
  rw [(covProd.toFun
    (horizontalLift (I := I) (J := J) (N := N) Z) x).map_add]
  rw [(covProd.toFun
    (verticalLift (I := I) (J := J) (M := M) W) x).map_add]
  rw [leviCivita_horizontal (I := I) (J := J) g h X Z hX hZ x]
  rw [leviCivita_vertical_horizontal (I := I) (J := J) g h Z Y hZ hY x]
  rw [leviCivita_horizontal_vertical (I := I) (J := J) g h X W hX hW x]
  rw [leviCivita_vertical (I := I) (J := J) g h Y W hY hW x]
  simp only [add_zero, zero_add]

private lemma riemannSec_productLift
    [CompleteSpace E] [CompleteSpace F] [T2Space M] [T2Space N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Z U : (x : M) → TangentSpace I x)
    (Y W V : (x : N) → TangentSpace J x)
    (hX : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% Z))
    (hU : ContMDiff I (I.prod (modelWithCornersSelf Real E)) ∞ (T% U))
    (hY : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% Y))
    (hW : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% W))
    (hV : ContMDiff J (J.prod (modelWithCornersSelf Real F)) ∞ (T% V))
    (x : M × N) :
    Curvature.riemannSec
        (Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h))
        (productLift (I := I) (J := J) X Y)
        (productLift (I := I) (J := J) Z W)
        (productLift (I := I) (J := J) U V) x =
      productLift (I := I) (J := J)
        (fun q : M => Curvature.riemannSec
          (Connection.leviCivitaConnectionOfMetric (I := I) g) X Z U q)
        (fun q : N => Curvature.riemannSec
          (Connection.leviCivitaConnectionOfMetric (I := J) h) Y W V q) x := by
  let covProd := Connection.leviCivitaConnectionOfMetric (I := I.prod J) (g.prod h)
  let covM := Connection.leviCivitaConnectionOfMetric (I := I) g
  let covN := Connection.leviCivitaConnectionOfMetric (I := J) h
  have hZU := leviCivita_covApply_contMDiff (I := I) g hZ hU
  have hWV := leviCivita_covApply_contMDiff (I := J) h hW hV
  have hXU := leviCivita_covApply_contMDiff (I := I) g hX hU
  have hYV := leviCivita_covApply_contMDiff (I := J) h hY hV
  have hcovZU : Curvature.covApply covProd
      (productLift (I := I) (J := J) Z W)
      (productLift (I := I) (J := J) U V) =
      productLift (I := I) (J := J)
        (Curvature.covApply covM Z U) (Curvature.covApply covN W V) := by
    funext p
    exact leviCivita_productLift (I := I) (J := J) g h Z U W V
      hZ hU hW hV p
  have hcovXU : Curvature.covApply covProd
      (productLift (I := I) (J := J) X Y)
      (productLift (I := I) (J := J) U V) =
      productLift (I := I) (J := J)
        (Curvature.covApply covM X U) (Curvature.covApply covN Y V) := by
    funext p
    exact leviCivita_productLift (I := I) (J := J) g h X U Y V
      hX hU hY hV p
  have hfirst : covProd.toFun
      (Curvature.covApply covProd
        (productLift (I := I) (J := J) Z W)
        (productLift (I := I) (J := J) U V)) x
      (productLift (I := I) (J := J) X Y x) =
      productLift (I := I) (J := J)
        (fun q : M => covM.toFun (Curvature.covApply covM Z U) q (X q))
        (fun q : N => covN.toFun (Curvature.covApply covN W V) q (Y q)) x := by
    rw [hcovZU]
    exact leviCivita_productLift (I := I) (J := J) g h
      X (Curvature.covApply covM Z U) Y (Curvature.covApply covN W V)
      hX hZU hY hWV x
  have hsecond : covProd.toFun
      (Curvature.covApply covProd
        (productLift (I := I) (J := J) X Y)
        (productLift (I := I) (J := J) U V)) x
      (productLift (I := I) (J := J) Z W x) =
      productLift (I := I) (J := J)
        (fun q : M => covM.toFun (Curvature.covApply covM X U) q (Z q))
        (fun q : N => covN.toFun (Curvature.covApply covN Y V) q (W q)) x := by
    rw [hcovXU]
    exact leviCivita_productLift (I := I) (J := J) g h
      Z (Curvature.covApply covM X U) W (Curvature.covApply covN Y V)
      hZ hXU hW hYV x
  obtain ⟨A, hAx⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x.1
      (VectorField.mlieBracket I X Z x.1)
  obtain ⟨B, hBx⟩ := ContMDiffSection.exists_eq_at
    (I := J) (F := F) (V := TangentSpace J) (n := (⊤ : ℕ∞)) x.2
      (VectorField.mlieBracket J Y W x.2)
  have hthird : covProd.toFun
      (productLift (I := I) (J := J) U V) x
      (VectorField.mlieBracket (I.prod J)
        (productLift (I := I) (J := J) X Y)
        (productLift (I := I) (J := J) Z W) x) =
      productLift (I := I) (J := J)
        (fun q : M => covM.toFun U q (A q))
        (fun q : N => covN.toFun V q (B q)) x := by
    rw [mlieBracket_productLift (I := I) (J := J) X Z Y W hX hZ hY hW x]
    have hAB : productLift (I := I) (J := J) A B x =
        productLift (I := I) (J := J)
          (VectorField.mlieBracket I X Z) (VectorField.mlieBracket J Y W) x := by
      unfold productLift horizontalLift verticalLift
      rw [hAx, hBx]
    rw [← hAB]
    exact leviCivita_productLift (I := I) (J := J) g h A U B V
      A.contMDiff hU B.contMDiff hV x
  rw [Curvature.riemannSec_def, hfirst, hsecond, hthird]
  simp only [productLift_apply]
  unfold Curvature.riemannSec
  apply Prod.ext
  · change
      covM.toFun (Curvature.covApply covM Z U) x.1 (X x.1) -
          covM.toFun (Curvature.covApply covM X U) x.1 (Z x.1) -
        covM.toFun U x.1 (A x.1) =
      covM.toFun (Curvature.covApply covM Z U) x.1 (X x.1) -
          covM.toFun (Curvature.covApply covM X U) x.1 (Z x.1) -
        covM.toFun U x.1 (VectorField.mlieBracket I X Z x.1)
    rw [hAx]
  · change
      covN.toFun (Curvature.covApply covN W V) x.2 (Y x.2) -
          covN.toFun (Curvature.covApply covN Y V) x.2 (W x.2) -
        covN.toFun V x.2 (B x.2) =
      covN.toFun (Curvature.covApply covN W V) x.2 (Y x.2) -
          covN.toFun (Curvature.covApply covN Y V) x.2 (W x.2) -
        covN.toFun V x.2 (VectorField.mlieBracket J Y W x.2)
    rw [hBx]

theorem Curvature.riemannOp_prod
    [CompleteSpace E] [CompleteSpace F] [T2Space M] [T2Space N]
    [BoundarylessManifold I M] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (u v w : TangentSpace (I.prod J) x) :
    Curvature.riemannOp
        (Connection.LeviCivita (I := I.prod J) (g.prod h)) x u v w =
      (Curvature.riemannOp
          (Connection.LeviCivita (I := I) g) x.1 u.1 v.1 w.1,
        Curvature.riemannOp
          (Connection.LeviCivita (I := J) h) x.2 u.2 v.2 w.2) := by
  let X := Curvature.smoothExtensionTangent (I := I) x.1 u.1
  let Y := Curvature.smoothExtensionTangent (I := J) x.2 u.2
  let Z := Curvature.smoothExtensionTangent (I := I) x.1 v.1
  let W := Curvature.smoothExtensionTangent (I := J) x.2 v.2
  let U := Curvature.smoothExtensionTangent (I := I) x.1 w.1
  let V := Curvature.smoothExtensionTangent (I := J) x.2 w.2
  have hX := Curvature.smoothExtensionTangent_contMDiff (I := I) x.1 u.1
  have hY := Curvature.smoothExtensionTangent_contMDiff (I := J) x.2 u.2
  have hZ := Curvature.smoothExtensionTangent_contMDiff (I := I) x.1 v.1
  have hW := Curvature.smoothExtensionTangent_contMDiff (I := J) x.2 v.2
  have hU := Curvature.smoothExtensionTangent_contMDiff (I := I) x.1 w.1
  have hV := Curvature.smoothExtensionTangent_contMDiff (I := J) x.2 w.2
  have hXx : X x.1 = u.1 := Curvature.smoothExtensionTangent_eq x.1 u.1
  have hYx : Y x.2 = u.2 := Curvature.smoothExtensionTangent_eq x.2 u.2
  have hZx : Z x.1 = v.1 := Curvature.smoothExtensionTangent_eq x.1 v.1
  have hWx : W x.2 = v.2 := Curvature.smoothExtensionTangent_eq x.2 v.2
  have hUx : U x.1 = w.1 := Curvature.smoothExtensionTangent_eq x.1 w.1
  have hVx : V x.2 = w.2 := Curvature.smoothExtensionTangent_eq x.2 w.2
  have hu : u = productLift (I := I) (J := J) X Y x := by
    rw [productLift_apply, hXx, hYx]
    exact (Prod.eta u).symm
  have hv : v = productLift (I := I) (J := J) Z W x := by
    rw [productLift_apply, hZx, hWx]
    exact (Prod.eta v).symm
  have hw : w = productLift (I := I) (J := J) U V x := by
    rw [productLift_apply, hUx, hVx]
    exact (Prod.eta w).symm
  have hsplit : Curvature.riemannSec
      (Connection.LeviCivita (I := I.prod J) (g.prod h))
      (productLift (I := I) (J := J) X Y)
      (productLift (I := I) (J := J) Z W)
      (productLift (I := I) (J := J) U V) x =
    productLift (I := I) (J := J)
      (fun q : M => Curvature.riemannSec
        (Connection.LeviCivita (I := I) g) X Z U q)
      (fun q : N => Curvature.riemannSec
        (Connection.LeviCivita (I := J) h) Y W V q) x := by
    exact riemannSec_productLift (I := I) (J := J) g h X Z U Y W V
      hX hZ hU hY hW hV x
  have hpoint : productLift (I := I) (J := J)
      (fun q : M => Curvature.riemannSec
        (Connection.LeviCivita (I := I) g) X Z U q)
      (fun q : N => Curvature.riemannSec
        (Connection.LeviCivita (I := J) h) Y W V q) x =
    ((Curvature.riemannOp
        (Connection.LeviCivita (I := I) g) x.1 u.1 v.1 w.1,
      Curvature.riemannOp
        (Connection.LeviCivita (I := J) h) x.2 u.2 v.2 w.2) :
      TangentSpace (I.prod J) x) := by
    rw [productLift_apply]
    rw [← Curvature.riemannOp_apply_smooth
      (Connection.LeviCivita (I := I) g) hX hZ hU]
    rw [← Curvature.riemannOp_apply_smooth
      (Connection.LeviCivita (I := J) h) hY hW hV]
    rw [Curvature.smoothExtensionTangent_eq x.1 u.1,
      Curvature.smoothExtensionTangent_eq x.2 u.2,
      Curvature.smoothExtensionTangent_eq x.1 v.1,
      Curvature.smoothExtensionTangent_eq x.2 v.2,
      Curvature.smoothExtensionTangent_eq x.1 w.1,
      Curvature.smoothExtensionTangent_eq x.2 w.2]
    rfl
  have hoplift : Curvature.riemannOp
      (Connection.LeviCivita (I := I.prod J) (g.prod h)) x u v w =
    Curvature.riemannOp
      (Connection.LeviCivita (I := I.prod J) (g.prod h)) x
      (productLift (I := I) (J := J) X Y x)
      (productLift (I := I) (J := J) Z W x)
      (productLift (I := I) (J := J) U V x) := by
    rw [← hu, ← hv, ← hw]
  have hopsec : Curvature.riemannOp
      (Connection.LeviCivita (I := I.prod J) (g.prod h)) x
      (productLift (I := I) (J := J) X Y x)
      (productLift (I := I) (J := J) Z W x)
      (productLift (I := I) (J := J) U V x) =
    Curvature.riemannSec
      (Connection.LeviCivita (I := I.prod J) (g.prod h))
      (productLift (I := I) (J := J) X Y)
      (productLift (I := I) (J := J) Z W)
      (productLift (I := I) (J := J) U V) x :=
    Curvature.riemannOp_apply_smooth
      (Connection.LeviCivita (I := I.prod J) (g.prod h))
      (productLift_contMDiff (I := I) (J := J) hX hY)
      (productLift_contMDiff (I := I) (J := J) hZ hW)
      (productLift_contMDiff (I := I) (J := J) hU hV)
  exact hoplift.trans (hopsec.trans (hsplit.trans hpoint))

theorem Curvature.ricciTensor_prod
    [CompleteSpace E] [CompleteSpace F] [T2Space M] [T2Space N]
    [BoundarylessManifold I M] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (x : M × N) (u v : TangentSpace (I.prod J) x) :
    Curvature.ricciTensor (I := I.prod J) (g.prod h) x u v =
      Curvature.ricciTensor (I := I) g x.1 u.1 v.1 +
        Curvature.ricciTensor (I := J) h x.2 u.2 v.2 := by
  let uM : TangentSpace I x.1 := u.1
  let uN : TangentSpace J x.2 := u.2
  let vM : TangentSpace I x.1 := v.1
  let vN : TangentSpace J x.2 := v.2
  change Curvature.ricciTensor (I := I.prod J) (g.prod h) x u v =
    Curvature.ricciTensor (I := I) g x.1 uM vM +
      Curvature.ricciTensor (I := J) h x.2 uN vN
  have hendo : Curvature.ricciEndo (I := I.prod J) (g.prod h) x u v =
      LinearMap.prodMap
        (Curvature.ricciEndo (I := I) g x.1 uM vM)
        (Curvature.ricciEndo (I := J) h x.2 uN vN) := by
    apply LinearMap.ext
    intro z
    change Curvature.riemannOp
        (Connection.LeviCivita (I := I.prod J) (g.prod h)) x z u v =
      (Curvature.riemannOp (Connection.LeviCivita (I := I) g)
          x.1 z.1 uM vM,
        Curvature.riemannOp (Connection.LeviCivita (I := J) h)
          x.2 z.2 uN vN)
    simpa only [uM, uN, vM, vN] using
      Curvature.riemannOp_prod (I := I) (J := J) g h x z u v
  rw [Curvature.ricciTensor_apply, hendo]
  change LinearMap.trace Real
      (TangentSpace I x.1 × TangentSpace J x.2)
      (LinearMap.prodMap
        (Curvature.ricciEndo (I := I) g x.1 uM vM)
        (Curvature.ricciEndo (I := J) h x.2 uN vN)) = _
  rw [LinearMap.trace_prodMap',
    ← Curvature.ricciTensor_apply, ← Curvature.ricciTensor_apply]

theorem Operator.gradFun_prod
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C^∞⟮I, M; Real⟯) (k : C^∞⟮J, N; Real⟯) (x : M × N) :
    Operator.gradFun (I := I.prod J) (g.prod h)
        (fun q : M × N => f q.1 + k q.2) x =
      (Operator.gradFun (I := I) g f x.1,
        Operator.gradFun (I := J) h k x.2) := by
  rw [← productLift_apply]
  symm
  apply Connection.gradFun_unique (I := I.prod J) (g.prod h)
  intro z
  let zM : TangentSpace I x.1 := z.1
  let zN : TangentSpace J x.2 := z.2
  have hfprod : ContMDiff (I.prod J) 𝓘(Real) ∞ (fun q : M × N => f q.1) :=
    f.contMDiff.comp contMDiff_fst
  have hkprod : ContMDiff (I.prod J) 𝓘(Real) ∞ (fun q : M × N => k q.2) :=
    k.contMDiff.comp contMDiff_snd
  have hdfst : mvfderiv (I := I.prod J) (fun q : M × N => f q.1) x z =
      mvfderiv (I := I) f x.1 zM := by
    rw [show (fun q : M × N => f q.1) = f ∘ Prod.fst by rfl]
    rw [mvfderiv_comp_apply x
      (f.contMDiff.mdifferentiableAt (by simp)) mdifferentiableAt_fst z]
    rw [mfderiv_fst]
    change mvfderiv (I := I) f x.1 z.1 = mvfderiv (I := I) f x.1 zM
    rfl
  have hdsnd : mvfderiv (I := I.prod J) (fun q : M × N => k q.2) x z =
      mvfderiv (I := J) k x.2 zN := by
    rw [show (fun q : M × N => k q.2) = k ∘ Prod.snd by rfl]
    rw [mvfderiv_comp_apply x
      (k.contMDiff.mdifferentiableAt (by simp)) mdifferentiableAt_snd z]
    rw [mfderiv_snd]
    change mvfderiv (I := J) k x.2 z.2 = mvfderiv (I := J) k x.2 zN
    rfl
  have hfstLift : mfderiv (I.prod J) I Prod.fst x
      (productLift (I := I) (J := J)
        (fun q : M => Operator.gradFun (I := I) g f q)
        (fun q : N => Operator.gradFun (I := J) h k q) x) =
      Operator.gradFun (I := I) g f x.1 := by
    rw [productLift_apply, mfderiv_fst]
    rfl
  have hsndLift : mfderiv (I.prod J) J Prod.snd x
      (productLift (I := I) (J := J)
        (fun q : M => Operator.gradFun (I := I) g f q)
        (fun q : N => Operator.gradFun (I := J) h k q) x) =
      Operator.gradFun (I := J) h k x.2 := by
    rw [productLift_apply, mfderiv_snd]
    rfl
  have hfstz : mfderiv (I.prod J) I Prod.fst x z = zM := by
    rw [mfderiv_fst]
    rfl
  have hsndz : mfderiv (I.prod J) J Prod.snd x z = zN := by
    rw [mfderiv_snd]
    rfl
  rw [SmoothRiemannianMetric.prod_inner, hfstLift, hsndLift, hfstz, hsndz]
  rw [Connection.gradFun_metricDual_mvfderiv,
    Connection.gradFun_metricDual_mvfderiv]
  calc
    mvfderiv (I := I) f x.1 zM + mvfderiv (I := J) k x.2 zN =
        mvfderiv (I := I.prod J) (fun q : M × N => f q.1) x z +
          mvfderiv (I := I.prod J) (fun q : M × N => k q.2) x z := by
      rw [hdfst, hdsnd]
    _ = mvfderiv (I := I.prod J)
        ((fun q : M × N => f q.1) + (fun q : M × N => k q.2)) x z := by
      rw [mvfderiv_add
        (hfprod.mdifferentiableAt (by simp)) (hkprod.mdifferentiableAt (by simp)),
        add_apply]
    _ = mvfderiv (I := I.prod J) (fun q : M × N => f q.1 + k q.2) x z := rfl

theorem Operator.hessFun_prod
    [CompleteSpace E] [CompleteSpace F] [T2Space M] [T2Space N]
    [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C^∞⟮I, M; Real⟯) (k : C^∞⟮J, N; Real⟯)
    (x : M × N) (u v : TangentSpace (I.prod J) x) :
    Operator.hessFun (I := I.prod J) (g.prod h)
        (fun q : M × N => f q.1 + k q.2) x u v =
      Operator.hessFun (I := I) g f x.1 u.1 v.1 +
        Operator.hessFun (I := J) h k x.2 u.2 v.2 := by
  let uM : TangentSpace I x.1 := u.1
  let uN : TangentSpace J x.2 := u.2
  let vM : TangentSpace I x.1 := v.1
  let vN : TangentSpace J x.2 := v.2
  change Operator.hessFun (I := I.prod J) (g.prod h)
      (fun q : M × N => f q.1 + k q.2) x u v =
    Operator.hessFun (I := I) g f x.1 uM vM +
      Operator.hessFun (I := J) h k x.2 uN vN
  have hF : ContMDiff (I.prod J) 𝓘(Real) ∞
      (fun q : M × N => f q.1 + k q.2) :=
    (f.contMDiff.comp contMDiff_fst).add (k.contMDiff.comp contMDiff_snd)
  have hgrad :
      (fun q : M × N => Operator.gradFun (I := I.prod J) (g.prod h)
        (fun p : M × N => f p.1 + k p.2) q) =
      productLift (I := I) (J := J)
        (fun q : M => Operator.gradFun (I := I) g f q)
        (fun q : N => Operator.gradFun (I := J) h k q) := by
    funext q
    rw [Operator.gradFun_prod (I := I) (J := J) g h f k q]
    exact (productLift_apply (I := I) (J := J)
      (fun p : M => Operator.gradFun (I := I) g f p)
      (fun p : N => Operator.gradFun (I := J) h k p) q).symm
  have hgradM := Connection.gradFun_contMDiff_total_section
    (I := I) g f.contMDiff
  have hgradN := Connection.gradFun_contMDiff_total_section
    (I := J) h k.contMDiff
  let X := Curvature.smoothExtensionTangent (I := I) x.1 uM
  let Y := Curvature.smoothExtensionTangent (I := J) x.2 uN
  have hX := Curvature.smoothExtensionTangent_contMDiff (I := I) x.1 uM
  have hY := Curvature.smoothExtensionTangent_contMDiff (I := J) x.2 uN
  have hXx : X x.1 = uM := Curvature.smoothExtensionTangent_eq x.1 uM
  have hYx : Y x.2 = uN := Curvature.smoothExtensionTangent_eq x.2 uN
  have hu : u = productLift (I := I) (J := J) X Y x := by
    rw [productLift_apply, hXx, hYx]
    exact (Prod.eta u).symm
  let A : (q : M) → TangentSpace I q := fun q =>
    (Connection.LeviCivita (I := I) g).toFun
      (fun p => Operator.gradFun (I := I) g f p) q (X q)
  let B : (q : N) → TangentSpace J q := fun q =>
    (Connection.LeviCivita (I := J) h).toFun
      (fun p => Operator.gradFun (I := J) h k p) q (Y q)
  have hconn : (Connection.LeviCivita (I := I.prod J) (g.prod h)).toFun
      (fun q : M × N => Operator.gradFun (I := I.prod J) (g.prod h)
        (fun p : M × N => f p.1 + k p.2) q) x u =
      productLift (I := I) (J := J) A B x := by
    rw [hgrad, hu]
    exact leviCivita_productLift (I := I) (J := J) g h
      X (fun p => Operator.gradFun (I := I) g f p)
      Y (fun p => Operator.gradFun (I := J) h k p)
      hX hgradM hY hgradN x
  have hfstConn : mfderiv (I.prod J) I Prod.fst x
      (productLift (I := I) (J := J) A B x) = A x.1 := by
    rw [productLift_apply, mfderiv_fst]
    rfl
  have hsndConn : mfderiv (I.prod J) J Prod.snd x
      (productLift (I := I) (J := J) A B x) = B x.2 := by
    rw [productLift_apply, mfderiv_snd]
    rfl
  have hfstv : mfderiv (I.prod J) I Prod.fst x v = vM := by
    rw [mfderiv_fst]
    rfl
  have hsndv : mfderiv (I.prod J) J Prod.snd x v = vN := by
    rw [mfderiv_snd]
    rfl
  rw [Connection.hessFun_eq_cov_grad (I := I.prod J) (g.prod h) hF x u v]
  rw [Connection.hessFun_eq_cov_grad (I := I) g f.contMDiff x.1 uM vM]
  rw [Connection.hessFun_eq_cov_grad (I := J) h k.contMDiff x.2 uN vN]
  rw [hconn, SmoothRiemannianMetric.prod_inner,
    hfstConn, hsndConn, hfstv, hsndv]
  change g.inner x.1
      ((Connection.LeviCivita (I := I) g).toFun
        (fun p => Operator.gradFun (I := I) g f p) x.1 (X x.1)) vM +
    h.inner x.2
      ((Connection.LeviCivita (I := J) h).toFun
        (fun p => Operator.gradFun (I := J) h k p) x.2 (Y x.2)) vN = _
  rw [hXx, hYx]

end DifferentialGeometry.Geometry
