import DifferentialGeometry.Geometry.Comparison.Busemann.Line.Product
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Construction.CompactPerturbationCompleteness

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold Topology

namespace DifferentialGeometry

open Geometry.Operator
open Geometry.Riemannian
open Geometry.Riemannian.BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mfderiv_busemannProdDiffeomorph
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
    ∀ (z : Topology.Morse.LevelSetSpace b 0) (t : ℝ)
        (v : Topology.Morse.MorseModel m) (s : ℝ),
      mfderiv
          ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I Φ (z, t) (v, s) =
        mfderiv I I
            (fun y : M ↦ busemannFlow (I := I) g hEnorm hγ hd hRic (-t) y) z.1
            (mfderiv (𝓘(ℝ, Topology.Morse.MorseModel m)) I
              (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) z v) -
          s • gradFun (I := I) g b
            (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) :=
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  let b : M → ℝ := busemann (I := I) γ
  let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
    I.transContinuousLinearEquiv e
  letI : J.Boundaryless := by
    constructor
    change Set.range (I.transContinuousLinearEquiv e) = Set.univ
    rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      Set.image_univ]
    exact Set.range_eq_univ.mpr e.surjective
  letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp [J]
    infer_instance
  let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
      (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
  let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
    intro x _ hx
    exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
      ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
  letI : ChartedSpace (Topology.Morse.MorseModel m)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
  letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
  let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
  by
    dsimp only
    intro z t v s
    have hΦ : ContMDiff
        ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
        ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := Φ.contMDiff
    have hsplit := mfderiv_prod_eq_add_apply
      (I := 𝓘(ℝ, Topology.Morse.MorseModel m)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
      (f := Φ) (p := (z, t)) (v := (v, s))
      (hΦ.contMDiffAt.mdifferentiableAt (by simp))
    have hlevelJ : ContMDiff (𝓘(ℝ, Topology.Morse.MorseModel m)) J
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) :=
      Topology.Morse.contMDiff_levelSetInclusion J b 0 hbJ hregJ
    have hlevelI : ContMDiff (𝓘(ℝ, Topology.Morse.MorseModel m)) I
        ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) :=
      (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right
        (I := I) (e := e)).1 hlevelJ
    have hflow : ContMDiff I I ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M ↦ busemannFlow (I := I) g hEnorm hγ hd hRic (-t) y) := by
      exact (contMDiff_busemannFlow (I := I) g hEnorm hγ hd hRic).comp
        (contMDiff_const.prodMk contMDiff_id)
    have hhorizontal :
        mfderiv (𝓘(ℝ, Topology.Morse.MorseModel m)) I
            (fun z' : Topology.Morse.LevelSetSpace b 0 ↦ Φ (z', t)) z v =
          mfderiv I I
              (fun y : M ↦ busemannFlow (I := I) g hEnorm hγ hd hRic (-t) y) z.1
              (mfderiv (𝓘(ℝ, Topology.Morse.MorseModel m)) I
                (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) z v) := by
      have hcomp := mfderiv_comp_apply
        (I := 𝓘(ℝ, Topology.Morse.MorseModel m)) (I' := I) (I'' := I)
        (x := z)
        (g := fun y : M ↦ busemannFlow (I := I) g hEnorm hγ hd hRic (-t) y)
        (f := fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1)
        (hflow.contMDiffAt.mdifferentiableAt (by simp))
        (hlevelI.contMDiffAt.mdifferentiableAt (by simp)) v
      exact hcomp
    have hneg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ ↦ -r) t
        (-1 : ℝ →L[ℝ] ℝ) :=
      (hasFDerivAt_id t).neg.hasMFDerivAt
    have hcurve := isMIntegralCurve_busemannFlow (I := I) g hEnorm hγ hd hRic z.1 (-t)
    have hchain := hcurve.comp t hneg
    have htime :
        mfderiv 𝓘(ℝ, ℝ) I
            (fun r : ℝ ↦ Φ (z, r)) t s =
          -s • gradFun (I := I) g b
            (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) := by
      change mfderiv 𝓘(ℝ, ℝ) I
          (fun r : ℝ ↦ busemannFlow (I := I) g hEnorm hγ hd hRic (-r) z.1) t s =
        -s • gradFun (I := I) g b
          (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)
      change (mfderiv 𝓘(ℝ, ℝ) I
          ((fun u : ℝ ↦ busemannFlow (I := I) g hEnorm hγ hd hRic u z.1) ∘ Neg.neg)
          t) s =
        -s • gradFun (I := I) g b
          (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)
      rw [hchain.mfderiv]
      change ((1 : ℝ →L[ℝ] ℝ) ((-1 : ℝ →L[ℝ] ℝ) s)) •
          gradFun (I := I) g (busemann (I := I) γ)
          (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) =
        -s • gradFun (I := I) g b
          (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)
      simp [b]
    rw [hsplit, hhorizontal, htime]
    simp only [sub_eq_add_neg, neg_smul]
    dsimp [b]
    rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def busemannLevelMetric
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    SmoothRiemannianMetric (𝓘(ℝ, Topology.Morse.MorseModel m))
      (Topology.Morse.LevelSetSpace b 0) :=
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  let b : M → ℝ := busemann (I := I) γ
  let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
    I.transContinuousLinearEquiv e
  letI : J.Boundaryless := by
    constructor
    change Set.range (I.transContinuousLinearEquiv e) = Set.univ
    rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      Set.image_univ]
    exact Set.range_eq_univ.mpr e.surjective
  letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp [J]
    infer_instance
  let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
      (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
  let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
    intro x _ hx
    exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
      ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
  letI : ChartedSpace (Topology.Morse.MorseModel m)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
  letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
  letI : T2Space (Topology.Morse.LevelSetSpace b 0) := inferInstance
  let hlevelJ : ContMDiff (𝓘(ℝ, Topology.Morse.MorseModel m)) J
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) :=
    Topology.Morse.contMDiff_levelSetInclusion J b 0 hbJ hregJ
  let hlevelI : ContMDiff (𝓘(ℝ, Topology.Morse.MorseModel m)) I
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) :=
    (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right
      (I := I) (e := e)).1 hlevelJ
  SmoothRiemannianMetric.pullbackOfImmersion (I := 𝓘(ℝ, Topology.Morse.MorseModel m)) (J := I) g
    (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) hlevelI (by
      intro z
      let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
      let ι₀ : Topology.Morse.LevelSetSpace b 0 →
          Topology.Morse.LevelSetSpace b 0 × ℝ := fun x ↦ (x, 0)
      have hΦ : ContMDiff
          ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
          ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := Φ.contMDiff
      have hι₀ : ContMDiff (𝓘(ℝ, Topology.Morse.MorseModel m))
          ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ))
          ((⊤ : ℕ∞) : WithTop ℕ∞) ι₀ :=
        contMDiff_id.prodMk contMDiff_const
      have hcomp := mfderiv_comp
        (I := 𝓘(ℝ, Topology.Morse.MorseModel m))
        (I' := (𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ))
        (I'' := I) (x := z) (g := Φ) (f := ι₀)
        (hΦ.contMDiffAt.mdifferentiableAt (by simp))
        (hι₀.contMDiffAt.mdifferentiableAt (by simp))
      have hfun : Φ ∘ ι₀ =
          (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) := by
        funext x
        change busemannFlow (I := I) g hEnorm hγ hd hRic (-(0 : ℝ)) x.1 = x.1
        rw [neg_zero, busemannFlow_zero]
      have hdiff :
          mfderiv (𝓘(ℝ, Topology.Morse.MorseModel m)) I
              (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) z =
            (mfderiv
              ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
              Φ (z, 0)).comp
              (ContinuousLinearMap.inl ℝ (Topology.Morse.MorseModel m) ℝ) := by
        rw [← hfun]
        rw [hcomp]
        congr 1
        exact mfderiv_prod_left
      rw [hdiff]
      exact ((Φ.isLocalDiffeomorph (z, 0)).mfderivToContinuousLinearEquiv
          (by simp)).injective.comp (by
            intro v w h
            exact congrArg Prod.fst h))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem busemannLevelMetric_inner
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    ∀ (z : Topology.Morse.LevelSetSpace b 0) (v w : Topology.Morse.MorseModel m),
      (busemannLevelMetric (I := I) g hEnorm hγ hd hRic e).inner z v w =
        g.inner z.1
          (mfderiv (𝓘(ℝ, Topology.Morse.MorseModel m)) I
            (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) z v)
          (mfderiv (𝓘(ℝ, Topology.Morse.MorseModel m)) I
            (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) z w) := by
  dsimp only
  intro z v w
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem inner_mfderiv_busemannProdDiffeomorph_inl_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
    ∀ (z : Topology.Morse.LevelSetSpace b 0) (t : ℝ)
        (v w : Topology.Morse.MorseModel m),
      g.inner (Φ (z, t))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (v, 0))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (w, 0)) =
        (busemannLevelMetric (I := I) g hEnorm hγ hd hRic e).inner z v w :=
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  let b : M → ℝ := busemann (I := I) γ
  let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
    I.transContinuousLinearEquiv e
  letI : J.Boundaryless := by
    constructor
    change Set.range (I.transContinuousLinearEquiv e) = Set.univ
    rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      Set.image_univ]
    exact Set.range_eq_univ.mpr e.surjective
  letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp [J]
    infer_instance
  let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
      (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
  let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
    intro x _ hx
    exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
      ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
  letI : ChartedSpace (Topology.Morse.MorseModel m)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
  letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
  let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
  by
    dsimp only
    intro z t v w
    have hv := mfderiv_busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e z t v 0
    have hw := mfderiv_busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e z t w 0
    simp only [zero_smul, sub_zero] at hv hw
    rw [hv, hw]
    change g.inner
        (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) _ _ =
      (busemannLevelMetric (I := I) g hEnorm hγ hd hRic e).inner z v w
    rw [inner_mfderiv_busemannFlow (I := I) g hEnorm hγ hd hRic]
    exact (busemannLevelMetric_inner (I := I) g hEnorm hγ hd hRic e z v w).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem inner_mfderiv_busemannProdDiffeomorph_inr_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
    ∀ (z : Topology.Morse.LevelSetSpace b 0) (t s r : ℝ),
      g.inner (Φ (z, t))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (0, s))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (0, r)) =
        (flatModelMetric ℝ).inner t s r :=
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  let b : M → ℝ := busemann (I := I) γ
  let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
    I.transContinuousLinearEquiv e
  letI : J.Boundaryless := by
    constructor
    change Set.range (I.transContinuousLinearEquiv e) = Set.univ
    rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      Set.image_univ]
    exact Set.range_eq_univ.mpr e.surjective
  letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp [J]
    infer_instance
  let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
      (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
  let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
    intro x _ hx
    exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
      ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
  letI : ChartedSpace (Topology.Morse.MorseModel m)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
  letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
  let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
  by
    dsimp only
    intro z t s r
    have hs := mfderiv_busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e z t 0 s
    have hr := mfderiv_busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e z t 0 r
    have hι0 :
        mfderiv (𝓘(ℝ, Topology.Morse.MorseModel m)) I
            (fun x : Topology.Morse.LevelSetSpace b 0 ↦ x.1) z
            (0 : Topology.Morse.MorseModel m) = 0 :=
      map_zero _
    have hF0 :
        mfderiv I I
            (fun y : M ↦ busemannFlow (I := I) g hEnorm hγ hd hRic (-t) y) z.1
            (0 : TangentSpace I z.1) = 0 :=
      map_zero _
    have hs' :
        mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (0, s) =
          (-s) • gradFun (I := I) g b
            (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) := by
      rw [hs, hι0, hF0, zero_sub, neg_smul]
    have hr' :
        mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (0, r) =
          (-r) • gradFun (I := I) g b
            (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) := by
      rw [hr, hι0, hF0, zero_sub, neg_smul]
    rw [hs', hr']
    change g.inner
        (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)
        ((-s) • gradFun (I := I) g b
          (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1))
        ((-r) • gradFun (I := I) g b
          (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)) =
      (flatModelMetric ℝ).inner t s r
    have hbI : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b :=
      hγ.busemann_contMDiff (I := I) hEnorm hd hRic
    have hunit :
        g.inner
            (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)
            (gradFun (I := I) g b
              (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1))
            (gradFun (I := I) g b
              (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)) = 1 := by
      simpa only [b, normGradSqFun] using
        normGradSqFun_busemann_eq_one (I := I) g hEnorm hγ.positive_ray
          (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)
          (hbI.contMDiffAt.mdifferentiableAt (by simp))
    rw [(g.inner _).map_smul, smul_apply,
      (g.inner _ _).map_smul, smul_eq_mul, smul_eq_mul, hunit]
    simp only [flatModelMetric, riemannianMetricVectorSpace]
    change -s * (-r * 1) = RCLike.re (inner ℝ s r)
    have h := RCLike.inner_apply s r
    have hrw : RCLike.re (inner ℝ s r) =
        RCLike.re (r * (starRingEnd ℝ) s) :=
      congrArg RCLike.re h
    rw [hrw]
    simp
    ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem inner_mfderiv_busemannProdDiffeomorph_inl_inr_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
    ∀ (z : Topology.Morse.LevelSetSpace b 0) (t s : ℝ)
        (v : Topology.Morse.MorseModel m),
      g.inner (Φ (z, t))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (v, 0))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (0, s)) = 0 :=
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  let b : M → ℝ := busemann (I := I) γ
  let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
    I.transContinuousLinearEquiv e
  letI : J.Boundaryless := by
    constructor
    change Set.range (I.transContinuousLinearEquiv e) = Set.univ
    rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      Set.image_univ]
    exact Set.range_eq_univ.mpr e.surjective
  letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp [J]
    infer_instance
  let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
      (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
  let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
    intro x _ hx
    exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
      ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
  letI : ChartedSpace (Topology.Morse.MorseModel m)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
  letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
  let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
  by
    dsimp only
    intro z t s v
    let incl : Topology.Morse.LevelSetSpace b 0 → M := fun x ↦ x.1
    let F : M → M := fun y ↦
      busemannFlow (I := I) g hEnorm hγ hd hRic (-t) y
    let u : TangentSpace I z.1 :=
      mfderiv (𝓘(ℝ, Topology.Morse.MorseModel m)) I incl z v
    have hv := mfderiv_busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e z t v 0
    simp only [zero_smul, sub_zero] at hv
    have hs := mfderiv_busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e z t 0 s
    have hs' :
        mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (0, s) =
          (-s) • gradFun (I := I) g b (F z.1) := by
      rw [hs]
      change mfderiv I I F z.1
            (mfderiv (𝓘(ℝ, Topology.Morse.MorseModel m)) I incl z 0) -
          s • gradFun (I := I) g b (F z.1) =
        (-s) • gradFun (I := I) g b (F z.1)
      simp only [map_zero, zero_sub, neg_smul]
    have hbI : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b :=
      hγ.busemann_contMDiff (I := I) hEnorm hd hRic
    have hFI : ContMDiff I I ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
      exact (contMDiff_busemannFlow (I := I) g hEnorm hγ hd hRic).comp
        (contMDiff_const.prodMk contMDiff_id)
    have hlevelJ : ContMDiff (𝓘(ℝ, Topology.Morse.MorseModel m)) J
        ((⊤ : ℕ∞) : WithTop ℕ∞) incl :=
      Topology.Morse.contMDiff_levelSetInclusion J b 0 hbJ hregJ
    have hlevelI : ContMDiff (𝓘(ℝ, Topology.Morse.MorseModel m)) I
        ((⊤ : ℕ∞) : WithTop ℕ∞) incl :=
      (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right
        (I := I) (e := e)).1 hlevelJ
    have hflowValue : b ∘ F = fun y : M ↦ b y + (-t) := by
      funext y
      dsimp [b, F]
      rw [busemann_busemannFlow (I := I) g hEnorm hγ hd hRic]
    have hadd :
        mfderiv I 𝓘(ℝ, ℝ) (fun y : M ↦ b y + (-t)) z.1 =
          mfderiv I 𝓘(ℝ, ℝ) b z.1 := by
      change mfderiv I 𝓘(ℝ, ℝ) (b + fun _ : M ↦ (-t)) z.1 =
        mfderiv I 𝓘(ℝ, ℝ) b z.1
      rw [mfderiv_add
        (hbI.contMDiffAt.mdifferentiableAt (by simp)) mdifferentiableAt_const,
        mfderiv_const]
      exact add_zero _
    have hmove :
        mfderiv I 𝓘(ℝ, ℝ) b (F z.1)
            (mfderiv I I F z.1 u) =
          mfderiv I 𝓘(ℝ, ℝ) b z.1 u := by
      have hchain := mfderiv_comp_apply
        (I := I) (I' := I) (I'' := 𝓘(ℝ, ℝ))
        (x := z.1) (g := b) (f := F)
        (hbI.contMDiffAt.mdifferentiableAt (by simp))
        (hFI.contMDiffAt.mdifferentiableAt (by simp)) u
      rw [hflowValue, hadd] at hchain
      exact hchain.symm
    have hlevelValue : b ∘ incl =
        fun _ : Topology.Morse.LevelSetSpace b 0 ↦ (0 : ℝ) := by
      funext x
      exact x.property
    have hzero : mfderiv I 𝓘(ℝ, ℝ) b z.1 u = 0 := by
      have hchain := mfderiv_comp_apply
        (I := 𝓘(ℝ, Topology.Morse.MorseModel m)) (I' := I)
        (I'' := 𝓘(ℝ, ℝ)) (x := z) (g := b) (f := incl)
        (hbI.contMDiffAt.mdifferentiableAt (by simp))
        (hlevelI.contMDiffAt.mdifferentiableAt (by simp)) v
      rw [hlevelValue, mfderiv_const] at hchain
      exact hchain.symm
    rw [hv, hs']
    change g.inner (F z.1) (mfderiv I I F z.1 u)
        ((-s) • gradFun (I := I) g b (F z.1)) = 0
    rw [(g.inner _ _).map_smul, smul_eq_mul,
      inner_gradFun_right (I := I), hmove, hzero]
    exact mul_zero _


private def splitModelEquiv
    (hd : 2 < Module.finrank ℝ E) :
    E ≃L[ℝ] Topology.Morse.MorseModel
      (Module.finrank ℝ E - 1 + 1) := by
  apply ContinuousLinearEquiv.ofFinrankEq
  rw [Module.finrank_fin_fun]
  omega


private theorem inner_add_blocks
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (a b c d : V) (A D : ℝ)
    (hac : B a c = A) (had : B a d = 0)
    (hbc : B b c = 0) (hbd : B b d = D) :
    B (a + b) (c + d) = A + D := by
  rw [B.map_add, add_apply,
    (B a).map_add, (B b).map_add, hac, had, hbc, hbd]
  simp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem inner_mfderiv_busemannProdDiffeomorph
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
    ∀ (z : Topology.Morse.LevelSetSpace b 0) (t : ℝ)
        (v w : Topology.Morse.MorseModel m) (s r : ℝ),
      g.inner (Φ (z, t))
          (mfderiv ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (v, s))
          (mfderiv ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (w, r)) =
        (busemannLevelMetric (I := I) g hEnorm hγ hd hRic e).inner z v w +
          (flatModelMetric ℝ).inner t s r :=
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  let b : M → ℝ := busemann (I := I) γ
  let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
    I.transContinuousLinearEquiv e
  letI : J.Boundaryless := by
    constructor
    change Set.range (I.transContinuousLinearEquiv e) = Set.univ
    rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      Set.image_univ]
    exact Set.range_eq_univ.mpr e.surjective
  letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp [J]
    infer_instance
  let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
      (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
  let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
    intro x _ hx
    exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
      ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
  letI : ChartedSpace (Topology.Morse.MorseModel m)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
  letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
  let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
  by
    dsimp only
    intro z t v w s r
    let L : Topology.Morse.MorseModel m × ℝ →L[ℝ] TangentSpace I (Φ (z, t)) :=
      mfderiv ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I Φ (z, t)
    have hvs : L (v, s) = L (v, 0) + L (0, s) := by
      exact (congrArg L (show (v, s) = (v, 0) + (0, s) by simp)).trans
        (L.map_add (v, 0) (0, s))
    have hwr : L (w, r) = L (w, 0) + L (0, r) := by
      exact (congrArg L (show (w, r) = (w, 0) + (0, r) by simp)).trans
        (L.map_add (w, 0) (0, r))
    have hcross : g.inner (Φ (z, t)) (L (0, s)) (L (w, 0)) = 0 :=
      (g.symm _ _ _).trans
        (inner_mfderiv_busemannProdDiffeomorph_inl_inr_eq
          (I := I) g hEnorm hγ hd hRic e z t s w)
    exact (congrArg₂ (fun x y ↦ g.inner (Φ (z, t)) x y) hvs hwr).trans
      (inner_add_blocks (g.inner (Φ (z, t))) _ _ _ _ _ _
        (inner_mfderiv_busemannProdDiffeomorph_inl_eq
          (I := I) g hEnorm hγ hd hRic e z t v w)
        (inner_mfderiv_busemannProdDiffeomorph_inl_inr_eq
          (I := I) g hEnorm hγ hd hRic e z t r v)
        hcross
        (inner_mfderiv_busemannProdDiffeomorph_inr_eq
          (I := I) g hEnorm hγ hd hRic e z t s r))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem inner_mfderiv_busemannProdDiffeomorph_inl
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
    ∀ (z : Topology.Morse.LevelSetSpace b 0) (t : ℝ)
        (v w : Topology.Morse.MorseModel m),
      g.inner (Φ (z, t))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (v, 0))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (w, 0)) =
        (busemannLevelMetric (I := I) g hEnorm hγ hd hRic e).inner z v w :=
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  let b : M → ℝ := busemann (I := I) γ
  let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
    I.transContinuousLinearEquiv e
  letI : J.Boundaryless := by
    constructor
    change Set.range (I.transContinuousLinearEquiv e) = Set.univ
    rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      Set.image_univ]
    exact Set.range_eq_univ.mpr e.surjective
  letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp [J]
    infer_instance
  let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
      (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
  let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
    intro x _ hx
    exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
      ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
  letI : ChartedSpace (Topology.Morse.MorseModel m)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
  letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
  letI : T2Space (Topology.Morse.LevelSetSpace b 0) := inferInstance
  let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
  by
    dsimp only
    intro z t v w
    have hflat : (flatModelMetric ℝ).inner t 0 0 = 0 := map_zero _
    exact (inner_mfderiv_busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
      z t v w 0 0).trans ((congrArg (fun q ↦
        (busemannLevelMetric (I := I) g hEnorm hγ hd hRic e).inner z v w + q)
          hflat).trans (add_zero _))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem inner_mfderiv_busemannProdDiffeomorph_inr
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
    ∀ (z : Topology.Morse.LevelSetSpace b 0) (t s r : ℝ),
      g.inner (Φ (z, t))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (0, s))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (0, r)) =
        (flatModelMetric ℝ).inner t s r :=
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  let b : M → ℝ := busemann (I := I) γ
  let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
    I.transContinuousLinearEquiv e
  letI : J.Boundaryless := by
    constructor
    change Set.range (I.transContinuousLinearEquiv e) = Set.univ
    rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      Set.image_univ]
    exact Set.range_eq_univ.mpr e.surjective
  letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp [J]
    infer_instance
  let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
      (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
  let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
    intro x _ hx
    exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
      ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
  letI : ChartedSpace (Topology.Morse.MorseModel m)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
  letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
  letI : T2Space (Topology.Morse.LevelSetSpace b 0) := inferInstance
  let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
  by
    dsimp only
    intro z t s r
    have hlevel : (busemannLevelMetric (I := I) g hEnorm hγ hd hRic e).inner z 0 0 = 0 :=
      map_zero _
    exact (inner_mfderiv_busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
      z t 0 0 s r).trans ((congrArg (fun q ↦ q + (flatModelMetric ℝ).inner t s r)
        hlevel).trans (zero_add _))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem inner_mfderiv_busemannProdDiffeomorph_inl_inr
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
    ∀ (z : Topology.Morse.LevelSetSpace b 0) (t s : ℝ)
        (v : Topology.Morse.MorseModel m),
      g.inner (Φ (z, t))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (v, 0))
          (mfderiv
            ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
            Φ (z, t) (0, s)) = 0 :=
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  let b : M → ℝ := busemann (I := I) γ
  let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
    I.transContinuousLinearEquiv e
  letI : J.Boundaryless := by
    constructor
    change Set.range (I.transContinuousLinearEquiv e) = Set.univ
    rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      Set.image_univ]
    exact Set.range_eq_univ.mpr e.surjective
  letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp [J]
    infer_instance
  let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
      (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
  let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
    intro x _ hx
    exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
      ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
  letI : ChartedSpace (Topology.Morse.MorseModel m)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
  letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
  letI : T2Space (Topology.Morse.LevelSetSpace b 0) := inferInstance
  let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
  by
    dsimp only
    intro z t s v
    have hlevel : (busemannLevelMetric (I := I) g hEnorm hγ hd hRic e).inner z v 0 = 0 :=
      map_zero _
    have hflat : (flatModelMetric ℝ).inner t 0 s = 0 := by
      exact DFunLike.congr_fun ((flatModelMetric ℝ).inner t).map_zero s
    exact (inner_mfderiv_busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
      z t v 0 0 s).trans ((congrArg₂ (· + ·) hlevel hflat).trans (zero_add _))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem pullbackMetricCross_busemannProdDiffeomorph
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0)
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1)) :
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    letI : T2Space (Topology.Morse.LevelSetSpace b 0) := inferInstance
    let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
    Diffeomorph.pullbackMetricCross
        (I := (𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ))
        (J := I) g Φ =
      SmoothRiemannianMetric.prod (I := 𝓘(ℝ, Topology.Morse.MorseModel m)) (J := 𝓘(ℝ, ℝ))
        (busemannLevelMetric (I := I) g hEnorm hγ hd hRic e)
        (flatModelMetric ℝ) :=
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  let b : M → ℝ := busemann (I := I) γ
  let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
    I.transContinuousLinearEquiv e
  letI : J.Boundaryless := by
    constructor
    change Set.range (I.transContinuousLinearEquiv e) = Set.univ
    rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
      Set.image_univ]
    exact Set.range_eq_univ.mpr e.surjective
  letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
    dsimp [J]
    infer_instance
  let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
      (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
  let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
    intro x _ hx
    exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
      ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
  letI : ChartedSpace (Topology.Morse.MorseModel m)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
  letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
      (Topology.Morse.LevelSetSpace b 0) :=
    Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
  letI : T2Space (Topology.Morse.LevelSetSpace b 0) := inferInstance
  let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
  by
    dsimp only
    apply SmoothRiemannianMetric.ext_inner
    intro p v w
    exact (Diffeomorph.pullbackMetricCross_inner g
      (busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e) p v w).trans
      ((inner_mfderiv_busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
        p.1 p.2 v.1 w.1 v.2 w.2).trans
        (SmoothRiemannianMetric.prod_inner _ _ p v w).symm)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem pullbackMetricCross_busemannProdDiffeomorph_finrank
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    let d := Module.finrank ℝ E
    let m := d - 1
    let e := splitModelEquiv (E := E) hd
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    let b : M → ℝ := busemann (I := I) γ
    let J : ModelWithCorners ℝ (Topology.Morse.MorseModel (m + 1)) H :=
      I.transContinuousLinearEquiv e
    letI : J.Boundaryless := by
      constructor
      change Set.range (I.transContinuousLinearEquiv e) = Set.univ
      rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
        Set.image_univ]
      exact Set.range_eq_univ.mpr e.surjective
    letI : IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      dsimp [J]
      infer_instance
    let hbJ : ContMDiff J 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
      exact (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left
        (I := I) (e := e)).2 (hγ.busemann_contMDiff (I := I) hEnorm hd hRic)
    let hregJ : ∀ x : M, b x = 0 → ¬ Topology.Morse.IsCriticalPointAt J b x := by
      intro x _ hx
      exact mfderiv_busemann_ne_zero (I := I) g hEnorm hγ.positive_ray x
        ((hγ.busemann_contMDiff hEnorm hd hRic).contMDiffAt.mdifferentiableAt (by simp))
        ((Topology.Morse.isCriticalPointAt_transContinuousLinearEquiv_iff I e b x).1 hx)
    letI : ChartedSpace (Topology.Morse.MorseModel m)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetChartedSpace J b 0 hbJ hregJ
    letI : IsManifold (𝓘(ℝ, Topology.Morse.MorseModel m)) (⊤ : ℕ∞)
        (Topology.Morse.LevelSetSpace b 0) :=
      Topology.Morse.manifoldLevelSetIsManifold J b 0 hbJ hregJ
    letI : T2Space (Topology.Morse.LevelSetSpace b 0) := inferInstance
    let Φ := busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic e
    Diffeomorph.pullbackMetricCross
        (I := (𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ))
        (J := I) g Φ =
      SmoothRiemannianMetric.prod (I := 𝓘(ℝ, Topology.Morse.MorseModel m)) (J := 𝓘(ℝ, ℝ))
        (busemannLevelMetric (I := I) g hEnorm hγ hd hRic e)
        (flatModelMetric ℝ) := by
  exact pullbackMetricCross_busemannProdDiffeomorph (I := I) g hEnorm hγ hd hRic
    (splitModelEquiv (E := E) hd)

end DifferentialGeometry
