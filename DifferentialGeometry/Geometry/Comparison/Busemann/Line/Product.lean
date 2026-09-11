import DifferentialGeometry.Geometry.Comparison.Busemann.Line.Flow
import DifferentialGeometry.Topology.Morse.CriticalPoint
import DifferentialGeometry.Topology.Morse.RegularLevel.Sublevel

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
def busemannProdEquiv
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    {x : M // busemann (I := I) γ x = 0} × ℝ ≃ M where
  toFun := fun p ↦
    busemannFlow (I := I) g hEnorm hγ hd hRic (-p.2) p.1.1
  invFun := fun y ↦
    (⟨busemannFlow (I := I) g hEnorm hγ hd hRic
        (-(busemann (I := I) γ y)) y, by
      rw [busemann_busemannFlow (I := I) g hEnorm hγ hd hRic]
      ring⟩,
      -(busemann (I := I) γ y))
  left_inv := by
    rintro ⟨z, t⟩
    have hb :
        busemann (I := I) γ
            (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) = -t := by
      rw [busemann_busemannFlow (I := I) g hEnorm hγ hd hRic, z.2, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change busemannFlow (I := I) g hEnorm hγ hd hRic
          (-(busemann (I := I) γ
            (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)))
          (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) = z.1
      rw [hb, neg_neg]
      calc
        busemannFlow (I := I) g hEnorm hγ hd hRic t
              (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1) =
            busemannFlow (I := I) g hEnorm hγ hd hRic ((-t) + t) z.1 :=
          (busemannFlow_add (I := I) g hEnorm hγ hd hRic z.1 (-t) t).symm
        _ = z.1 := by rw [neg_add_cancel, busemannFlow_zero]
    · change -(busemann (I := I) γ
          (busemannFlow (I := I) g hEnorm hγ hd hRic (-t) z.1)) = t
      rw [hb, neg_neg]
  right_inv := by
    intro y
    change busemannFlow (I := I) g hEnorm hγ hd hRic
        (-(-(busemann (I := I) γ y)))
        (busemannFlow (I := I) g hEnorm hγ hd hRic
          (-(busemann (I := I) γ y)) y) = y
    rw [neg_neg]
    calc
      busemannFlow (I := I) g hEnorm hγ hd hRic
            (busemann (I := I) γ y)
            (busemannFlow (I := I) g hEnorm hγ hd hRic
              (-(busemann (I := I) γ y)) y) =
          busemannFlow (I := I) g hEnorm hγ hd hRic
            (-(busemann (I := I) γ y) + busemann (I := I) γ y) y :=
        (busemannFlow_add (I := I) g hEnorm hγ hd hRic y
          (-(busemann (I := I) γ y)) (busemann (I := I) γ y)).symm
      _ = y := by rw [neg_add_cancel, busemannFlow_zero]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def busemannProdHomeomorph
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
    (hd : 2 < Module.finrank ℝ E)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    {x : M // busemann (I := I) γ x = 0} × ℝ ≃ₜ M where
  toEquiv := busemannProdEquiv (I := I) g hEnorm hγ hd hRic
  continuous_toFun := by
    exact (contMDiff_busemannFlow (I := I) g hEnorm hγ hd hRic).continuous.comp
      ((continuous_neg.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst))
  continuous_invFun := by
    let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      hEnorm.isContinuousRiemannianBundle
    have hb : Continuous (busemann (I := I) γ) :=
      (hγ.busemann_contMDiff (I := I) hEnorm hd hRic).continuous
    have ht : Continuous (fun y : M ↦ -(busemann (I := I) γ y)) :=
      continuous_neg.comp hb
    have hflow : Continuous (fun y : M ↦
        busemannFlow (I := I) g hEnorm hγ hd hRic
          (-(busemann (I := I) γ y)) y) :=
      (contMDiff_busemannFlow (I := I) g hEnorm hγ hd hRic).continuous.comp
        (ht.prodMk continuous_id)
    exact (Continuous.subtype_mk hflow (fun y ↦ by
      rw [busemann_busemannFlow (I := I) g hEnorm hγ hd hRic]
      ring)).prodMk ht

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def busemannProdDiffeomorph
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
    (Topology.Morse.LevelSetSpace b 0 × ℝ) ≃ₘ^((⊤ : ℕ∞) : WithTop ℕ∞)⟮
      (𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ), I⟯ M :=
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
  { toEquiv := busemannProdEquiv (I := I) g hEnorm hγ hd hRic
    contMDiff_toFun := by
      have hlevelJ : ContMDiff (𝓘(ℝ, Topology.Morse.MorseModel m)) J
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : Topology.Morse.LevelSetSpace b 0 => x.1) :=
        Topology.Morse.contMDiff_levelSetInclusion J b 0 hbJ hregJ
      have hlevelI : ContMDiff (𝓘(ℝ, Topology.Morse.MorseModel m)) I
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : Topology.Morse.LevelSetSpace b 0 => x.1) :=
        (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right
          (I := I) (e := e)).1 hlevelJ
      have htime : ContMDiff
          ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : Topology.Morse.LevelSetSpace b 0 × ℝ => -p.2) :=
        contMDiff_snd.neg
      have hbase : ContMDiff
          ((𝓘(ℝ, Topology.Morse.MorseModel m)).prod 𝓘(ℝ, ℝ)) I
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : Topology.Morse.LevelSetSpace b 0 × ℝ => p.1.1) :=
        hlevelI.comp contMDiff_fst
      exact (contMDiff_busemannFlow (I := I) g hEnorm hγ hd hRic).comp
        (htime.prodMk hbase)
    contMDiff_invFun := by
      have hbI : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) b :=
        hγ.busemann_contMDiff (I := I) hEnorm hd hRic
      have htime : ContMDiff I 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => -b y) := hbI.neg
      let F : M → M := fun y =>
        busemannFlow (I := I) g hEnorm hγ hd hRic (-b y) y
      have hFI : ContMDiff I I ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
        exact (contMDiff_busemannFlow (I := I) g hEnorm hγ hd hRic).comp
          (htime.prodMk contMDiff_id)
      have hFJ : ContMDiff I J ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
        (ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right
          (I := I) (e := e)).2 hFI
      have hFzero : ∀ y : M, b (F y) = 0 := by
        intro y
        dsimp [F, b]
        rw [busemann_busemannFlow (I := I) g hEnorm hγ hd hRic]
        ring
      have hfirst : ContMDiff I (𝓘(ℝ, Topology.Morse.MorseModel m))
          ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M =>
            (⟨F y, hFzero y⟩ : Topology.Morse.LevelSetSpace b 0)) :=
        Topology.Morse.contMDiff_levelSet_factor J b 0 hbJ hregJ F hFJ hFzero
      exact hfirst.prodMk htime }


section Evaluation

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
  {γ : ℝ → M} (hγ : IsMinimizingLine (I := I) g γ)
  (hd : 2 < Module.finrank ℝ E) (hRic : RicciBoundedBelow (I := I) g 0)

theorem busemannProdEquiv_apply
    (p : {x : M // busemann (I := I) γ x = 0} × ℝ) :
    busemannProdEquiv g hEnorm hγ hd hRic p =
      busemannFlow g hEnorm hγ hd hRic (-p.2) p.1.1 := rfl

@[simp]
theorem busemannProdEquiv_symm_apply_fst_coe (x : M) :
    ((busemannProdEquiv g hEnorm hγ hd hRic).symm x).1.1 =
      busemannFlow g hEnorm hγ hd hRic (-busemann (I := I) γ x) x := rfl

@[simp]
theorem busemannProdEquiv_symm_apply_snd (x : M) :
    ((busemannProdEquiv g hEnorm hγ hd hRic).symm x).2 =
      -busemann (I := I) γ x := rfl

@[simp]
theorem busemann_busemannProdEquiv
    (p : {x : M // busemann (I := I) γ x = 0} × ℝ) :
    busemann (I := I) γ (busemannProdEquiv g hEnorm hγ hd hRic p) = -p.2 := by
  rw [busemannProdEquiv_apply, busemann_busemannFlow, p.1.2, zero_add]

@[simp]
theorem busemannProdEquiv_apply_zero
    (z : {x : M // busemann (I := I) γ x = 0}) :
    busemannProdEquiv g hEnorm hγ hd hRic (z, 0) = z.1 := by
  rw [busemannProdEquiv_apply, neg_zero, busemannFlow_zero]

@[simp]
theorem busemannProdHomeomorph_toEquiv :
    (busemannProdHomeomorph g hEnorm hγ hd hRic).toEquiv =
      busemannProdEquiv g hEnorm hγ hd hRic := rfl

@[simp]
theorem busemannProdHomeomorph_apply
    (p : {x : M // busemann (I := I) γ x = 0} × ℝ) :
    busemannProdHomeomorph g hEnorm hγ hd hRic p =
      busemannFlow g hEnorm hγ hd hRic (-p.2) p.1.1 := rfl

@[simp]
theorem busemannProdDiffeomorph_toEquiv
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
    (busemannProdDiffeomorph g hEnorm hγ hd hRic e).toEquiv =
      busemannProdEquiv g hEnorm hγ hd hRic := by
  dsimp only
  rfl

theorem busemannProdDiffeomorph_apply
    {m : ℕ} (e : E ≃L[ℝ] Topology.Morse.MorseModel (m + 1))
    (p : {x : M // busemann (I := I) γ x = 0} × ℝ) :
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
    (busemannProdDiffeomorph g hEnorm hγ hd hRic e).toEquiv p =
      busemannFlow g hEnorm hγ hd hRic (-p.2) p.1.1 := by
  dsimp only
  rfl

end Evaluation

end DifferentialGeometry
