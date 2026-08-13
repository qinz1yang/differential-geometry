import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PartialDiffeomorphOpens
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

section PartialCovNaturality

open TopologicalSpace

omit [SigmaCompactSpace M] in
theorem tensor02_eq_covDOF
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (gRef : SmoothRiemannianMetric I M) :
    ∀ a : ℕ, tensor02CovDeriv (I := I) A gRef a = covDerivOfField (I := I) gRef A a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
      change metricCovDerivStep (I := I) gRef a (tensor02CovDeriv (I := I) A gRef a)
        = covDerivOfField (I := I) gRef A (a + 1)
      rw [ih, covDerivOfField_succ]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem srm_ext {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] {g g' : SmoothRiemannianMetric I M'}
    (h : ∀ (x : M') (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) : g = g' := by
  obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
  obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
  have hi : i₁ = i₂ :=
    funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
  subst hi
  rfl

omit [SigmaCompactSpace M] in
theorem covNormWith_pd_zone [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [T2Space N] [SigmaCompactSpace N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {V : Opens M} [Nonempty V]
    [SigmaCompactSpace V]
    (hV : (V : Set M) ⊆ Φ.source)
    [SigmaCompactSpace
      (⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ : Opens N)]
    (g' : SmoothRiemannianMetric I N)
    (δN : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2)
    (δM : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (G : SmoothRiemannianMetric I M)
    (hδ : ∀ x ∈ (V : Set M), ∀ v : Fin 2 → TangentSpace I x,
      δM x v = δN ((Φ : M → N) x)
        (fun q => mfderiv I I (Φ : M → N) x (v q)))
    (hG : ∀ x ∈ (V : Set M), ∀ v w : TangentSpace I x,
      G.inner x v w = g'.inner ((Φ : M → N) x)
        (mfderiv I I (Φ : M → N) x v) (mfderiv I I (Φ : M → N) x w))
    (a : ℕ) (x : M) (hx : x ∈ (V : Set M)) :
    tensor02CovDerivNormWith (I := I) a δM G G x
      = tensor02CovDerivNormWith (I := I) a δN g' g' ((Φ : M → N) x) := by
  classical
  set W : Opens N := ⟨(Φ : M → N) '' (V : Set M), image_opens_isOpen Φ hV⟩ with hWdef
  haveI : Nonempty W := ⟨⟨(Φ : M → N) x, x, hx, rfl⟩⟩
  set F := PartialDiffeomorph.toOpensDiffeo Φ hV with hFdef
  set xV : V := ⟨x, hx⟩ with hxVdef
  have hmfd : ∀ (p : V) (v : TangentSpace I p),
      mfderiv I I (F : V → W) p v = mfderiv I I (Φ : M → N) (p : M) v := by
    intro p v
    have hFd : MDifferentiableAt I I (F : V → W) p :=
      F.contMDiff.contMDiffAt.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hvalW : MDifferentiableAt I I (Subtype.val : W → N) (F p) :=
      ((contMDiff_subtype_val (I := I) (U := W)).contMDiffAt).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hvalV : MDifferentiableAt I I (Subtype.val : V → M) p :=
      ((contMDiff_subtype_val (I := I) (U := V)).contMDiffAt).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hΦd : MDifferentiableAt I I (Φ : M → N) (p : M) :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds (hV p.2))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have h1 : mfderiv I I (fun y : V => ((F y : W) : N)) p
        = (mfderiv I I (Subtype.val : W → N) (F p)).comp
            (mfderiv I I (F : V → W) p) :=
      mfderiv_comp p hvalW hFd
    have h2 : mfderiv I I (fun y : V => (Φ : M → N) (y : M)) p
        = (mfderiv I I (Φ : M → N) (p : M)).comp
            (mfderiv I I (Subtype.val : V → M) p) :=
      mfderiv_comp p hΦd hvalV
    have happ := DFunLike.congr_fun (h1.symm.trans h2) v
    simpa [ContinuousLinearMap.comp_apply,
      mfderiv_subtype_val (I := I) W (F p),
      mfderiv_subtype_val (I := I) V p] using happ
  set δMV := restrictOpen0S (I := I) 2 (V := V) δM with hδMVdef
  set δNW := restrictOpen0S (I := I) 2 (V := W) δN with hδNWdef
  have hδMV_apply : ∀ (p : V) (slots : Fin 2 → TangentSpace I p),
      δMV p slots = δM (p : M) slots := fun _ _ => rfl
  have hδNW_apply : ∀ (q : W) (slots : Fin 2 → TangentSpace I q),
      δNW q slots = δN (q : N) slots := fun _ _ => rfl
  have hswap : G.restrictOpen (I := I) V
      = Diffeomorph.pullbackMetric (I := I) (g'.restrictOpen (I := I) W) F := by
    apply srm_ext
    intro p v w
    have hL : (G.restrictOpen (I := I) V).inner p v w = G.inner (p : M) v w := rfl
    have hR : (Diffeomorph.pullbackMetric (I := I) (g'.restrictOpen (I := I) W) F).inner p v w
        = g'.inner ((F p : W) : N)
            (mfderiv I I (F : V → W) p v) (mfderiv I I (F : V → W) p w) := by
      rw [Diffeomorph.pullbackMetric_inner]
      rfl
    rw [hL, hR, hmfd, hmfd]
    exact hG (p : M) p.2 v w
  have hA0 : ∀ (p : V) (slots : Fin 2 → TangentSpace I p),
      δMV p slots = δNW (F p) (fun q => mfderiv I I (F : V → W) p (slots q)) := by
    intro p slots
    rw [hδMV_apply, hδNW_apply, hδ (p : M) p.2]
    change δN ((Φ : M → N) (p : M)) _ = δN ((F p : W) : N) _
    congr 1
    funext q
    rw [hmfd]
  have hres1 := covDerivOfField_restrictOpen (I := I) G V δMV δM hδMV_apply a xV
  have hpull := covDerivOfField_pullback (I := I) (g'.restrictOpen (I := I) W) F δMV δNW
    hA0 a xV
  have hres2 := covDerivOfField_restrictOpen (I := I) g' W δNW δN hδNW_apply a (F xV)
  have htensor1 : ∀ slots : Fin (a + 2) → TangentSpace I x,
      covDerivOfField (I := I) G δM a x slots
        = covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I)
            (g'.restrictOpen (I := I) W) F) δMV a xV slots := by
    intro slots
    rw [← hswap]
    exact (hres1 slots).symm
  have htensor2 : ∀ slots : Fin (a + 2) → TangentSpace I x,
      covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I)
          (g'.restrictOpen (I := I) W) F) δMV a xV slots
        = covDerivOfField (I := I) g' δN a ((Φ : M → N) x)
            (fun q => mfderiv I I (F : V → W) xV (slots q)) := by
    intro slots
    rw [hpull]
    have := hres2 (fun q => mfderiv I I (F : V → W) xV (slots q))
    convert this using 2
  have hT1 : covDerivOfField (I := I) G δM a x
      = covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I)
          (g'.restrictOpen (I := I) W) F) δMV a xV :=
    ContinuousMultilinearMap.ext htensor1
  have hT2 : covDerivOfField (I := I) g' δN a ((Φ : M → N) x)
      = covDerivOfField (I := I) (g'.restrictOpen (I := I) W) δNW a (F xV) :=
    (ContinuousMultilinearMap.ext hres2).symm
  unfold tensor02CovDerivNormWith
  rw [tensor02_eq_covDOF, tensor02_eq_covDOF]
  obtain ⟨basis, hONb⟩ := DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I)
    (Diffeomorph.pullbackMetric (I := I) (g'.restrictOpen (I := I) W) F) xV
  have hnorm1 : Tensor0SBundle.normSq0S (I := I) G x (a + 2)
        (covDerivOfField (I := I) G δM a x)
      = Tensor0SBundle.normSq0S (I := I)
          (Diffeomorph.pullbackMetric (I := I) (g'.restrictOpen (I := I) W) F) xV (a + 2)
          (covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I)
            (g'.restrictOpen (I := I) W) F) δMV a xV) := by
    rw [hT1, ← hswap]
    exact (normSq0S_restrictOpen_apply (I := I) G V (a + 2) xV _).symm
  have hnorm2 : Tensor0SBundle.normSq0S (I := I)
        (Diffeomorph.pullbackMetric (I := I) (g'.restrictOpen (I := I) W) F) xV (a + 2)
        (covDerivOfField (I := I) (Diffeomorph.pullbackMetric (I := I)
          (g'.restrictOpen (I := I) W) F) δMV a xV)
      = Tensor0SBundle.normSq0S (I := I) (g'.restrictOpen (I := I) W) (F xV) (a + 2)
          (covDerivOfField (I := I) (g'.restrictOpen (I := I) W) δNW a (F xV)) :=
    normSq0S_pullback_eval_of_orthonormal (I := I) (g'.restrictOpen (I := I) W) F
      xV (a + 2) basis hONb _ _ (hpull)
  have hnorm3 : Tensor0SBundle.normSq0S (I := I) (g'.restrictOpen (I := I) W) (F xV) (a + 2)
        (covDerivOfField (I := I) (g'.restrictOpen (I := I) W) δNW a (F xV))
      = Tensor0SBundle.normSq0S (I := I) g' ((Φ : M → N) x) (a + 2)
          (covDerivOfField (I := I) g' δN a ((Φ : M → N) x)) := by
    rw [hT2]
    exact normSq0S_restrictOpen_apply (I := I) g' W (a + 2) (F xV) _
  rw [hnorm1, hnorm2, hnorm3]

end PartialCovNaturality

end HCGCompactness
end DifferentialGeometry
