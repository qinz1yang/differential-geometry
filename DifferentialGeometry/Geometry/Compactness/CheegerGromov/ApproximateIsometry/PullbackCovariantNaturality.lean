import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PartialDiffeomorphOpens
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativeRestriction
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNormRestriction


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
theorem covNormWith_pd_zone
    [T2Space N]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 1 N] [IsManifold I 2 N] (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {V : Opens M}
    (hV : (V : Set M) ⊆ Φ.source)
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
  have : Nonempty W := ⟨⟨(Φ : M → N) x, x, hx, rfl⟩⟩
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
    rw [ContinuousLinearMap.comp_apply,
      mfderiv_subtype_val (I := I) W (F p),
      mfderiv_subtype_val (I := I) V p] at happ
    change mfderiv I I (F : V → W) p v =
      mfderiv I I (Φ : M → N) (p : M) v at happ
    exact happ
  have hmfdAmbient (p : V) (v : TangentSpace I p) :
      mfderiv I I (Subtype.val : W → N) (F p)
          (mfderiv I I (F : V → W) p v) =
        mfderiv I I (Φ : M → N) (p : M)
          (mfderiv I I (Subtype.val : V → M) p v) := by
    rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
    exact hmfd p v
  set δMV := restrictOpen0S (I := I) 2 (V := V) δM with hδMVdef
  set δNW := restrictOpen0S (I := I) 2 (V := W) δN with hδNWdef
  have hδMV_apply : ∀ (p : V) (slots : Fin 2 → TangentSpace I p),
      δMV p slots = δM (p : M) slots := fun _ _ => rfl
  have hδNW_apply : ∀ (q : W) (slots : Fin 2 → TangentSpace I q),
      δNW q slots = δN (q : N) slots := fun _ _ => rfl
  have hδMV_model (p : V) :
      Tensor0SBundle.Tensor0SSpace.toModel (δMV p) =
        Tensor0SBundle.Tensor0SSpace.toModel (δM (p : M)) := by
    rw [hδMVdef]
    rfl
  have hδNW_model (q : W) :
      Tensor0SBundle.Tensor0SSpace.toModel (δNW q) =
        Tensor0SBundle.Tensor0SSpace.toModel (δN (q : N)) := by
    rw [hδNWdef]
    rfl
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
    let slotsE : Fin 2 → E :=
      fun q => tangentSpaceModelContinuousLinearEquiv (I := I) p (slots q)
    let slotsM : Fin 2 → TangentSpace I (p : M) :=
      fun q => (tangentSpaceModelContinuousLinearEquiv (I := I) (p : M)).symm (slotsE q)
    have hbase := hδ (p : M) p.2 slotsM
    change Tensor0SBundle.Tensor0SSpace.toModel (δMV p) slotsE =
      Tensor0SBundle.Tensor0SSpace.toModel (δNW (F p))
        (fun q => tangentSpaceModelContinuousLinearEquiv (I := I) (F p)
          (mfderiv I I (F : V → W) p (slots q)))
    rw [hδMV_model, hδNW_model]
    rw [Tensor0SBundle.Tensor0SSpace.toModel_apply_model_vector,
      Tensor0SBundle.Tensor0SSpace.toModel_apply_model_vector]
    convert hbase using 1
    rw [← show ((F p : W) : N) = (Φ : M → N) (p : M) from rfl]
    congr 1
    funext q
    have hleft :
        (tangentSpaceModelContinuousLinearEquiv (I := I) ((F p : W) : N)).symm
            (tangentSpaceModelContinuousLinearEquiv (I := I) (F p)
              (mfderiv I I (F : V → W) p (slots q))) =
          mfderiv I I (Subtype.val : W → N) (F p)
            (mfderiv I I (F : V → W) p (slots q)) := by
      apply (tangentSpaceModelContinuousLinearEquiv
        (I := I) ((F p : W) : N)).injective
      rw [ContinuousLinearEquiv.apply_symm_apply, mfderiv_subtype_val_apply]
      exact (tangentSpaceModelContinuousLinearEquiv_apply (I := I) (F p)
        (mfderiv I I (F : V → W) p (slots q))).trans
          (tangentSpaceModelContinuousLinearEquiv_apply (I := I) ((F p : W) : N)
            (mfderiv I I (F : V → W) p (slots q))).symm
    rw [hleft, hmfdAmbient]
    congr 1
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) (p : M)).injective
    rw [mfderiv_subtype_val_apply]
    change tangentSpaceModelContinuousLinearEquiv (I := I) (p : M) (slots q) =
      tangentSpaceModelContinuousLinearEquiv (I := I) (p : M)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) (p : M)).symm
          (tangentSpaceModelContinuousLinearEquiv (I := I) p (slots q)))
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (tangentSpaceModelContinuousLinearEquiv_apply (I := I) (p : M) (slots q)).trans
      (tangentSpaceModelContinuousLinearEquiv_apply (I := I) p (slots q)).symm
  have hres1 := covDerivOfField_restrictOpen (I := I) G V δMV δM hδMV_apply a xV
  have hpull := covDerivOfField_pullback (I := I) (g'.restrictOpen (I := I) W) F δMV δNW
    hA0 a xV
  have hres2 := covDerivOfField_restrictOpen (I := I) g' W δNW δN hδNW_apply a (F xV)
  have hFx : ((F xV : W) : N) = (Φ : M → N) x := by
    rfl
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
    calc
      _ = covDerivOfField (I := I) (g'.restrictOpen (I := I) W) δNW a (F xV)
            (fun q => mfderiv I I (F : V → W) xV (slots q)) := hpull slots
      _ = covDerivOfField (I := I) g' δN a ((F xV : W) : N)
            (fun q => mfderiv I I (F : V → W) xV (slots q)) :=
        hres2 (fun q => mfderiv I I (F : V → W) xV (slots q))
      _ = _ := by rw [hFx]
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
