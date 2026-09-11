import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

noncomputable section

open scoped ContDiff Manifold

open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.Ehresmann

variable {E E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
variable {f : M → N}
variable {X : (x : M) → TangentSpace I x}
variable {Z : (y : N) → TangentSpace J y}
variable {γ : ℝ → M}

set_option backward.isDefEq.respectTransparency false in
theorem isMIntegralCurve_comp_of_mfderiv_eq
    (hf : ContMDiff I J 1 f)
    (hrel : ∀ x, mfderiv I J f x (X x) = Z (f x))
    (hγ : IsMIntegralCurve γ X) :
    IsMIntegralCurve (f ∘ γ) Z := by
  intro t
  apply (HasMFDerivAt.comp t
    ((hf (γ t)).mdifferentiableAt (by norm_num)).hasMFDerivAt
    (hγ t)).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    map_smul,
    ← one_apply_eq_self
      (F := TangentSpace (modelWithCornersSelf ℝ ℝ) t →L[ℝ]
        TangentSpace (modelWithCornersSelf ℝ ℝ) t) r,
    ← ContinuousLinearMap.smulRight_apply, hrel, Function.comp_apply]

theorem isMIntegralCurve_id_comp (hγ : IsMIntegralCurve γ X) :
    IsMIntegralCurve ((id : M → M) ∘ γ) X := by
  apply isMIntegralCurve_comp_of_mfderiv_eq (I := I) (J := I)
    (f := id) (X := X) (Z := X) contMDiff_id
  · intro x
    simp [mfderiv_id]
  · exact hγ

section TargetFlow

variable [J.Boundaryless] [IsManifold J ∞ N] [T2Space N]

theorem curveAt_map_of_mfderiv_eq
    (hf : ContMDiff I J 1 f)
    (hX : ∀ x, ∃ γ, γ 0 = x ∧ IsMIntegralCurve γ X)
    (hZ : ∀ y, ∃ γ, γ 0 = y ∧ IsMIntegralCurve γ Z)
    (hZsmooth : ContMDiff J J.tangent 1
      (fun y : N ↦ (⟨y, Z y⟩ : TangentBundle J N)))
    (hrel : ∀ x, mfderiv I J f x (X x) = Z (f x))
    (x : M) (t : ℝ) :
    f (curveAt X hX x t) = curveAt Z hZ (f x) t := by
  have hcomp : IsMIntegralCurve (f ∘ curveAt X hX x) Z :=
    isMIntegralCurve_comp_of_mfderiv_eq hf hrel
      (curveAt_integralCurve X hX x)
  have heq : f ∘ curveAt X hX x = curveAt Z hZ (f x) :=
    integralCurve_eq_of_agree_zero Z hZsmooth hcomp
      (curveAt_integralCurve Z hZ (f x)) (by
        simp only [Function.comp_apply, curveAt_zero])
  exact congrFun heq t

end TargetFlow

section IdentityRegression

variable [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

theorem curveAt_map_id
    (hX : ∀ x, ∃ γ, γ 0 = x ∧ IsMIntegralCurve γ X)
    (hXsmooth : ContMDiff I I.tangent 1
      (fun x : M ↦ (⟨x, X x⟩ : TangentBundle I M)))
    (x : M) (t : ℝ) :
    (id : M → M) (curveAt X hX x t) =
      curveAt X hX ((id : M → M) x) t := by
  exact curveAt_map_of_mfderiv_eq (I := I) (J := I)
    (f := id) (X := X) (Z := X) contMDiff_id hX hX hXsmooth
    (by intro y; simp [mfderiv_id]) x t

end IdentityRegression

section CompactSupportFlow

variable [FiniteDimensional ℝ E] [CompleteSpace E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

noncomputable def compactSupportFlowDiffeomorph
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport V)) (t : ℝ) :
    M ≃ₘ⟮I, I⟯ M := by
  let hcomplete := exists_globalIntegralCurve_of_compactSupport V hV hsupp
  have hVone : ContMDiff I I.tangent 1
      (fun x : M ↦ (⟨x, V x⟩ : TangentBundle I M)) :=
    hV.of_le (by norm_num)
  exact
    { toEquiv :=
        { toFun := fun x ↦ curveAt V hcomplete x t
          invFun := fun x ↦ curveAt V hcomplete x (-t)
          left_inv := by
            intro x
            change curveAt V hcomplete (curveAt V hcomplete x t) (-t) = x
            rw [← curveAt_add V hVone hcomplete x t (-t)]
            simp only [add_neg_cancel, curveAt_zero]
          right_inv := by
            intro x
            change curveAt V hcomplete (curveAt V hcomplete x (-t)) t = x
            rw [← curveAt_add V hVone hcomplete x (-t) t]
            simp only [neg_add_cancel, curveAt_zero] }
      contMDiff_toFun := fun x ↦
        contMDiffAt_globalFlow_of_compactSupport V hV hsupp t x
      contMDiff_invFun := fun x ↦
        contMDiffAt_globalFlow_of_compactSupport V hV hsupp (-t) x }

@[simp]
theorem compactSupportFlowDiffeomorph_apply
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport V)) (t : ℝ) (x : M) :
    compactSupportFlowDiffeomorph V hV hsupp t x =
      curveAt V (exists_globalIntegralCurve_of_compactSupport V hV hsupp) x t :=
  rfl

@[simp]
theorem compactSupportFlowDiffeomorph_symm_apply
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport V)) (t : ℝ) (x : M) :
    (compactSupportFlowDiffeomorph V hV hsupp t).symm x =
      curveAt V (exists_globalIntegralCurve_of_compactSupport V hV hsupp) x (-t) :=
  rfl

theorem compactSupportFlowDiffeomorph_symm
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport V)) (t : ℝ) :
    (compactSupportFlowDiffeomorph V hV hsupp t).symm =
      compactSupportFlowDiffeomorph V hV hsupp (-t) := by
  apply Diffeomorph.ext
  intro x
  rfl

theorem compactSupportFlowDiffeomorph_trans
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport V)) (s t : ℝ) :
    (compactSupportFlowDiffeomorph V hV hsupp s).trans
        (compactSupportFlowDiffeomorph V hV hsupp t) =
      compactSupportFlowDiffeomorph V hV hsupp (s + t) := by
  apply Diffeomorph.ext
  intro x
  change curveAt V (exists_globalIntegralCurve_of_compactSupport V hV hsupp)
      (curveAt V (exists_globalIntegralCurve_of_compactSupport V hV hsupp) x s) t =
    curveAt V (exists_globalIntegralCurve_of_compactSupport V hV hsupp) x (s + t)
  exact (curveAt_add V (hV.of_le (by norm_num))
    (exists_globalIntegralCurve_of_compactSupport V hV hsupp) x s t).symm

@[simp]
theorem compactSupportFlowDiffeomorph_zero
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, V x⟩ : TangentBundle I M)))
    (hsupp : IsCompact (tsupport V)) :
    compactSupportFlowDiffeomorph V hV hsupp 0 = Diffeomorph.refl I M ∞ := by
  apply Diffeomorph.ext
  intro x
  exact curveAt_zero V
    (exists_globalIntegralCurve_of_compactSupport V hV hsupp) x

set_option backward.isDefEq.respectTransparency false in
theorem compactSupportFlowDiffeomorph_zeroField (t : ℝ) :
    compactSupportFlowDiffeomorph
      (I := I) (M := M) (fun _ : M ↦ 0)
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _))
      (by simp) t = Diffeomorph.refl I M ∞ := by
  apply Diffeomorph.ext
  intro x
  change curveAt (fun _ : M ↦ 0)
      (exists_globalIntegralCurve_of_compactSupport
        (fun _ : M ↦ 0)
        (Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _))
        (by simp)) x t = x
  apply curveAt_eq_self_of_not_mem_tsupport
    (v := fun _ : M ↦ 0)
    (hv := Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _))
    (hcomplete := exists_globalIntegralCurve_of_compactSupport
      (fun _ : M ↦ 0)
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _))
      (by simp))
  change x ∉ tsupport (0 : M → E)
  simp

end CompactSupportFlow

section CompactSupportRelatedFlow

theorem compactSupportFlowDiffeomorph_map_of_mfderiv_eq
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E'] [CompleteSpace E']
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
    [J.Boundaryless] [IsManifold J ∞ N] [T2Space N]
    (f : M → N) (hf : ContMDiff I J 1 f)
    (X : (x : M) → TangentSpace I x)
    (hX : ContMDiff I I.tangent ∞
      (fun x : M ↦ (⟨x, X x⟩ : TangentBundle I M)))
    (hXsupp : IsCompact (tsupport X))
    (Z : (y : N) → TangentSpace J y)
    (hZ : ContMDiff J J.tangent ∞
      (fun y : N ↦ (⟨y, Z y⟩ : TangentBundle J N)))
    (hZsupp : IsCompact (tsupport Z))
    (hrel : ∀ x, mfderiv I J f x (X x) = Z (f x))
    (t : ℝ) (x : M) :
    f (compactSupportFlowDiffeomorph X hX hXsupp t x) =
      compactSupportFlowDiffeomorph Z hZ hZsupp t (f x) := by
  exact curveAt_map_of_mfderiv_eq hf
    (exists_globalIntegralCurve_of_compactSupport X hX hXsupp)
    (exists_globalIntegralCurve_of_compactSupport Z hZ hZsupp)
    (hZ.of_le (by norm_num)) hrel x t

end CompactSupportRelatedFlow

end DifferentialGeometry.Topology.Ehresmann
