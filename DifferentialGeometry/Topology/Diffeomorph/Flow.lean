import DifferentialGeometry.Analysis.ODE.CompactSupportFlow
import Mathlib.Geometry.Manifold.Diffeomorph

open scoped Manifold ContDiff

namespace Diffeomorph

open DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  (v : (x : M) → TangentSpace I x)
  (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
  (hsupp : IsCompact (tsupport v))

noncomputable def compactSupportFlow (t : ℝ) : Diffeomorph I I M M ∞ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let hc := exists_globalIntegralCurve_of_compactSupport v hv hsupp
  have hv1 : CMDiff 1 (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) := hv.of_le (by simp)
  have hj := contMDiff_globalFlow_joint_of_compactSupport v hv hsupp
  refine
    { toEquiv :=
        { toFun := fun x => curveAt v hc x t
          invFun := fun x => curveAt v hc x (-t)
          left_inv := ?_
          right_inv := ?_ }
      contMDiff_toFun := hj.comp (contMDiff_const.prodMk contMDiff_id)
      contMDiff_invFun := hj.comp (contMDiff_const.prodMk contMDiff_id) }
  · intro x
    dsimp only
    rw [← curveAt_add v hv1 hc, add_neg_cancel, curveAt_zero]
  · intro x
    dsimp only
    rw [← curveAt_add v hv1 hc, neg_add_cancel, curveAt_zero]

theorem compactSupportFlow_apply (t : ℝ) (x : M) :
    compactSupportFlow v hv hsupp t x =
      curveAt v (by
        let : CompleteSpace E := FiniteDimensional.complete ℝ E
        exact exists_globalIntegralCurve_of_compactSupport v hv hsupp) x t := rfl

theorem isMIntegralCurve_compactSupportFlow (x : M) :
    IsMIntegralCurve (fun t => compactSupportFlow v hv hsupp t x) v := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact curveAt_integralCurve v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) x

@[simp] theorem compactSupportFlow_zero :
    compactSupportFlow v hv hsupp 0 = Diffeomorph.refl I M ∞ := by
  apply Diffeomorph.ext
  intro x
  exact curveAt_zero v _ x

theorem compactSupportFlow_add (s t : ℝ) :
    compactSupportFlow v hv hsupp (s + t) =
      (compactSupportFlow v hv hsupp s).trans (compactSupportFlow v hv hsupp t) := by
  apply Diffeomorph.ext
  intro x
  exact curveAt_add v (hv.of_le (by simp)) _ x s t

@[simp] theorem compactSupportFlow_symm (t : ℝ) :
    (compactSupportFlow v hv hsupp t).symm = compactSupportFlow v hv hsupp (-t) := by
  apply Diffeomorph.ext
  intro x
  rfl

theorem contMDiff_compactSupportFlow :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => compactSupportFlow v hv hsupp p.1 p.2) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact contMDiff_globalFlow_joint_of_compactSupport v hv hsupp

theorem contMDiff_compactSupportFlow_symm :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => (compactSupportFlow v hv hsupp p.1).symm p.2) := by
  have hj := contMDiff_compactSupportFlow v hv hsupp
  have hn : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M => (-p.1, p.2)) :=
    (contMDiff_neg 𝓘(ℝ, ℝ) ∞ |>.comp contMDiff_fst).prodMk contMDiff_snd
  exact hj.comp hn

theorem compactSupportFlow_apply_eq_self_of_eq_zero {x : M} (hx : v x = 0) (t : ℝ) :
    compactSupportFlow v hv hsupp t x = x := by
  exact curveAt_eq_self_of_eq_zero v (hv.of_le (by simp)) _ hx t

theorem compactSupportFlow_symm_apply_eq_self_of_eq_zero {x : M} (hx : v x = 0) (t : ℝ) :
    (compactSupportFlow v hv hsupp t).symm x = x := by
  rw [compactSupportFlow_symm]
  exact compactSupportFlow_apply_eq_self_of_eq_zero v hv hsupp hx (-t)

theorem compactSupportFlow_eqOn_compl_tsupport (t : ℝ) :
    Set.EqOn (compactSupportFlow v hv hsupp t) id (tsupport v)ᶜ ∧
      Set.EqOn (compactSupportFlow v hv hsupp t).symm id (tsupport v)ᶜ := by
  constructor
  · intro x hx
    exact compactSupportFlow_apply_eq_self_of_eq_zero v hv hsupp
      (image_eq_zero_of_notMem_tsupport hx) t
  · intro x hx
    exact compactSupportFlow_symm_apply_eq_self_of_eq_zero v hv hsupp
      (image_eq_zero_of_notMem_tsupport hx) t

end Diffeomorph
