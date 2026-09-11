import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem contMDiff_injective_and_injective_mfderiv_of_product_chart_section
    {E H N F H' P G H'' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace P] [ChartedSpace H' P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H'']
    {K : ModelWithCorners ℝ G H''} [TopologicalSpace M] [ChartedSpace H'' M]
    (O : TopologicalSpace.Opens (N × P)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮I.prod J, K⟯ V) (t : P) (hsection : ∀ p : N, (p, t) ∈ O) :
    let e : N → M := fun p ↦ (Φ ⟨(p, t), hsection p⟩ : M)
    ContMDiff I K ∞ e ∧ Function.Injective e ∧
      ∀ p, Function.Injective (mfderiv I K e p) := by
  let s : N → O := fun p ↦ ⟨(p, t), hsection p⟩
  have hs : ContMDiff I (I.prod J) ∞ s :=
    (ContMDiff.subtypeVal_comp_iff O s).mp (contMDiff_id.prodMk contMDiff_const)
  let f : N → V := Φ ∘ s
  have hf : ContMDiff I K ∞ f := Φ.contMDiff.comp hs
  let back : V → N := fun y ↦ (Φ.symm y : N × P).1
  have hb : ContMDiff K I ∞ back :=
    contMDiff_fst.comp (contMDiff_subtype_val.comp Φ.symm.contMDiff)
  have hleft : Function.LeftInverse back f := fun p ↦ by
    change (Φ.symm (Φ (s p)) : N × P).1 = p
    rw [Φ.symm_apply_apply]
  have hd (p : N) : mfderiv I K (fun p ↦ (f p : M)) p = mfderiv I K f p := by
    change mfderiv I K (Subtype.val ∘ f) p = _
    rw [mfderiv_comp p ((contMDiff_subtype_val (I := K) (n := ∞)).mdifferentiable (by decide) (f p))
      (hf.mdifferentiable (by decide) p), mfderiv_subtype_val]
    change (ContinuousLinearMap.id ℝ G).comp (mfderiv I K f p : E →L[ℝ] G) = _
    exact ContinuousLinearMap.id_comp _
  refine ⟨contMDiff_subtype_val.comp hf, Subtype.val_injective.comp hleft.injective, ?_⟩
  intro p
  change Function.Injective (mfderiv I K (fun p ↦ (f p : M)) p)
  rw [hd]
  have hcomp : back ∘ f = id := funext hleft
  have hderiv := mfderiv_comp p (hb.mdifferentiable (by decide) (f p))
    (hf.mdifferentiable (by decide) p)
  rw [hcomp, mfderiv_id] at hderiv
  intro v w hvw
  have hv := DFunLike.congr_fun hderiv v
  have hw := DFunLike.congr_fun hderiv w
  change (mfderiv I K f p : E →L[ℝ] G) v = (mfderiv I K f p : E →L[ℝ] G) w at hvw
  change v = (mfderiv K I back (f p) : G →L[ℝ] E) (mfderiv I K f p v) at hv
  change w = (mfderiv K I back (f p) : G →L[ℝ] E) (mfderiv I K f p w) at hw
  exact hv.trans ((congrArg (mfderiv K I back (f p)) hvw).trans hw.symm)

end DifferentialGeometry.Topology.Manifold
