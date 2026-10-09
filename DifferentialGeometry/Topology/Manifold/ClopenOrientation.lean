import DifferentialGeometry.Topology.Manifold.ClopenDecomposition
import DifferentialGeometry.Topology.Manifold.SmoothOrientationOpen
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]
variable (U : Opens M) (hU : IsClosed (U : Set M))

theorem clopenSumDiffeomorph_mfderiv
    (p : U ⊕ (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : Opens M)) :
    mfderiv I I (clopenSumDiffeomorph I U hU) p = ContinuousLinearMap.id ℝ E := by
  let V : Opens M := ⟨(U : Set M)ᶜ, hU.isOpen_compl⟩
  let D := clopenSumDiffeomorph I U hU
  cases p with
  | inl q =>
    have hι : ContMDiff I I ∞ (Sum.inl : U → U ⊕ V) := ContMDiff.inl
    have hc := mfderiv_comp (f := (Sum.inl : U → U ⊕ V)) (g := D) q
      (D.contMDiff.mdifferentiableAt (by simp)) (hι.mdifferentiableAt (by simp))
    rw [mfderiv_sumInl (p := Sum.inl q)] at hc
    have hc' : (mfderiv I I (D ∘ (Sum.inl : U → U ⊕ V)) q : E →L[ℝ] E) =
        mfderiv I I D (Sum.inl q) := hc
    have hv : (mfderiv I I (D ∘ (Sum.inl : U → U ⊕ V)) q : E →L[ℝ] E) =
        ContinuousLinearMap.id ℝ E := DifferentialGeometry.mfderiv_subtype_val (I := I) U q
    exact hc'.symm.trans hv
  | inr q =>
    have hι : ContMDiff I I ∞ (Sum.inr : V → U ⊕ V) := ContMDiff.inr
    have hc := mfderiv_comp (f := (Sum.inr : V → U ⊕ V)) (g := D) q
      (D.contMDiff.mdifferentiableAt (by simp)) (hι.mdifferentiableAt (by simp))
    rw [mfderiv_sumInr] at hc
    have hc' : (mfderiv I I (D ∘ (Sum.inr : V → U ⊕ V)) q : E →L[ℝ] E) =
        mfderiv I I D (Sum.inr q) := hc
    have hv : (mfderiv I I (D ∘ (Sum.inr : V → U ⊕ V)) q : E →L[ℝ] E) =
        ContinuousLinearMap.id ℝ E := DifferentialGeometry.mfderiv_subtype_val (I := I) V q
    exact hc'.symm.trans hv

theorem clopenSumDiffeomorph_symm_mfderiv (p : M) :
    mfderiv I I (clopenSumDiffeomorph I U hU).symm p = ContinuousLinearMap.id ℝ E := by
  let D := clopenSumDiffeomorph I U hU
  have hc := mfderiv_comp (f := D.symm) (g := D) p
    (D.contMDiff.mdifferentiableAt (by simp)) (D.symm.contMDiff.mdifferentiableAt (by simp))
  rw [clopenSumDiffeomorph_mfderiv] at hc
  have hc' : (mfderiv I I (D ∘ D.symm) p : E →L[ℝ] E) = mfderiv I I D.symm p := hc
  have hm : D ∘ D.symm = id := funext D.apply_symm_apply
  let d : (M → M) → (E →L[ℝ] E) := fun g => mfderiv I I g p
  have hd : (mfderiv I I (D ∘ D.symm) p : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E :=
    (congrArg d hm).trans (mfderiv_id (I := I) (x := p))
  exact hc'.symm.trans hd

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

def clopenSumSmoothOrientation (o : SmoothOrientation I M) :
    SmoothOrientation I (U ⊕ (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : Opens M)) :=
  pullbackSmoothOrientation I I (clopenSumDiffeomorph I U hU)
    (clopenSumDiffeomorph I U hU).contMDiff
    (fun p => ((clopenSumDiffeomorph I U hU).mfderivToContinuousLinearEquiv (by simp) p).bijective) o

theorem clopenSumSmoothOrientation_apply (o : SmoothOrientation I M)
    (p : U ⊕ (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : Opens M)) :
    (clopenSumSmoothOrientation I U hU o).val p = o.val (clopenSumDiffeomorph I U hU p) := by
  let D := clopenSumDiffeomorph I U hU
  let e := differentialEquivOfBijective I I D
    (fun x => (D.mfderivToContinuousLinearEquiv (by simp) x).bijective) p
  have he : e = ContinuousLinearEquiv.refl ℝ E := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact congrArg (fun A : E →L[ℝ] E => A v) (clopenSumDiffeomorph_mfderiv I U hU p)
  change tangentOrientationEquiv e.symm.toLinearEquiv (o.val (D p)) = o.val (D p)
  rw [he]
  exact tangentOrientationEquiv_refl (o.val (D p))

theorem clopenSumSmoothOrientation_pushforward (o : SmoothOrientation I M)
    (p : U ⊕ (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : Opens M)) :
    tangentOrientationEquiv (differentialEquivOfBijective I I (clopenSumDiffeomorph I U hU)
      (fun x => ((clopenSumDiffeomorph I U hU).mfderivToContinuousLinearEquiv (by simp) x).bijective) p).toLinearEquiv
        ((clopenSumSmoothOrientation I U hU o).val p) = o.val (clopenSumDiffeomorph I U hU p) :=
  pullbackSmoothOrientation_pushforward I I (clopenSumDiffeomorph I U hU)
    (clopenSumDiffeomorph I U hU).contMDiff
    (fun x => ((clopenSumDiffeomorph I U hU).mfderivToContinuousLinearEquiv (by simp) x).bijective) o p

theorem clopenSumSmoothOrientation_symm_preserves (o : SmoothOrientation I M) (p : M) :
    tangentOrientationEquiv (differentialEquivOfBijective I I (clopenSumDiffeomorph I U hU).symm
      (fun x => ((clopenSumDiffeomorph I U hU).symm.mfderivToContinuousLinearEquiv (by simp) x).bijective) p).toLinearEquiv
        (o.val p) = (clopenSumSmoothOrientation I U hU o).val ((clopenSumDiffeomorph I U hU).symm p) := by
  let D := clopenSumDiffeomorph I U hU
  let e := differentialEquivOfBijective I I D.symm
    (fun x => (D.symm.mfderivToContinuousLinearEquiv (by simp) x).bijective) p
  have he : e = ContinuousLinearEquiv.refl ℝ E := by
    apply ContinuousLinearEquiv.ext
    funext v
    exact congrArg (fun A : E →L[ℝ] E => A v) (clopenSumDiffeomorph_symm_mfderiv I U hU p)
  change tangentOrientationEquiv e.toLinearEquiv (o.val p) = _
  rw [he]
  have hr : tangentOrientationEquiv (ContinuousLinearEquiv.refl ℝ E).toLinearEquiv (o.val p) = o.val p :=
    tangentOrientationEquiv_refl (o.val p)
  exact hr.trans ((congrArg o.val (D.apply_symm_apply p).symm).trans
    (clopenSumSmoothOrientation_apply I U hU o (D.symm p)).symm)
end DifferentialGeometry.Topology.Manifold
