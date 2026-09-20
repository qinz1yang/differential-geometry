import DifferentialGeometry.Topology.Covering.Smooth.Manifold
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
noncomputable section
open Set Function
open scoped _root_.Topology _root_.Manifold ContDiff
namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {X : Type*} [TopologicalSpace X] {a b c : X}

private def changeBasepointMap (γ : Path.Homotopic.Quotient b a) :
    @UniversalCover X _ ⟨a⟩ → @UniversalCover X _ ⟨b⟩ :=
  fun p => ⟨p.1, γ.trans p.2⟩

private theorem changeBasepointMap_preimage (γ : Path.Homotopic.Quotient b a)
    (p : @UniversalCover X _ ⟨b⟩) (U : Set X) :
    changeBasepointMap γ ⁻¹' @basicOpen X _ ⟨b⟩ p U =
      @basicOpen X _ ⟨a⟩ (changeBasepointMap γ.symm p) U := by
  rcases p with ⟨px, pp⟩
  ext q
  rcases q with ⟨qx, qp⟩
  constructor
  · rintro ⟨η, hη, hq⟩
    change Path px qx at η
    change γ.trans qp = pp.trans (Path.Homotopic.Quotient.mk η) at hq
    refine ⟨η, hη, ?_⟩
    change qp = (γ.symm.trans pp).trans (Path.Homotopic.Quotient.mk η)
    rw [Path.Homotopic.Quotient.trans_assoc, ← hq,
      ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
  · rintro ⟨η, hη, hq⟩
    change Path px qx at η
    change qp = (γ.symm.trans pp).trans (Path.Homotopic.Quotient.mk η) at hq
    refine ⟨η, hη, ?_⟩
    change γ.trans qp = pp.trans (Path.Homotopic.Quotient.mk η)
    rw [hq, ← Path.Homotopic.Quotient.trans_assoc,
      ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]

private theorem changeBasepointMap_continuous (γ : Path.Homotopic.Quotient b a) :
    Continuous (changeBasepointMap γ) := by
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨p, U, hU, hp, rfl⟩
  rw [changeBasepointMap_preimage]
  exact TopologicalSpace.GenerateOpen.basic _ ⟨changeBasepointMap γ.symm p, U, hU, hp, rfl⟩

def changeBasepointHomeomorph (γ : Path.Homotopic.Quotient b a) :
    @UniversalCover X _ ⟨a⟩ ≃ₜ @UniversalCover X _ ⟨b⟩ where
  toFun := changeBasepointMap γ
  invFun := changeBasepointMap γ.symm
  left_inv p := by
    rcases p with ⟨x, p⟩
    simp only [changeBasepointMap, ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]
    rfl
  right_inv p := by
    rcases p with ⟨x, p⟩
    simp only [changeBasepointMap, ← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans]
    rfl
  continuous_toFun := changeBasepointMap_continuous γ
  continuous_invFun := changeBasepointMap_continuous γ.symm

theorem changeBasepointHomeomorph_apply (γ : Path.Homotopic.Quotient b a)
    (p : @UniversalCover X _ ⟨a⟩) :
    changeBasepointHomeomorph γ p = ⟨p.1, γ.trans p.2⟩ := rfl

@[simp] theorem changeBasepointHomeomorph_symm (γ : Path.Homotopic.Quotient b a) :
    (changeBasepointHomeomorph γ).symm = changeBasepointHomeomorph γ.symm := by
  ext p
  rfl

@[simp] theorem proj_changeBasepointHomeomorph (γ : Path.Homotopic.Quotient b a)
    (p : @UniversalCover X _ ⟨a⟩) :
    @proj X _ ⟨b⟩ (changeBasepointHomeomorph γ p) = @proj X _ ⟨a⟩ p := rfl

@[simp] theorem changeBasepointHomeomorph_refl (a : X) :
    changeBasepointHomeomorph (Path.Homotopic.Quotient.refl a) =
      Homeomorph.refl (@UniversalCover X _ ⟨a⟩) := by
  ext p
  rcases p with ⟨x, p⟩
  exact congrArg (fun q => (⟨x, q⟩ : @UniversalCover X _ ⟨a⟩))
    (Path.Homotopic.Quotient.refl_trans p)

theorem changeBasepointHomeomorph_trans (γ : Path.Homotopic.Quotient b a)
    (η : Path.Homotopic.Quotient c b) :
    (changeBasepointHomeomorph γ).trans (changeBasepointHomeomorph η) =
      changeBasepointHomeomorph (η.trans γ) := by
  ext p
  rcases p with ⟨x, p⟩
  exact congrArg (fun q => (⟨x, q⟩ : @UniversalCover X _ ⟨c⟩))
    (Path.Homotopic.Quotient.trans_assoc η γ p).symm

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
  {a b : M}

private theorem changeBasepointHomeomorph_contMDiff (γ : Path.Homotopic.Quotient b a) :
    ContMDiff I I ∞ (changeBasepointHomeomorph γ) := by
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨(changeBasepointHomeomorph γ).continuous.continuousAt, ?_⟩
  have hcharts :
      (extChartAt I (changeBasepointHomeomorph γ x) : @UniversalCover M _ ⟨b⟩ → E) ∘
        changeBasepointHomeomorph γ = extChartAt I x := by
    funext y
    simp only [Function.comp_apply]
    let _ : Inhabited M := ⟨a⟩
    have hs := extChartAt_proj_eq (I := I) x y
    let _ : Inhabited M := ⟨b⟩
    have ht := extChartAt_proj_eq (I := I) (changeBasepointHomeomorph γ x)
      (changeBasepointHomeomorph γ y)
    rw [ht, hs]
    rfl
  rw [hcharts]
  exact contMDiffAt_extChartAt

def changeBasepointDiffeomorph (I : ModelWithCorners ℝ E H)
    (γ : Path.Homotopic.Quotient b a) :
    @UniversalCover M _ ⟨a⟩ ≃ₘ⟮I, I⟯ @UniversalCover M _ ⟨b⟩ where
  toEquiv := (changeBasepointHomeomorph γ).toEquiv
  contMDiff_toFun := changeBasepointHomeomorph_contMDiff γ
  contMDiff_invFun := changeBasepointHomeomorph_contMDiff γ.symm

theorem changeBasepointDiffeomorph_apply (γ : Path.Homotopic.Quotient b a)
    (p : @UniversalCover M _ ⟨a⟩) :
    changeBasepointDiffeomorph I γ p = ⟨p.1, γ.trans p.2⟩ := rfl

@[simp] theorem proj_changeBasepointDiffeomorph (γ : Path.Homotopic.Quotient b a)
    (p : @UniversalCover M _ ⟨a⟩) :
    @proj M _ ⟨b⟩ (changeBasepointDiffeomorph I γ p) = @proj M _ ⟨a⟩ p := rfl

@[simp] theorem changeBasepointDiffeomorph_symm (γ : Path.Homotopic.Quotient b a) :
    (changeBasepointDiffeomorph I γ).symm = changeBasepointDiffeomorph I γ.symm := by
  ext p
  rfl

@[simp] theorem changeBasepointDiffeomorph_refl (a : M) :
    changeBasepointDiffeomorph I (Path.Homotopic.Quotient.refl a) =
      Diffeomorph.refl I (@UniversalCover M _ ⟨a⟩) ∞ := by
  ext p
  rcases p with ⟨x, p⟩
  exact congrArg (fun q => (⟨x, q⟩ : @UniversalCover M _ ⟨a⟩))
    (Path.Homotopic.Quotient.refl_trans p)

theorem changeBasepointDiffeomorph_trans {c : M} (γ : Path.Homotopic.Quotient b a)
    (η : Path.Homotopic.Quotient c b) :
    (changeBasepointDiffeomorph I γ).trans (changeBasepointDiffeomorph I η) =
      changeBasepointDiffeomorph I (η.trans γ) := by
  ext p
  rcases p with ⟨x, p⟩
  exact congrArg (fun q => (⟨x, q⟩ : @UniversalCover M _ ⟨c⟩))
    (Path.Homotopic.Quotient.trans_assoc η γ p).symm

@[simp] theorem changeBasepointDiffeomorph_toHomeomorph (γ : Path.Homotopic.Quotient b a) :
    (changeBasepointDiffeomorph I γ).toHomeomorph = changeBasepointHomeomorph γ := rfl

end Smooth
end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
