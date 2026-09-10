import DifferentialGeometry.Topology.Manifold.RegularLevel.Sublevel
import DifferentialGeometry.Topology.Manifold.MFDeriv.ModelTransport
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Manifold.RegularLevel

variable {m : ℕ} {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
  (e : E ≃L[ℝ] MorseModel (m + 1))

@[reducible]
private def interiorModel := (𝓘(ℝ, E)).transContinuousLinearEquiv e

private instance interiorModel_boundaryless : (interiorModel e).Boundaryless where
  range_eq_univ := by
    rw [interiorModel, ModelWithCorners.transContinuousLinearEquiv_range,
      ModelWithCorners.range_eq_univ, image_univ]
    exact e.surjective.range_eq

private theorem interiorFunction_smooth {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    let U := intrinsicInterior I ∞ (by simp) (M := M)
    let _ := interiorChartedSpace I ∞ (M := U)
    ContMDiff (interiorModel e) 𝓘(ℝ, ℝ) ∞ (fun x : U => f x) := by
  let U := intrinsicInterior I ∞ (by simp) (M := M)
  let _ := interiorChartedSpace I ∞ (M := U)
  change ContMDiff (interiorModel e) 𝓘(ℝ, ℝ) ∞ (fun x : U => f x)
  have h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : U => f x) :=
    hf.comp (contMDiff_intrinsicInterior_val I ∞ (show (∞ : ℕ∞ω) ≠ 0 from by simp))
  simpa only [interiorModel, ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left] using h

private theorem interiorFunction_regular {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    let U := intrinsicInterior I ∞ (by simp) (M := M)
    let _ := interiorChartedSpace I ∞ (M := U)
    ∀ x : U, f x = a → mfderiv (interiorModel e) 𝓘(ℝ, ℝ) (fun y : U => f y) x ≠ 0 := by
  let U := intrinsicInterior I ∞ (by simp) (M := M)
  have hgold : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : U => f x) := hf.comp contMDiff_subtype_val
  let _ := interiorChartedSpace I ∞ (M := U)
  let _ : IsManifold 𝓘(ℝ, E) ∞ U := interiorIsManifold I ∞
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x : U => f x) :=
    hgold.comp (contMDiff_interiorAtlas_id I ∞)
  change ∀ x : U, f x = a → mfderiv (interiorModel e) 𝓘(ℝ, ℝ) (fun y : U => f y) x ≠ 0
  intro x hx hz
  have hd := mfderiv_transContinuousLinearEquiv 𝓘(ℝ, E) e hg
    (x := x) BoundarylessManifold.isInteriorPoint
  have ho := mfderiv_interiorAtlas I hgold x
  have hu := mfderiv_openRestriction I hf x x.property
  have hz' : (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x.val).comp e.symm.toContinuousLinearMap = 0 := by
    exact (congrArg (fun L : E →L[ℝ] ℝ => L.comp e.symm.toContinuousLinearMap)
      (ho.trans hu)).symm.trans (hd.symm.trans hz)
  apply hr x hx
  apply ContinuousLinearMap.ext
  intro v
  have hv := DFunLike.congr_fun hz' (e v)
  change (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x.val) (e.symm (e v)) = 0 at hv
  exact (congrArg (fun w : E => (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x.val) w)
    (e.symm_apply_apply v)).symm.trans hv

private def interiorSublevelHomeomorph {f : M → ℝ} {a : ℝ}
    (hi : {x | f x ≤ a} ⊆ I.interior M) :
    {x : M // f x ≤ a} ≃ₜ
      {x : intrinsicInterior I ∞ (by simp) (M := M) // f x ≤ a} where
  toFun x := ⟨⟨x.val, hi x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[reducible]
def interiorSublevelChartedSpace {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hi : {x | f x ≤ a} ⊆ I.interior M) :
    ChartedSpace (MorseHalfSpace m) {x : M // f x ≤ a} := by
  let U := intrinsicInterior I ∞ (by simp) (M := M)
  let _ := interiorChartedSpace I ∞ (M := U)
  let _ : IsManifold 𝓘(ℝ, E) ∞ U := interiorIsManifold I ∞
  let _ := sublevelChartedSpace (interiorModel e)
    (interiorFunction_smooth I e hf) (interiorFunction_regular I e hf hr)
  exact DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := MorseHalfSpace m) (interiorSublevelHomeomorph I hi)

theorem interiorSublevelIsManifold {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hi : {x | f x ≤ a} ⊆ I.interior M) :
    let _ := interiorSublevelChartedSpace I e hf hr hi
    IsManifold (morseModelWithCornersHalfSpace m) ∞ {x : M // f x ≤ a} := by
  let U := intrinsicInterior I ∞ (by simp) (M := M)
  let _ := interiorChartedSpace I ∞ (M := U)
  let _ : IsManifold 𝓘(ℝ, E) ∞ U := interiorIsManifold I ∞
  let _ := sublevelChartedSpace (interiorModel e)
    (interiorFunction_smooth I e hf) (interiorFunction_regular I e hf hr)
  let _ := sublevelIsManifold (interiorModel e)
    (interiorFunction_smooth I e hf) (interiorFunction_regular I e hf hr)
  exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := morseModelWithCornersHalfSpace m) (n := ∞) (interiorSublevelHomeomorph I hi)

theorem interiorSublevelBoundary_iff
    {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hi : {x | f x ≤ a} ⊆ I.interior M) (x : {x : M // f x ≤ a}) :
    let _ := interiorSublevelChartedSpace I e hf hr hi
    (morseModelWithCornersHalfSpace m).IsBoundaryPoint x ↔ f x = a := by
  let U := intrinsicInterior I ∞ (by simp) (M := M)
  let _ := interiorChartedSpace I ∞ (M := U)
  let _ : IsManifold 𝓘(ℝ, E) ∞ U := interiorIsManifold I ∞
  let _ := sublevelChartedSpace (interiorModel e)
    (interiorFunction_smooth I e hf) (interiorFunction_regular I e hf hr)
  let _ := sublevelIsManifold (interiorModel e)
    (interiorFunction_smooth I e hf) (interiorFunction_regular I e hf hr)
  let _ := interiorSublevelChartedSpace I e hf hr hi
  let d := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := morseModelWithCornersHalfSpace m) (n := ∞)
    (interiorSublevelHomeomorph I hi)
  let _ := interiorSublevelIsManifold I e hf hr hi
  exact ((d.isLocalDiffeomorph x).isBoundaryPoint_iff (by simp)).trans
    (sublevelBoundary_iff (interiorModel e) (interiorFunction_smooth I e hf)
      (interiorFunction_regular I e hf hr) (d x))


theorem contMDiff_interiorSublevel_inclusion
    {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hi : {x | f x ≤ a} ⊆ I.interior M) :
    let _ := interiorSublevelChartedSpace I e hf hr hi
    ContMDiff (morseModelWithCornersHalfSpace m) I ∞
      (Subtype.val : {x : M // f x ≤ a} → M) := by
  let U := intrinsicInterior I ∞ (by simp) (M := M)
  let _ := interiorChartedSpace I ∞ (M := U)
  let _ : IsManifold 𝓘(ℝ, E) ∞ U := interiorIsManifold I ∞
  let _ := sublevelChartedSpace (interiorModel e)
    (interiorFunction_smooth I e hf) (interiorFunction_regular I e hf hr)
  let _ := sublevelIsManifold (interiorModel e)
    (interiorFunction_smooth I e hf) (interiorFunction_regular I e hf hr)
  let _ := interiorSublevelChartedSpace I e hf hr hi
  let d := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := morseModelWithCornersHalfSpace m) (n := ∞)
    (interiorSublevelHomeomorph I hi)
  have hinc := contMDiff_sublevel_inclusion (interiorModel e)
    (interiorFunction_smooth I e hf) (interiorFunction_regular I e hf hr)
  have hval : ContMDiff (interiorModel e) I ∞ (Subtype.val : U → M) := by
    simpa only [interiorModel, ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left] using
      (contMDiff_intrinsicInterior_val I ∞ (show (∞ : ℕ∞ω) ≠ 0 from by simp))
  exact hval.comp (hinc.comp d.contMDiff)

theorem contMDiff_interiorSublevel_iff
    {E' H' X : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] [TopologicalSpace X] [ChartedSpace H' X]
    (J : ModelWithCorners ℝ E' H')
    {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (hi : {x | f x ≤ a} ⊆ I.interior M) {g : X → {x : M // f x ≤ a}} :
    let _ := interiorSublevelChartedSpace I e hf hr hi
    ContMDiff J (morseModelWithCornersHalfSpace m) ∞ g ↔
      ContMDiff J I ∞ (Subtype.val ∘ g) := by
  let U := intrinsicInterior I ∞ (by simp) (M := M)
  let _ := interiorChartedSpace I ∞ (M := U)
  let _ : IsManifold 𝓘(ℝ, E) ∞ U := interiorIsManifold I ∞
  let _ := sublevelChartedSpace (interiorModel e)
    (interiorFunction_smooth I e hf) (interiorFunction_regular I e hf hr)
  let _ := sublevelIsManifold (interiorModel e)
    (interiorFunction_smooth I e hf) (interiorFunction_regular I e hf hr)
  let _ := interiorSublevelChartedSpace I e hf hr hi
  let d := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := morseModelWithCornersHalfSpace m) (n := ∞)
    (interiorSublevelHomeomorph I hi)
  change ContMDiff J (morseModelWithCornersHalfSpace m) ∞ g ↔
    ContMDiff J I ∞ (Subtype.val ∘ g)
  constructor
  · intro hg
    exact (contMDiff_interiorSublevel_inclusion I e hf hr hi).comp hg
  · intro hg
    let q : X → U := fun x => ⟨(g x).val, hi (g x).property⟩
    have hqold : ContMDiff J I ∞ q :=
      (ContMDiff.subtypeVal_comp_iff U q).mp hg
    have hqnew : ContMDiff J 𝓘(ℝ, E) ∞ q :=
      (contMDiff_id_interiorAtlas I ∞ (M := U)).comp hqold
    have hq : ContMDiff J (interiorModel e) ∞ q := by
      simpa only [interiorModel, ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_right] using hqnew
    have hgd : ContMDiff J (morseModelWithCornersHalfSpace m) ∞ (d ∘ g) :=
      (contMDiff_sublevel_iff (interiorModel e) J
        (interiorFunction_smooth I e hf) (interiorFunction_regular I e hf hr) le_rfl).mpr hq
    exact (d.contMDiff_diffeomorph_comp_iff le_rfl).mp hgd

end DifferentialGeometry.Manifold.RegularLevel
