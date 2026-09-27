import DifferentialGeometry.Topology.Manifold.RegularZero.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Manifold.RegularZero
variable {A B C : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]
  {S : Set A} {n : ℕ∞ω}


theorem injective_fderiv_fiberChart_symm (hn : n ≠ 0) (g : A → B)
    (Φ : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, B × C) A (B × C) n)
    (hΦ : ∀ y, (Φ y).1 = g y) (hΦS : Φ.source ⊆ S)
    (a : {y : A // y ∈ S ∧ g y = 0}) {z : C}
    (hz : z ∈ (fiberChart g Φ hΦ hΦS a).target) :
    Injective (fderiv ℝ (fun u => ((fiberChart g Φ hΦ hΦS a).symm u).val) z) := by
  let c := fiberChart g Φ hΦ hΦS a
  let h : C → A := fun u => (c.symm u).val
  have hh : DifferentiableAt ℝ h z :=
    ((contDiffOn_fiberChart_symm g Φ hΦ hΦS a).contDiffAt
      (c.open_target.mem_nhds hz)).differentiableAt hn
  have hs : h z ∈ Φ.source := c.map_target hz
  have hF : DifferentiableAt ℝ (fun y => (Φ y).2) (h z) :=
    (((contMDiffOn_iff_contDiffOn.mp Φ.contMDiffOn).contDiffAt
      (Φ.open_source.mem_nhds hs)).snd).differentiableAt hn
  have heq : (fun u => (Φ (h u)).2) =ᶠ[𝓝 z] id := by
    filter_upwards [c.open_target.mem_nhds hz] with u hu
    rw [show h u = Φ.symm (0,u) from fiberChart_symm_apply g Φ hΦ hΦS a hu]
    exact congrArg Prod.snd (Φ.right_inv hu)
  have hid : (fderiv ℝ (fun y => (Φ y).2) (h z)).comp (fderiv ℝ h z) = ContinuousLinearMap.id ℝ C := by
    exact (hF.hasFDerivAt.comp z hh.hasFDerivAt).unique
      ((hasFDerivAt_id z).congr_of_eventuallyEq heq)
  intro v w hvw
  have hh := congrArg (fderiv ℝ (fun y => (Φ y).2) (h z)) hvw
  change ((fderiv ℝ (fun y => (Φ y).2) (h z)).comp (fderiv ℝ h z)) v =
    ((fderiv ℝ (fun y => (Φ y).2) (h z)).comp (fderiv ℝ h z)) w at hh
  simpa only [hid, ContinuousLinearMap.id_apply] using hh

section FiniteDimension
variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] {g : A → B}


theorem mfderiv_inclusion (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    let _ := chartedSpace hn hs hg hr
    (show (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) →L[ℝ] A from
      mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A)
        (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x) =
      fderiv ℝ (fun u => ((chart hn hs hg hr x).symm u).val)
        (chart hn hs hg hr x x) := by
  let _ := chartedSpace hn hs hg hr
  let c := chart hn hs hg hr x
  have hh := (contDiffOn_chart_symm hn hs hg hr x).contDiffAt
    (c.open_target.mem_nhds (c.map_source (mem_chart_source hn hs hg hr x)))
  have hd : HasMFDerivAt 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A)
      (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x
      (fderiv ℝ (fun u => (c.symm u).val) (c x)) := by
    refine ⟨continuous_subtype_val.continuousAt,?_⟩
    simp only [mfld_simps]
    exact hh.differentiableAt hn |>.hasFDerivAt.hasFDerivWithinAt
  exact hd.mfderiv


theorem injective_mfderiv_inclusion (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    let _ := chartedSpace hn hs hg hr
    Injective (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A)
      (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x) := by
  let _ := chartedSpace hn hs hg hr
  let L : (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) →L[ℝ] A :=
    mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A)
      (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x
  change Injective L
  have he : L = fderiv ℝ (fun u => ((chart hn hs hg hr x).symm u).val)
      (chart hn hs hg hr x x) := mfderiv_inclusion hn hs hg hr x
  rw [he]
  unfold chart
  apply injective_fderiv_fiberChart_symm hn
  exact (chart hn hs hg hr x).map_source (mem_chart_source hn hs hg hr x)


theorem range_mfderiv_inclusion (hn : n ≠ 0) (hs : IsOpen S) (hg : ContDiffOn ℝ n g S)
    (hr : ∀ x ∈ S, g x = 0 → Surjective (fderiv ℝ g x)) (x : {y : A // y ∈ S ∧ g y = 0}) :
    let _ := chartedSpace hn hs hg hr
    LinearMap.range (show (Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) →ₗ[ℝ] A from
      (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ) 𝓘(ℝ, A)
        (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x).toLinearMap) =
      (fderiv ℝ g x.val).ker := by
  let _ := chartedSpace hn hs hg hr
  let P := Fin (Module.finrank ℝ A - Module.finrank ℝ B) → ℝ
  let L : P →L[ℝ] A := mfderiv 𝓘(ℝ, P) 𝓘(ℝ, A)
    (Subtype.val : {y : A // y ∈ S ∧ g y = 0} → A) x
  let c := chart hn hs hg hr x
  let h : P → A := fun u => (c.symm u).val
  have hx : x ∈ c.source := mem_chart_source hn hs hg hr x
  have hhx : h (c x) = x.val := congrArg Subtype.val (c.left_inv hx)
  have hh : DifferentiableAt ℝ h (c x) :=
    ((contDiffOn_chart_symm hn hs hg hr x).contDiffAt
      (c.open_target.mem_nhds (c.map_source hx))).differentiableAt hn
  have he : L = fderiv ℝ h (c x) := mfderiv_inclusion hn hs hg hr x
  have hg' : DifferentiableAt ℝ g (h (c x)) := by
    rw [hhx]
    exact (hg.contDiffAt (hs.mem_nhds x.property.1)).differentiableAt hn
  have hzero : (fun u : P => g (h u)) = fun _ => 0 := funext fun u => (c.symm u).property.2
  have hcomp : (fderiv ℝ g x.val).comp L = 0 := by
    rw [he, ← hhx]
    exact (hg'.hasFDerivAt.comp (c x) hh.hasFDerivAt).unique
      ((hasFDerivAt_const (𝕜 := ℝ) (0 : B) (c x)).congr_of_eventuallyEq (Eventually.of_forall fun u => congrFun hzero u))
  have hle : L.toLinearMap.range ≤ (fderiv ℝ g x.val).ker := by
    rintro v ⟨u,rfl⟩
    exact congrArg (fun T : P →L[ℝ] B => T u) hcomp
  change L.toLinearMap.range = (fderiv ℝ g x.val).ker
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (show Injective L from injective_mfderiv_inclusion hn hs hg hr x)]
  have hk := (fderiv ℝ g x.val).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (hr x x.property.1 x.property.2), finrank_top] at hk
  rw [Module.finrank_fin_fun]
  omega

end FiniteDimension
end DifferentialGeometry.Manifold.RegularZero
