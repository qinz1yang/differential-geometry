import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype

open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.Interval

theorem exists_iccInteriorStrip_diffeomorph
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (J : ModelWithCorners ℝ E H) (m : ℕ∞ω) {a b : ℝ} [Fact (a < b)] :
    let U : Opens (B × Icc a b) :=
      ⟨{q | a < q.2.val ∧ q.2.val < b},
        (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
          (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)⟩
    let V : Opens (B × ℝ) :=
      ⟨{q | a < q.2 ∧ q.2 < b},
        (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)⟩
    ∃ d : Diffeomorph (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) U V m,
      (∀ q : U, (d q : B × ℝ) = (q.val.1, q.val.2.val)) ∧
      ∀ y : V, ((d.symm y).val.1, (d.symm y).val.2.val) = y.val := by
  intro U V
  let f : U → V := fun q => ⟨(q.val.1, q.val.2.val), q.property⟩
  let g : V → U := fun y =>
    ⟨(y.val.1, ⟨y.val.2, y.property.1.le, y.property.2.le⟩), y.property⟩
  have hgf (q : U) : g (f q) = q := rfl
  have hfg (y : V) : f (g y) = y := rfl
  have hf : ContMDiff (J.prod (𝓡∂ 1)) (J.prod 𝓘(ℝ, ℝ)) m f := by
    apply (Poincare.Manifold.contMDiff_subtypeVal_comp_iff (n := m) V f).mp
    exact (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      (contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp contMDiff_subtype_val))
  have hg : ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod (𝓡∂ 1)) m g := by
    apply (Poincare.Manifold.contMDiff_subtypeVal_comp_iff (n := m) U g).mp
    apply ContMDiff.prodMk
    · exact contMDiff_fst.comp contMDiff_subtype_val
    · apply (contMDiff_iff_comp_subtypeVal_Icc (n := m)).mpr
      exact ⟨by fun_prop, contMDiff_snd.comp contMDiff_subtype_val⟩
  exact ⟨⟨⟨f, g, hgf, hfg⟩, hf, hg⟩, (fun _ => rfl), (fun _ => rfl)⟩

end Poincare.Manifold.Interval
