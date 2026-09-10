import DifferentialGeometry.Topology.Manifold.Involution.LocalLift
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {Q : Type*} [TopologicalSpace Q]

private theorem involutionQuotient_chart_transition
    (tau : M ≃ₘ⟮I, I⟯ M) (hfree : ∀ x : M, tau x ≠ x)
    (pi : M → Q)
    (hfibres : ∀ x y : M, pi x = pi y ↔ y = x ∨ y = tau x)
    (e e' : OpenPartialHomeomorph Q M)
    (he : (e.symm : M → Q) = pi) (he' : (e'.symm : M → Q) = pi)
    (a b : M) :
    ContMDiffOn I I ∞ ((e.trans (chartAt H a)).symm.trans (e'.trans (chartAt H b)))
      ((e.trans (chartAt H a)).symm.trans (e'.trans (chartAt H b))).source := by
  intro z hz
  change (z ∈ (chartAt H a).target ∧ (chartAt H a).symm z ∈ e.target) ∧
    (e.symm ((chartAt H a).symm z) ∈ e'.source ∧
      e' (e.symm ((chartAt H a).symm z)) ∈ (chartAt H b).source) at hz
  have hza : ContMDiffAt I I ∞ (chartAt H a).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) hz.1.1
  have hzlift : (chartAt H a).symm z ∈ (e.symm.trans e').source := ⟨hz.1.2, hz.2.1⟩
  have hzl : ContMDiffAt I I ∞ (e.symm.trans e') ((chartAt H a).symm z) :=
    ((involution_lift_transition_contMDiffOn tau hfree pi hfibres e e' he he')
      _ hzlift).contMDiffAt ((e.symm.trans e').open_source.mem_nhds hzlift)
  have hzb : ContMDiffAt I I ∞ (chartAt H b)
      ((e.symm.trans e') ((chartAt H a).symm z)) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas b) hz.2.2
  exact (hzb.comp z (hzl.comp z hza)).contMDiffWithinAt

theorem involutionQuotient_isManifold_of_rightInverse
    (tau : M ≃ₘ⟮I, I⟯ M) (hfree : ∀ x : M, tau x ≠ x)
    (pi : M → Q)
    (hfibres : ∀ x y : M, pi x = pi y ↔ y = x ∨ y = tau x)
    (hlocal : IsLocalHomeomorph pi) (g : Q → M) (hg : Function.RightInverse g pi) :
    let _ : ChartedSpace H Q := hlocal.chartedSpaceOfRightInverse hg
    IsManifold I ∞ Q := by
  let _ : ChartedSpace H Q := hlocal.chartedSpaceOfRightInverse hg
  refine { compatible := ?_ }
  rintro c c' ⟨q, rfl⟩ ⟨q', rfl⟩
  let e := hlocal.localInverseAt (g q)
  let e' := hlocal.localInverseAt (g q')
  have he : (e.symm : M → Q) = pi := hlocal.localInverseAt_symm (g q)
  have he' : (e'.symm : M → Q) = pi := hlocal.localInverseAt_symm (g q')
  let f := (e.trans (chartAt H (g q))).symm.trans (e'.trans (chartAt H (g q')))
  have hforward : ContMDiffOn I I ∞ f f.source :=
    involutionQuotient_chart_transition tau hfree pi hfibres e e' he he' (g q) (g q')
  have hbackward : ContMDiffOn I I ∞ f.symm f.target :=
    involutionQuotient_chart_transition tau hfree pi hfibres e' e he' he (g q') (g q)
  have hmaximal := f.mem_maximalAtlas_of_contMDiffOn hforward hbackward
  have hcompatible := (contDiffGroupoid ∞ I).compatible_of_mem_maximalAtlas
    (contDiffGroupoid ∞ I).id_mem_maximalAtlas hmaximal
  simpa only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans] using
    hcompatible

theorem involutionQuotient_isManifold
    (tau : M ≃ₘ⟮I, I⟯ M) (hfree : ∀ x : M, tau x ≠ x)
    (pi : M → Q)
    (hfibres : ∀ x y : M, pi x = pi y ↔ y = x ∨ y = tau x)
    (hlocal : IsLocalHomeomorph pi) (hsurjective : Function.Surjective pi) :
    let _ : ChartedSpace H Q := hlocal.chartedSpace hsurjective
    IsManifold I ∞ Q :=
  involutionQuotient_isManifold_of_rightInverse tau hfree pi hfibres hlocal
    hsurjective.hasRightInverse.choose hsurjective.hasRightInverse.choose_spec

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
