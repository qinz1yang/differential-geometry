import DifferentialGeometry.Topology.Manifold.Involution.QuotientManifold

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open scoped Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {Q : Type*} [TopologicalSpace Q]

private theorem involutionQuotient_projection_smooth
    (tau : M ≃ₘ⟮I, I⟯ M) (hfree : ∀ x : M, tau x ≠ x)
    (pi : M → Q)
    (hfibres : ∀ x y : M, pi x = pi y ↔ y = x ∨ y = tau x)
    (hlocal : IsLocalHomeomorph pi) (g : Q → M) (hg : Function.RightInverse g pi) :
    let _ : ChartedSpace H Q := hlocal.chartedSpaceOfRightInverse hg
    ContMDiff I I ∞ pi := by
  let _ : ChartedSpace H Q := hlocal.chartedSpaceOfRightInverse hg
  let _ : IsManifold I ∞ Q :=
    involutionQuotient_isManifold_of_rightInverse tau hfree pi hfibres hlocal g hg
  change ContMDiff I I ∞ pi
  intro x
  let q := pi x
  let a := g q
  let e := hlocal.localInverseAt a
  let c := chartAt H q
  have hga : pi a = q := hg q
  have heq : e q = a := by
    simpa only [hga] using (hlocal.localInverseAt_apply_self (x := a))
  have he_source : q ∈ e.source := by
    simpa only [hga] using (hlocal.apply_self_mem_localInverseAt_source (x := a))
  have hlift : ContMDiffAt I I ∞ (e ∘ pi) x :=
    (involution_inverseLift_contMDiffOn tau hfree pi hlocal.continuous hfibres e
      (fun _ hy => hlocal.apply_localInverseAt_of_mem hy)).contMDiffAt
        ((e.open_source.preimage hlocal.continuous).mem_nhds he_source)
  have ha_chart : e q ∈ (chartAt H a).source := by
    rw [heq]
    exact mem_chart_source H a
  have hchart : ContMDiffAt I I ∞ (chartAt H a) (e q) :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) ha_chart
  have hcoordinate : ContMDiffAt I I ∞ (c ∘ pi) x := by
    change ContMDiffAt I I ∞ ((chartAt H a) ∘ (e ∘ pi)) x
    exact hchart.comp x hlift
  have hinverse : ContMDiffAt I I ∞ c.symm (c q) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q)
      (mem_chart_target H q)
  apply (hinverse.comp x hcoordinate).congr_of_eventuallyEq
  filter_upwards [hlocal.continuous.continuousAt.preimage_mem_nhds
    (c.open_source.mem_nhds (mem_chart_source H q))] with y hy
  exact (c.left_inv hy).symm

private theorem involutionQuotient_localInverse_smooth
    (tau : M ≃ₘ⟮I, I⟯ M) (hfree : ∀ x : M, tau x ≠ x)
    (pi : M → Q)
    (hfibres : ∀ x y : M, pi x = pi y ↔ y = x ∨ y = tau x)
    (hlocal : IsLocalHomeomorph pi) (g : Q → M) (hg : Function.RightInverse g pi)
    (sigma : OpenPartialHomeomorph Q M) (hsigma : (sigma.symm : M → Q) = pi) :
    let _ : ChartedSpace H Q := hlocal.chartedSpaceOfRightInverse hg
    ContMDiffOn I I ∞ sigma sigma.source := by
  let _ : ChartedSpace H Q := hlocal.chartedSpaceOfRightInverse hg
  let _ : IsManifold I ∞ Q :=
    involutionQuotient_isManifold_of_rightInverse tau hfree pi hfibres hlocal g hg
  change ContMDiffOn I I ∞ sigma sigma.source
  intro q hq
  let a := g q
  let e := hlocal.localInverseAt a
  let c := chartAt H q
  have hga : pi a = q := hg q
  have heq : e q = a := by
    simpa only [hga] using (hlocal.localInverseAt_apply_self (x := a))
  have hsection : ∀ y ∈ sigma.source, pi (sigma y) = y := by
    intro y hy
    rw [← hsigma]
    exact sigma.left_inv hy
  have ha : a ∈ pi ⁻¹' sigma.source := by
    change pi a ∈ sigma.source
    rw [hga]
    exact hq
  have hlift : ContMDiffAt I I ∞ (sigma ∘ pi) a :=
    (involution_inverseLift_contMDiffOn tau hfree pi hlocal.continuous hfibres
      sigma hsection).contMDiffAt
        ((sigma.open_source.preimage hlocal.continuous).mem_nhds ha)
  have htarget : c q ∈ (chartAt H a).target := by
    change (chartAt H a) (e q) ∈ (chartAt H a).target
    rw [heq]
    exact mem_chart_target H a
  have hinverse_value : (chartAt H a).symm (c q) = a := by
    change (chartAt H a).symm ((chartAt H a) (e q)) = a
    rw [heq]
    exact (chartAt H a).left_inv (mem_chart_source H a)
  have hinverse : ContMDiffAt I I ∞ (chartAt H a).symm (c q) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) htarget
  have hchart : ContMDiffAt I I ∞ c q :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q)
      (mem_chart_source H q)
  have hlift' : ContMDiffAt I I ∞ (sigma ∘ pi) ((chartAt H a).symm (c q)) := by
    rw [hinverse_value]
    exact hlift
  have hsmooth : ContMDiffAt I I ∞ sigma q := by
    apply (hlift'.comp q (hinverse.comp q hchart)).congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds (mem_chart_source H q)] with y hy
    change y ∈ e.source ∧ e y ∈ (chartAt H a).source at hy
    change sigma y = sigma (pi ((chartAt H a).symm ((chartAt H a) (e y))))
    rw [(chartAt H a).left_inv hy.2, hlocal.apply_localInverseAt_of_mem hy.1]
  exact hsmooth.contMDiffWithinAt

theorem involutionQuotient_projection_isLocalDiffeomorph_of_rightInverse
    (tau : M ≃ₘ⟮I, I⟯ M) (hfree : ∀ x : M, tau x ≠ x)
    (pi : M → Q)
    (hfibres : ∀ x y : M, pi x = pi y ↔ y = x ∨ y = tau x)
    (hlocal : IsLocalHomeomorph pi) (g : Q → M) (hg : Function.RightInverse g pi) :
    let _ : ChartedSpace H Q := hlocal.chartedSpaceOfRightInverse hg
    IsLocalDiffeomorph I I ∞ pi := by
  let _ : ChartedSpace H Q := hlocal.chartedSpaceOfRightInverse hg
  change IsLocalDiffeomorph I I ∞ pi
  have hprojection : ContMDiff I I ∞ pi :=
    involutionQuotient_projection_smooth tau hfree pi hfibres hlocal g hg
  intro x
  let e := hlocal.localInverseAt x
  have he : (e.symm : M → Q) = pi := hlocal.localInverseAt_symm x
  let d : PartialDiffeomorph I I M Q ∞ := {
    toPartialEquiv := e.symm.toPartialEquiv
    open_source := e.open_target
    open_target := e.open_source
    contMDiffOn_toFun := by
      change ContMDiffOn I I ∞ e.symm e.target
      rw [he]
      exact hprojection.contMDiffOn
    contMDiffOn_invFun :=
      involutionQuotient_localInverse_smooth tau hfree pi hfibres hlocal g hg e he }
  refine ⟨d, hlocal.self_mem_localInverseAt_target, ?_⟩
  intro y _
  exact (congrFun he y).symm

theorem involutionQuotient_projection_isLocalDiffeomorph
    (tau : M ≃ₘ⟮I, I⟯ M) (hfree : ∀ x : M, tau x ≠ x)
    (pi : M → Q)
    (hfibres : ∀ x y : M, pi x = pi y ↔ y = x ∨ y = tau x)
    (hlocal : IsLocalHomeomorph pi) (hsurjective : Function.Surjective pi) :
    let _ : ChartedSpace H Q := hlocal.chartedSpace hsurjective
    IsLocalDiffeomorph I I ∞ pi :=
  involutionQuotient_projection_isLocalDiffeomorph_of_rightInverse tau hfree pi hfibres hlocal
    hsurjective.hasRightInverse.choose hsurjective.hasRightInverse.choose_spec

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
