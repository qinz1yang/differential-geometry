import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set Filter
open scoped Topology Manifold ContDiff

theorem isLocalHomeomorph_of_free_two_point_fibres
    {X Q : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Q]
    (tau : X → X) (htau : Continuous tau) (hfree : ∀ x : X, tau x ≠ x)
    (pi : X → Q) (hpi : Continuous pi) (hopen : IsOpenMap pi)
    (hfibres : ∀ x y : X, pi x = pi y ↔ y = x ∨ y = tau x) :
    IsLocalHomeomorph pi := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨U, V, hU, hV, hx, htaux, hdisjoint⟩ := t2_separation (hfree x).symm
  let W : Set X := U ∩ tau ⁻¹' V
  have hW : IsOpen W := hU.inter (hV.preimage htau)
  refine ⟨W, hW.mem_nhds ⟨hx, htaux⟩, ?_⟩
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hpi.comp continuous_subtype_val) _ (hopen.comp hW.isOpenMap_subtype_val)
  intro p q hpq
  apply Subtype.ext
  rcases (hfibres p q).mp hpq with heq | heq
  · exact heq.symm
  · have hqV : (q : X) ∈ V := heq.symm ▸ p.2.2
    exact False.elim (Set.disjoint_left.mp hdisjoint q.2.1 hqV)

theorem continuousOn_eventuallyEq_or_of_two_separated_branches
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {U : Set X} (hU : IsOpen U) {f g h : X → Y}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) (hh : ContinuousOn h U)
    (hseparated : ∀ x ∈ U, g x ≠ h x)
    (hbranches : ∀ x ∈ U, f x = g x ∨ f x = h x)
    {x : X} (hx : x ∈ U) :
    f =ᶠ[𝓝 x] g ∨ f =ᶠ[𝓝 x] h := by
  have hfx := (hf x hx).continuousAt (hU.mem_nhds hx)
  have hgx := (hg x hx).continuousAt (hU.mem_nhds hx)
  have hhx := (hh x hx).continuousAt (hU.mem_nhds hx)
  rcases hbranches x hx with heq | heq
  · have hne : f x ≠ h x := by
      rw [heq]
      exact hseparated x hx
    have hnear := (hfx.ne_iff_eventually_ne hhx).mp hne
    left
    filter_upwards [hU.mem_nhds hx, hnear] with y hy hyne
    exact (hbranches y hy).resolve_right hyne
  · have hne : f x ≠ g x := by
      rw [heq]
      exact (hseparated x hx).symm
    have hnear := (hfx.ne_iff_eventually_ne hgx).mp hne
    right
    filter_upwards [hU.mem_nhds hx, hnear] with y hy hyne
    exact (hbranches y hy).resolve_left hyne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N]

theorem contMDiffOn_of_two_separated_branches
    {U : Set M} (hU : IsOpen U) {f g h : M → N}
    (hf : ContinuousOn f U) (hg : ContMDiffOn I J ∞ g U)
    (hh : ContMDiffOn I J ∞ h U)
    (hseparated : ∀ x ∈ U, g x ≠ h x)
    (hbranches : ∀ x ∈ U, f x = g x ∨ f x = h x) :
    ContMDiffOn I J ∞ f U := by
  intro x hx
  rcases continuousOn_eventuallyEq_or_of_two_separated_branches hU
      hf hg.continuousOn hh.continuousOn hseparated hbranches hx with heq | heq
  · have hs : ContMDiffAt I J ∞ f x :=
      ((hg x hx).contMDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq heq
    exact hs.contMDiffWithinAt
  · have hs : ContMDiffAt I J ∞ f x :=
      ((hh x hx).contMDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq heq
    exact hs.contMDiffWithinAt

variable [T2Space M]

theorem contMDiffOn_of_eq_self_or_free_diffeomorph
    (tau : M ≃ₘ⟮I, I⟯ M) (hfree : ∀ x : M, tau x ≠ x)
    {U : Set M} (hU : IsOpen U) {f : M → M} (hf : ContinuousOn f U)
    (hbranches : ∀ x ∈ U, f x = x ∨ f x = tau x) :
    ContMDiffOn I I ∞ f U :=
  contMDiffOn_of_two_separated_branches hU hf contMDiff_id.contMDiffOn
    tau.contMDiff.contMDiffOn (fun x _ => (hfree x).symm) hbranches

theorem involution_inverseLift_contMDiffOn
    {Q : Type*} [TopologicalSpace Q]
    (tau : M ≃ₘ⟮I, I⟯ M) (hfree : ∀ x : M, tau x ≠ x)
    (pi : M → Q) (hpi : Continuous pi)
    (hfibres : ∀ x y : M, pi x = pi y ↔ y = x ∨ y = tau x)
    (e : OpenPartialHomeomorph Q M)
    (hsection : ∀ y ∈ e.source, pi (e y) = y) :
    ContMDiffOn I I ∞ (e ∘ pi) (pi ⁻¹' e.source) := by
  apply contMDiffOn_of_eq_self_or_free_diffeomorph tau hfree (e.open_source.preimage hpi)
  · exact e.continuousOn.comp hpi.continuousOn (fun _ hx => hx)
  · intro x hx
    exact (hfibres x (e (pi x))).mp (hsection (pi x) hx).symm

theorem involution_lift_transition_contMDiffOn
    {Q : Type*} [TopologicalSpace Q]
    (tau : M ≃ₘ⟮I, I⟯ M) (hfree : ∀ x : M, tau x ≠ x)
    (pi : M → Q)
    (hfibres : ∀ x y : M, pi x = pi y ↔ y = x ∨ y = tau x)
    (e e' : OpenPartialHomeomorph Q M)
    (he : (e.symm : M → Q) = pi) (he' : (e'.symm : M → Q) = pi) :
    ContMDiffOn I I ∞ (e.symm.trans e') (e.symm.trans e').source := by
  apply contMDiffOn_of_eq_self_or_free_diffeomorph tau hfree
    (e.symm.trans e').open_source (e.symm.trans e').continuousOn
  intro x hx
  have hx' : e.symm x ∈ e'.source := hx.2
  have hprojection : pi ((e.symm.trans e') x) = pi x := by
    change pi (e' (e.symm x)) = pi x
    calc
      pi (e' (e.symm x)) = e'.symm (e' (e.symm x)) :=
        congrFun he'.symm (e' (e.symm x))
      _ = e.symm x := e'.left_inv hx'
      _ = pi x := congrFun he x
  exact (hfibres x ((e.symm.trans e') x)).mp hprojection.symm

theorem involution_lift_transition_exists_partialDiffeomorph
    {Q : Type*} [TopologicalSpace Q]
    (tau : M ≃ₘ⟮I, I⟯ M) (hfree : ∀ x : M, tau x ≠ x)
    (pi : M → Q)
    (hfibres : ∀ x y : M, pi x = pi y ↔ y = x ∨ y = tau x)
    (e e' : OpenPartialHomeomorph Q M)
    (he : (e.symm : M → Q) = pi) (he' : (e'.symm : M → Q) = pi) :
    ∃ d : PartialDiffeomorph I I M M ∞,
      d.toOpenPartialHomeomorph = e.symm.trans e' := by
  let d : PartialDiffeomorph I I M M ∞ := {
    toPartialEquiv := (e.symm.trans e').toPartialEquiv
    open_source := (e.symm.trans e').open_source
    open_target := (e.symm.trans e').open_target
    contMDiffOn_toFun := involution_lift_transition_contMDiffOn tau hfree pi hfibres
      e e' he he'
    contMDiffOn_invFun := involution_lift_transition_contMDiffOn tau hfree pi hfibres
      e' e he' he }
  exact ⟨d, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
