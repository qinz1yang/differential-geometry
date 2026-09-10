import DifferentialGeometry.Topology.VectorField.ChartPatchIndex
import DifferentialGeometry.Analysis.Calculus.BumpPerturbation
import DifferentialGeometry.Topology.LocalDegree.FiniteZeros

set_option autoImplicit false
noncomputable section
open Bundle Set Metric Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.VectorField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ E H} [IsManifold I 1 M]
  (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
  (V : ∀ x : M, TangentSpace I x)

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I 1 M] in
theorem support_patchInCoordinates_bumpPerturbation (ρ : E → ℝ) (v : E)
    (hρ : Function.support ρ ⊆ c.target) :
    Function.support (fun x => patchInCoordinates c V
      (DifferentialGeometry.Calculus.bumpPerturbation
        (_root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V) ρ v) x - V x) =
      c.symm '' {y | ρ y ≠ 0 ∧ v ≠ 0} := by
  let f : E → E := _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V
  let g : E → E := DifferentialGeometry.Calculus.bumpPerturbation f ρ v
  have heq (x : M) (hx : x ∈ c.source) :
      patchInCoordinates c V g x = V x ↔ ρ (c x) = 0 ∨ v = 0 := by
    rw [patchInCoordinates_of_mem c V g hx]
    change (mfderiv I 𝓘(ℝ, E) c x).inverse (g (c x)) = V x ↔ _
    erw [(isInvertible_mfderiv_partialDiffeomorph c (by simp) hx).inverse_apply_eq]
    rw [← mpullback_symm_partialDiffeomorph_apply c (by simp) V hx]
    change f (c x) - ρ (c x) • v = f (c x) ↔ _
    rw [sub_eq_self, smul_eq_zero]
  ext x
  change patchInCoordinates c V g x - V x ≠ 0 ↔ _
  rw [sub_ne_zero]
  constructor
  · intro hx
    have hxc : x ∈ c.source := by
      by_contra hn
      exact hx (patchInCoordinates_of_not_mem c V g hn)
    have hh : ρ (c x) ≠ 0 ∧ v ≠ 0 := not_or.mp (hx ∘ (heq x hxc).mpr)
    exact ⟨c x, hh, c.left_inv hxc⟩
  · rintro ⟨y, hy, rfl⟩
    have hyt := hρ hy.1
    intro hh
    have hh' := (heq _ (c.map_target hyt)).mp hh
    erw [c.right_inv hyt] at hh'
    exact (not_or.mpr hy) hh'

theorem exists_small_regular_chart_perturbation
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (a : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRt : closedBall a R ⊆ c.target)
    (hannulus : ∀ y ∈ closedBall a R, r ≤ dist y a → V (c.symm y) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ρ : E → ℝ) (v : E) (G : ∀ x : M, TangentSpace I x)
      (hG : ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M))),
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ Function.support ρ = ball a R ∧
      EqOn ρ 1 (closedBall a r) ∧ (∀ y, ρ y ∈ Icc (0 : ℝ) 1) ∧
      G = patchInCoordinates c V (DifferentialGeometry.Calculus.bumpPerturbation
        (_root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V) ρ v) ∧
      ‖v‖ < ε ∧
      Function.support (fun x => G x - V x) = {x ∈ c.symm '' ball a R | v ≠ 0} ∧
      IsCompact (tsupport (fun x => G x - V x)) ∧
      tsupport (fun x => G x - V x) ⊆ c.symm '' closedBall a R ∧
      (∀ x ∉ c.symm '' closedBall a R,
        (fun y => (⟨y, G y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
          (fun y => (⟨y, V y⟩ : TangentBundle I M))) ∧
      (∀ y ∈ c.target, _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm G y =
        DifferentialGeometry.Calculus.bumpPerturbation
          (_root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V) ρ v y) ∧
      (∀ y ∈ c.target, ‖(show E from _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm G y) -
        (show E from _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V y)‖ < ε) ∧
      (∀ y ∈ sphere a R, _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm G y =
        _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V y) ∧
      {x ∈ c.symm '' closedBall a R | G x = 0}.Finite ∧
      (∀ x ∈ c.symm '' closedBall a R, ∀ hz : G x = 0,
        x ∈ c.symm '' ball a r ∧ HasContinuousIsolatedZero I G x ∧
        LinearMap.det (linearizationAtZero ((hG x).mdifferentiableAt (by simp)) hz).toLinearMap ≠ 0) := by
  let f : E → E := _root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V
  have hf : ContDiffOn ℝ ∞ f c.target :=
    contMDiffOn_vectorSpace_iff_contDiffOn.mp
      (contMDiffOn_mpullback_partialDiffeomorph c.symm (by simp) hV.contMDiffOn)
  have hn : ∀ y ∈ closedBall a R, r ≤ dist y a → f y ≠ 0 := by
    intro y hy hyr hz
    exact hannulus y hy hyr
      ((mpullback_partialDiffeomorph_eq_zero_iff c.symm (by simp) V (hRt hy)).mp hz)
  obtain ⟨ρ, v, hρ, hρcompact, hρsupport, hρone, hρrange, hv, _, hg, hfixed, hsmall, hregular, hfinite⟩ :=
    DifferentialGeometry.Calculus.exists_small_regular_ball_perturbation a hr hrR c.open_target hRt hf hn hε
  let g : E → E := DifferentialGeometry.Calculus.bumpPerturbation f ρ v
  have hagree : ∀ y ∈ c.target \ closedBall a R, g y = f y := by
    intro y hy
    exact hfixed y (le_of_lt (lt_of_not_ge hy.2))
  let G := patchInCoordinates c V g
  have hG : ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)) :=
    contMDiff_patchInCoordinates c V g hV hg (isCompact_closedBall a R) hRt hagree
  refine ⟨ρ, v, G, hG, hρ, hρcompact, hρsupport, hρone, hρrange, rfl, hv, ?_,
    isCompact_tsupport_patchInCoordinates_sub c V g (isCompact_closedBall a R) hRt hagree,
    tsupport_patchInCoordinates_sub_subset c V g (isCompact_closedBall a R) hRt hagree,
    fun x hx => patchInCoordinates_eventuallyEq_self c V g (isCompact_closedBall a R) hRt hagree hx,
    fun y hy => mpullback_patchInCoordinates c V g hy, ?_, ?_, ?_, ?_⟩
  · have hs : Function.support ρ ⊆ c.target := by
      rw [hρsupport]
      exact ball_subset_closedBall.trans hRt
    rw [support_patchInCoordinates_bumpPerturbation c V ρ v hs]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hρsupport ▸ hy.1, rfl⟩, hy.2⟩
    · rintro ⟨⟨y, hy, rfl⟩, hv⟩
      exact ⟨y, ⟨(show y ∈ Function.support ρ from hρsupport.symm ▸ hy), hv⟩, rfl⟩
  · intro y hy
    erw [mpullback_patchInCoordinates c V g hy]
    exact hsmall y
  · intro y hy
    erw [mpullback_patchInCoordinates c V g (hRt (sphere_subset_closedBall hy))]
    exact hfixed y (mem_sphere.mp hy).ge
  · apply (hfinite.image c.symm).subset
    rintro x ⟨⟨y, hy, rfl⟩, hz⟩
    have hzy := (patchInCoordinates_eq_zero_iff c V g (c.map_target (hRt hy))).mp hz
    have hgzero : g y = 0 := by
      erw [c.right_inv (hRt hy)] at hzy
      exact hzy
    exact ⟨y, ⟨hy, hgzero⟩, rfl⟩
  · rintro x ⟨y, hy, rfl⟩ hz
    have hx := c.map_target (hRt hy)
    have hzy := (patchInCoordinates_eq_zero_iff c V g hx).mp hz
    have hgzero : g y = 0 := by
      erw [c.right_inv (hRt hy)] at hzy
      exact hzy
    obtain ⟨hinner, hdet⟩ := hregular y hy hgzero
    have hiso : DifferentialGeometry.LocalDegree.isolatedZero g y :=
      DifferentialGeometry.LocalDegree.isolatedZero_of_finite_zeroSet
        (closedBall_mem_nhds_of_mem (ball_subset_ball hrR.le hinner))
        (hg.continuousOn.mono hRt) hfinite hgzero
    have hiso' : DifferentialGeometry.LocalDegree.isolatedZero g (c (c.symm y)) := by
      erw [c.right_inv (hRt hy)]
      exact hiso
    refine ⟨⟨y, hinner, rfl⟩,
      hasContinuousIsolatedZero_patchInCoordinates c V g hx hiso', ?_⟩
    have hd : DifferentiableAt ℝ g (c (c.symm y)) :=
      (hg.contDiffAt (c.open_target.mem_nhds (c.map_source hx))).differentiableAt (by simp)
    have heq := det_linearizationAtZero_patchInCoordinates c V g hx hd hzy
    erw [heq]
    erw [c.right_inv (hRt hy)]
    exact hdet

end DifferentialGeometry.VectorField
