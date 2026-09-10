import DifferentialGeometry.Analysis.Calculus.RegularSplice
import DifferentialGeometry.Topology.VectorField.ChartPatchIndex
import DifferentialGeometry.Topology.VectorField.InteriorIndexLinearization
import DifferentialGeometry.Topology.VectorField.FiniteZeros

set_option autoImplicit false
noncomputable section
open Set Metric Filter Bundle
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M]
  (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H) [IsManifold I ∞ M]
  (c : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) M
    (EuclideanSpace ℝ (Fin (d + 1))) ∞)

omit [T2Space M] [IsManifold I ∞ M] in
private theorem patch_eq_of_component_eq
    (V W : ∀ x : M, TangentSpace I x)
    (g : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    {x : M} (hx : x ∈ c.source)
    (he : g (c x) = _root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm W (c x)) :
    patchInCoordinates c V g x = W x := by
  rw [patchInCoordinates_of_mem c V g hx]
  change (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) c x).inverse (g (c x)) = _
  rw [he, mpullback_symm_partialDiffeomorph_apply c (by simp) W hx]
  exact (isInvertible_mfderiv_partialDiffeomorph c (by simp) hx).inverse_apply_self _

omit [T2Space M] in
private theorem component_regular
    (V : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hreg : ∀ x, ∀ hz : V x = 0,
      (linearizationAtZero ((hV x).mdifferentiableAt (by simp)) hz).det ≠ 0)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (hy : y ∈ c.target)
    (hz : _root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V y = 0) :
    (fderiv ℝ (_root_.VectorField.mpullback
      𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V) y).det ≠ 0 := by
  have hvz := (mpullback_partialDiffeomorph_eq_zero_iff c.symm (by simp) V hy).mp hz
  have he := det_fderiv_mpullback_eq_linearizationAtZero I c.symm
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) hy
    ((hV (c.symm y)).mdifferentiableAt (by simp)) hvz
  change LinearMap.det (fderiv ℝ (_root_.VectorField.mpullback
    𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V) y).toLinearMap ≠ 0
  rw [he]
  exact hreg _ hvz

variable [CompactSpace M]

theorem exists_regular_chart_splice
    (V W : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M)))
    (hVreg : ∀ x, ∀ hz : V x = 0,
      (linearizationAtZero ((hV x).mdifferentiableAt (by simp)) hz).det ≠ 0)
    (hWreg : ∀ x, ∀ hz : W x = 0,
      (linearizationAtZero ((hW x).mdifferentiableAt (by simp)) hz).det ≠ 0)
    (hVint : ∀ x, V x = 0 → I.IsInteriorPoint x)
    (a : EuclideanSpace ℝ (Fin (d + 1))) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRt : closedBall a R ⊆ c.target) {S : Set M} (hS : IsCompact S)
    (hagree : ∀ x ∈ S, V =ᶠ[𝓝 x] W) :
    ∃ (G : ∀ x : M, TangentSpace I x)
      (hG : ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M))),
      (∀ x ∈ c.symm '' closedBall a r, G x = W x) ∧
      (∀ x ∉ c.symm '' ball a R, G x = V x) ∧
      (∀ x ∈ S, G =ᶠ[𝓝 x] V) ∧
      (∀ x ∉ c.symm '' closedBall a R, G =ᶠ[𝓝 x] V) ∧
      (∀ x, G x = 0 → I.IsInteriorPoint x) ∧
      (∀ x, ∀ hz : G x = 0,
        (linearizationAtZero ((hG x).mdifferentiableAt (by simp)) hz).det ≠ 0) ∧
      (∀ x, G x = 0 → HasContinuousIsolatedZero I G x) ∧ {x | G x = 0}.Finite := by
  let f := _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm V
  let w := _root_.VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm W
  have hf : ContDiffOn ℝ ∞ f c.target := contMDiffOn_vectorSpace_iff_contDiffOn.mp
    (contMDiffOn_mpullback_partialDiffeomorph c.symm (by simp) hV.contMDiffOn)
  have hw : ContDiffOn ℝ ∞ w c.target := contMDiffOn_vectorSpace_iff_contDiffOn.mp
    (contMDiffOn_mpullback_partialDiffeomorph c.symm (by simp) hW.contMDiffOn)
  let C := c.symm '' closedBall a R
  have hC : IsCompact C := (isCompact_closedBall a R).image_of_continuousOn
    (c.symm.contMDiffOn.continuousOn.mono hRt)
  have hCs : C ⊆ c.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.map_target (hRt hy)
  let A := c '' (S ∩ C)
  have hA : IsCompact A := (hS.inter_right hC.isClosed).image_of_continuousOn
    (c.contMDiffOn.continuousOn.mono (inter_subset_right.trans hCs))
  have hAt : A ⊆ c.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_source (hCs hx.2)
  have hAgerm : ∀ y ∈ A, f =ᶠ[𝓝 y] w := by
    rintro _ ⟨x, hx, rfl⟩
    have he := hagree x hx.1
    have ht := c.symm.toOpenPartialHomeomorph.continuousAt (c.map_source (hCs hx.2))
    have ht' : Tendsto c.symm (𝓝 (c x)) (𝓝 x) := by
      change Tendsto c.symm (𝓝 (c x)) (𝓝 (c.symm (c x))) at ht
      erw [c.left_inv (hCs hx.2)] at ht
      exact ht
    filter_upwards [ht'.eventually he] with y hy
    change (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I c.symm y).inverse
      (V (c.symm y)) = _
    rw [hy]
    rfl
  obtain ⟨g, hg, hinner, houter, hprotected, hreg, _⟩ :=
    Poincare.Calculus.exists_regular_ball_splice_preserving_germs a hr hrR c.open_target hRt
      hA hAt hf hw (component_regular I c V hV hVreg) (component_regular I c W hW hWreg) hAgerm
  have hfixed : ∀ y ∈ c.target \ closedBall a R, g y = f y :=
    fun _ hy => houter (fun h => hy.2 (ball_subset_closedBall h))
  let G := patchInCoordinates c V g
  have hG : ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)) :=
    contMDiff_patchInCoordinates c V g hV hg (isCompact_closedBall a R) hRt hfixed
  have hout : ∀ x ∉ C, G =ᶠ[𝓝 x] V := by
    intro x hx
    filter_upwards [patchInCoordinates_eventuallyEq_self c V g
      (isCompact_closedBall a R) hRt hfixed hx] with y hy
    exact TotalSpace.mk_injective y hy
  have hGI : ∀ x, G x = 0 → I.IsInteriorPoint x := by
    intro x hz
    by_cases hx : x ∈ c.source
    · have hh := Poincare.Manifold.isInteriorPoint_of_model_partialDiffeomorph I ∞ c.symm
        (by simp) (c.map_source hx)
      erw [c.left_inv hx] at hh
      exact hh
    · exact hVint x ((patchInCoordinates_of_not_mem c V g hx).symm.trans hz)
  have hGR : ∀ x, ∀ hz : G x = 0,
      (linearizationAtZero ((hG x).mdifferentiableAt (by simp)) hz).det ≠ 0 := by
    intro x hz
    by_cases hx : x ∈ c.source
    · have hd := (hg.contDiffAt (c.open_target.mem_nhds (c.map_source hx))).differentiableAt (by simp)
      have hgz := (patchInCoordinates_eq_zero_iff c V g hx).mp hz
      have he := det_linearizationAtZero_patchInCoordinates c V g hx hd hgz
      change LinearMap.det (linearizationAtZero
        (mdifferentiableAt_patchInCoordinates c V g hx hd)
        ((patchInCoordinates_eq_zero_iff c V g hx).mpr hgz)).toLinearMap ≠ 0
      rw [he]
      exact hreg _ (c.map_source hx) hgz
    · have he := hout x (fun h => hx (hCs h))
      have hvz : V x = 0 := he.self_of_nhds.symm.trans hz
      have htotal : (fun y => (⟨y, G y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
          (fun y => (⟨y, V y⟩ : TangentBundle I M)) := by
        filter_upwards [he] with y hy
        exact congrArg (fun v => (⟨y, v⟩ : TangentBundle I M)) hy
      rw [linearizationAtZero_congr_of_eventuallyEq
        ((hG x).mdifferentiableAt (by simp)) ((hV x).mdifferentiableAt (by simp)) hz hvz htotal]
      exact hVreg x hvz
  have hGIso : ∀ x, G x = 0 → HasContinuousIsolatedZero I G x := by
    intro x hz
    exact hasContinuousIsolatedZero_of_isInteriorPoint_det_ne_zero I (hGI x hz)
      ⟨univ, univ_mem, hG.continuous.continuousOn⟩ ((hG x).mdifferentiableAt (by simp)) hz (hGR x hz)
  refine ⟨G, hG, ?_, ?_, ?_, hout, hGI, hGR, hGIso,
    finite_zeroSet hG.continuous (fun x hz => (hGIso x hz).isolated)⟩
  · rintro x ⟨y, hy, rfl⟩
    have hyt := hRt (closedBall_subset_closedBall hrR.le hy)
    apply patch_eq_of_component_eq I c V W g (c.map_target hyt)
    erw [c.right_inv hyt]
    exact hinner hy
  · intro x hx
    exact patchInCoordinates_eq_self_off c V g (fun _ hy => houter hy.2) hx
  · intro x hx
    by_cases hxC : x ∈ C
    · have hxs := hCs hxC
      have he := hprotected (c x) ⟨x, ⟨hx, hxC⟩, rfl⟩
      have ht := c.toOpenPartialHomeomorph.continuousAt hxs
      filter_upwards [c.open_source.mem_nhds hxs, ht.eventually he] with y hy hye
      exact patch_eq_of_component_eq I c V V g hy hye
    · exact hout x hxC

end Poincare.VectorField
