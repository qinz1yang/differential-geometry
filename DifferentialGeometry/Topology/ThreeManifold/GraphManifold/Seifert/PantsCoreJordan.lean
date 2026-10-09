import DifferentialGeometry.Topology.PlanarJordan.BoundaryGermExtension
import DifferentialGeometry.Topology.PlanarJordan.CompactRegion
import DifferentialGeometry.Topology.PlanarJordan.AmbientExtension
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding

/-!
# Replacing a map inside a round circle by a plane diffeomorphism

A smooth injective map with invertible differential on an open annulus around a round circle in
`ℂ`, whose outer half meets an unbounded connected set avoiding the image circle, agrees near the
circle with a diffeomorphism of `ℂ` carrying the open disc into the bounded side of the image
circle.
-/

set_option autoImplicit false

open Set Metric Bornology
open scoped ContDiff Manifold

namespace GC.Seifert

open Schoenflies (Plane)
open DifferentialGeometry.Topology.Manifold
  (isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv exists_partialDiffeomorph_of_injOn)
open DifferentialGeometry.Topology.PlanarJordan (isJordanCurve_range_of_isEmbedding_addCircle
  closure_inside_frontier_eq_of_isCompact exists_diffeomorph_eqOn_neighborhood_of_jordan_curve)

private theorem subset_outside_of_isPreconnected {C S : Set Plane} (hS : IsPreconnected S)
    (hb : ¬ IsBounded S) (hd : Disjoint S C) : S ⊆ Schoenflies.outside C := by
  intro x hx
  refine ⟨disjoint_left.mp hd hx, fun hc => hb (hc.subset ?_)⟩
  exact hS.subset_connectedComponentIn hx (fun y hy => disjoint_left.mp hd hy)

private theorem isPreconnected_annulus (c : Plane) {a b : ℝ} (ha : 0 ≤ a) :
    IsPreconnected {x : Plane | a < ‖x - c‖ ∧ ‖x - c‖ < b} := by
  have hrank : 1 < Module.rank ℝ Plane := by rw [← Module.finrank_eq_rank]; simp
  let g : Plane × ℝ → Plane := fun p => c + p.2 • p.1
  have hg : Continuous g := continuous_const.add (continuous_snd.smul continuous_fst)
  have heq : g '' (sphere (0 : Plane) 1 ×ˢ Ioo a b) =
      {x : Plane | a < ‖x - c‖ ∧ ‖x - c‖ < b} := by
    ext x
    constructor
    · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
      have hu' : ‖u‖ = 1 := by simpa using hu
      have ht0 : 0 < t := ha.trans_lt ht.1
      simp only [g, add_sub_cancel_left, norm_smul, hu', mul_one, Real.norm_eq_abs,
        abs_of_pos ht0, mem_ofPred_eq]
      exact ht
    · rintro ⟨h1, h2⟩
      have hpos : 0 < ‖x - c‖ := ha.trans_lt h1
      refine ⟨(‖x - c‖⁻¹ • (x - c), ‖x - c‖), ⟨?_, h1, h2⟩, ?_⟩
      · simp [norm_smul, hpos.ne']
      · simp only [g, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, add_sub_cancel]
  rw [← heq]
  exact ((isConnected_sphere hrank 0 zero_le_one).isPreconnected.prod isPreconnected_Ioo).image g
    hg.continuousOn

private theorem closure_inside_sphere {c : Plane} {r : ℝ} (hr : 0 < r) :
    closure (Schoenflies.inside (sphere c r)) = closedBall c r := by
  obtain ⟨γ, hγ, hγr⟩ := exists_isSmoothEmbedding_addCircle_range_eq_sphere
    (E := Plane) (by simp) c hr
  have hJ : Schoenflies.IsJordanCurve (frontier (closedBall c r)) := by
    rw [frontier_closedBall c hr.ne', ← hγr]
    exact isJordanCurve_range_of_isEmbedding_addCircle
      one_ne_zero hγ.isEmbedding
  have hne : (interior (closedBall c r)).Nonempty := by
    rw [interior_closedBall c hr.ne']
    exact nonempty_ball.mpr hr
  have h := closure_inside_frontier_eq_of_isCompact
    (isCompact_closedBall c r) hJ hne
  rwa [frontier_closedBall c hr.ne'] at h

private theorem exists_plane_core_replacement {F : Plane → Plane} {c : Plane} {r δ : ℝ}
    (hδ : 0 < δ) (hδr : δ < r)
    (hF : ContDiffOn ℝ ∞ F {x | r - δ < ‖x - c‖ ∧ ‖x - c‖ < r + δ})
    (hder : ∀ x, r - δ < ‖x - c‖ → ‖x - c‖ < r + δ →
      ∃ L : Plane ≃L[ℝ] Plane, HasFDerivAt F (L : Plane →L[ℝ] Plane) x)
    (hinj : InjOn F {x | r - δ < ‖x - c‖ ∧ ‖x - c‖ < r + δ})
    (hout : ∃ z₀, r < ‖z₀ - c‖ ∧ ‖z₀ - c‖ < r + δ ∧ ∃ S : Set Plane, IsPreconnected S ∧
      F z₀ ∈ S ∧ Disjoint S (F '' sphere c r) ∧ ¬ IsBounded S) :
    ∃ Q : Plane ≃ₘ[ℝ] Plane, (∃ V : Set Plane, IsOpen V ∧ sphere c r ⊆ V ∧ EqOn Q F V) ∧
      ∀ S : Set Plane, IsPreconnected S → ¬ IsBounded S →
        Disjoint S (F '' sphere c r) → Disjoint S (Q '' ball c r) := by
  set A : Set Plane := {x | r - δ < ‖x - c‖ ∧ ‖x - c‖ < r + δ} with hAdef
  have hr : 0 < r := hδ.trans hδr
  have hcont : Continuous fun x : Plane => ‖x - c‖ :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have hA : IsOpen A := (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hsph : sphere c r ⊆ A := by
    intro x hx
    have hx' : ‖x - c‖ = r := mem_sphere_iff_norm.mp hx
    exact ⟨by linarith, by linarith⟩
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) ∞ F A := by
    rintro ⟨x, hx1, hx2⟩
    obtain ⟨L, hL⟩ := hder x hx1 hx2
    exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv
      F hF.contMDiffOn hA x ⟨hx1, hx2⟩ L hL.hasMFDerivAt
  obtain ⟨d, hds, hdt, hdF⟩ :=
    exists_partialDiffeomorph_of_injOn hA hlocal hinj
  obtain ⟨γ₀, hγ₀, hγ₀r⟩ := exists_isSmoothEmbedding_addCircle_range_eq_sphere
    (E := Plane) (by simp) c hr
  have hγ₀d : range γ₀ ⊆ d.source := by rw [hγ₀r, hds]; exact hsph
  have hγ₁ := DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph d hγ₀ hγ₀d
  set C : Set Plane := F '' sphere c r with hCdef
  have hγ₁r : range (d ∘ γ₀) = C := by rw [range_comp, hγ₀r, hdF]
  have hJ : Schoenflies.IsJordanCurve C := by
    rw [← hγ₁r]
    exact isJordanCurve_range_of_isEmbedding_addCircle
      one_ne_zero hγ₁.isEmbedding
  have hsep := Schoenflies.jordan_curve_theorem hJ
  have hnotC : ∀ x ∈ A, ‖x - c‖ ≠ r → F x ∉ C := by
    rintro x hxA hx ⟨y, hy, hxy⟩
    have hyx := hinj (hsph hy) hxA hxy
    rw [← hyx] at hx
    exact hx (mem_sphere_iff_norm.mp hy)
  obtain ⟨z₀, hz₁, hz₂, S, hSc, hzS, hSd, hSb⟩ := hout
  have hOA : {x : Plane | r < ‖x - c‖ ∧ ‖x - c‖ < r + δ} ⊆ A :=
    fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hOut : F '' {x : Plane | r < ‖x - c‖ ∧ ‖x - c‖ < r + δ} ⊆ Schoenflies.outside C := by
    have hU : IsPreconnected (S ∪ F '' {x : Plane | r < ‖x - c‖ ∧ ‖x - c‖ < r + δ}) :=
      hSc.union (F z₀) hzS ⟨z₀, ⟨hz₁, hz₂⟩, rfl⟩
        ((isPreconnected_annulus c hr.le).image F (hF.continuousOn.mono hOA))
    refine subset_union_right.trans (subset_outside_of_isPreconnected hU
      (fun hb => hSb (hb.subset subset_union_left)) ?_)
    rw [disjoint_union_left]
    refine ⟨hSd, disjoint_left.mpr ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hnotC x (hOA hx) (ne_of_gt hx.1)
  have hIA : {x : Plane | r - δ < ‖x - c‖ ∧ ‖x - c‖ < r} ⊆ A :=
    fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hIn : F '' {x : Plane | r - δ < ‖x - c‖ ∧ ‖x - c‖ < r} ⊆ Schoenflies.inside C := by
    have hcov : F '' {x : Plane | r - δ < ‖x - c‖ ∧ ‖x - c‖ < r} ⊆
        Schoenflies.inside C ∪ Schoenflies.outside C := by
      rw [Schoenflies.inside_union_outside]
      rintro _ ⟨x, hx, rfl⟩
      exact hnotC x (hIA hx) (ne_of_lt hx.2)
    refine (((isPreconnected_annulus c (by linarith : (0 : ℝ) ≤ r - δ)).image F
      (hF.continuousOn.mono hIA)).subset_or_subset hsep.isOpen_inside hsep.isOpen_outside
      Schoenflies.disjoint_inside_outside hcov).resolve_right ?_
    intro hIo
    obtain ⟨y, hy⟩ : C.Nonempty := (NormedSpace.sphere_nonempty.mpr hr.le).image F
    have hyfr : y ∈ frontier (Schoenflies.inside C) := by rw [hsep.frontier_inside]; exact hy
    have hT : IsOpen (F '' A) := hdt ▸ d.open_target
    obtain ⟨v, ⟨x, hxA, rfl⟩, hxi⟩ :=
      mem_closure_iff.mp (frontier_subset_closure hyfr) _ hT (image_mono hsph hy)
    rcases lt_trichotomy ‖x - c‖ r with h | h | h
    · exact disjoint_left.mp Schoenflies.disjoint_inside_outside hxi (hIo ⟨x, ⟨hxA.1, h⟩, rfl⟩)
    · exact hxi.1 ⟨x, mem_sphere_iff_norm.mpr h, rfl⟩
    · exact disjoint_left.mp Schoenflies.disjoint_inside_outside hxi (hOut ⟨x, ⟨h, hxA.2⟩, rfl⟩)
  have hclC : closure (Schoenflies.inside C) = Schoenflies.inside C ∪ C :=
    (Schoenflies.IsRegionOf.inside C).closure_eq hsep
  have hc : d.toOpenPartialHomeomorph.IsImage (closure (Schoenflies.inside (range γ₀)))
      (closure (Schoenflies.inside (range (d ∘ γ₀)))) := by
    rw [hγ₀r, hγ₁r, closure_inside_sphere hr, hclC]
    intro x hx
    have hxA : x ∈ A := by rw [← hds]; exact hx
    change d x ∈ Schoenflies.inside C ∪ C ↔ x ∈ closedBall c r
    rw [hdF, mem_closedBall_iff_norm]
    rcases lt_trichotomy ‖x - c‖ r with h | h | h
    · exact iff_of_true (Or.inl (hIn ⟨x, ⟨hxA.1, h⟩, rfl⟩)) h.le
    · exact iff_of_true (Or.inr ⟨x, mem_sphere_iff_norm.mpr h, rfl⟩) h.le
    · refine iff_of_false ?_ (not_le.mpr h)
      have ho := hOut ⟨x, ⟨h, hxA.2⟩, rfl⟩
      rintro (hi | hC)
      · exact disjoint_left.mp Schoenflies.disjoint_inside_outside hi ho
      · exact ho.1 hC
  obtain ⟨Q, -, hQcl, V, hV, hγV, -, hQV⟩ :=
    exists_diffeomorph_eqOn_neighborhood_of_jordan_curve
      hγ₀ hγ₁ d hc hγ₀d
  rw [hγ₀r, hγ₁r, closure_inside_sphere hr] at hQcl
  rw [hγ₀r] at hγV
  refine ⟨Q, ⟨V, hV, hγV, fun x hx => (hQV hx).trans (congrFun hdF x)⟩, ?_⟩
  intro T hT hTb hTd
  have hTo := subset_outside_of_isPreconnected hT hTb hTd
  rw [hsep.outside_eq_compl_closure_inside] at hTo
  rw [disjoint_right]
  rintro _ ⟨x, hx, rfl⟩ hQx
  exact hTo hQx (hQcl ▸ mem_image_of_mem Q (ball_subset_closedBall hx))

theorem exists_core_replacement {E : ℂ → ℂ} {c : ℂ} {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r)
    (hE : ContDiffOn ℝ ∞ E {z | r - δ < ‖z - c‖ ∧ ‖z - c‖ < r + δ})
    (hdet : ∀ z, r - δ < ‖z - c‖ → ‖z - c‖ < r + δ → (fderiv ℝ E z).det ≠ 0)
    (hinj : Set.InjOn E {z | r - δ < ‖z - c‖ ∧ ‖z - c‖ < r + δ})
    (hout : ∃ z₀, r < ‖z₀ - c‖ ∧ ‖z₀ - c‖ < r + δ ∧ ∃ S : Set ℂ, IsPreconnected S ∧
      E z₀ ∈ S ∧ Disjoint S (E '' Metric.sphere c r) ∧ ¬ Bornology.IsBounded S) :
    ∃ Q : ℂ → ℂ, ContDiff ℝ ∞ Q ∧ Function.Injective Q ∧ (∀ u, (fderiv ℝ Q u).det ≠ 0) ∧
      (∃ V : Set ℂ, IsOpen V ∧ Metric.sphere c r ⊆ V ∧ Set.EqOn Q E V) ∧
      ∀ S : Set ℂ, IsPreconnected S → ¬ Bornology.IsBounded S →
        Disjoint S (E '' Metric.sphere c r) → Disjoint S (Q '' Metric.ball c r) := by
  let e : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr
  have hn (z w : ℂ) : ‖e z - e w‖ = ‖z - w‖ := by rw [← map_sub, LinearIsometryEquiv.norm_map]
  have hn' (x : Plane) (w : ℂ) : ‖e.symm x - w‖ = ‖x - e w‖ := by
    rw [← hn, LinearIsometryEquiv.apply_symm_apply]
  have hcont : Continuous fun z : ℂ => ‖z - c‖ :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have hA : IsOpen {z : ℂ | r - δ < ‖z - c‖ ∧ ‖z - c‖ < r + δ} :=
    (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hmem (x : Plane) (hx : r - δ < ‖x - e c‖ ∧ ‖x - e c‖ < r + δ) :
      e.symm x ∈ {z : ℂ | r - δ < ‖z - c‖ ∧ ‖z - c‖ < r + δ} := by
    change r - δ < ‖e.symm x - c‖ ∧ ‖e.symm x - c‖ < r + δ
    rw [hn']
    exact hx
  let F : Plane → Plane := fun x => e (E (e.symm x))
  have hF : ContDiffOn ℝ ∞ F {x | r - δ < ‖x - e c‖ ∧ ‖x - e c‖ < r + δ} :=
    e.contDiff.comp_contDiffOn (hE.comp e.symm.contDiff.contDiffOn hmem)
  have hder : ∀ x, r - δ < ‖x - e c‖ → ‖x - e c‖ < r + δ →
      ∃ L : Plane ≃L[ℝ] Plane, HasFDerivAt F (L : Plane →L[ℝ] Plane) x := by
    intro x h1 h2
    have hz := hmem x ⟨h1, h2⟩
    have hd : HasFDerivAt E (fderiv ℝ E (e.symm x)) (e.symm x) :=
      ((hE.contDiffAt (hA.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt
    let D : ℂ ≃L[ℝ] ℂ := (LinearMap.equivOfDetNeZero (fderiv ℝ E (e.symm x) : ℂ →ₗ[ℝ] ℂ)
      (hdet _ hz.1 hz.2)).toContinuousLinearEquiv
    refine ⟨(e.symm.toContinuousLinearEquiv.trans D).trans e.toContinuousLinearEquiv, ?_⟩
    have h := e.toContinuousLinearEquiv.hasFDerivAt.comp x
      (hd.comp x e.symm.toContinuousLinearEquiv.hasFDerivAt)
    exact h.congr_fderiv (by ext v; rfl)
  have hinj' : InjOn F {x | r - δ < ‖x - e c‖ ∧ ‖x - e c‖ < r + δ} := by
    intro x hx y hy hxy
    exact e.symm.injective (hinj (hmem x hx) (hmem y hy) (e.injective hxy))
  have himsph : e.symm '' sphere (e c) r = sphere c r := by simp
  have hFsph : F '' sphere (e c) r = e '' (E '' sphere c r) := by
    rw [← himsph, image_image, image_image]
  have hbd (S : Set ℂ) (hS : ¬ IsBounded S) : ¬ IsBounded (e '' S) := by
    intro hb
    apply hS
    have h := e.symm.lipschitzWith.isBounded_image hb
    rwa [← image_comp, show (e.symm ∘ e : ℂ → ℂ) = id from funext e.symm_apply_apply,
      image_id] at h
  obtain ⟨z₀, hz₁, hz₂, S, hSc, hzS, hSd, hSb⟩ := hout
  have hout' : ∃ x₀, r < ‖x₀ - e c‖ ∧ ‖x₀ - e c‖ < r + δ ∧ ∃ S' : Set Plane,
      IsPreconnected S' ∧ F x₀ ∈ S' ∧ Disjoint S' (F '' sphere (e c) r) ∧ ¬ IsBounded S' := by
    refine ⟨e z₀, by rw [hn]; exact hz₁, by rw [hn]; exact hz₂, e '' S,
      hSc.image e e.continuous.continuousOn, ?_, ?_, hbd S hSb⟩
    · simp only [F, LinearIsometryEquiv.symm_apply_apply]
      exact mem_image_of_mem e hzS
    · rw [hFsph]
      exact (disjoint_image_iff e.injective).mpr hSd
  obtain ⟨Qp, ⟨V, hV, hsV, hQV⟩, hfin⟩ := exists_plane_core_replacement hδ hδr hF hder hinj' hout'
  let Q : ℂ → ℂ := fun u => e.symm (Qp (e u))
  let Q' : ℂ → ℂ := fun u => e.symm (Qp.symm (e u))
  have hQ : ContDiff ℝ ∞ Q := e.symm.contDiff.comp (Qp.contDiff.comp e.contDiff)
  have hQ' : ContDiff ℝ ∞ Q' := e.symm.contDiff.comp (Qp.symm.contDiff.comp e.contDiff)
  refine ⟨Q, hQ, e.symm.injective.comp (Qp.injective.comp e.injective), ?_,
    ⟨e ⁻¹' V, hV.preimage e.continuous, ?_, ?_⟩, ?_⟩
  · intro u
    have hcomp : Q' ∘ Q = id := by
      funext v
      simp [Q, Q']
    have h := fderiv_comp u (hQ'.differentiable (by simp) (Q u)) (hQ.differentiable (by simp) u)
    rw [hcomp, fderiv_id] at h
    have hd := congrArg ContinuousLinearMap.det h
    change LinearMap.det (LinearMap.id : ℂ →ₗ[ℝ] ℂ) =
      LinearMap.det ((fderiv ℝ Q' (Q u) : ℂ →ₗ[ℝ] ℂ) ∘ₗ (fderiv ℝ Q u : ℂ →ₗ[ℝ] ℂ)) at hd
    rw [LinearMap.det_id, LinearMap.det_comp] at hd
    intro h0
    change LinearMap.det (fderiv ℝ Q u : ℂ →ₗ[ℝ] ℂ) = 0 at h0
    rw [h0, mul_zero] at hd
    exact one_ne_zero hd
  · intro z hz
    apply hsV
    rw [mem_sphere_iff_norm, hn]
    exact mem_sphere_iff_norm.mp hz
  · intro z hz
    change e.symm (Qp (e z)) = E z
    rw [hQV hz]
    simp [F]
  · intro T hT hTb hTd
    have h := hfin (e '' T) (hT.image e e.continuous.continuousOn) (hbd T hTb)
      (by rw [hFsph]; exact (disjoint_image_iff e.injective).mpr hTd)
    rw [disjoint_left] at h ⊢
    rintro _ hzT ⟨u, hu, rfl⟩
    refine h (mem_image_of_mem e hzT) ⟨e u, ?_, ?_⟩
    · rw [mem_ball_iff_norm, hn]
      exact mem_ball_iff_norm.mp hu
    · simp [Q]

end GC.Seifert
