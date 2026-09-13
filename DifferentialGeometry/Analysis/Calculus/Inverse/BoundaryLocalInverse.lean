import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpaceExtension
import DifferentialGeometry.Geometry.Boundary.ModelCollarCoordinates

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis

open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_contDiffOn_extension_across_range_frontier {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U ∩ range I) (hf : ContDiffOn ℝ ∞ f (U ∩ range I)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ g : E → F, ContDiffOn ℝ ∞ g V ∧ EqOn g f (V ∩ range I) := by
  by_cases hsm : x ∈ interior (range I)
  · exact ⟨interior (U ∩ range I), isOpen_interior,
      mem_interior_iff_mem_nhds.mpr
        (mem_of_superset (inter_mem (hU.mem_nhds hx.1) (isOpen_interior.mem_nhds hsm))
          (fun y hy => ⟨hy.1, interior_subset hy.2⟩)),
      interior_subset.trans inter_subset_left, f, hf.mono interior_subset, fun _ _ => rfl⟩
  · obtain ⟨p, hp⟩ : ∃ p : hI.boundaryE, modelBoundaryParam I p = x := by
      have h : x ∈ range (modelBoundaryParam I) := by
        rw [range_modelBoundaryParam I]
        rw [I.isClosed_range.frontier_eq]
        exact ⟨hx.2, hsm⟩
      exact h
    obtain ⟨e, hpe, he, hei, heq⟩ := exists_modelBoundary_coordinates I p
    let U₁ : Set (hI.boundaryE × ℝ) := e.source ∩ e ⁻¹' U
    have hU₁ : IsOpen U₁ := e.isOpen_inter_preimage hU
    have he0 : e (p, (0 : ℝ)) = x := by
      have h := heq (p, 0)
      rw [zero_smul, add_zero] at h
      exact h.trans hp
    have hp₁ : (p, (0 : ℝ)) ∈ U₁ := ⟨hpe, by rw [Set.mem_preimage, he0]; exact hx.1⟩
    have hΦ₁ : ContDiffOn ℝ ∞ (f ∘ ⇑e) (U₁ ∩ (univ ×ˢ Ici (0 : ℝ))) := by
      refine hf.comp (he.mono (fun z hz => hz.1.1)) ?_
      rintro z ⟨hz, -, hz0⟩
      refine ⟨hz.2, ?_⟩
      rw [heq z]
      exact (modelBoundaryParam_add_mem_range_iff I z.1 z.2).2 hz0
    obtain ⟨V₁, hV₁, hpV₁, hV₁U₁, Ψ, hΨ, hΨeq⟩ :=
      exists_contDiffOn_extension_across_halfSpace_boundary hU₁ hp₁ hΦ₁
    have hV₁sub : V₁ ⊆ e.source := fun z hz => (hV₁U₁ hz).1
    have himage : IsOpen (e '' V₁) := by
      rw [e.image_eq_target_inter_inv_preimage hV₁sub]
      exact e.symm.isOpen_inter_preimage hV₁
    refine ⟨e '' V₁, himage, ⟨(p, 0), hpV₁, he0⟩, ?_, Ψ ∘ ⇑e.symm, ?_, ?_⟩
    · rintro y ⟨z, hz, rfl⟩
      exact (hV₁U₁ hz).2
    · refine hΨ.comp (hei.mono ?_) ?_
      · rintro y ⟨z, hz, rfl⟩
        exact e.map_source (hV₁U₁ hz).1
      · rintro y ⟨z, hz, rfl⟩
        rw [OpenPartialHomeomorph.left_inv _ (hV₁U₁ hz).1]
        exact hz
    · intro y hy
      obtain ⟨⟨z, hz, rfl⟩, hyr⟩ := hy
      have hz0 : 0 ≤ z.2 := by
        have h2 : modelBoundaryParam I z.1 + z.2 • hI.inwardCoordE ∈ range I := by
          rw [← heq z]
          exact hyr
        exact (modelBoundaryParam_add_mem_range_iff I z.1 z.2).1 h2
      rw [Function.comp_apply, OpenPartialHomeomorph.left_inv _ (hV₁U₁ hz).1]
      exact hΨeq ⟨hz, mem_univ z.1, hz0⟩

omit [FiniteDimensional ℝ E] in
theorem uniqueDiffWithinAt_of_isOpen_inter_range {U : Set E} {x : E} (hU : IsOpen U)
    (hx : x ∈ U ∩ range I) : UniqueDiffWithinAt ℝ (U ∩ range I) x := by
  have hInterior : (interior (range I)).Nonempty := by
    obtain ⟨ε, hε, h⟩ := hI.inwardCoordE_enters (modelBoundaryParam I (hI.projE 0))
      (by rw [← range_modelBoundaryParam I]; exact mem_range_self _)
    exact ⟨_, h ε ⟨hε, le_rfl⟩⟩
  rw [inter_comm]
  exact (uniqueDiffWithinAt_convex I.convex_range hInterior (subset_closure hx.2)).inter'
    (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx.1))

theorem exists_localInverse_of_hasFDerivWithinAt_equiv_of_ne_zero {f : E → F} {U T : Set E}
    {x : E} {A : E ≃L[ℝ] F} (hU : IsOpen U) (hT : T = U ∩ range I) (hx : x ∈ T)
    (hf : ContDiffOn ℝ ∞ f T) (hd : HasFDerivWithinAt f (A : E →L[ℝ] F) T x) :
    ∃ e : OpenPartialHomeomorph E F, x ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧ EqOn e f (e.source ∩ T) := by
  subst hT
  by_cases hnhds : U ∩ range I ∈ 𝓝 x
  · obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hnhds
    obtain ⟨e, hxe, hsub, he, hei, heq⟩ :=
      exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero (𝕜 := ℝ) (n := ∞) (by simp)
        (hf.mono hVU) hVopen hxV (hd.hasFDerivAt hnhds)
    exact ⟨e, hxe, hsub.trans (hVU.trans inter_subset_left), he, hei, fun y _ => heq y⟩
  · have hxnotint : x ∉ interior (range I) := fun hc =>
      hnhds (mem_of_superset (inter_mem (hU.mem_nhds hx.1) (isOpen_interior.mem_nhds hc))
        (fun y hy => ⟨hy.1, interior_subset hy.2⟩))
    have hxfront : x ∈ frontier (range I) := by
      rw [I.isClosed_range.frontier_eq]
      exact ⟨hx.2, hxnotint⟩
    have hUD : UniqueDiffWithinAt ℝ (U ∩ range I) x :=
      uniqueDiffWithinAt_of_isOpen_inter_range hU hx
    obtain ⟨V, hV, hxV, hVU, Φ, hΦ, hΦeq⟩ :=
      exists_contDiffOn_extension_across_range_frontier hU hx hf
    have hΦeq' : Φ =ᶠ[𝓝[U ∩ range I] x] f := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), self_mem_nhdsWithin]
        with y hy hyT
      exact hΦeq ⟨hy, hyT.2⟩
    have hdΦ : HasFDerivWithinAt Φ (A : E →L[ℝ] F) (U ∩ range I) x :=
      hd.congr_of_eventuallyEq hΦeq' (hΦeq ⟨hxV, hx.2⟩)
    have hderivΦ : HasFDerivAt Φ (fderiv ℝ Φ x) x :=
      ((hΦ.contDiffAt (hV.mem_nhds hxV)).differentiableAt (by simp)).hasFDerivAt
    have hA : (A : E →L[ℝ] F) = fderiv ℝ Φ x :=
      UniqueDiffWithinAt.eq hUD hdΦ hderivΦ.hasFDerivWithinAt
    obtain ⟨e, hxe, hsub, he, hei, heq⟩ :=
      exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero (𝕜 := ℝ) (n := ∞) (by simp)
        hΦ hV hxV (hA.symm ▸ hderivΦ)
    exact ⟨e, hxe, hsub.trans hVU, he, hei,
      fun y hy => (heq y).trans (hΦeq ⟨hsub hy.1, hy.2.2⟩)⟩

example (p : hI.boundaryE) :
    ∃ e : OpenPartialHomeomorph E E, modelBoundaryParam I p ∈ e.source ∧ e.source ⊆ univ ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      EqOn e id (e.source ∩ range I) := by
  have hp : modelBoundaryParam I p ∈ range I :=
    I.isClosed_range.closure_subset
      (frontier_subset_closure (by rw [← range_modelBoundaryParam I]; exact mem_range_self p))
  exact exists_localInverse_of_hasFDerivWithinAt_equiv_of_ne_zero (I := I) (U := univ)
    (T := range I) (f := id) (x := modelBoundaryParam I p) (A := 1) isOpen_univ
    (univ_inter (range I)).symm hp contDiff_id.contDiffOn (hasFDerivWithinAt_id _ _)

end DifferentialGeometry.Analysis
