import DifferentialGeometry.Analysis.Calculus.Inverse.TransverseImmersion
import DifferentialGeometry.Geometry.Boundary.Model.Basic
import Mathlib.Analysis.Convex.Topology

noncomputable section
open Set Function
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

def modelBoundaryParam : hI.boundaryE → E := I ∘ hI.inclH ∘ hI.boundaryI.symm

theorem range_modelBoundaryParam : range (modelBoundaryParam I) = frontier (range I) := by
  rw [← hI.range_I_inclH]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨hI.boundaryI.symm x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨hI.boundaryI x, ?_⟩
    change I (hI.inclH (hI.boundaryI.symm (hI.boundaryI x))) = I (hI.inclH x)
    rw [hI.boundaryI.left_inv x]

theorem isClosedEmbedding_modelBoundaryParam : Topology.IsClosedEmbedding (modelBoundaryParam I) :=
  (HasSmoothBoundary.isClosedEmbedding_I_inclH I).comp hI.boundaryI.toHomeomorph.symm.isClosedEmbedding

private theorem negative_ray_not_mem {S : Set E} (hS : Convex ℝ S) {y v : E}
    (hy : y ∈ frontier S) {ε r : ℝ} (hε : 0 < ε)
    (hin : y + ε • v ∈ interior S) (hr : r < 0) : y + r • v ∉ S := by
  intro hout
  have hd : 0 < ε - r := by linarith
  have ha : 0 ≤ ε / (ε - r) := (div_pos hε hd).le
  have hb : 0 < -r / (ε - r) := div_pos (neg_pos.mpr hr) hd
  have hsum : ε / (ε - r) + -r / (ε - r) = 1 := by field_simp; ring
  have h := hS.combo_self_interior_mem_interior hout hin ha hb hsum
  have heq : (ε / (ε - r)) • (y + r • v) + (-r / (ε - r)) • (y + ε • v) = y := by
    calc
      _ = (ε / (ε - r) + -r / (ε - r)) • y +
          (ε / (ε - r) * r + -r / (ε - r) * ε) • v := by module
      _ = y := by rw [hsum, show ε / (ε - r) * r + -r / (ε - r) * ε = 0 by ring]; simp
  rw [heq] at h
  exact hy.2 h

private theorem negative_inward_ray_not_mem {y : E} (hy : y ∈ frontier (range I))
    {r : ℝ} (hr : r < 0) : y + r • hI.inwardCoordE ∉ range I := by
  obtain ⟨ε, hε, henter⟩ := hI.inwardCoordE_enters y hy
  exact negative_ray_not_mem I.convex_range hy hε (henter ε ⟨hε, le_rfl⟩) hr

private theorem positive_inward_ray_mem_interior {y : E} (hy : y ∈ frontier (range I))
    {r : ℝ} (hr : 0 < r) : y + r • hI.inwardCoordE ∈ interior (range I) := by
  let f : ℝ → E := fun t ↦ y + t • hI.inwardCoordE
  have hf : Continuous f := by fun_prop
  have hyn : y ∈ range I := I.isClosed_range.closure_subset hy.1
  have hfront : ∀ t ∈ Ioi (0 : ℝ), f t ∉ frontier (range I) := by
    intro t ht hft
    have hneg := negative_inward_ray_not_mem I hft (neg_neg_of_pos ht)
    have heq : f t + -t • hI.inwardCoordE = y := by dsimp [f]; module
    exact hneg (heq.symm ▸ hyn)
  have hcover : f '' Ioi (0 : ℝ) ⊆ interior (range I) ∪ (range I)ᶜ := by
    rintro z ⟨t, ht, rfl⟩
    by_cases hmem : f t ∈ range I
    · left
      by_contra hn
      exact hfront t ht ⟨subset_closure hmem, hn⟩
    · exact Or.inr hmem
  obtain ⟨ε, hε, henter⟩ := hI.inwardCoordE_enters y hy
  have hmeet : (f '' Ioi (0 : ℝ) ∩ interior (range I)).Nonempty :=
    ⟨f ε, ⟨ε, hε, rfl⟩, henter ε ⟨hε, le_rfl⟩⟩
  have hsubset := (isPreconnected_Ioi.image f hf.continuousOn).subset_left_of_subset_union
    isOpen_interior I.isClosed_range.isOpen_compl
    (Set.disjoint_left.mpr (fun _ hi hn ↦ hn (interior_subset hi))) hcover hmeet
  exact hsubset ⟨r, hr, rfl⟩

theorem modelBoundaryParam_add_mem_interior_iff (p : hI.boundaryE) (r : ℝ) :
    modelBoundaryParam I p + r • hI.inwardCoordE ∈ interior (range I) ↔ 0 < r := by
  have hp : modelBoundaryParam I p ∈ frontier (range I) :=
    range_modelBoundaryParam I ▸ mem_range_self p
  constructor
  · intro h
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · exact False.elim (negative_inward_ray_not_mem I hp hr (interior_subset h))
    · exact False.elim (hp.2 (by simpa using h))
    · exact hr
  · exact positive_inward_ray_mem_interior I hp

theorem modelBoundaryParam_add_mem_range_iff (p : hI.boundaryE) (r : ℝ) :
    modelBoundaryParam I p + r • hI.inwardCoordE ∈ range I ↔ 0 ≤ r := by
  have hp : modelBoundaryParam I p ∈ frontier (range I) :=
    range_modelBoundaryParam I ▸ mem_range_self p
  constructor
  · intro h
    by_contra hn
    exact negative_inward_ray_not_mem I hp (lt_of_not_ge hn) h
  · intro hr
    rcases hr.eq_or_lt with rfl | hr
    · simpa using I.isClosed_range.closure_subset hp.1
    · exact interior_subset ((modelBoundaryParam_add_mem_interior_iff I p r).2 hr)

theorem modelBoundaryParam_add_mem_frontier_iff (p : hI.boundaryE) (r : ℝ) :
    modelBoundaryParam I p + r • hI.inwardCoordE ∈ frontier (range I) ↔ r = 0 := by
  rw [I.isClosed_range.frontier_eq, mem_sdiff, modelBoundaryParam_add_mem_range_iff,
    modelBoundaryParam_add_mem_interior_iff]
  exact ⟨fun h ↦ le_antisymm (not_lt.mp h.2) h.1, fun h ↦ by simp [h]⟩

theorem injective_modelBoundaryParam_add : Function.Injective
    (fun z : hI.boundaryE × ℝ ↦ modelBoundaryParam I z.1 + z.2 • hI.inwardCoordE) := by
  rintro ⟨p, r⟩ ⟨q, s⟩ heq
  change modelBoundaryParam I p + r • hI.inwardCoordE =
    modelBoundaryParam I q + s • hI.inwardCoordE at heq
  have hpoint : modelBoundaryParam I q + (s - r) • hI.inwardCoordE =
      modelBoundaryParam I p := by
    calc
      _ = (modelBoundaryParam I q + s • hI.inwardCoordE) - r • hI.inwardCoordE := by module
      _ = modelBoundaryParam I p := by rw [← heq]; module
  have hboundary : modelBoundaryParam I q + (s - r) • hI.inwardCoordE ∈
      frontier (range I) := hpoint ▸ (range_modelBoundaryParam I ▸ mem_range_self p)
  have hrs : s = r := sub_eq_zero.mp ((modelBoundaryParam_add_mem_frontier_iff I q (s - r)).1 hboundary)
  subst s
  have hpq := (isClosedEmbedding_modelBoundaryParam I).injective (add_right_cancel heq)
  exact Prod.ext hpq rfl

theorem injective_fderiv_modelBoundaryParam (p : hI.boundaryE) :
    Function.Injective (fderiv ℝ (modelBoundaryParam I) p) := by
  have hparam : ContDiff ℝ ∞ (modelBoundaryParam I) := hI.I_inclH_boundaryI_symm_contDiff
  have hproj : hI.projE ∘ modelBoundaryParam I = id := by
    funext x
    change hI.projE (I (hI.inclH (hI.boundaryI.symm x))) = x
    rw [hI.proj_inclH_compat]
    exact hI.boundaryI.toHomeomorph.right_inv x
  have hL : (fderiv ℝ hI.projE (modelBoundaryParam I p)).comp
      (fderiv ℝ (modelBoundaryParam I) p) = ContinuousLinearMap.id ℝ hI.boundaryE := by
    rw [← fderiv_comp p (hI.projE_contDiff.differentiable (by simp) _)
      (hparam.differentiable (by simp) p), hproj, fderiv_id]
  have hleft : Function.LeftInverse
      (fderiv ℝ hI.projE (modelBoundaryParam I p))
      (fderiv ℝ (modelBoundaryParam I) p) := by
    intro x
    exact congrArg (fun A : hI.boundaryE →L[ℝ] hI.boundaryE ↦ A x) hL
  exact hleft.injective

theorem exists_modelBoundary_coordinates [FiniteDimensional ℝ E] (p : hI.boundaryE) :
    ∃ e : OpenPartialHomeomorph (hI.boundaryE × ℝ) E,
      (p, 0) ∈ e.source ∧ ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z, e z = modelBoundaryParam I z.1 + z.2 • hI.inwardCoordE := by
  have hparam : ContDiff ℝ ∞ (modelBoundaryParam I) := hI.I_inclH_boundaryI_symm_contDiff
  have hinj := injective_fderiv_modelBoundaryParam I p
  obtain ⟨e, hp, _, he, hi, heq⟩ := DifferentialGeometry.Analysis.exists_localInverse_of_transverse_immersion
    hparam.contDiffOn isOpen_univ (mem_univ p) hinj hI.finrank_boundaryE_succ
    (hI.inwardCoordE_transverse p)
  exact ⟨e, hp, he, hi, heq⟩

end DifferentialGeometry.Geometry.Boundary
