import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GGlobalFacesSign
import DifferentialGeometry.Topology.Ehresmann.SideBoundaryInterval

/-!
# FC39 GROUP G, global face functions (F3–F4): one face function from local germs

Lane FC39-G-GFF(b), external draft 58 §二 F3–F4, disposition D58-3. On a boundaryless Hausdorff
surface `M` (model `𝓡 2`; no countability assumption — only FINITELY many smooth bumps are used),
for a compact `K` and ONE closed face trace `Bf ⊆ K`:

* `contMDiff_mul_of_tsupport_GGFF` — a bump times a function smooth on a neighbourhood of the bump's
  closed support is smooth;
* `exists_regular_open_GGFF` — a smooth function regular at a point is regular on a neighbourhood
  (openness of submersions, `isOpen_setOf_surjective_mfderiv`, through a bump);
* `exists_bump_cover_GGFF` — a compact set is covered by the supports of finitely many smooth bumps
  centred in it, each with closed support in a prescribed neighbourhood of its centre;
* `exists_faceFunction_GGFF` — **the relative co-oriented extension (F4) with protected canonical
  germs (F3)**: from the corner charts `(X_e, Y_e)` (`K = {X_e ≥ 0, Y_e ≥ 0}`, the trace is
  `{X_e = 0}` resp. `{Y_e = 0}` inside `K` near the corner) and a regular local defining function at
  every non-corner point of `Bf`, ONE smooth function `F` with `F ≤ 0` on `K`, `{F = 0} ∩ K = Bf`,
  `dF ≠ 0` and `F > 0` just outside `K` at every non-corner point of `Bf`, and `F = −X_e` (resp.
  `−Y_e`) near every corner of the face. `F = ∑ β_j ψ_j − G`: corner bumps times `−X_e`/`−Y_e`, bumps
  at the non-corner points times the local functions, minus a non-negative background sum of bumps
  supported off `Bf` (positive weights only; no averaging of unrelated functions).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace GC.GraphManifold.Assembly.FC39P0

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- A bump times a function smooth on an open neighbourhood of the bump's closed support is
smooth. -/
theorem contMDiff_mul_of_tsupport_GGFF {β ψ : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hβU : tsupport β ⊆ U) (hβ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ β)
    (hψ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ ψ U) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ fun u => β u * ψ u := by
  refine contMDiff_of_tsupport fun x hx => ?_
  have hxU : x ∈ U := hβU (tsupport_mul_subset_left hx)
  exact (hβ x).mul ((hψ x hxU).contMDiffAt (hU.mem_nhds hxU))

/-- A real linear functional is surjective iff it is nonzero. -/
theorem surjective_iff_ne_zero_GGFF {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : F →L[ℝ] ℝ} : Surjective L ↔ L ≠ 0 := by
  constructor
  · rintro h rfl
    obtain ⟨w, hw⟩ := h 1
    simp at hw
  · intro h r
    obtain ⟨w, hw⟩ : ∃ w, L w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h (ContinuousLinearMap.ext hcon)
    exact ⟨(r / L w) • w, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hw]⟩

variable [IsManifold (𝓡 2) ∞ M] [T2Space M]

/-- **Openness of regularity**: a function smooth on an open set and regular at a point is regular
on a neighbourhood of the point. -/
theorem exists_regular_open_GGFF {φ : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hφ : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ φ U) {c : M} (hcU : c ∈ U)
    (hc : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) φ c ≠ 0) :
    ∃ U' : Set M, IsOpen U' ∧ c ∈ U' ∧ U' ⊆ U ∧
      ∀ y ∈ U', mfderiv (𝓡 2) 𝓘(ℝ, ℝ) φ y ≠ 0 := by
  obtain ⟨g, hg⟩ := (SmoothBumpFunction.nhds_basis_support (I := 𝓡 2) (hU.mem_nhds hcU)).ex_mem
  have hG : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ fun u => g u * φ u :=
    contMDiff_mul_of_tsupport_GGFF hU hg g.contMDiff hφ
  obtain ⟨O, hO1, hOo, hcO⟩ := eventually_nhds_iff.1 g.eventuallyEq_one
  have hder : ∀ y ∈ U ∩ O, HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (fun u => g u * φ u) y
      (mderivR_GTR (𝓡 2) φ y) := by
    rintro y ⟨hyU, hyO⟩
    have hφd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) φ y :=
      ((hφ y hyU).contMDiffAt (hU.mem_nhds hyU)).mdifferentiableAt (by simp)
    refine hφd.hasMFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [hOo.mem_nhds hyO] with u hu
    rw [hO1 u hu, Pi.one_apply, one_mul]
  have hS := DifferentialGeometry.Topology.Ehresmann.isOpen_setOf_surjective_mfderiv hG
  refine ⟨U ∩ O ∩ {y | Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun u => g u * φ u) y)},
    (hU.inter hOo).inter hS, ⟨⟨hcU, hcO⟩, ?_⟩, fun y hy => hy.1.1, ?_⟩
  · have h1 := (hder c ⟨hcU, hcO⟩).mfderiv
    change Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun u => g u * φ u) c)
    rw [h1]
    exact (surjective_iff_ne_zero_GGFF (L := mderivR_GTR (𝓡 2) φ c)).2 hc
  · rintro y ⟨hyUO, hyS⟩
    have h1 := (hder y hyUO).mfderiv
    have hyS' : Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun u => g u * φ u) y) := hyS
    rw [h1] at hyS'
    exact (surjective_iff_ne_zero_GGFF (L := mderivR_GTR (𝓡 2) φ y)).1 hyS'

/-- **Finite bump covers**: a compact set is covered by the supports of finitely many smooth bumps
centred in it, the bump at `y` having closed support in the prescribed neighbourhood `N y`. -/
theorem exists_bump_cover_GGFF {Q : Set M} (hQ : IsCompact Q) (N : M → Set M)
    (hN : ∀ y ∈ Q, N y ∈ 𝓝 y) :
    ∃ (t : Finset M) (β : M → M → ℝ), (∀ y, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (β y)) ∧
      (∀ y u, 0 ≤ β y u) ∧ (∀ y ∈ Q, tsupport (β y) ⊆ N y) ∧ (∀ y ∈ t, y ∈ Q) ∧
      Q ⊆ ⋃ y ∈ t, support (β y) := by
  classical
  have hex : ∀ y ∈ Q, ∃ g : SmoothBumpFunction (𝓡 2) y, tsupport g ⊆ N y := fun y hy =>
    (SmoothBumpFunction.nhds_basis_support (I := 𝓡 2) (hN y hy)).ex_mem
  choose g hg using hex
  let β : M → M → ℝ := fun y u => if h : y ∈ Q then g y h u else 0
  have hβeq : ∀ y (h : y ∈ Q), β y = g y h := fun y h => funext fun u => by simp [β, h]
  have hβ0 : ∀ y, y ∉ Q → β y = 0 := fun y h => funext fun u => by simp [β, h]
  obtain ⟨t, htQ, hcov⟩ := hQ.elim_nhds_subcover (fun y => support (β y)) fun y hy => by
    rw [hβeq y hy]
    exact (g y hy).support_mem_nhds
  refine ⟨t, β, fun y => ?_, fun y u => ?_, fun y hy => ?_, htQ, hcov⟩
  · by_cases hy : y ∈ Q
    · rw [hβeq y hy]
      exact (g y hy).contMDiff
    · rw [hβ0 y hy]
      exact contMDiff_const
  · by_cases hy : y ∈ Q
    · rw [hβeq y hy]
      exact (g y hy).nonneg
    · rw [hβ0 y hy]
      exact le_rfl
  · rw [hβeq y hy]
    exact hg y hy

end GC.GraphManifold.Assembly.FC39P0
