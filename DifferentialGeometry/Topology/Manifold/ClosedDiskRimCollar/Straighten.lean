import DifferentialGeometry.Topology.Manifold.ClosedDiskRimCollar.Extension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Rim collar straightening for diffeomorphisms of a closed cell

`exists_closedCell_isotopy_to_identity_near_boundary_of_fix_boundary`: a diffeomorphism `μ` of
`ClosedCell (m + 1)` fixing the boundary sphere pointwise is smoothly isotopic, through
diffeomorphisms fixing the boundary sphere pointwise, to one that is the identity on an open
neighbourhood of the boundary. The isotopy `K` is jointly smooth with jointly smooth inverses,
equals `μ` for `t ≤ 1/3` and is the identity near the boundary for `t ≥ 2/3`.

Construction: with `Φ` the rim collar isotopy of `μ.symm`
(`exists_ambient_isotopy_eq_closedCell_diffeomorph_near_boundary`) and
`β t = smoothTransition (3 t - 1)`, let `R t` be the restriction of `Φ (β t)` to the closed cell
(`closedCellDiffeomorph`) and `K t := (R t).trans μ`. Near the boundary and for `t ≥ 2/3`,
`R t = μ.symm`, so `K t = id` there.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {m : ℕ}

local instance closedCellChartsStr_D2S1RIM :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  Handle.closedCellChartedSpaceSucc m

local instance closedCellSmoothStr_D2S1RIM : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m

/-- **Rim collar straightening.** A diffeomorphism of the closed cell fixing the boundary sphere
pointwise is isotopic, through diffeomorphisms fixing the boundary sphere pointwise, to one that is
the identity on an open neighbourhood `N` of the boundary sphere. The isotopy is jointly smooth with
jointly smooth inverses, equals `μ` for `t ≤ 1/3` and is the identity on `N` for `t ≥ 2/3`. -/
theorem exists_closedCell_isotopy_to_identity_near_boundary_of_fix_boundary
    (μ : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1))
    (hμ : ∀ x : ClosedCell (m + 1), ‖x.val‖ = 1 → μ x = x) :
    ∃ K : ℝ → (ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1)),
      ContMDiff ((𝓡∂ (m + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (m + 1)) ∞
        (fun x : ClosedCell (m + 1) × ℝ => K x.2 x.1) ∧
      ContMDiff ((𝓡∂ (m + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (m + 1)) ∞
        (fun x : ClosedCell (m + 1) × ℝ => (K x.2).symm x.1) ∧
      (∀ t (x : ClosedCell (m + 1)), ‖x.val‖ = 1 → K t x = x) ∧
      (∀ t x, t ≤ 1 / 3 → K t x = μ x) ∧
      ∃ N : Set (ClosedCell (m + 1)), IsOpen N ∧ {x | ‖x.val‖ = 1} ⊆ N ∧
        ∀ t, ∀ x ∈ N, 2 / 3 ≤ t → K t x = x := by
  have hν : ∀ x : ClosedCell (m + 1), ‖x.val‖ = 1 → μ.symm x = x := fun x hx => by
    have h := μ.symm_apply_apply x
    rwa [hμ x hx] at h
  obtain ⟨V, hV, hSV, Φ, hΦ, hΦi, hΦ0, hΦ1, hΦfix, hΦball⟩ :=
    exists_ambient_isotopy_eq_closedCell_diffeomorph_near_boundary μ.symm hν
  let β : ℝ → ℝ := fun t => Real.smoothTransition (3 * t - 1)
  have hβI (t : ℝ) : β t ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hβc : ContDiff ℝ ∞ β :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  let R : ℝ → (ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1)) :=
    fun t => closedCellDiffeomorph (Φ (β t)) (hΦball _ (hβI t))
  have hRval (t : ℝ) (x : ClosedCell (m + 1)) : (R t x).val = Φ (β t) x.val := rfl
  refine ⟨fun t => (R t).trans μ, ?_, ?_, ?_, ?_, ?_⟩
  · have hR : ContMDiff ((𝓡∂ (m + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (m + 1)) ∞
        (fun x : ClosedCell (m + 1) × ℝ => R x.2 x.1) :=
      contMDiff_closedCell_family_of_val (G := fun z => Φ (β z.1) z.2)
        (hΦ.comp ((hβc.comp contDiff_fst).prodMk contDiff_snd)) (fun _ => rfl)
    exact μ.contMDiff.comp hR
  · have hRi : ContMDiff ((𝓡∂ (m + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (m + 1)) ∞
        (fun x : ClosedCell (m + 1) × ℝ => (R x.2).symm x.1) :=
      contMDiff_closedCell_family_of_val (G := fun z => (Φ (β z.1)).symm z.2)
        (hΦi.comp ((hβc.comp contDiff_fst).prodMk contDiff_snd)) (fun _ => rfl)
    exact hRi.comp ((μ.symm.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  · intro t x hx
    have hRx : R t x = x := Subtype.ext ((hRval t x).trans (hΦfix _ _ hx))
    change μ (R t x) = x
    rw [hRx, hμ x hx]
  · intro t x ht
    have hb : β t = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    have hRx : R t x = x := Subtype.ext (by rw [hRval, hb, hΦ0])
    change μ (R t x) = μ x
    rw [hRx]
  · refine ⟨Subtype.val ⁻¹' V, hV.preimage continuous_subtype_val,
      fun x hx => hSV (by simpa using hx), ?_⟩
    intro t x hx ht
    have hb : β t = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    have hRx : R t x = μ.symm x := Subtype.ext (by rw [hRval, hb, hΦ1 x hx])
    change μ (R t x) = x
    rw [hRx, Diffeomorph.apply_symm_apply]

end DifferentialGeometry.Topology.Manifold
