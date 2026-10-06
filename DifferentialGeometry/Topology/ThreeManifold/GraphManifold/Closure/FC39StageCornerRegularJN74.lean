import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerComponentJN74

/-!
# Draft 74, regular defining functions stay regular near an endpoint

Lane S-JUNCTIONS (by S-JUNCTIONS3), G10 part 2 (suffix `_JN74`). On a one-dimensional manifold,
a smooth `b` with `db(e) ≠ 0` has `db ≠ 0` on a neighbourhood of `e` (inverse function theorem:
`b` is a local diffeomorphism on a neighbourhood, so its differential is invertible there):

* `exists_nhds_mfderiv_ne_zero_JN74`: generic;
* `EdgeBundle.exists_endpoint_regular_JN74`: the endpoint chart of `exists_endpoint_chart_JN74` with
  `db ≠ 0` on the whole neighbourhood (the input of the rim-regularity step of FDC03's `g5`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

universe u

namespace DifferentialGeometry.Topology.Manifold

/-- **`db ≠ 0` near an endpoint** (one-dimensional manifold). -/
theorem exists_nhds_mfderiv_ne_zero_JN74 {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) Y] [IsManifold (𝓡 1) ∞ Y] {e : Y}
    {U : TopologicalSpace.Opens Y} (heU : e ∈ U) {b : Y → ℝ}
    (hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U) (hreg : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e ≠ 0) :
    ∃ U' : TopologicalSpace.Opens Y, e ∈ U' ∧ (U' : Set Y) ⊆ U ∧
      ∀ c ∈ U', mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b c ≠ 0 := by
  have hinv : (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e).IsInvertible := by
    have hsurj : Function.Surjective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e) := by
      obtain ⟨v, hv⟩ : ∃ v, (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e) v ≠ 0 := by
        by_contra h
        exact hreg (ContinuousLinearMap.ext fun w => by
          by_contra hw
          exact h ⟨w, hw⟩)
      intro t
      obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e) v := ⟨_, rfl⟩
      have ha0 : a ≠ 0 := by
        rw [ha]
        exact hv
      let t' : ℝ := t
      refine ⟨(a⁻¹ * t') • v, ?_⟩
      rw [map_smul, ← ha]
      change (a⁻¹ * t') * a = t'
      field_simp
    have hfin : Module.finrank ℝ (TangentSpace (𝓡 1) e) =
        Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℝ) (b e)) := by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ ℝ
      simp
    have hinj : Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr hsurj
    exact ⟨(LinearEquiv.ofBijective (mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e).toLinearMap
      ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩
  obtain ⟨Φ, heΦ, hΦ⟩ :=
    DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
      U.isOpen heU hb hinv
  refine ⟨⟨Φ.source ∩ (U : Set Y), Φ.open_source.inter U.isOpen⟩, ⟨heΦ, heU⟩,
    fun c hc => hc.2, fun c hc h0 => ?_⟩
  have hloc : IsLocalDiffeomorphAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ b c := ⟨Φ, hc.1, hΦ⟩
  have hi := hloc.isInvertible_mfderiv (by simp)
  obtain ⟨v, hv⟩ := hi.bijective.2 (show TangentSpace 𝓘(ℝ, ℝ) (b c) from (1 : ℝ))
  rw [h0] at hv
  have h1 : ((0 : ℝ) : ℝ) = 1 := hv
  exact zero_ne_one h1

end DifferentialGeometry.Topology.Manifold

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold

namespace GC.GraphManifold.Assembly.FC39P0

open DifferentialGeometry.Topology.Manifold

/-- **The endpoint chart with `db ≠ 0` on the whole neighbourhood**: the data of
`exists_endpoint_chart_JN74` and, in addition, `db ≠ 0` at every point of `U`. -/
theorem EdgeBundle.exists_endpoint_regular_JN74 {W : CompactCarrier.{u}} (P : EdgeBundle W)
    (e : P.EdgeEnd) :
    ∃ (b : P.Base → ℝ) (U : TopologicalSpace.Opens P.Base), e.1 ∈ U ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧ b e.1 = 0 ∧
      (∀ c ∈ U, mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b c ≠ 0) ∧
      P.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c} ∧
      ∀ c ∈ U, (c ∈ e.component.1 ↔ 0 ≤ b c) := by
  obtain ⟨b, U, heU, hb, hb0, hreg, hcU, hcomp⟩ := P.exists_endpoint_chart_JN74 e
  obtain ⟨U', heU', hU'U, hreg'⟩ := exists_nhds_mfderiv_ne_zero_JN74 heU hb hreg
  refine ⟨b, U', heU', hb.mono hU'U, hb0, hreg', ?_, fun c hc => hcomp c (hU'U hc)⟩
  ext c
  constructor
  · rintro ⟨hc, hcU'⟩
    exact ⟨hcU', ((Set.ext_iff.1 hcU c).1 ⟨hc, hU'U hcU'⟩).2⟩
  · rintro ⟨hcU', hc0⟩
    exact ⟨((Set.ext_iff.1 hcU c).2 ⟨hU'U hcU', hc0⟩).1, hcU'⟩

end GC.GraphManifold.Assembly.FC39P0
