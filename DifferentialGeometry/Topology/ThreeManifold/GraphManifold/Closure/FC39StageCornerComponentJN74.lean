import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base

/-!
# Draft 74, the small input `hC` of the corner rank lemma: components near an endpoint

Lane S-JUNCTIONS (by S-JUNCTIONS3), G10 part 1 (suffix `_JN74`). The field
`cbase_domain` of an edge bundle gives, at every endpoint `e` of `C₂ = cbase`, a smooth function
`b` near `e` with `b e = 0`, `db(e) ≠ 0` and `cbase ∩ U = {b ≥ 0}`. The corner rank lemma
(`exists_cornerRank_descended_of_local_JN74`) needs in addition that, near `e`, a base point lies in
the actual component of `e` iff `b ≥ 0` (its input `hC`):

* `exists_nhds_component_iff_JN74` (generic, a one-dimensional manifold `Y`): `b` is a coordinate
  near `e` (inverse function theorem on the line), so `{b ≥ 0}` near `e` is a half interval, hence
  preconnected and contained in the component of `e`; the converse is the inclusion
  `component ⊆ C ∩ U = {b ≥ 0}`;
* `EdgeBundle.exists_endpoint_chart_JN74`: the same for the edge bundle's `cbase_domain` and the
  component `e.component` of an endpoint.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open scoped Manifold ContDiff Topology

universe u

namespace DifferentialGeometry.Topology.Manifold

/-- **Near an endpoint, a smooth coordinate `b ≥ 0` cuts out the component** (generic, on a
one-dimensional manifold): if `C ∩ U = {b ≥ 0}` with `b e = 0`, `db(e) ≠ 0`, then on a neighbourhood
`U' ⊆ U` of `e`, `c ∈ connectedComponentIn C e ↔ 0 ≤ b c`. -/
theorem exists_nhds_component_iff_JN74 {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) Y] [IsManifold (𝓡 1) ∞ Y] {C : Set Y} {e : Y}
    {U : TopologicalSpace.Opens Y} (heU : e ∈ U) {b : Y → ℝ}
    (hb : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U) (hb0 : b e = 0)
    (hreg : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e ≠ 0) (hCU : C ∩ U = {c | c ∈ U ∧ 0 ≤ b c}) :
    ∃ U' : TopologicalSpace.Opens Y, e ∈ U' ∧ (U' : Set Y) ⊆ U ∧
      ∀ c ∈ U', (c ∈ connectedComponentIn C e ↔ 0 ≤ b c) := by
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
  let Ψ := Φ.toOpenPartialHomeomorph
  have hVo : IsOpen (Ψ.source ∩ (U : Set Y)) := Ψ.open_source.inter U.isOpen
  have hbΦ : ∀ v ∈ Ψ.source, b v = Ψ v := fun v hv => hΦ hv
  have heV : e ∈ Ψ.source ∩ (U : Set Y) := ⟨heΦ, heU⟩
  have hWo : IsOpen (Ψ '' (Ψ.source ∩ (U : Set Y))) :=
    Ψ.isOpen_image_of_subset_source hVo inter_subset_left
  have h0W : (0 : ℝ) ∈ Ψ '' (Ψ.source ∩ (U : Set Y)) :=
    ⟨e, heV, by rw [← hbΦ e heΦ, hb0]⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hWo 0 h0W
  have hU'o : IsOpen (Ψ.source ∩ (U : Set Y) ∩ b ⁻¹' Metric.ball 0 ε) :=
    ((hb.continuousOn).mono inter_subset_right).isOpen_inter_preimage hVo Metric.isOpen_ball
  have hsub : Ico (0 : ℝ) ε ⊆ Ψ.target := fun t ht => by
    obtain ⟨v, hv, hvt⟩ := hball (show t ∈ Metric.ball (0 : ℝ) ε by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact ht.2)
    rw [← hvt]
    exact Ψ.map_source hv.1
  have hSeq : {c | c ∈ Ψ.source ∩ (U : Set Y) ∩ b ⁻¹' Metric.ball 0 ε ∧ 0 ≤ b c} =
      Ψ.symm '' Ico 0 ε := by
    ext c
    constructor
    · rintro ⟨⟨⟨hcΨ, -⟩, hcb⟩, hc0⟩
      refine ⟨b c, ⟨hc0, ?_⟩, ?_⟩
      · have := hcb
        rw [mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hc0] at this
        exact this
      · rw [hbΦ c hcΨ]
        exact Ψ.left_inv hcΨ
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨v, hv, hvt⟩ := hball (show t ∈ Metric.ball (0 : ℝ) ε by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
        exact ht.2)
      have hsymm : Ψ.symm t = v := by
        rw [← hvt]
        exact Ψ.left_inv hv.1
      have hbv : b v = t := by rw [hbΦ v hv.1, hvt]
      rw [hsymm]
      refine ⟨⟨hv, ?_⟩, ?_⟩
      · rw [mem_preimage, hbv, Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
        exact ht.2
      · rw [hbv]
        exact ht.1
  have hSpre : IsPreconnected
      {c | c ∈ Ψ.source ∩ (U : Set Y) ∩ b ⁻¹' Metric.ball 0 ε ∧ 0 ≤ b c} := by
    rw [hSeq]
    exact isPreconnected_Ico.image _ (Ψ.continuousOn_symm.mono hsub)
  have heS : e ∈ {c | c ∈ Ψ.source ∩ (U : Set Y) ∩ b ⁻¹' Metric.ball 0 ε ∧ 0 ≤ b c} :=
    ⟨⟨heV, by rw [mem_preimage, hb0]; exact Metric.mem_ball_self hε⟩, by rw [hb0]⟩
  have hSC : {c | c ∈ Ψ.source ∩ (U : Set Y) ∩ b ⁻¹' Metric.ball 0 ε ∧ 0 ≤ b c} ⊆ C := by
    rintro c ⟨⟨⟨-, hcU⟩, -⟩, hc0⟩
    have : c ∈ C ∩ (U : Set Y) := by
      rw [hCU]
      exact ⟨hcU, hc0⟩
    exact this.1
  refine ⟨⟨_, hU'o⟩, ⟨heV, by rw [mem_preimage, hb0]; exact Metric.mem_ball_self hε⟩,
    fun c hc => hc.1.2, fun c hc => ⟨fun hcomp => ?_, fun h0 => ?_⟩⟩
  · have hcC : c ∈ C := connectedComponentIn_subset C e hcomp
    have : c ∈ C ∩ (U : Set Y) := ⟨hcC, hc.1.2⟩
    rw [hCU] at this
    exact this.2
  · exact hSpre.subset_connectedComponentIn heS hSC ⟨hc, h0⟩

end DifferentialGeometry.Topology.Manifold

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold

namespace GC.GraphManifold.Assembly.FC39P0

open DifferentialGeometry.Topology.Manifold

/-- **The endpoint chart of an edge bundle with the component clause `hC`**: at an endpoint `e`
of `C₂` there are `U ∋ e` and `b` smooth on `U` with `b e = 0`, `db(e) ≠ 0`, `C₂ ∩ U = {b ≥ 0}` and
(`hC`, shrinking `U`) `c ∈ e.component ↔ 0 ≤ b c` on `U`. -/
theorem EdgeBundle.exists_endpoint_chart_JN74 {W : CompactCarrier.{u}} (P : EdgeBundle W)
    (e : P.EdgeEnd) :
    ∃ (b : P.Base → ℝ) (U : TopologicalSpace.Opens P.Base), e.1 ∈ U ∧
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ b U ∧ b e.1 = 0 ∧
      mfderiv (𝓡 1) 𝓘(ℝ, ℝ) b e.1 ≠ 0 ∧
      P.cbase ∩ U = {c | c ∈ U ∧ 0 ≤ b c} ∧
      ∀ c ∈ U, (c ∈ e.component.1 ↔ 0 ≤ b c) := by
  obtain ⟨U, heU, φ, hφ, hφ0, hreg, hcU⟩ := P.cbase_domain e.1 e.2
  obtain ⟨U', heU', hU'U, hcomp⟩ := exists_nhds_component_iff_JN74 (C := P.cbase) heU hφ hφ0 hreg
    hcU
  refine ⟨φ, U', heU', hφ.mono hU'U, hφ0, hreg, ?_, hcomp⟩
  ext c
  constructor
  · rintro ⟨hc, hcU'⟩
    exact ⟨hcU', ((Set.ext_iff.1 hcU c).1 ⟨hc, hU'U hcU'⟩).2⟩
  · rintro ⟨hcU', hc0⟩
    exact ⟨((Set.ext_iff.1 hcU c).2 ⟨hU'U hcU', hc0⟩).1, hcU'⟩

end GC.GraphManifold.Assembly.FC39P0

