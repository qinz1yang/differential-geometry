import DifferentialGeometry.Topology.Manifold.GraphBand
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphRange
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace G M]

theorem exists_smoothTwoSidedCollar_of_product_chart_graph [CompactSpace N]
    (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : Diffeomorph (I.prod 𝓘(ℝ)) J O V ∞)
    (a : N → ℝ) (ha : ContMDiff I 𝓘(ℝ) ∞ a)
    (hgraph : ∀ p, (p, a p) ∈ O) {r : ℝ} (hr : 0 < r) :
    ∃ c : SmoothTwoSidedCollar I J (fun p ↦ (Φ ⟨(p, a p), hgraph p⟩ : M)),
      c.radius < r ∧
      (∀ p t, t ∈ Icc (-c.radius) c.radius → (p, a p + t) ∈ O) ∧
      ∀ p : N × symmetricOpenInterval c.radius,
        ∃ hp : (p.1, a p.1 + (p.2 : ℝ)) ∈ O,
          c.toFun p = (Φ ⟨(p.1, a p.1 + (p.2 : ℝ)), hp⟩ : M) := by
  let IP := I.prod 𝓘(ℝ)
  let g : Diffeomorph IP IP (N × ℝ) (N × ℝ) ∞ :=
    graphBandDiffeomorph a (fun p ↦ a p + 1) ha (ha.add contMDiff_const)
      (fun p ↦ lt_add_one (a p))
  have hg (p : N × ℝ) : g p = (p.1, a p.1 + p.2) := by
    simpa only [add_sub_cancel_left, one_mul] using
      graphBandDiffeomorph_apply a (fun p ↦ a p + 1) ha (ha.add contMDiff_const)
        (fun p ↦ lt_add_one (a p)) p
  have hzero : (univ : Set N) ×ˢ {(0 : ℝ)} ⊆ g ⁻¹' (O : Set (N × ℝ)) := by
    rintro ⟨p, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    simpa [hg, ht0] using hgraph p
  obtain ⟨U, W, _, hW, hU, hW0, hUW⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton
      (O.isOpen.preimage g.contMDiff.continuous) hzero
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds (hW0 (mem_singleton 0)))
  let δ := min (ε / 2) (r / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδr : δ < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hstrip (p : N) (t : ℝ) (ht : t ∈ Icc (-δ) δ) : (p, a p + t) ∈ O := by
    have htε : t ∈ Metric.ball (0 : ℝ) ε := by
      rw [Real.ball_eq_Ioo]
      constructor <;> linarith [ht.1, ht.2]
    have : g (p, t) ∈ O := hUW ⟨hU (mem_univ p), hεW htε⟩
    simpa only [mem_preimage, hg] using this
  let Z : TopologicalSpace.Opens (N × ℝ) :=
    ⟨univ ×ˢ Ioo (-δ) δ, isOpen_univ.prod isOpen_Ioo⟩
  let d : Diffeomorph IP IP (N × symmetricOpenInterval δ) Z ∞ := {
    toEquiv := {
      toFun := fun p ↦ ⟨(p.1, p.2.val), mem_univ _, p.2.property⟩
      invFun := fun p ↦ (p.val.1, ⟨p.val.2, p.property.2⟩)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    contMDiff_toFun := by
      apply (ContMDiff.subtypeVal_comp_iff Z _).mp
      exact contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
    contMDiff_invFun := by
      apply ContMDiff.prodMk
      · exact contMDiff_fst.comp contMDiff_subtype_val
      · apply (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval δ) _).mp
        exact contMDiff_snd.comp contMDiff_subtype_val }
  have hgO (p : Z) : g p.val ∈ O := by
    rw [hg]
    exact hstrip p.val.1 p.val.2 ⟨p.property.2.1.le, p.property.2.2.le⟩
  let gO : Z → O := fun p ↦ ⟨g p.val, hgO p⟩
  have hlocg : IsLocalDiffeomorph IP IP ∞ gO := by
    intro p
    apply isLocalDiffeomorphAt_subtypeCodRestrict hgO
    exact (isLocalDiffeomorph_restrict_open Z
      (g.isLocalDiffeomorph.isLocalDiffeomorphOn Z)) p
  let f : N × symmetricOpenInterval δ → M := fun p ↦ (Φ (gO (d p)) : M)
  have hlocf : IsLocalDiffeomorph IP J ∞ f :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val V)
      (isLocalDiffeomorph_comp Φ.isLocalDiffeomorph
        (isLocalDiffeomorph_comp hlocg d.isLocalDiffeomorph))
  have hinjf : Function.Injective f := by
    intro p q hpq
    apply d.injective
    apply Subtype.ext
    apply g.injective
    exact congrArg Subtype.val (Φ.injective (Subtype.ext hpq))
  let c : SmoothTwoSidedCollar I J (fun p ↦ (Φ ⟨(p, a p), hgraph p⟩ : M)) := {
    radius := δ
    radius_pos := hδ
    neighborhood := hlocf.image
    toDiffeomorph := diffeomorphRangeOfInjective hlocf hinjf
    zero_eq := by
      intro p
      change (Φ (gO (d (p, ⟨0, neg_lt_zero.mpr hδ, hδ⟩))) : M) = _
      apply congrArg (fun z : O ↦ (Φ z : M))
      apply Subtype.ext
      change g (p, 0) = (p, a p)
      rw [hg]
      simp only [add_zero] }
  refine ⟨c, hδr, hstrip, ?_⟩
  intro p
  refine ⟨hstrip p.1 p.2 ⟨p.2.property.1.le, p.2.property.2.le⟩, ?_⟩
  change (Φ (gO (d p)) : M) = _
  apply congrArg (fun z : O ↦ (Φ z : M))
  apply Subtype.ext
  exact hg (p.1, p.2.val)

end DifferentialGeometry.Topology
