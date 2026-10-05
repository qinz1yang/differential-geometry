import DifferentialGeometry.Topology.Manifold.RegularLevel.HalfSpaceSliceImmersion
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts

/-!
# FC39 GROUP G arcs (A3): the trace of one defining function is a compact one-manifold

Lane FC39-G-ARC (external draft 58 §四 A3, disposition D58-5). For a circle region `R` and a
defining index `i`, the UNROUNDED trace

  `R.traceSet_GARC i = {c ∈ R.cornerBase | R.defining i c = 0}`

is a compact smooth one-manifold with boundary (modelled on `EuclideanHalfSpace 1`), smoothly
embedded in the base, whose INTRINSIC boundary is the set of its points where a second defining
function vanishes (`R.traceBd_GARC i`) — not the ambient frontier.

* `CircleRegion.exists_traceChart_GARC` — a slice chart at every point of the trace, with positive
  first coordinate on its whole source: one active function (`defining_regular`, the other ones
  negative near the point) or a double zero (`defining_independent`, `depth_le_two`: the third
  ones negative near the point);
* `CircleRegion.traceChartedSpace_GARC`, `traceIsManifold_GARC`, `traceCompactSpace_GARC`;
* `CircleRegion.trace_isBoundaryPoint_iff_GARC` — boundary point ⇔ second zero;
* `CircleRegion.trace_val_isSmoothEmbedding_GARC` — the inclusion is a smooth embedding into the
  base (the immersion is `slice_isImmersionOfComplement_val_GARC`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold Topology GC.Endpoint
open DifferentialGeometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

variable {W : CompactCarrier.{u}} (R : CircleRegion W) (i : Fin R.definingCount)

/-- The unrounded trace of the defining function `i` in the cornered base. -/
def CircleRegion.traceSet_GARC : Set R.Base :=
  {c | c ∈ R.cornerBase ∧ R.defining i c = 0}

/-- A point of the base where a defining function other than `i` vanishes. -/
def CircleRegion.traceBd_GARC (c : R.Base) : Prop :=
  ∃ l, l ≠ i ∧ R.defining l c = 0

theorem CircleRegion.defining_continuous_GARC (l : Fin R.definingCount) :
    Continuous (R.defining l) :=
  (R.defining_smooth l).continuous

theorem CircleRegion.isClosed_cornerBase_GARC : IsClosed R.cornerBase :=
  R.cornerBase_compact.isClosed

theorem CircleRegion.isCompact_traceSet_GARC : IsCompact (R.traceSet_GARC i) := by
  refine R.cornerBase_compact.of_isClosed_subset ?_ (fun c hc => hc.1)
  exact R.isClosed_cornerBase_GARC.inter
    (isClosed_eq (R.defining_continuous_GARC i) continuous_const)

theorem CircleRegion.defining_nonpos_GARC {c : R.Base} (hc : c ∈ R.cornerBase)
    (l : Fin R.definingCount) : R.defining l c ≤ 0 := by
  rw [R.cornerBase_eq] at hc
  exact hc l

/-- A nonzero continuous linear functional is onto. -/
theorem surjective_of_ne_zero_GARC {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (L : V →L[ℝ] ℝ) (h : L ≠ 0) : Surjective L := by
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hc
    exact h (ContinuousLinearMap.ext fun v => not_not.mp fun hn => hc ⟨v, hn⟩)
  intro t
  refine ⟨(t / L v) • v, ?_⟩
  rw [map_smul, smul_eq_mul]
  field_simp

/-- The differential of a defining function at a zero is onto `ℝ`. -/
theorem CircleRegion.defining_mfderiv_surjective_GARC {l : Fin R.definingCount} {c : R.Base}
    (hc : R.defining l c = 0) :
    Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (R.defining l) c) :=
  surjective_of_ne_zero_GARC _ (R.defining_regular l c hc)

/-- Restriction of a slice chart to an open set around `x` on which the first coordinate is
positive. -/
theorem exists_restrict_sliceChart_pos_GARC {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    (Φ : PartialDiffeomorph (𝓡 2) ((𝓡∂ 1).prod 𝓘(ℝ, ℝ)) M (EuclideanHalfSpace 1 × ℝ) ∞)
    (U : Set M) (hU : IsOpen U) {x : M} (hxΦ : x ∈ Φ.source) (hxU : x ∈ U)
    (hx0 : 0 < (Φ x).1.1 0) :
    ∃ Ψ : PartialDiffeomorph (𝓡 2) ((𝓡∂ 1).prod 𝓘(ℝ, ℝ)) M (EuclideanHalfSpace 1 × ℝ) ∞,
      x ∈ Ψ.source ∧ Ψ.source ⊆ Φ.source ∩ U ∧ (∀ y, Ψ y = Φ y) ∧
      ∀ y ∈ Ψ.source, 0 < (Ψ y).1.1 0 := by
  have hcont : Continuous fun q : EuclideanHalfSpace 1 × ℝ => q.1.1 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp (continuous_subtype_val.comp continuous_fst)
  have hV : IsOpen (Φ.source ∩ Φ ⁻¹' {q | 0 < q.1.1 0}) :=
    Φ.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage Φ.open_source
      (isOpen_lt continuous_const hcont)
  refine ⟨DifferentialGeometry.Topology.PartialDiffeomorph.restrict Φ _ (hV.inter hU),
    ⟨hxΦ, ⟨hxΦ, hx0⟩, hxU⟩, fun y hy => ⟨hy.1, hy.2.2⟩, fun y => rfl, fun y hy => hy.2.1.2⟩

/-- The open set where the defining functions outside `S` are negative. -/
theorem CircleRegion.isOpen_others_neg_GARC (S : Finset (Fin R.definingCount)) :
    IsOpen {y : R.Base | ∀ l, l ∉ S → R.defining l y < 0} := by
  have : {y : R.Base | ∀ l, l ∉ S → R.defining l y < 0} =
      ⋂ l ∈ (Finset.univ.filter fun l => l ∉ S), {y | R.defining l y < 0} := by
    ext y
    simp
  rw [this]
  exact isOpen_biInter_finset fun l _ =>
    isOpen_lt (R.defining_continuous_GARC l) continuous_const

/-- **A slice chart at every point of the trace** with positive first coordinate on its whole
source; height `0` at a simple zero, height `1` at a double zero. -/
theorem CircleRegion.exists_traceChart_GARC (x : R.Base) (hx : x ∈ R.traceSet_GARC i) :
    ∃ p : PartialDiffeomorph (𝓡 2) ((𝓡∂ 1).prod 𝓘(ℝ, ℝ)) R.Base
        (EuclideanHalfSpace 1 × ℝ) ∞ × ℝ,
      0 ≤ p.2 ∧ x ∈ p.1.source ∧
      (∀ y ∈ p.1.source, y ∈ R.traceSet_GARC i ↔ ((p.1 y).2 = 0 ∧ p.2 ≤ (p.1 y).1.1 0)) ∧
      ((p.1 x).1.1 0 = p.2 ↔ R.traceBd_GARC i x) ∧ ∀ y ∈ p.1.source, 0 < (p.1 y).1.1 0 := by
  classical
  have hint : (𝓡 2).IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 0 + 1 + Module.finrank ℝ ℝ := by
    simp
  by_cases hbd : R.traceBd_GARC i x
  · -- double zero: `Ψ = defining i`, `B = -defining l`
    obtain ⟨l, hli, hlx⟩ := hbd
    have hreg : Surjective (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × ℝ)
        (fun y => (R.defining i y, -R.defining l y)) x) := by
      have hdi : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (R.defining i) x :=
        ((R.defining_smooth i) x).mdifferentiableAt (by simp)
      have hdl : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (R.defining l) x :=
        ((R.defining_smooth l) x).mdifferentiableAt (by simp)
      have hF : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ × ℝ) (fun y => (R.defining i y, -R.defining l y)) x
          ((mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (R.defining i) x).prod
            (-mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (R.defining l) x)) :=
        ⟨hdi.continuousAt.prodMk hdl.continuousAt.neg,
          hdi.hasMFDerivAt.2.prodMk hdl.hasMFDerivAt.neg.2⟩
      rw [hF.mfderiv]
      intro w
      obtain ⟨w1, w2⟩ := w
      obtain ⟨v, hv⟩ := R.defining_independent x i l hli.symm hx.2 hlx (w1, -w2)
      obtain ⟨hv1, hv2⟩ := Prod.ext_iff.mp hv
      refine ⟨v, Prod.ext hv1 ?_⟩
      have h2 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (R.defining l) x v = -w2 := hv2
      change -(mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (R.defining l) x v) = w2
      rw [h2]
      exact neg_neg w2
    obtain ⟨Φ, hxΦ, hΦx, hΦ⟩ := exists_sliceChart_of_zero (d := 0) hdim (R.defining_smooth i)
      ((R.defining_smooth l).neg) hint (by rw [hlx, neg_zero]) hreg
    let U : Set R.Base := {y | ∀ l', l' ∉ ({i, l} : Finset _) → R.defining l' y < 0}
    have hxU : x ∈ U := by
      intro l' hl'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl'
      refine lt_of_le_of_ne (R.defining_nonpos_GARC hx.1 l') fun h0 => ?_
      have hcard := R.depth_le_two x
      have hsub : ({i, l, l'} : Finset (Fin R.definingCount)) ⊆
          Finset.univ.filter fun l => R.defining l x = 0 := by
        intro m hm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl | rfl <;> simp [hx.2, hlx, h0]
      have h3 : ({i, l, l'} : Finset (Fin R.definingCount)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hl'.2)]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hli.symm, Ne.symm hl'.1⟩
      have := Finset.card_le_card hsub
      omega
    obtain ⟨Ψ, hxΨ, hΨsub, hΨeq, hΨpos⟩ := exists_restrict_sliceChart_pos_GARC Φ U
      (R.isOpen_others_neg_GARC {i, l}) hxΦ hxU (by rw [hΦx]; norm_num)
    refine ⟨(Ψ, 1), zero_le_one, hxΨ, fun y hy => ?_, ?_, hΨpos⟩
    · have hyU := (hΨsub hy).2
      change y ∈ R.traceSet_GARC i ↔ (Ψ y).2 = 0 ∧ 1 ≤ (Ψ y).1.1 0
      rw [hΨeq, ← hΦ y (hΨsub hy).1]
      constructor
      · rintro ⟨hyc, hyi⟩
        exact ⟨hyi, by rw [neg_nonneg]; exact R.defining_nonpos_GARC hyc l⟩
      · rintro ⟨hyi, hyl⟩
        refine ⟨?_, hyi⟩
        rw [R.cornerBase_eq]
        intro m
        by_cases hm : m ∈ ({i, l} : Finset _)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl
          · rw [hyi]
          · linarith
        · exact (hyU m hm).le
    · change (Ψ x).1.1 0 = 1 ↔ _
      rw [hΨeq, hΦx]
      exact iff_of_true rfl ⟨l, hli, hlx⟩
  · -- simple zero: `Ψ = defining i`, `B = 1`
    obtain ⟨Φ, hxΦ, hΦpos, hΦ⟩ := exists_sliceChart_of_pos (d := 0) hdim (R.defining_smooth i)
      (contMDiff_const (c := (1 : ℝ))) hint one_pos (R.defining_mfderiv_surjective_GARC hx.2)
    let U : Set R.Base := {y | ∀ l', l' ∉ ({i} : Finset _) → R.defining l' y < 0}
    have hxU : x ∈ U := by
      intro l' hl'
      rw [Finset.mem_singleton] at hl'
      exact lt_of_le_of_ne (R.defining_nonpos_GARC hx.1 l') fun h0 => hbd ⟨l', hl', h0⟩
    obtain ⟨Ψ, hxΨ, hΨsub, hΨeq, hΨpos⟩ := exists_restrict_sliceChart_pos_GARC Φ U
      (R.isOpen_others_neg_GARC {i}) hxΦ hxU (hΦpos x hxΦ)
    refine ⟨(Ψ, 0), le_rfl, hxΨ, fun y hy => ?_, ?_, hΨpos⟩
    · have hyU := (hΨsub hy).2
      change y ∈ R.traceSet_GARC i ↔ (Ψ y).2 = 0 ∧ 0 ≤ (Ψ y).1.1 0
      rw [hΨeq, ← hΦ y (hΨsub hy).1]
      constructor
      · rintro ⟨-, hyi⟩
        exact ⟨hyi, zero_le_one⟩
      · rintro ⟨hyi, -⟩
        refine ⟨?_, hyi⟩
        rw [R.cornerBase_eq]
        intro m
        by_cases hm : m = i
        · rw [hm, hyi]
        · exact (hyU m (by rw [Finset.mem_singleton]; exact hm)).le
    · change (Ψ x).1.1 0 = 0 ↔ _
      exact iff_of_false (hΨpos x hxΨ).ne' hbd

/-- The slice-chart hypothesis of `sliceChartedSpace` for the trace. -/
theorem CircleRegion.traceHP_GARC :
    ∀ x, x ∈ R.traceSet_GARC i →
      ∃ p : PartialDiffeomorph (𝓡 2) ((𝓡∂ (0 + 1)).prod 𝓘(ℝ, ℝ)) R.Base
          (EuclideanHalfSpace (0 + 1) × ℝ) ∞ × ℝ,
        0 ≤ p.2 ∧ x ∈ p.1.source ∧
        (∀ y ∈ p.1.source, y ∈ R.traceSet_GARC i ↔ ((p.1 y).2 = 0 ∧ p.2 ≤ (p.1 y).1.1 0)) ∧
        ((p.1 x).1.1 0 = p.2 ↔ R.traceBd_GARC i x) := fun x hx =>
  (R.exists_traceChart_GARC i x hx).imp fun _ hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

/-- **The trace as a smooth one-manifold with boundary.** -/
instance CircleRegion.traceChartedSpace_GARC :
    ChartedSpace (EuclideanHalfSpace 1) (R.traceSet_GARC i) :=
  sliceChartedSpace (fun c => c ∈ R.traceSet_GARC i) (R.traceBd_GARC i) (R.traceHP_GARC i)

instance CircleRegion.traceIsManifold_GARC : IsManifold (𝓡∂ 1) ∞ (R.traceSet_GARC i) :=
  slice_isManifold (fun c => c ∈ R.traceSet_GARC i) (R.traceBd_GARC i) (R.traceHP_GARC i)

instance CircleRegion.traceCompactSpace_GARC : CompactSpace (R.traceSet_GARC i) :=
  isCompact_iff_compactSpace.mp (R.isCompact_traceSet_GARC i)

/-- **The intrinsic boundary of the trace** is the set of its points where a second defining
function vanishes. -/
theorem CircleRegion.trace_isBoundaryPoint_iff_GARC {R : CircleRegion W} {i : Fin R.definingCount}
    {x : R.traceSet_GARC i} :
    (𝓡∂ 1).IsBoundaryPoint x ↔ R.traceBd_GARC i x.1 :=
  slice_isBoundaryPoint_iff (R.traceHP_GARC i)

/-- **The inclusion of the trace is a smooth embedding into the base.** -/
theorem CircleRegion.trace_val_isSmoothEmbedding_GARC :
    IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ (Subtype.val : R.traceSet_GARC i → R.Base) := by
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin (0 + 1)) × ℝ) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    simp
  let L : (EuclideanSpace ℝ (Fin (0 + 1)) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofFinrankEq hrank
  have himm := slice_isImmersionOfComplement_val_GARC (fun c => c ∈ R.traceSet_GARC i)
    (R.traceBd_GARC i) (R.traceHP_GARC i) L (fun x hx =>
      (R.exists_traceChart_GARC i x hx).imp fun _ hp =>
        ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.2⟩)
  let _ : ChartedSpace (EuclideanHalfSpace (0 + 1)) (R.traceSet_GARC i) :=
    R.traceChartedSpace_GARC i
  exact ⟨himm.isImmersion, IsEmbedding.subtypeVal⟩

end GC.GraphManifold.Assembly
