import DifferentialGeometry.Topology.Manifold.BoundaryIntegralCurve
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Lattice.Fold

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_uniform_localFlow_of_compact
    {v : (x : M) → TangentSpace I x} {K : Set M} (hK : IsCompact K)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hlocal : ∀ x ∈ K, ∃ ε > 0, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∃ Φ : M × ℝ → M, (∀ y ∈ V, Φ (y, 0) = y) ∧
        ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ (V ×ˢ Ico 0 ε) ∧
        (∀ y ∈ V, IsMIntegralCurveOn (fun t ↦ Φ (y, t)) v (Ico 0 ε)) ∧
        ∀ y ∈ V, ∀ t ∈ Ioo 0 ε, I.IsInteriorPoint (Φ (y, t))) :
    ∃ ε > 0, ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧
      ∃ Φ : M × ℝ → M, (∀ y ∈ U, Φ (y, 0) = y) ∧
        ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ (U ×ˢ Ico 0 ε) ∧
        (∀ y ∈ U, IsMIntegralCurveOn (fun t ↦ Φ (y, t)) v (Ico 0 ε)) ∧
        ∀ y ∈ U, ∀ t ∈ Ioo 0 ε, I.IsInteriorPoint (Φ (y, t)) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, ∅, isOpen_empty, empty_subset _, Prod.fst,
      fun _ _ ↦ rfl, contMDiffOn_fst, (fun _ hy ↦ hy.elim), fun _ hy ↦ hy.elim⟩
  have hlocal' := fun x : K ↦ hlocal x.1 x.2
  choose τ hτ V hV hxV F hzero hF hcurve hinside using hlocal'
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hxV _⟩)
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    obtain ⟨i, hi, _⟩ := mem_iUnion.mp (hs hx) |>.imp fun i hi ↦ mem_iUnion.mp hi
    exact ⟨i, hi⟩
  let ε := s.inf' hsne τ
  have hε : 0 < ε := (Finset.lt_inf'_iff hsne).mpr (fun i _ ↦ hτ i)
  have hbound : ∀ i ∈ s, ε ≤ τ i := fun i hi ↦ Finset.inf'_le τ hi
  have htime : ∀ i ∈ s, Ico (0 : ℝ) ε ⊆ Ico 0 (τ i) :=
    fun i hi t ht ↦ ⟨ht.1, ht.2.trans_le (hbound i hi)⟩
  let U := ⋃ i ∈ s, V i
  have hU : IsOpen U := isOpen_biUnion (fun i _ ↦ hV i)
  have hselect : ∀ y ∈ U, ∃ i, i ∈ s ∧ y ∈ V i := by
    intro y hy
    simpa only [U, mem_iUnion, exists_prop] using hy
  let index : U → K := fun y ↦ Classical.choose (hselect y.1 y.2)
  have hindex : ∀ y : U, index y ∈ s ∧ y.1 ∈ V (index y) :=
    fun y ↦ Classical.choose_spec (hselect y.1 y.2)
  let Φ : M × ℝ → M := fun z ↦ if hz : z.1 ∈ U then F (index ⟨z.1, hz⟩) z else z.1
  have hagree : ∀ i ∈ s, ∀ j ∈ s, ∀ y ∈ V i ∩ V j,
      EqOn (fun t ↦ F i (y, t)) (fun t ↦ F j (y, t)) (Ico 0 ε) := by
    intro i hi j hj y hy
    apply isMIntegralCurveOn_Ico_eqOn ⟨le_rfl, hε⟩ hv
      ((hcurve i y hy.1).mono (htime i hi)) ((hcurve j y hy.2).mono (htime j hj))
    rw [hzero i y hy.1, hzero j y hy.2]
  have hΦeq : ∀ i ∈ s, ∀ y ∈ V i, ∀ t ∈ Ico 0 ε, Φ (y, t) = F i (y, t) := by
    intro i hi y hy t ht
    have hyU : y ∈ U := mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hy⟩⟩
    dsimp only [Φ]
    rw [dif_pos hyU]
    exact hagree _ (hindex ⟨y, hyU⟩).1 i hi y ⟨(hindex ⟨y, hyU⟩).2, hy⟩ ht
  have hsmooth : ContMDiffOn (I.prod 𝓘(ℝ)) I ∞ Φ (U ×ˢ Ico 0 ε) := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro z hz
    obtain ⟨i, hi, hzi⟩ := hselect z.1 hz.1
    refine ⟨V i ×ˢ univ, (hV i).prod isOpen_univ, ⟨hzi, mem_univ _⟩, ?_⟩
    apply ((hF i).mono (fun q hq ↦ ⟨hq.2.1, htime i hi hq.1.2⟩)).congr
    intro q hq
    exact hΦeq i hi q.1 hq.2.1 q.2 hq.1.2
  refine ⟨ε, hε, U, hU, hs, Φ, ?_, hsmooth, ?_, ?_⟩
  · intro y hy
    obtain ⟨i, hi, hyi⟩ := hselect y hy
    rw [hΦeq i hi y hyi 0 ⟨le_rfl, hε⟩, hzero i y hyi]
  · intro y hy t ht
    obtain ⟨i, hi, hyi⟩ := hselect y hy
    have hd := ((hcurve i y hyi).mono (htime i hi)) t ht
    apply (hd.congr_mono (fun r hr ↦ hΦeq i hi y hyi r hr)
      (hΦeq i hi y hyi t ht) subset_rfl).congr_mfderiv
    dsimp only
    rw [hΦeq i hi y hyi t ht]
  · intro y hy t ht
    obtain ⟨i, hi, hyi⟩ := hselect y hy
    rw [hΦeq i hi y hyi t ⟨ht.1.le, ht.2⟩]
    exact hinside i y hyi t ⟨ht.1, ht.2.trans_le (hbound i hi)⟩

end Poincare.Topology.Manifold
