import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckTubeIndexBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry.Geometry.Curvature

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem abs_ratio_sub_one_le_of_common_scale
    (R Q₀ Q₁ η : ℝ) (hQ₀ : 0 < Q₀) (hQ₁ : 0 < Q₁) (hη : η ≤ 1 / 2)
    (h₀ : |R / Q₀ - 1| ≤ η) (h₁ : |R / Q₁ - 1| ≤ η) :
    |Q₀ / Q₁ - 1| ≤ 4 * η := by
  have hlow : 1 / 2 ≤ R / Q₀ := by
    have h := (abs_le.mp h₀).1
    linarith only [h, hη]
  have hid : (R / Q₀) * (Q₀ / Q₁ - 1) = (R / Q₁ - 1) - (R / Q₀ - 1) := by
    field_simp
    ring
  have hdiff : |(R / Q₀) * (Q₀ / Q₁ - 1)| ≤ 2 * η := by
    rw [hid]
    exact (abs_sub _ _).trans (by linarith only [h₀, h₁])
  rw [abs_mul, abs_of_pos (lt_of_lt_of_le (by norm_num) hlow)] at hdiff
  have hprod := mul_le_mul_of_nonneg_right hlow (abs_nonneg (Q₀ / Q₁ - 1))
  linarith only [hdiff, hprod]

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]

omit [T2Space M] in
theorem NormalizedNeck.scale_eq_of_center_eq {g : SmoothRiemannianMetric ThreeModel M}
    {δ₁ δ₂ : ℝ} {k₁ k₂ : ℕ} (N₁ : NormalizedNeck g δ₁ k₁)
    (N₂ : NormalizedNeck g δ₂ k₂)
    (h : N₁.center = N₂.center) : N₁.scale = N₂.scale := by
  rw [N₁.scale_scalar, N₂.scale_scalar, h]

theorem NormalizedNeck.scale_ratio_of_common_point {g : SmoothRiemannianMetric ThreeModel M}
    {δ₁ δ₂ : ℝ} {k₁ k₂ : ℕ} (N₁ : NormalizedNeck g δ₁ k₁)
    (N₂ : NormalizedNeck g δ₂ k₂)
    (hk₁ : 2 ≤ k₁) (hk₂ : 2 ≤ k₂) (hd₁ : δ₁ ≤ 1 / 2) (hd₂ : δ₂ ≤ 1 / 2)
    {x₁ : neckBuffer δ₁} {x₂ : neckBuffer δ₂} (hx₁ : x₁ ∈ neckClosedTest δ₁)
    (hx₂ : x₂ ∈ neckClosedTest δ₂) (hcommon : N₁.chart x₁ = N₂.chart x₂)
    (hsmall : 4323 * max δ₁ δ₂ ≤ 1 / 2) :
    |N₁.scale / N₂.scale - 1| ≤ 17292 * max δ₁ δ₂ := by
  have e₁ := N₁.abs_scalar_ratio_sub_one_le hk₁ hd₁ x₁ hx₁
  have e₂ := N₂.abs_scalar_ratio_sub_one_le hk₂ hd₂ x₂ hx₂
  rw [hcommon] at e₁
  have h₁ : |metricScalarAt g (N₂.chart x₂) / N₁.scale - 1| ≤ 4323 * max δ₁ δ₂ :=
    e₁.trans (mul_le_mul_of_nonneg_left (le_max_left δ₁ δ₂) (by norm_num))
  have h₂ : |metricScalarAt g (N₂.chart x₂) / N₂.scale - 1| ≤ 4323 * max δ₁ δ₂ :=
    e₂.trans (mul_le_mul_of_nonneg_left (le_max_right δ₁ δ₂) (by norm_num))
  have h := abs_ratio_sub_one_le_of_common_scale (metricScalarAt g (N₂.chart x₂))
    N₁.scale N₂.scale (4323 * max δ₁ δ₂) N₁.scale_pos N₂.scale_pos hsmall h₁ h₂
  have h4 : 4 * (4323 * max δ₁ δ₂) = 17292 * max δ₁ δ₂ := by ring
  linarith only [h, h4]

theorem isPreconnected_sphereTwo_univ : IsPreconnected (Set.univ : Set (Sphere 2)) := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Set.image_univ, Subtype.range_val]
  exact isPreconnected_sphere (E := EuclideanSpace ℝ (Fin 3))
    (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 1

omit [T2Space M] in
theorem NormalizedNeck.isPreconnected_upperSide {g : SmoothRiemannianMetric ThreeModel M}
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) :
    IsPreconnected (N.chart '' {z : neckBuffer δ | 2 < z.1.2}) := by
  have hprod : IsPreconnected
      ((Set.univ : Set (Sphere 2)) ×ˢ Set.Ioo (2 : ℝ) (δ⁻¹ + 1)) :=
    isPreconnected_sphereTwo_univ.prod isPreconnected_Ioo
  have hset : Subtype.val '' {z : neckBuffer δ | 2 < z.1.2} =
      (Set.univ : Set (Sphere 2)) ×ˢ Set.Ioo (2 : ℝ) (δ⁻¹ + 1) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨trivial, hz, z.2.2⟩
    · rintro ⟨-, h2, hlt⟩
      have hbuf : q ∈ neckBuffer δ := by
        change -δ⁻¹ - 1 < q.2 ∧ q.2 < δ⁻¹ + 1
        constructor <;> linarith
      exact ⟨⟨q, hbuf⟩, h2, rfl⟩
  have hamb : IsPreconnected (Subtype.val '' {z : neckBuffer δ | 2 < z.1.2}) := by
    rw [hset]
    exact hprod
  have hsub : IsPreconnected {z : neckBuffer δ | 2 < z.1.2} := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    exact hamb
  exact hsub.image (fun z : neckBuffer δ => N.chart z) N.chart.continuous.continuousOn

omit [T2Space M] in
theorem NormalizedNeck.isPreconnected_lowerSide {g : SmoothRiemannianMetric ThreeModel M}
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k) :
    IsPreconnected (N.chart '' {z : neckBuffer δ | z.1.2 < -2}) := by
  have hprod : IsPreconnected
      ((Set.univ : Set (Sphere 2)) ×ˢ Set.Ioo (-δ⁻¹ - 1) (-2 : ℝ)) :=
    isPreconnected_sphereTwo_univ.prod isPreconnected_Ioo
  have hset : Subtype.val '' {z : neckBuffer δ | z.1.2 < -2} =
      (Set.univ : Set (Sphere 2)) ×ˢ Set.Ioo (-δ⁻¹ - 1) (-2 : ℝ) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨trivial, z.2.1, hz⟩
    · rintro ⟨-, hgt, hlt⟩
      have hbuf : q ∈ neckBuffer δ := by
        change -δ⁻¹ - 1 < q.2 ∧ q.2 < δ⁻¹ + 1
        have h := inv_pos.mpr N.delta_pos
        constructor <;> linarith
      exact ⟨⟨q, hbuf⟩, hlt, rfl⟩
  have hamb : IsPreconnected (Subtype.val '' {z : neckBuffer δ | z.1.2 < -2}) := by
    rw [hset]
    exact hprod
  have hsub : IsPreconnected {z : neckBuffer δ | z.1.2 < -2} := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    exact hamb
  exact hsub.image (fun z : neckBuffer δ => N.chart z) N.chart.continuous.continuousOn

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}

theorem GeometricCutoffRecord.nominalRadius_ratio_of_common_point
    (G : GeometricCutoffRecord H i parameters)
    {α β : (H.event i).transition.trace.tubes.Index}
    (hk : 2 ≤ G.order α) (hk' : 2 ≤ G.order β)
    (hd : G.delta α ≤ 1 / 2) (hd' : G.delta β ≤ 1 / 2)
    {xα : neckBuffer (G.delta α)} {xβ : neckBuffer (G.delta β)}
    (hxα : xα ∈ neckClosedTest (G.delta α)) (hxβ : xβ ∈ neckClosedTest (G.delta β))
    (hcommon : (G.neck α).chart xα = (G.neck β).chart xβ)
    (hsmall : 4323 * max (G.delta α) (G.delta β) ≤ 1 / 2) :
    |(G.nominalRadius ⟨β⟩ / G.nominalRadius ⟨α⟩) ^ 2 - 1| ≤
      17292 * max (G.delta α) (G.delta β) := by
  have h := NormalizedNeck.scale_ratio_of_common_point (G.neck α) (G.neck β) hk hk' hd hd'
    hxα hxβ hcommon hsmall
  rw [G.scale_eq α, G.scale_eq β] at h
  have hα : G.nominalRadius ⟨α⟩ ≠ 0 := ne_of_gt (G.nominal_pos ⟨α⟩)
  have hβ : G.nominalRadius ⟨β⟩ ≠ 0 := ne_of_gt (G.nominal_pos ⟨β⟩)
  have hscale : (G.nominalRadius ⟨α⟩ ^ 2)⁻¹ / (G.nominalRadius ⟨β⟩ ^ 2)⁻¹ =
      (G.nominalRadius ⟨β⟩ / G.nominalRadius ⟨α⟩) ^ 2 := by
    field_simp
  rwa [hscale] at h

def neckChartSideOf (δ : (H.event i).transition.trace.tubes.Index → ℝ)
    (k : (H.event i).transition.trace.tubes.Index → ℕ)
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (δ α) (k α))
    (α : (H.event i).transition.trace.tubes.Index) (s : Bool) :
    Set ↥(H.event i).incoming.terminalRegularOpen :=
  (neck α).chart '' {z : neckBuffer (δ α) | if s then 2 < z.1.2 else z.1.2 < -2}

theorem neckChartTail_eq_union_sides_of
    (δ : (H.event i).transition.trace.tubes.Index → ℝ)
    (k : (H.event i).transition.trace.tubes.Index → ℕ)
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (δ α) (k α))
    (α : (H.event i).transition.trace.tubes.Index) :
    neckChartTailOf δ k neck α =
      neckChartSideOf δ k neck α true ∪ neckChartSideOf δ k neck α false := by
  have hset : {z : neckBuffer (δ α) | 2 < |z.1.2|} =
      {z : neckBuffer (δ α) | 2 < z.1.2} ∪ {z : neckBuffer (δ α) | z.1.2 < -2} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    have h1 : (2 : ℝ) < -z.1.2 ↔ z.1.2 < -2 := by
      constructor <;> intro h <;> linarith
    rw [lt_abs, h1]
  rw [neckChartTailOf, neckChartSideOf, neckChartSideOf, hset, Set.image_union]
  simp

theorem neckChartSide_nonempty_of
    (δ : (H.event i).transition.trace.tubes.Index → ℝ)
    (k : (H.event i).transition.trace.tubes.Index → ℕ)
    (neck : ∀ α, NormalizedNeck (H.event i).terminal.metric (δ α) (k α))
    (α : (H.event i).transition.trace.tubes.Index) (s : Bool) :
    (neckChartSideOf δ k neck α s).Nonempty := by
  have hinv : 1 < (δ α)⁻¹ := (one_lt_inv₀ (neck α).delta_pos).mpr (neck α).delta_lt_one
  have hb : -((δ α)⁻¹) - 1 < -2 := by linarith
  have hup : 2 < (δ α)⁻¹ + 1 := by linarith
  cases s
  · refine ⟨(neck α).chart ⟨(sphereNorth, -(2 + ((δ α)⁻¹ + 1)) / 2), ?_⟩,
      ⟨⟨(sphereNorth, -(2 + ((δ α)⁻¹ + 1)) / 2), ?_⟩, ?_, rfl⟩⟩
    · rw [mem_neckBuffer_iff]
      constructor <;> linarith
    · rw [mem_neckBuffer_iff]
      constructor <;> linarith
    · change -(2 + ((δ α)⁻¹ + 1)) / 2 < -2
      linarith
  · refine ⟨(neck α).chart ⟨(sphereNorth, (2 + ((δ α)⁻¹ + 1)) / 2), ?_⟩,
      ⟨⟨(sphereNorth, (2 + ((δ α)⁻¹ + 1)) / 2), ?_⟩, ?_, rfl⟩⟩
    · rw [mem_neckBuffer_iff]
      constructor <;> linarith
    · rw [mem_neckBuffer_iff]
      constructor <;> linarith
    · change 2 < (2 + ((δ α)⁻¹ + 1)) / 2
      linarith

namespace GeometricCutoffRecord

abbrev neckChartSide (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) (s : Bool) :
    Set ↥(H.event i).incoming.terminalRegularOpen :=
  neckChartSideOf G.delta G.order G.neck α s

theorem neckChartTail_eq_union_sides (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) :
    neckChartTail G α = neckChartSide G α true ∪ neckChartSide G α false :=
  neckChartTail_eq_union_sides_of G.delta G.order G.neck α

theorem neckChartSide_nonempty (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) (s : Bool) :
    (neckChartSide G α s).Nonempty :=
  neckChartSide_nonempty_of G.delta G.order G.neck α s

theorem isPreconnected_neckChartSide (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) (s : Bool) :
    IsPreconnected (neckChartSide G α s) := by
  cases s
  · exact (G.neck α).isPreconnected_lowerSide
  · exact (G.neck α).isPreconnected_upperSide

theorem neckChartSide_disjoint_upper_lower (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) :
    Disjoint (neckChartSide G α true) (neckChartSide G α false) := by
  refine Set.disjoint_left.mpr fun y hy hy' => ?_
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨z', hz', hz'y⟩ := hy'
  have hzz : z = z' := (G.neck α).chart_smooth.isEmbedding.injective (hzy.trans hz'y.symm)
  subst hzz
  have h1 : 2 < z.1.2 := by simpa using hz
  have h2 : z.1.2 < -2 := by simpa using hz'
  linarith

theorem neckChartSide_disjoint_of_ne (G : GeometricCutoffRecord H i parameters)
    (α : (H.event i).transition.trace.tubes.Index) {s s' : Bool} (h : s ≠ s') :
    Disjoint (neckChartSide G α s) (neckChartSide G α s') := by
  cases s <;> cases s'
  · exact absurd rfl h
  · exact (neckChartSide_disjoint_upper_lower G α).symm
  · exact neckChartSide_disjoint_upper_lower G α
  · exact absurd rfl h

theorem neckChartTail_subset_iff_sides_subset (G : GeometricCutoffRecord H i parameters)
    {ε Λ : ℝ} {P : TerminalCorePresentation (OneStepIncoming.ofRecord G) ε Λ}
    {c : ConnectedComponents ↥(H.event i).incoming.terminalRegularOpen}
    {e : P.hornIndex c} (α : (H.event i).transition.trace.tubes.Index) :
    neckChartTail G α ⊆ TerminalCorePresentation.hornHalfRange P c e ↔
      neckChartSide G α true ⊆ TerminalCorePresentation.hornHalfRange P c e ∧
        neckChartSide G α false ⊆ TerminalCorePresentation.hornHalfRange P c e := by
  rw [neckChartTail_eq_union_sides G α]
  exact Set.union_subset_iff

end GeometricCutoffRecord

namespace TerminalCorePresentation

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ}

theorem exists_hornHalfRange_of_mem_component_not_mem_core (P : TerminalCorePresentation D ε Λ)
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen} (hc : c ∈ P.component)
    {y : ↥D.slab.terminalRegularOpen} (hmk : ConnectedComponents.mk y = c)
    (hcore : y ∉ P.core c) :
    ∃ e : P.hornIndex c, y ∈ hornHalfRange P c e := by
  have hy : y ∈ ({x : ↥D.slab.terminalRegularOpen | ConnectedComponents.mk x = c} : Set _) :=
    hmk
  rw [P.horn_covers_component c hc] at hy
  rcases hy with hy | hy
  · exact absurd hy hcore
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hy
    exact ⟨e, he⟩

theorem hornHalfRange_unique (P : TerminalCorePresentation D ε Λ)
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen} {y : ↥D.slab.terminalRegularOpen}
    {e e' : P.hornIndex c} (he : y ∈ hornHalfRange P c e) (he' : y ∈ hornHalfRange P c e') :
    e = e' := by
  by_contra hne
  exact Set.disjoint_left.mp (P.horn_range_disjoint c e e' hne) he he'

theorem exists_hornHalfRange_superset_of_isPreconnected (P : TerminalCorePresentation D ε Λ)
    {c : ConnectedComponents ↥D.slab.terminalRegularOpen} (hc : c ∈ P.component)
    {S : Set ↥D.slab.terminalRegularOpen} (hS : IsPreconnected S) (hne : S.Nonempty)
    (hcomp : ∀ y ∈ S, ConnectedComponents.mk y = c) (hcore : ∀ y ∈ S, y ∉ P.core c) :
    ∃ e : P.hornIndex c, S ⊆ hornHalfRange P c e := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨e₀, he₀⟩ :=
    exists_hornHalfRange_of_mem_component_not_mem_core P hc (hcomp y₀ hy₀) (hcore y₀ hy₀)
  refine ⟨e₀, fun y hy => ?_⟩
  by_contra hye
  obtain ⟨e₁, he₁⟩ :=
    exists_hornHalfRange_of_mem_component_not_mem_core P hc (hcomp y hy) (hcore y hy)
  have hne₁ : e₁ ≠ e₀ := fun h => hye (h ▸ he₁)
  have hu : IsClosed (hornHalfRange P c e₀) := by
    simpa only [hornHalfRange] using (P.horn_proper c e₀).isClosed_range
  have hv : IsClosed (⋃ e : {e : P.hornIndex c // e ≠ e₀}, hornHalfRange P c e.1) := by
    have hfin : ({e : P.hornIndex c | e ≠ e₀} : Set (P.hornIndex c)).Finite :=
      (Set.finite_univ_iff.mpr (P.hornIndex_finite c)).subset (Set.subset_univ _)
    rw [Set.iUnion_subtype]
    exact hfin.isClosed_biUnion fun e _ => by
      simpa only [hornHalfRange] using (P.horn_proper c e).isClosed_range
  have hsub : S ⊆ hornHalfRange P c e₀ ∪
      ⋃ e : {e : P.hornIndex c // e ≠ e₀}, hornHalfRange P c e.1 := by
    intro z hz
    by_cases hzu : z ∈ hornHalfRange P c e₀
    · exact Or.inl hzu
    · obtain ⟨e, he⟩ :=
        exists_hornHalfRange_of_mem_component_not_mem_core P hc (hcomp z hz) (hcore z hz)
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨e, fun h => hzu (h ▸ he)⟩, he⟩)
  have huinter : hornHalfRange P c e₀ ∩
      (⋃ e : {e : P.hornIndex c // e ≠ e₀}, hornHalfRange P c e.1) = ∅ := by
    refine Set.disjoint_iff_inter_eq_empty.mp (Set.disjoint_left.mpr fun z hzu hzv => ?_)
    obtain ⟨⟨e, hene⟩, hez⟩ := Set.mem_iUnion.mp hzv
    exact Set.disjoint_left.mp (P.horn_range_disjoint c e e₀ hene) hez hzu
  have hinter : S ∩ (hornHalfRange P c e₀ ∩
      (⋃ e : {e : P.hornIndex c // e ≠ e₀}, hornHalfRange P c e.1)) = ∅ := by
    simp [huinter]
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS _ _ hu hv hsub hinter with h | h
  · exact hye (h hy)
  · obtain ⟨⟨e₂, hene₂⟩, he₂⟩ := Set.mem_iUnion.mp (h hy₀)
    exact (Set.disjoint_left.mp (P.horn_range_disjoint c e₂ e₀ hene₂) he₂) he₀

end TerminalCorePresentation

namespace GeometricCutoffRecord

theorem exists_hornHalfRange_superset_neckChartTail {G : GeometricCutoffRecord H i parameters}
    {ε Λ : ℝ} {P : TerminalCorePresentation (OneStepIncoming.ofRecord G) ε Λ}
    (α : (H.event i).transition.trace.tubes.Index) (hpc : IsPreconnected (neckChartTail G α))
    (hne : (neckChartTail G α).Nonempty)
    (hcomp : ∃ c ∈ P.component,
      ∀ y ∈ neckChartTail G α, ConnectedComponents.mk y = c)
    (hcore : ∀ y ∈ neckChartTail G α, ∀ c ∈ P.component,
      ConnectedComponents.mk y = c → y ∉ P.core c) :
    ∃ c : ConnectedComponents ↥(H.event i).incoming.terminalRegularOpen,
      ∃ e : P.hornIndex c,
        neckChartTail G α ⊆ TerminalCorePresentation.hornHalfRange P c e := by
  obtain ⟨c, hc, hmk⟩ := hcomp
  exact ⟨c, TerminalCorePresentation.exists_hornHalfRange_superset_of_isPreconnected P hc hpc hne
    hmk fun y hy => hcore y hy c hc (hmk y hy)⟩

theorem chartTail_disjoint_central_of_mk_ne {G : GeometricCutoffRecord H i parameters}
    {ε Λ : ℝ} {P : TerminalCorePresentation (OneStepIncoming.ofRecord G) ε Λ}
    {α β : (H.event i).transition.trace.tubes.Index}
    {c : ConnectedComponents ↥(H.event i).incoming.terminalRegularOpen}
    {e : P.hornIndex c} (hsub : neckChartTail G α ⊆ TerminalCorePresentation.hornHalfRange P c e)
    (hne : ∀ y ∈ neckChartCentral G β, ConnectedComponents.mk y ≠ c) :
    Disjoint (neckChartTail G α) (neckChartCentral G β) := by
  refine Set.disjoint_left.mpr fun y hy hy' => hne y hy' ?_
  exact TerminalCorePresentation.hornHalfRange_mk_eq P c e (hsub hy)

theorem exists_hornHalfRange_superset_neckChartSide {G : GeometricCutoffRecord H i parameters}
    {ε Λ : ℝ} {P : TerminalCorePresentation (OneStepIncoming.ofRecord G) ε Λ}
    (α : (H.event i).transition.trace.tubes.Index) (s : Bool)
    (hcomp : ∃ c ∈ P.component,
      ∀ y ∈ neckChartSide G α s, ConnectedComponents.mk y = c)
    (hcore : ∀ y ∈ neckChartSide G α s, ∀ c ∈ P.component,
      ConnectedComponents.mk y = c → y ∉ P.core c) :
    ∃ c : ConnectedComponents ↥(H.event i).incoming.terminalRegularOpen,
      ∃ e : P.hornIndex c, neckChartSide G α s ⊆
        TerminalCorePresentation.hornHalfRange P c e := by
  obtain ⟨c, hc, hmk⟩ := hcomp
  exact ⟨c, TerminalCorePresentation.exists_hornHalfRange_superset_of_isPreconnected P hc
    (isPreconnected_neckChartSide G α s) (neckChartSide_nonempty G α s) hmk
    fun y hy => hcore y hy c hc (hmk y hy)⟩

theorem buffer_disjoint_of_injective_indexHorn {G : GeometricCutoffRecord H i parameters}
    {ε Λ : ℝ} {P : TerminalCorePresentation (OneStepIncoming.ofRecord G) ε Λ}
    (f : (H.event i).transition.trace.tubes.Index →
      (c : ConnectedComponents ↥(H.event i).incoming.terminalRegularOpen) × P.hornIndex c)
    (hf : Injective f)
    (hsub : ∀ α, neckChartTail G α ⊆
      TerminalCorePresentation.hornHalfRange P (f α).1 (f α).2)
    (hdis : ∀ α β, α ≠ β → Disjoint (neckChartTail G α) (neckChartCentral G β)) :
    Pairwise fun α β => Disjoint (Set.range (G.neck α).chart) (Set.range (G.neck β).chart) := by
  refine (buffer_disjoint_iff_neckChartTail_disjoint G).mpr fun α β hab => ?_
  rw [neckChart_eq_central_union_tail G β]
  refine disjoint_union_right.mpr ⟨hdis α β hab, ?_⟩
  exact (TerminalCorePresentation.hornHalfRange_pairwise_disjoint P (fun h => hab (hf h))).mono
    (hsub α) (hsub β)

theorem exists_injective_indexHorn_of_isEmpty {G : GeometricCutoffRecord H i parameters}
    {ε Λ : ℝ} {P : TerminalCorePresentation (OneStepIncoming.ofRecord G) ε Λ}
    [IsEmpty (H.event i).transition.trace.tubes.Index] :
    ∃ f : (H.event i).transition.trace.tubes.Index →
        (c : ConnectedComponents ↥(H.event i).incoming.terminalRegularOpen) × P.hornIndex c,
      Injective f ∧
        (∀ α, neckChartTail G α ⊆
          TerminalCorePresentation.hornHalfRange P (f α).1 (f α).2) ∧
        (∀ α β, α ≠ β → Disjoint (neckChartTail G α) (neckChartCentral G β)) :=
  ⟨fun α => isEmptyElim α, fun a => isEmptyElim a, fun α => isEmptyElim α,
    fun α => isEmptyElim α⟩

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
