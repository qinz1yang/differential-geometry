import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornReparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCutRetention
import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornComponents
import DifferentialGeometry.Topology.Order.IntermediateValue

import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornBaseCoordinates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckEssentiality
import DifferentialGeometry.Topology.SphereSeparation.PositiveProductBand

set_option autoImplicit false

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem exists_horn_first_scalar_level
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {Q : ℝ} (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q) :
    ∃ t : ℝ, 0 < t ∧ ∃ y : Sphere 2,
      metricScalarAt D.terminal.metric (P.horn c e (y, t)) = Q ∧
      (∀ s ∈ Ico 0 t, ∀ z : Sphere 2,
        metricScalarAt D.terminal.metric (P.horn c e (z, s)) < Q) ∧
      ∀ z : Sphere 2, metricScalarAt D.terminal.metric (P.horn c e (z, t)) ≤ Q := by
  obtain ⟨r, hr⟩ := P.horn_scalar_diverges c e Q
  let T := max r 1
  have hT : 0 ≤ T := zero_le_one.trans (le_max_right _ _)
  have hcont : ContinuousOn
      (fun p : ℝ × Sphere 2 => metricScalarAt D.terminal.metric (P.horn c e (p.2, p.1)))
      (Icc 0 T ×ˢ univ) := by
    apply (metricScalar_smooth D.terminal.metric).continuous.comp_continuousOn
    exact (P.horn_smooth c e).continuousOn.comp continuous_swap.continuousOn
      (fun p hp => ⟨mem_univ _, hp.1.1⟩)
  have hstart : ∀ y : Sphere 2, metricScalarAt D.terminal.metric (P.horn c e (y, 0)) < Q :=
    fun y => (P.horn_base_scalar c e y).trans_lt hQ
  have hend : ∃ y : Sphere 2, Q ≤ metricScalarAt D.terminal.metric (P.horn c e (y, T)) :=
    ⟨DifferentialGeometry.Geometry.Neck.spherePoint,
      (hr DifferentialGeometry.Geometry.Neck.spherePoint T (le_max_left _ _)).le⟩
  obtain ⟨t, ht, y, heq, hbefore, hlevel⟩ :=
    hcont.exists_first_level_of_compact hT hstart hend
  exact ⟨t, ht.1, y, heq, hbefore, hlevel⟩

theorem exists_neck_at_horn_first_scalar_level
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    {Q : ℝ} (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q) :
    ∃ t : ℝ, 0 < t ∧ ∃ y : Sphere 2, ∃ δ : ℝ, ∃ k : ℕ,
      ∃ N : NormalizedNeck D.terminal.metric δ k,
        N.center = P.horn c e (y, t) ∧ N.scale = Q ∧
        δ ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k ∧
        (∀ s ∈ Ico 0 t, ∀ z : Sphere 2,
          metricScalarAt D.terminal.metric (P.horn c e (z, s)) < Q) ∧
        ∀ z : Sphere 2, metricScalarAt D.terminal.metric (P.horn c e (z, t)) ≤ Q := by
  obtain ⟨t, ht, y, heq, hbefore, hlevel⟩ := P.exists_horn_first_scalar_level c e hQ
  have hsub : P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) ⊆
      range (fun p : HalfNeckCylinder => P.horn c e p.val) := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp.2.le⟩, rfl⟩
  have hin : P.horn c e (y, t) ∈
      interior (range (fun p : HalfNeckCylinder => P.horn c e p.val)) :=
    interior_maximal hsub (P.isOpen_positive_horn c e) ⟨(y, t), ⟨mem_univ _, ht⟩, rfl⟩
  obtain ⟨δ, k, N, hcenter, hδ, hk⟩ := P.horn_spatial_neck c e _ hin
  refine ⟨t, ht, y, δ, k, N, hcenter, ?_, hδ, hk, hbefore, hlevel⟩
  rw [N.scale_scalar, hcenter, heq]

theorem exists_neck_family_at_first_scalar_level
    {Q : ℝ} (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q) :
    ∃ (t : ∀ c, P.hornIndex c → ℝ) (y : ∀ c, P.hornIndex c → Sphere 2)
      (δ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
      (N : ∀ c e, NormalizedNeck D.terminal.metric (δ c e) (k c e)),
      ∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y c e, t c e) ∧
        (N c e).scale = Q ∧ δ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e ∧
        (∀ s ∈ Ico 0 (t c e), ∀ z : Sphere 2,
          metricScalarAt D.terminal.metric (P.horn c e (z, s)) < Q) ∧
        ∀ z : Sphere 2, metricScalarAt D.terminal.metric (P.horn c e (z, t c e)) ≤ Q := by
  classical
  choose t ht y δ k N hcenter hscale hδ hk hbefore hlevel using
    fun c e => P.exists_neck_at_horn_first_scalar_level c e hQ
  exact ⟨t, y, δ, k, N, fun c e =>
    ⟨ht c e, hcenter c e, hscale c e, hδ c e, hk c e, hbefore c e, hlevel c e⟩⟩

theorem exists_neck_family_with_truncated_scalar_bound_of_core_bound
    {Q : ℝ} (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q)
    (hcore : ∀ c ∈ P.component, ∀ x ∈ P.core c, metricScalarAt D.terminal.metric x ≤ Q) :
    ∃ (t : ∀ c, P.hornIndex c → ℝ) (y : ∀ c, P.hornIndex c → Sphere 2)
      (δ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
      (N : ∀ c e, NormalizedNeck D.terminal.metric (δ c e) (k c e)),
      (∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y c e, t c e) ∧
        (N c e).scale = Q ∧ δ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e ∧
        (∀ s ∈ Ico 0 (t c e), ∀ z : Sphere 2,
          metricScalarAt D.terminal.metric (P.horn c e (z, s)) < Q) ∧
        ∀ z : Sphere 2, metricScalarAt D.terminal.metric (P.horn c e (z, t c e)) ≤ Q) ∧
      ∀ x ∈ P.truncatedRegion t, metricScalarAt D.terminal.metric x ≤ Q := by
  obtain ⟨t, y, δ, k, N, hN⟩ := P.exists_neck_family_at_first_scalar_level hQ
  refine ⟨t, y, δ, k, N, hN, ?_⟩
  intro x hx
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
  rcases hxc with hxc | hxc
  · exact hcore c hc x hxc
  · obtain ⟨e, p, hp, hpx⟩ := mem_iUnion.mp hxc
    have hbound : metricScalarAt D.terminal.metric (P.horn c e p) ≤ Q := by
      rcases hp.2.2.eq_or_lt with heq | hlt
      · exact (congrArg (fun u => metricScalarAt D.terminal.metric (P.horn c e (p.1, u)))
          heq).trans_le ((hN c e).2.2.2.2.2.2 p.1)
      · exact ((hN c e).2.2.2.2.2.1 p.2 ⟨hp.2.1, hlt⟩ p.1).le
    exact hpx ▸ hbound

private theorem scalar_le_on_retainedCore_of_truncated_bound
    {Q : ℝ} (t : ∀ c, P.hornIndex c → ℝ) (ht : ∀ c e, 0 < t c e)
    (hbound : ∀ x ∈ P.truncatedRegion t, metricScalarAt D.terminal.metric x ≤ Q)
    {ι : Type*} {δ : ι → ℝ} (f : ∀ i, bufferedCylinder (δ i) → D.stage.Carrier)
    (hcut : ∀ c ∈ P.component, ∀ e : P.hornIndex c, ∀ y : Sphere 2,
      (P.horn c e (y, t c e)).val ∈ ⋃ i, removedSlab (f i))
    (x : cutCore f)
    (hx : x ∈ retainedCore f (scalarSublevelComponents D.slab.terminalRegularOpen
      D.terminal.metric f (P.coreRadius ^ 2)⁻¹)) :
    ∃ p : D.slab.terminalRegularOpen, p.val = x.val ∧
      p ∈ P.truncatedRegion t ∧ metricScalarAt D.terminal.metric p ≤ Q := by
  let T := (Subtype.val : D.slab.terminalRegularOpen → D.stage.Carrier) '' P.truncatedRegion t
  have hfront : frontier T ⊆ ⋃ i, removedSlab (f i) := by
    intro z hz
    obtain ⟨c, hc, e, y, heq⟩ := by
      simpa only [mem_iUnion, mem_range] using P.ambient_truncatedRegion_frontier_subset_slices t ht hz
    exact heq ▸ hcut c hc e y
  have hsub := scalarSublevelComponents_retained_subset_of_frontier_removed
    D.slab.terminalRegularOpen D.terminal.metric f (P.coreRadius ^ 2)⁻¹ T
    (fun p hp => ⟨p, P.low_subset_truncatedRegion t hp, rfl⟩) hfront
  obtain ⟨p, hp, hpx⟩ := interior_subset (hsub ⟨x, hx, rfl⟩)
  exact ⟨p, hpx, hp, hbound p hp⟩

theorem exists_neck_family_with_retained_scalar_bound_of_core_bound
    {Q : ℝ} (hQ : Λ * (P.coreRadius ^ 2)⁻¹ < Q)
    (hcore : ∀ c ∈ P.component, ∀ x ∈ P.core c, metricScalarAt D.terminal.metric x ≤ Q) :
    ∃ (t : ∀ c, P.hornIndex c → ℝ) (y : ∀ c, P.hornIndex c → Sphere 2)
      (δ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
      (N : ∀ c e, NormalizedNeck D.terminal.metric (δ c e) (k c e)),
      (∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y c e, t c e) ∧
        (N c e).scale = Q ∧ δ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e ∧
        (∀ s ∈ Ico 0 (t c e), ∀ z : Sphere 2,
          metricScalarAt D.terminal.metric (P.horn c e (z, s)) < Q) ∧
        ∀ z : Sphere 2, metricScalarAt D.terminal.metric (P.horn c e (z, t c e)) ≤ Q) ∧
      ∀ (d : P.HornCutIndex → ℝ), (∀ j, 0 < d j) →
        ∀ x : cutCore (P.hornCutMap d t),
          x ∈ retainedCore (P.hornCutMap d t)
            (scalarSublevelComponents D.slab.terminalRegularOpen D.terminal.metric
              (P.hornCutMap d t) (P.coreRadius ^ 2)⁻¹) →
          ∃ p : D.slab.terminalRegularOpen, p.val = x.val ∧
            p ∈ P.truncatedRegion t ∧ metricScalarAt D.terminal.metric p ≤ Q := by
  obtain ⟨t, y, δ, k, N, hN, hbound⟩ :=
    P.exists_neck_family_with_truncated_scalar_bound_of_core_bound hQ hcore
  refine ⟨t, y, δ, k, N, hN, ?_⟩
  intro d hd x hx
  exact P.scalar_le_on_retainedCore_of_truncated_bound t (fun c e => (hN c e).1)
    hbound (P.hornCutMap d t) (P.hornCutMap_slices_removed d hd t) x hx


theorem exists_neck_family_with_truncated_scalar_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ Q : ℝ, max K (Λ * (P.coreRadius ^ 2)⁻¹) < Q →
      ∃ (t : ∀ c, P.hornIndex c → ℝ) (y : ∀ c, P.hornIndex c → Sphere 2)
        (δ : ∀ c, P.hornIndex c → ℝ) (k : ∀ c, P.hornIndex c → ℕ)
        (N : ∀ c e, NormalizedNeck D.terminal.metric (δ c e) (k c e)),
        (∀ c e, 0 < t c e ∧ (N c e).center = P.horn c e (y c e, t c e) ∧
          (N c e).scale = Q ∧ δ c e ≤ ε ∧ ⌊ε⁻¹⌋₊ + 1 ≤ k c e) ∧
        ∀ x ∈ P.truncatedRegion t, metricScalarAt D.terminal.metric x ≤ Q := by
  have hcore : IsCompact (⋃ c ∈ P.component, P.core c) :=
    P.component_finite.isCompact_biUnion (fun c hc => P.core_isCompact c hc)
  obtain ⟨K₀, hK₀⟩ := (hcore.image (metricScalar_smooth D.terminal.metric).continuous).bddAbove
  let K := max K₀ 1
  refine ⟨K, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro Q hQ
  obtain ⟨t, y, δ, k, N, hN, hbound⟩ :=
    P.exists_neck_family_with_truncated_scalar_bound_of_core_bound
      ((le_max_right _ _).trans_lt hQ) (by
        intro c hc x hx
        have hb : metricScalarAt D.terminal.metric x ≤ K₀ :=
          hK₀ ⟨x, mem_iUnion₂.mpr ⟨c, hc, hx⟩, rfl⟩
        exact (hb.trans (le_max_left _ _)).trans ((le_max_left _ _).trans hQ.le))
  exact ⟨t, y, δ, k, N, fun c e =>
    ⟨(hN c e).1, (hN c e).2.1, (hN c e).2.2.1, (hN c e).2.2.2.1,
      (hN c e).2.2.2.2.1⟩, hbound⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

noncomputable section

open Manifold
open DifferentialGeometry.Topology.SphereSeparation

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u


private local instance : ConnectedSpace (Sphere 2) :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M}

private theorem normalized_neck_scalar_bounds
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2)
    (z : neckBuffer δ) (hz : z ∈ neckClosedTest δ) :
    (1 - 4323 * δ) * N.scale ≤ metricScalarAt g (N.chart z) ∧
      metricScalarAt g (N.chart z) ≤ (1 + 4323 * δ) * N.scale := by
  obtain ⟨hl, hu⟩ := abs_le.mp (N.abs_scalar_ratio_sub_one_le hk hδ z hz)
  constructor
  · exact (le_div_iff₀ N.scale_pos).mp (by linarith)
  · exact (div_le_iff₀ N.scale_pos).mp (by linarith)

private theorem normalized_neck_scalar_bounds_of_small
    {δ : ℝ} {k : ℕ} (N : NormalizedNeck g δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 8646)
    (z : neckBuffer δ) (hz : z ∈ neckClosedTest δ) :
    N.scale / 2 ≤ metricScalarAt g (N.chart z) ∧
      metricScalarAt g (N.chart z) ≤ 3 * N.scale / 2 := by
  obtain ⟨hl, hu⟩ := normalized_neck_scalar_bounds N hk (by linarith) z hz
  have hb := mul_le_mul_of_nonneg_right hδ N.scale_pos.le
  constructor <;> nlinarith

end

theorem exists_horn_first_scalar_level_inner_scalar_bound_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
          {Q : ℝ}, 2 * (Λ * (P.coreRadius ^ 2)⁻¹) < Q →
          ∃ (t : ℝ), 0 < t ∧ ∃ (y : Sphere 2) (δ : ℝ) (k : ℕ)
            (N : NormalizedNeck D.terminal.metric δ k),
            N.center = P.horn c e (y,t) ∧ N.scale = Q ∧ δ ≤ ε ∧
            ⌊ε⁻¹⌋₊ + 1 ≤ k ∧
            (∀ s ∈ Ico 0 t, ∀ z : Sphere 2,
              metricScalarAt D.terminal.metric (P.horn c e (z,s)) < Q) ∧
            (∀ s ∈ Icc 0 t, ∀ z : Sphere 2,
              metricScalarAt D.terminal.metric (P.horn c e (z,s)) ≤ Q) ∧
            ∃ Θ : neckCentralOpen δ → positiveHornDomain,
              IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
              (∀ z, P.horn c e (Θ z).val =
                N.chart (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ) z)) ∧
              ∃ (p : ComplementPair (range (fun q : Sphere 2 => Θ ⟨(q,0),mem_univ _,
                    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)))
                (R : ℝ), 0 < R ∧
                (closure p.left = p.left ∪ range (fun q : Sphere 2 => Θ ⟨(q,0),mem_univ _,
                    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
                (closure p.right = p.right ∪ range (fun q : Sphere 2 => Θ ⟨(q,0),mem_univ _,
                    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)) ∧
                IsCompact (closure ((Subtype.val : positiveHornDomain → NeckCylinder) '' p.left)) ∧
                (∀ q : positiveHornDomain, q.val.2 < Real.exp (-R) → q ∈ p.left) ∧
                (∀ q : positiveHornDomain, Real.exp R < q.val.2 → q ∈ p.right) ∧
                ∀ x ∈ closure p.left,
                  metricScalarAt D.terminal.metric (P.horn c e x.val) ≤ 3 * Q := by
  obtain ⟨eta,heta,hseparate⟩ := exists_horn_neck_end_separation_tolerance
  refine ⟨min eta (1 / 8646),lt_min heta (by norm_num),?_⟩
  intro D ε Λ P hε c e Q hQ
  have hεsmall : ε ≤ 1 / 8646 := hε.trans (min_le_right _ _)
  have hεeta : ε ≤ eta := hε.trans (min_le_left _ _)
  have hbase : 0 < Λ * (P.coreRadius ^ 2)⁻¹ :=
    mul_pos (zero_lt_one.trans_le P.Lambda_ge_one) (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos))
  have hQpos : 0 < Q := by linarith
  have hε1 : 1 ≤ ε⁻¹ := ((one_lt_inv₀ P.epsilon_pos).mpr (by linarith : ε < 1)).le
  have hfloor : 1 ≤ ⌊ε⁻¹⌋₊ := Nat.le_floor (by exact_mod_cast hε1)
  obtain ⟨t,ht,y,δ,k,N,hcenter,hscale,hδ,hk,hbefore,hlevel⟩ :=
    P.exists_neck_at_horn_first_scalar_level c e (Q := Q) (by linarith)
  have hk2 : 2 ≤ k := by omega
  have hδsmall : δ ≤ 1 / 8646 := hδ.trans hεsmall
  have hNscale : Λ * (P.coreRadius ^ 2)⁻¹ < (1 - 4323 * δ) * N.scale := by
    rw [hscale]
    nlinarith [mul_le_mul_of_nonneg_right hδsmall hQpos.le]
  have hNpos : N.center ∈ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) := by
    rw [hcenter]
    exact ⟨(y,t),⟨mem_univ _,ht⟩,rfl⟩
  obtain ⟨Θ,hΘ,hmap⟩ := P.exists_neck_coordinates_in_horn_of_base_scalar_bound c e N
    hk2 (by linarith) hNpos hNscale
  obtain ⟨p,R,hR,hfrontl,hfrontr,hcll,hclr,hfullcompact,hcompact,hlo,hhi,hband⟩ :=
    hseparate P hεeta c e N hδ ((Nat.ceil_le_floor_add_one ε⁻¹).trans hk) Θ hΘ hmap
  have hprefix : ∀ s ∈ Icc 0 t, ∀ z : Sphere 2,
      metricScalarAt D.terminal.metric (P.horn c e (z,s)) ≤ Q := by
    intro s hs z
    rcases hs.2.eq_or_lt with rfl | hlt
    · exact hlevel z
    · exact (hbefore s ⟨hs.1,hlt⟩ z).le
  let S := range (fun q : Sphere 2 => Θ ⟨(q,0),mem_univ _,
    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)
  have hSbound : ∀ x ∈ S, metricScalarAt D.terminal.metric (P.horn c e x.val) ≤ 3 * Q / 2 := by
    rintro x ⟨z,rfl⟩
    rw [hmap]
    have hb := (normalized_neck_scalar_bounds_of_small N hk2 hδsmall
      (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ)
        ⟨(z,0),mem_univ _,neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩)
      (by change -δ⁻¹ ≤ 0 ∧ 0 ≤ δ⁻¹; constructor <;> linarith [inv_pos.mpr N.delta_pos])).2
    simpa only [hscale] using hb
  refine ⟨t,ht,y,δ,k,N,hcenter,hscale,hδ,hk,hbefore,hprefix,Θ,hΘ,hmap,
    p,R,hR,hcll,hclr,hfullcompact,hlo,hhi,?_⟩
  intro x hx
  rw [hcll] at hx
  rcases hx with hx | hx
  · by_contra hnot
    have hxhigh : 3 * Q < metricScalarAt D.terminal.metric (P.horn c e x.val) := lt_of_not_ge hnot
    have hxpos : P.horn c e x.val ∈ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) :=
      ⟨x.val,x.property,rfl⟩
    have hxin : P.horn c e x.val ∈ interior (range (fun q : HalfNeckCylinder => P.horn c e q.val)) := by
      apply (P.isOpen_positive_horn c e).subset_interior_iff.mpr ?_ hxpos
      rintro z ⟨q,hq,rfl⟩
      exact ⟨⟨q,hq.2.le⟩,rfl⟩
    obtain ⟨δx,kx,Nx,hNxcenter,hδx,hkx⟩ := P.horn_spatial_neck c e _ hxin
    have hNxscale : Nx.scale = metricScalarAt D.terminal.metric (P.horn c e x.val) := by
      rw [Nx.scale_scalar,hNxcenter]
    have hkx2 : 2 ≤ kx := by omega
    have hδxsmall : δx ≤ 1 / 8646 := hδx.trans hεsmall
    have hNxscalegap : Λ * (P.coreRadius ^ 2)⁻¹ < (1 - 4323 * δx) * Nx.scale := by
      have hb := mul_le_mul_of_nonneg_right hδxsmall Nx.scale_pos.le
      rw [hNxscale] at *
      nlinarith
    obtain ⟨Θx,hΘx,hmapx⟩ := P.exists_neck_coordinates_in_horn_of_base_scalar_bound c e Nx
      hkx2 (by linarith) (hNxcenter.symm ▸ hxpos) hNxscalegap
    obtain ⟨px,Rx,hRx,hxfrontl,hxfrontr,hxcll,hxclr,hxfullcompact,hxcompact,hxlo,hxhi,hxband⟩ :=
      hseparate P hεeta c e Nx hδx ((Nat.ceil_le_floor_add_one ε⁻¹).trans hkx) Θx hΘx hmapx
    let T := range (fun q : Sphere 2 => Θx ⟨(q,0),mem_univ _,
      neg_lt_zero.mpr (inv_pos.mpr Nx.delta_pos),inv_pos.mpr Nx.delta_pos⟩)
    have hTbound : ∀ z ∈ T, 3 * Q / 2 < metricScalarAt D.terminal.metric (P.horn c e z.val) := by
      rintro z ⟨w,rfl⟩
      rw [hmapx]
      have hb := (normalized_neck_scalar_bounds_of_small Nx hkx2 hδxsmall
        (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δx)
          ⟨(w,0),mem_univ _,neg_lt_zero.mpr (inv_pos.mpr Nx.delta_pos),inv_pos.mpr Nx.delta_pos⟩)
        (by change -δx⁻¹ ≤ 0 ∧ 0 ≤ δx⁻¹; constructor <;> linarith [inv_pos.mpr Nx.delta_pos])).1
      rw [hNxscale] at hb
      linarith
    have hTx : x ∈ T := by
      refine ⟨Nx.sphereMark,?_⟩
      apply (P.horn_interior_embedding c e).isEmbedding.injective
      exact (hmapx _).trans (Nx.marked.trans hNxcenter)
    have hTconn : IsPreconnected T :=
      (isConnected_range (hΘx.contMDiff.continuous.comp
        ((continuous_id.prodMk continuous_const).subtype_mk _))).isPreconnected
    have hTS : T ⊆ Sᶜ := by
      intro z hz hzS
      exact (not_lt_of_ge (hSbound z hzS)) (hTbound z hz)
    have hTleft : T ⊆ p.left := by
      rcases p.subset_left_or_subset_right hTconn hTS with h | h
      · exact h
      · exact False.elim (p.disjoint.le_bot ⟨hx,h hTx⟩)
    have hrightmeet : (p.right ∩ px.right).Nonempty := by
      let r := max (Real.exp R) (Real.exp Rx) + 1
      have hr : 0 < r := by dsimp [r]; positivity
      refine ⟨⟨(y,r),mem_univ _,hr⟩,hhi _ ?_,hxhi _ ?_⟩
      · dsimp only [r]; linarith [le_max_left (Real.exp R) (Real.exp Rx)]
      · dsimp only [r]; linarith [le_max_right (Real.exp R) (Real.exp Rx)]
    have hSright : S ⊆ px.right :=
      p.sphere_subset_right_of_sphere_subset_left px
        (by rw [hclr]; exact subset_union_right) hTleft hrightmeet
    have hTafter : ∀ z ∈ T, t < z.val.2 := by
      intro z hz
      by_contra hn
      have hb := hprefix z.val.2 ⟨z.property.2.le,le_of_not_gt hn⟩ z.val.1
      have hb' := hTbound z hz
      linarith
    have hprefixleft := px.lower_band_subset_left_of_separator_above
      (Real.exp_pos (-Rx)) hxlo hTafter
    have hyS : (⟨(y,t),mem_univ _,ht⟩ : positiveHornDomain) ∈ S := by
      refine ⟨N.sphereMark,?_⟩
      apply (P.horn_interior_embedding c e).isEmbedding.injective
      exact (hmap _).trans (N.marked.trans hcenter)
    exact px.disjoint.le_bot ⟨hprefixleft _ le_rfl,hSright hyS⟩
  · have hb := hSbound x hx
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end


noncomputable section
open Manifold
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.SphereSeparation

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u
variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

private theorem reparametrized_prefix_scalar_le
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
    {r b a Q : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hfix : ∀ q : NeckCylinder, q.2 ≤ r → F q = q)
    {S : Set positiveHornDomain} (p : ComplementPair S)
    (hlow : ∀ q : positiveHornDomain, q.val.2 < b → q ∈ p.left)
    (hslice : ∀ x ∈ S, ∃ z : Sphere 2, F (z,a) = x.val)
    (hbound : ∀ x ∈ closure p.left, metricScalarAt D.terminal.metric (P.horn c e x.val) ≤ Q) :
    ∀ z : Sphere 2, ∀ t ∈ Ioc (0 : ℝ) a,
      metricScalarAt D.terminal.metric (P.horn c e (F (z,t))) ≤ Q := by
  have hfix0 : ∀ q : NeckCylinder, q.2 ≤ 0 → F q = q :=
    fun q hq => hfix q (hq.trans hr.le)
  let f := (positiveCylinderDiffeomorph F hfix0).toHomeomorph
  have hfix' : ∀ q : positiveHornDomain, q.val.2 ≤ r → f q = q := by
    intro q hq
    apply Subtype.ext
    exact hfix q.val hq
  have hsep : S ⊆ f '' {q | q.val.2 = a} := by
    intro x hx
    obtain ⟨z, hz⟩ := hslice x hx
    have ha : 0 < a := by
      have hp : 0 < (F (z,a)).2 := by rw [hz]; exact x.property.2
      exact (halfCylinder_image_pos_iff F hfix0 (z,a)).mp hp
    refine ⟨⟨(z,a),mem_univ _,ha⟩,rfl,?_⟩
    apply Subtype.ext
    exact hz
  intro z t ht
  have hm := p.image_lower_band_subset_closure_left f f.continuous f.injective hr hb
    hfix' hlow hsep ⟨(z,t),mem_univ _,ht.1⟩ ht.2
  exact hbound (f ⟨(z,t),mem_univ _,ht.1⟩) hm


theorem exists_horn_first_scalar_level_reparametrized_scalar_bound_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ),
        ε ≤ eta → ∀ (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
          {Q : ℝ}, 2 * (Λ * (P.coreRadius ^ 2)⁻¹) < Q →
          ∃ t : ℝ, 0 < t ∧ ∃ (y : Sphere 2) (δ : ℝ) (k : ℕ)
            (N : NormalizedNeck D.terminal.metric δ k),
            N.center = P.horn c e (y,t) ∧ N.scale = Q ∧ δ ≤ ε ∧
            ⌊ε⁻¹⌋₊ + 1 ≤ k ∧
            (∀ s ∈ Ico 0 t, ∀ z : Sphere 2,
              metricScalarAt D.terminal.metric (P.horn c e (z,s)) < Q) ∧
            ∀ (F : NeckCylinder ≃ₘ⟮NeckCylinderModel, NeckCylinderModel⟯ NeckCylinder)
              (a r : ℝ), 0 < r →
              (∀ q : NeckCylinder, q.2 ≤ r → F q = q) →
              (∀ w : Sphere 2, ∃ z : Sphere 2,
                P.horn c e (F (z,a)) = N.chart ⟨(w,0),by
                  have hp := inv_pos.mpr N.delta_pos
                  constructor <;> linarith⟩) →
              ∀ z : Sphere 2, ∀ s ∈ Icc (0 : ℝ) a,
                metricScalarAt D.terminal.metric (P.horn c e (F (z,s))) ≤ 3 * Q := by
  obtain ⟨eta, heta, hinner⟩ := exists_horn_first_scalar_level_inner_scalar_bound_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro D ε Λ P hε c e Q hQ
  obtain ⟨t, ht, y, δ, k, N, hcenter, hscale, hδ, hk, hbefore, hprefix,
    Θ, hΘ, hmap, p, R, hR, hcl, hcr, hcompact, hlo, hhi, hbound⟩ :=
    hinner P hε c e hQ
  refine ⟨t, ht, y, δ, k, N, hcenter, hscale, hδ, hk, hbefore, ?_⟩
  intro F a r hr hfix hmatch z s hs
  have hfix0 : ∀ q : NeckCylinder, q.2 ≤ 0 → F q = q :=
    fun q hq => hfix q (hq.trans hr.le)
  have hbase : 0 < Λ * (P.coreRadius ^ 2)⁻¹ :=
    mul_pos (zero_lt_one.trans_le P.Lambda_ge_one) (inv_pos.mpr (sq_pos_of_pos P.coreRadius_pos))
  have hQpos : 0 < Q := by linarith
  by_cases hs0 : s = 0
  · subst s
    rw [hfix (z,0) hr.le]
    have hb := P.horn_base_scalar c e z
    linarith
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    apply P.reparametrized_prefix_scalar_le c e F hr (Real.exp_pos (-R)) hfix p hlo ?_ hbound z s ⟨hspos,hs.2⟩
    rintro x ⟨w, rfl⟩
    obtain ⟨z, hz⟩ := hmatch w
    refine ⟨z, ?_⟩
    have hFa : 0 < (F (z,a)).2 := by
      by_contra hn
      have hfixa := hfix0 (F (z,a)) (le_of_not_gt hn)
      have hza : F (z,a) = (z,a) := F.injective hfixa
      have hale : a ≤ 0 := by rw [hza] at hn; exact le_of_not_gt hn
      have hslt := hspos.trans_le hs.2
      linarith
    let qw : neckCentralOpen δ := ⟨(w,0),mem_univ _,
      neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),inv_pos.mpr N.delta_pos⟩
    have hTheta : 0 < (Θ qw).val.2 := (Θ qw).property.2
    exact P.horn_injOn c e
      (show F (z,a) ∈ univ ×ˢ Ici (0 : ℝ) from ⟨mem_univ _,hFa.le⟩)
      (show (Θ qw).val ∈ univ ×ˢ Ici (0 : ℝ) from ⟨mem_univ _,hTheta.le⟩)
      (hz.trans (hmap qw).symm)


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
