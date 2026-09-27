import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChartTailHornBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.TerminalCoreTruncation

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : ConnectedSpace (Sphere 2) :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))

theorem isPreconnected_neckCentralDomain (δ : ℝ) : IsPreconnected (neckCentralDomain δ) := by
  apply (_root_.Topology.IsInducing.subtypeVal.isPreconnected_image).mp
  have himage : (Subtype.val : neckBuffer δ → NeckCylinder) '' neckCentralDomain δ =
      (univ : Set (Sphere 2)) ×ˢ Ioo (-δ⁻¹) δ⁻¹ := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨mem_univ _, hq⟩
    · rintro ⟨_, hp⟩
      refine ⟨⟨p, ?_⟩, hp, rfl⟩
      change -δ⁻¹ - 1 < p.2 ∧ p.2 < δ⁻¹ + 1
      constructor <;> linarith [hp.1, hp.2]
  erw [himage]
  exact isPreconnected_univ.prod isPreconnected_Ioo

namespace TerminalCorePresentation

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem exists_scalar_upper_core
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component) :
    ∃ C : ℝ, ∀ x ∈ P.core c, metricScalarAt D.terminal.metric x ≤ C := by
  obtain ⟨C, hC⟩ := (P.core_isCompact c hc).bddAbove_image
    (metricScalar_smooth D.terminal.metric).continuous.continuousOn
  exact ⟨C, fun x hx => hC (mem_image_of_mem _ hx)⟩

theorem neckCentralDomain_subset_horn_of_scalar_high
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (e : P.hornIndex c) {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck D.terminal.metric δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2)
    (hcenter : N.center ∈ hornHalfRange P c e)
    (C : ℝ) (hC : ∀ x ∈ P.core c, metricScalarAt D.terminal.metric x ≤ C)
    (hhigh : C < (1 - 4323 * δ) * N.scale) :
    N.chart '' neckCentralDomain δ ⊆ hornHalfRange P c e := by
  let z : neckBuffer δ := ⟨(N.sphereMark, 0), by
    change -δ⁻¹ - 1 < 0 ∧ 0 < δ⁻¹ + 1
    constructor <;> linarith [inv_pos.mpr N.delta_pos]⟩
  have hz : z ∈ neckCentralDomain δ := by
    change -δ⁻¹ < 0 ∧ 0 < δ⁻¹
    constructor <;> linarith [inv_pos.mpr N.delta_pos]
  have hmark : N.chart z = N.center := N.marked
  let S := N.chart '' neckCentralDomain δ
  have hS : IsPreconnected S :=
    (isPreconnected_neckCentralDomain δ).image _ N.chart.continuous.continuousOn
  have hne : S.Nonempty := ⟨N.chart z, ⟨z, hz, rfl⟩⟩
  have hcenterS : N.center ∈ S := hmark ▸ mem_image_of_mem N.chart hz
  have hcenterc : ConnectedComponents.mk N.center = c := by
    have hmem : N.center ∈ P.core c ∪ ⋃ e, hornHalfRange P c e :=
      Or.inr (mem_iUnion.mpr ⟨e, hcenter⟩)
    change N.center ∈ P.core c ∪ ⋃ e, range (fun p : HalfNeckCylinder => P.horn c e p.val) at hmem
    rw [← P.horn_covers_component c hc] at hmem
    exact hmem
  have hcomp : ∀ y ∈ S, ConnectedComponents.mk y = c := by
    intro y hy
    exact (ConnectedComponents.coe_eq_coe'.mpr
      (hS.subset_connectedComponent hcenterS hy)).trans hcenterc
  have hcore : ∀ y ∈ S, y ∉ P.core c := by
    rintro y ⟨q, hq, rfl⟩ hy
    have hratio := (abs_le.mp (N.abs_scalar_ratio_sub_one_le hk hδ q ⟨hq.1.le, hq.2.le⟩)).1
    have hlower : (1 - 4323 * δ) * N.scale ≤ metricScalarAt D.terminal.metric (N.chart q) :=
      (le_div_iff₀ N.scale_pos).mp (by linarith)
    exact (not_lt_of_ge (hlower.trans (hC _ hy))) hhigh
  obtain ⟨e', he'⟩ := P.exists_hornHalfRange_superset_of_isPreconnected hc hS hne hcomp hcore
  have heq : e' = e := P.hornHalfRange_unique (he' hcenterS) hcenter
  exact heq ▸ he'

end TerminalCorePresentation

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def positiveHornDomain : Opens NeckCylinder :=
  ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩

def neckCentralOpen (δ : ℝ) : Opens NeckCylinder :=
  ⟨univ ×ˢ Ioo (-δ⁻¹) δ⁻¹, isOpen_univ.prod isOpen_Ioo⟩

theorem neckCentralOpen_le_buffer (δ : ℝ) : neckCentralOpen δ ≤ neckBuffer δ := by
  rintro x ⟨_, hx⟩
  change -δ⁻¹ - 1 < x.2 ∧ x.2 < δ⁻¹ + 1
  constructor <;> linarith [hx.1, hx.2]

namespace TerminalCorePresentation

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

def positiveHornMap (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    positiveHornDomain → D.slab.terminalRegularOpen := fun q => P.horn c e q.val

theorem positiveHornMap_local (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (P.positiveHornMap c e) :=
  isLocalDiffeomorph_of_injective_mfderiv _ (P.horn_interior_embedding c e).contMDiff
    (fun q => injective_mfderiv_of_isImmersionAt _ _ _ q
      ((P.horn_interior_embedding c e).isImmersion.isImmersionAt q)) (by simp [ThreeSpace])

def positiveHornDiffeomorph (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    positiveHornDomain ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ (P.positiveHornMap_local c e).image :=
  diffeomorphOntoImage (P.positiveHornMap c e) (P.positiveHornMap_local c e)
    (P.horn_interior_embedding c e).isEmbedding.injective

theorem neckCentralOpen_mem_positiveHorn_image
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (e : P.hornIndex c) {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck D.terminal.metric δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2) (hcenter : N.center ∈ hornHalfRange P c e)
    (C : ℝ) (hC : ∀ x ∈ P.core c, metricScalarAt D.terminal.metric x ≤ C)
    (hhigh : C < (1 - 4323 * δ) * N.scale) (q : neckCentralOpen δ) :
    N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q) ∈ (P.positiveHornMap_local c e).image := by
  let z := Opens.inclusion (neckCentralOpen_le_buffer δ) q
  have hz : z ∈ neckCentralDomain δ := q.property.2
  have hmem := P.neckCentralDomain_subset_horn_of_scalar_high c hc e N hk hδ hcenter C hC hhigh
    (mem_image_of_mem N.chart hz)
  obtain ⟨p, hp⟩ := hmem
  have hcore : N.chart z ∉ P.core c := by
    intro hcore
    have hratio := (abs_le.mp (N.abs_scalar_ratio_sub_one_le hk hδ z ⟨hz.1.le, hz.2.le⟩)).1
    have hlower : (1 - 4323 * δ) * N.scale ≤ metricScalarAt D.terminal.metric (N.chart z) :=
      (le_div_iff₀ N.scale_pos).mp (by linarith)
    exact (not_lt_of_ge (hlower.trans (hC _ hcore))) hhigh
  have hpos : 0 < p.val.2 := by
    by_contra hn
    have hzero : p.val.2 = 0 := le_antisymm (le_of_not_gt hn) p.property
    have hp0 : P.horn c e p.val ∈ P.core c := by
      convert P.horn_base_mem_core c e p.val.1 using 1
      exact congrArg (P.horn c e) (Prod.ext rfl hzero)
    exact hcore (hp ▸ hp0)
  exact ⟨⟨p.val, mem_univ _, hpos⟩, hp⟩

theorem exists_neck_coordinates_in_horn
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (e : P.hornIndex c) {δ : ℝ} {k : ℕ}
    (N : NormalizedNeck D.terminal.metric δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2) (hcenter : N.center ∈ hornHalfRange P c e)
    (C : ℝ) (hC : ∀ x ∈ P.core c, metricScalarAt D.terminal.metric x ≤ C)
    (hhigh : C < (1 - 4323 * δ) * N.scale) :
    ∃ Θ : neckCentralOpen δ → positiveHornDomain,
      IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
      ∀ q : neckCentralOpen δ,
        P.horn c e (Θ q).val = N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q) := by
  let F : neckCentralOpen δ → (P.positiveHornMap_local c e).image :=
    fun q => ⟨N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q),
      P.neckCentralOpen_mem_positiveHorn_image c hc e N hk hδ hcenter C hC hhigh q⟩
  let Θ := (P.positiveHornDiffeomorph c e).symm ∘ F
  have hinc : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞
      (Opens.inclusion (neckCentralOpen_le_buffer δ)) := by
    apply isSmoothEmbedding_intoOpen NeckCylinderModel NeckCylinderModel (neckBuffer δ)
    exact IsSmoothEmbedding.of_opens (I := NeckCylinderModel) (neckCentralOpen δ)
  have hcomp : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
      ((N.chart : neckBuffer δ → D.slab.terminalRegularOpen) ∘ Opens.inclusion (neckCentralOpen_le_buffer δ)) :=
    IsSmoothEmbedding.comp N.chart_smooth hinc (by simp)
  have hF : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ F :=
    isSmoothEmbedding_intoOpen NeckCylinderModel ThreeModel _ F hcomp
  have hΘ : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ :=
    IsSmoothEmbedding.comp (DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.diffeomorph_isSmoothEmbedding (P.positiveHornDiffeomorph c e).symm) hF (by simp)
  refine ⟨Θ, hΘ, ?_⟩
  intro q
  exact diffeomorphOntoImage_symm_apply (P.positiveHornMap c e) (P.positiveHornMap_local c e)
    (P.horn_interior_embedding c e).isEmbedding.injective (F q)

end TerminalCorePresentation

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem exists_scale_threshold_neck_coordinates_beyond_depth
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (e : P.hornIndex c) (r : ℝ) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ {δ : ℝ} {k : ℕ}
      (N : NormalizedNeck D.terminal.metric δ k),
      2 ≤ k → δ ≤ 1 / 8646 → N.center ∈ hornHalfRange P c e → Q < N.scale →
      ∃ Θ : neckCentralOpen δ → positiveHornDomain,
        IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
        (∀ q : neckCentralOpen δ,
          P.horn c e (Θ q).val = N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q)) ∧
        ∀ q : neckCentralOpen δ, r < (Θ q).val.2 := by
  let K := P.truncatedCore c (fun _ => max r 0)
  obtain ⟨C, hC⟩ := (P.truncatedCore_isCompact c hc (fun _ => max r 0)).bddAbove_image
    (metricScalar_smooth D.terminal.metric).continuous.continuousOn
  let Q := 2 * (max C 0 + 1)
  refine ⟨Q, by dsimp only [Q]; positivity, ?_⟩
  intro δ k N hk hδ hcenter hscale
  have hδhalf : δ ≤ 1 / 2 := hδ.trans (by norm_num)
  have hfactor : (1 / 2 : ℝ) ≤ 1 - 4323 * δ := by linarith
  have hhigh : C < (1 - 4323 * δ) * N.scale := by
    have hC0 : C ≤ max C 0 := le_max_left _ _
    have hmul := mul_le_mul_of_nonneg_right hfactor N.scale_pos.le
    change 2 * (max C 0 + 1) < N.scale at hscale
    linarith
  have hcore : ∀ x ∈ P.core c, metricScalarAt D.terminal.metric x ≤ C :=
    fun x hx => hC (mem_image_of_mem _ (Or.inl hx))
  obtain ⟨Θ, hΘ, heq⟩ := P.exists_neck_coordinates_in_horn c hc e N hk hδhalf hcenter C hcore hhigh
  refine ⟨Θ, hΘ, heq, ?_⟩
  intro q
  by_contra hnot
  have hqr : (Θ q).val.2 ≤ max r 0 := (le_of_not_gt hnot).trans (le_max_left _ _)
  have hxK : P.horn c e (Θ q).val ∈ K :=
    Or.inr (mem_iUnion.mpr ⟨e, (Θ q).val, ⟨mem_univ _, (Θ q).property.2.le, hqr⟩, rfl⟩)
  have hscalar : metricScalarAt D.terminal.metric
      (N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q)) ≤ C := by
    rw [← heq q]
    exact hC (mem_image_of_mem _ hxK)
  have hratio := (abs_le.mp (N.abs_scalar_ratio_sub_one_le hk hδhalf
    (Opens.inclusion (neckCentralOpen_le_buffer δ) q) ⟨q.property.2.1.le, q.property.2.2.le⟩)).1
  have hlower : (1 - 4323 * δ) * N.scale ≤ metricScalarAt D.terminal.metric
      (N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q)) :=
    (le_div_iff₀ N.scale_pos).mp (by linarith)
  exact (not_lt_of_ge (hlower.trans hscalar)) hhigh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

end
