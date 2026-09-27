import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import DifferentialGeometry.Topology.Manifold.ImmersionRange
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

universe u
variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem isOpen_positive_horn
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    IsOpen (P.horn c e '' (univ ×ˢ Ioi (0 : ℝ))) := by
  let V : TopologicalSpace.Opens NeckCylinder :=
    ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
  have h := Manifold.isOpen_range_of_isSmoothEmbedding
    (by simp [ThreeSpace, Module.finrank_prod]) (P.horn_interior_embedding c e)
  have heq : range (fun x : V => P.horn c e x.val) = P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rwa [heq] at h

theorem isConnected_positive_horn
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    IsConnected (P.horn c e '' (univ ×ˢ Ioi (0 : ℝ))) := by
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))
  apply (isConnected_univ.prod isConnected_Ioi).image (P.horn c e)
  exact (P.horn_smooth c e).continuousOn.mono fun z hx => ⟨hx.1, (show 0 < z.2 from hx.2).le⟩

theorem positive_horn_eq_half_range_sdiff_base
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) =
      (range fun x : HalfNeckCylinder => P.horn c e x.val) \
        range (fun y : Sphere 2 => P.horn c e (y, 0)) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨⟨z, hz.2.le⟩, rfl⟩, ?_⟩
    rintro ⟨y, hy⟩
    have heq := P.horn_injOn c e (show (y, (0 : ℝ)) ∈ univ ×ˢ Ici (0 : ℝ) from
      ⟨mem_univ _, by change (0 : ℝ) ≤ 0; rfl⟩) ⟨hz.1, (show 0 < z.2 from hz.2).le⟩ hy
    exact hz.2.ne' (congrArg Prod.snd heq).symm
  · rintro ⟨⟨z, rfl⟩, hnot⟩
    refine ⟨z.val, ⟨mem_univ _, ?_⟩, rfl⟩
    apply lt_of_le_of_ne z.property
    intro hz
    exact hnot ⟨z.val.1, congrArg (P.horn c e) (Prod.ext rfl hz)⟩

theorem closure_positive_horn_subset_half_range
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    closure (P.horn c e '' (univ ×ˢ Ioi (0 : ℝ))) ⊆
      range (fun x : HalfNeckCylinder => P.horn c e x.val) := by
  apply closure_minimal _ (P.horn_proper c e).isClosed_range
  rintro x ⟨z,hz,rfl⟩
  exact ⟨⟨z,hz.2.le⟩,rfl⟩

theorem positive_horn_eq_connectedComponentIn_compl_base
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (y : Sphere 2) {t : ℝ} (ht : 0 < t) :
    connectedComponentIn (range (fun q : Sphere 2 => P.horn c e (q,0)))ᶜ
      (P.horn c e (y,t)) = P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) := by
  let T := P.horn c e '' (univ ×ˢ Ioi (0 : ℝ))
  let S := range (fun q : Sphere 2 => P.horn c e (q,0))
  have hTS : T ⊆ Sᶜ := by
    intro x hx
    change x ∈ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) at hx
    rw [P.positive_horn_eq_half_range_sdiff_base] at hx
    exact hx.2
  have hx : P.horn c e (y,t) ∈ T := ⟨(y,t),⟨mem_univ _,ht⟩,rfl⟩
  apply Subset.antisymm _
    ((P.isConnected_positive_horn c e).isPreconnected.subset_connectedComponentIn hx hTS)
  apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
    (P.isOpen_positive_horn c e)
    ⟨P.horn c e (y,t),mem_connectedComponentIn (hTS hx),hx⟩
  intro x hx
  rw [P.positive_horn_eq_half_range_sdiff_base]
  exact ⟨P.closure_positive_horn_subset_half_range c e hx.1,
    connectedComponentIn_subset Sᶜ _ hx.2⟩

theorem closure_positive_horn_eq_half_range
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    closure (P.horn c e '' (univ ×ˢ Ioi (0 : ℝ))) =
      range (fun x : HalfNeckCylinder => P.horn c e x.val) := by
  apply Subset.antisymm (P.closure_positive_horn_subset_half_range c e)
  rintro x ⟨z, rfl⟩
  by_cases hz : 0 < z.val.2
  · exact subset_closure ⟨z.val, ⟨mem_univ _,hz⟩,rfl⟩
  · have hz0 : z.val.2 = 0 := le_antisymm (le_of_not_gt hz) z.property
    have hf : ContinuousOn (fun t : ℝ => P.horn c e (z.val.1,t)) (closure (Ioi (0 : ℝ))) := by
      rw [closure_Ioi]
      exact (P.horn_smooth c e).continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨mem_univ _,ht⟩)
    have hm : P.horn c e (z.val.1,0) ∈ closure ((fun t : ℝ => P.horn c e (z.val.1,t)) '' Ioi 0) :=
      hf.image_closure ⟨(0 : ℝ), by simp, rfl⟩
    have hsub : (fun t : ℝ => P.horn c e (z.val.1,t)) '' Ioi 0 ⊆
        P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) := by
      rintro x ⟨t,ht,rfl⟩
      exact ⟨(z.val.1,t),⟨mem_univ _,ht⟩,rfl⟩
    have heq : z.val = (z.val.1, (0 : ℝ)) := Prod.ext rfl hz0
    change P.horn c e z.val ∈ _
    exact (congrArg (P.horn c e) heq).symm ▸ closure_mono hsub hm

theorem frontier_positive_horn_eq_base
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    frontier (P.horn c e '' (univ ×ˢ Ioi (0 : ℝ))) =
      range (fun q : Sphere 2 => P.horn c e (q,0)) := by
  rw [frontier, P.closure_positive_horn_eq_half_range,
    (P.isOpen_positive_horn c e).interior_eq, P.positive_horn_eq_half_range_sdiff_base]
  have hbase : range (fun q : Sphere 2 => P.horn c e (q,0)) ⊆
      range (fun x : HalfNeckCylinder => P.horn c e x.val) := by
    rintro x ⟨q,rfl⟩
    exact ⟨⟨(q,0),le_rfl⟩,rfl⟩
  exact sdiff_sdiff_cancel_left hbase

theorem horn_collar_mem_positive_horn_iff
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (x : Sphere 2 × symmetricOpenInterval (P.hornCollar c e).radius) :
    (P.hornCollar c e).toFun x ∈ P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)) ↔ 0 < (x.2 : ℝ) := by
  constructor
  · intro hx
    by_contra hnot
    have hcore := (P.horn_collar_core_side c e x).mpr (le_of_not_gt hnot)
    obtain ⟨z,hz,heq⟩ := hx
    exact P.horn_pos_notMem_core c e z.1 (show 0 < z.2 from hz.2) (heq.symm ▸ hcore)
  · intro hx
    rw [P.horn_collar_eq c e x hx.le]
    exact ⟨(x.1,x.2),⟨mem_univ _,hx⟩,rfl⟩

theorem not_isCompact_closure_positive_horn
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c) :
    ¬ IsCompact (closure (P.horn c e '' (univ ×ˢ Ioi (0 : ℝ)))) := by
  intro hcompact
  rw [P.closure_positive_horn_eq_half_range] at hcompact
  obtain ⟨B,hB⟩ := hcompact.bddAbove_image
    (metricScalar_smooth D.terminal.metric).continuous.continuousOn
  obtain ⟨r,hr⟩ := P.horn_scalar_diverges c e B
  let t := max r 0 + 1
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hrt : r ≤ t := (le_max_left r 0).trans (le_add_of_nonneg_right zero_le_one)
  have hx : P.horn c e (DifferentialGeometry.Topology.sphereTwoNorth,t) ∈
      range (fun x : HalfNeckCylinder => P.horn c e x.val) :=
    ⟨⟨(DifferentialGeometry.Topology.sphereTwoNorth,t),ht⟩,rfl⟩
  exact (not_lt_of_ge (hB (mem_image_of_mem _ hx))) (hr _ _ hrt)

theorem horn_collar_mem_complement_component_iff
    (c : ConnectedComponents D.slab.terminalRegularOpen) (e : P.hornIndex c)
    (y : Sphere 2) {t : ℝ} (ht : 0 < t)
    (x : Sphere 2 × symmetricOpenInterval (P.hornCollar c e).radius) :
    (P.hornCollar c e).toFun x ∈
        connectedComponentIn (range (fun q : Sphere 2 => P.horn c e (q,0)))ᶜ
          (P.horn c e (y,t)) ↔ 0 < (x.2 : ℝ) := by
  rw [P.positive_horn_eq_connectedComponentIn_compl_base c e y ht]
  exact P.horn_collar_mem_positive_horn_iff c e x

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
