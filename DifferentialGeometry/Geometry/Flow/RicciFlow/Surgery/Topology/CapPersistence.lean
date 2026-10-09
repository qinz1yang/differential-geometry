import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CappingCover

set_option autoImplicit false

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v w z

section Capping

variable {M : Type u} [TopologicalSpace M] {N : Type v} [TopologicalSpace N]
  {T : TubeSystem M}

theorem Capping.cap_mem_component_coreBoundary (K : Capping T N) (b : T.Boundary)
    (y : ThreeBall) (z : Sphere 2) :
    ConnectedComponents.mk (K.cap b y) =
      ConnectedComponents.mk
        (K.coreInclusion (T.coreBoundarySphere b (K.attaching b z))) := by
  have hpc : IsPreconnected (Set.range (K.cap b)) :=
    isPreconnected_range (K.cap b).continuous
  have hmem : K.coreInclusion (T.coreBoundarySphere b (K.attaching b z)) ∈
      Set.range (K.cap b) :=
    ⟨sphereToThreeBall z, K.boundary_eq b z⟩
  exact (ConnectedComponents.coe_eq_coe'.mpr
    (hpc.subset_connectedComponent ⟨y, rfl⟩ hmem)).symm

end Capping

namespace CutCapTopology

variable {M : Type u} [TopologicalSpace M] {Q : Type v} [TopologicalSpace Q]
  {D : Type w} [TopologicalSpace D] {N : Type z} [TopologicalSpace N]

def capRetained (E : CutCapTopology M Q D N) (b : E.tubes.Boundary) : Prop :=
  ∀ y : ThreeBall, E.presentation (E.capping.cap b y) ∈ Set.range (Sum.inl : Q → Q ⊕ D)

def capDiscarded (E : CutCapTopology M Q D N) (b : E.tubes.Boundary) : Prop :=
  ∀ y : ThreeBall, E.presentation (E.capping.cap b y) ∈ Set.range (Sum.inr : D → Q ⊕ D)

theorem cap_retained_or_discarded (E : CutCapTopology M Q D N) (b : E.tubes.Boundary) :
    E.capRetained b ∨ E.capDiscarded b := by
  have hpc : IsPreconnected
      (Set.range fun y : ThreeBall => E.presentation (E.capping.cap b y)) :=
    isPreconnected_range (E.presentation.continuous.comp (E.capping.cap b).continuous)
  have hbase : E.presentation (E.capping.cap b threeBallNorth) ∈
      Set.range fun y : ThreeBall => E.presentation (E.capping.cap b y) :=
    ⟨threeBallNorth, rfl⟩
  have hsame : ∀ y : ThreeBall,
      E.presentation (E.capping.cap b y) ∈
        connectedComponent (E.presentation (E.capping.cap b threeBallNorth)) :=
    fun y => hpc.subset_connectedComponent hbase ⟨y, rfl⟩
  have hsum : ∀ x : Q ⊕ D, x ∈ Set.range (Sum.inl : Q → Q ⊕ D) ∨
      x ∈ Set.range (Sum.inr : D → Q ⊕ D) := by
    intro x
    cases x with
    | inl q => exact Or.inl ⟨q, rfl⟩
    | inr d => exact Or.inr ⟨d, rfl⟩
  by_cases h : E.presentation (E.capping.cap b threeBallNorth) ∈
      Set.range (Sum.inl : Q → Q ⊕ D)
  · left
    intro y
    exact isClopen_range_inl.connectedComponent_subset h (hsame y)
  · right
    rcases hsum (E.presentation (E.capping.cap b threeBallNorth)) with h' | h'
    · exact absurd h' h
    · intro y
      exact isClopen_range_inr.connectedComponent_subset h' (hsame y)

theorem capDiscarded_iff_not_capRetained (E : CutCapTopology M Q D N) (b : E.tubes.Boundary) :
    E.capDiscarded b ↔ ¬ E.capRetained b := by
  constructor
  · intro hd hr
    obtain ⟨d, hd'⟩ := hd (sphereToThreeBall sphereNorth)
    obtain ⟨q, hq⟩ := hr (sphereToThreeBall sphereNorth)
    exact Sum.inr_ne_inl (hd'.trans hq.symm)
  · intro hr
    rcases E.cap_retained_or_discarded b with h | h
    · exact absurd h hr
    · exact h

theorem capRetained_coreBoundarySphere_mem_retainedCore (E : CutCapTopology M Q D N)
    (b : E.tubes.Boundary) (h : E.capRetained b) (z : Sphere 2) :
    E.tubes.coreBoundarySphere b z ∈ E.retainedCore := by
  have hb := E.capping.boundary_eq b ((E.capping.attaching b).symm z)
  have hz : E.capping.attaching b ((E.capping.attaching b).symm z) = z :=
    (E.capping.attaching b).apply_symm_apply z
  rw [hz] at hb
  obtain ⟨q, hq⟩ := h (sphereToThreeBall ((E.capping.attaching b).symm z))
  exact ⟨q, by rw [← hb]; exact hq.symm⟩

theorem capDiscarded_coreBoundarySphere_not_mem_retainedCore (E : CutCapTopology M Q D N)
    (b : E.tubes.Boundary) (h : E.capDiscarded b) (z : Sphere 2) :
    E.tubes.coreBoundarySphere b z ∉ E.retainedCore := by
  rintro ⟨q, hq⟩
  have hb := E.capping.boundary_eq b ((E.capping.attaching b).symm z)
  have hz : E.capping.attaching b ((E.capping.attaching b).symm z) = z :=
    (E.capping.attaching b).apply_symm_apply z
  rw [hz] at hb
  obtain ⟨d, hd⟩ := h (sphereToThreeBall ((E.capping.attaching b).symm z))
  rw [hb, hq] at hd
  exact Sum.inr_ne_inl hd

theorem capRetained_of_coreBoundarySphere_mem_retainedCore (E : CutCapTopology M Q D N)
    (b : E.tubes.Boundary) (z₀ : Sphere 2)
    (h : E.tubes.coreBoundarySphere b z₀ ∈ E.retainedCore) :
    E.capRetained b := by
  obtain ⟨q, hq⟩ := h
  intro y
  have hcomp := Capping.cap_mem_component_coreBoundary E.capping b y
    ((E.capping.attaching b).symm z₀)
  have hz : E.capping.attaching b ((E.capping.attaching b).symm z₀) = z₀ :=
    (E.capping.attaching b).apply_symm_apply z₀
  rw [hz] at hcomp
  have hmap := congrArg E.presentation.continuous.connectedComponentsMap hcomp
  simp only [Continuous.connectedComponentsMap_mk] at hmap
  rw [hq] at hmap
  refine isClopen_range_inl.connectedComponent_subset (Set.mem_range_self q) ?_
  exact ConnectedComponents.coe_eq_coe'.mp hmap

theorem capRetained_iff_coreBoundarySphere_mem_retainedCore (E : CutCapTopology M Q D N)
    (b : E.tubes.Boundary) :
    E.capRetained b ↔ ∀ z : Sphere 2, E.tubes.coreBoundarySphere b z ∈ E.retainedCore := by
  constructor
  · intro h z
    exact E.capRetained_coreBoundarySphere_mem_retainedCore b h z
  · intro h
    exact E.capRetained_of_coreBoundarySphere_mem_retainedCore b sphereNorth (h sphereNorth)

end CutCapTopology

private theorem norm_eq_one_of_mem_sphere (y : Sphere 2) : ‖(y : ThreeSpace)‖ = 1 := by
  have h : dist (y : ThreeSpace) 0 = 1 := Metric.mem_sphere.mp y.2
  rwa [dist_eq_norm, sub_zero] at h

private theorem norm_le_one_of_mem_closedBall (v : ThreeBall) : ‖(v : ThreeSpace)‖ ≤ 1 := by
  have h : dist (v : ThreeSpace) 0 ≤ 1 := Metric.mem_closedBall.mp v.2
  rwa [dist_eq_norm, sub_zero] at h

private theorem mem_threeBall_of_norm_le {v : ThreeSpace} (h : ‖v‖ ≤ 1) : v ∈ ThreeBall := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact h

private theorem radius_abs_le_two (z : TubeDomain) : |(z.2 : ℝ)| ≤ 2 :=
  abs_le.mpr ⟨z.2.2.1, z.2.2.2⟩

def cylinderTubeSystem : TubeSystem TubeDomain where
  Index := PUnit
  finiteIndex := inferInstance
  tube := fun _ => ContinuousMap.id TubeDomain
  embedding := fun _ => by
    simpa using (Topology.IsEmbedding.id : Topology.IsEmbedding (id : TubeDomain → TubeDomain))
  disjoint := fun a b hab => (hab (Subsingleton.elim a b)).elim

private theorem mem_cylinderTubeSystem_core_iff (z : TubeDomain) :
    z ∈ cylinderTubeSystem.core ↔ (z.2 : ℝ) ≤ -1 ∨ 1 ≤ (z.2 : ℝ) := by
  have hiff : z ∈ cylinderTubeSystem.core ↔ ¬(-1 < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1) := by
    simp [TubeSystem.core, TubeSystem.removedBand, cylinderTubeSystem]
  rw [hiff]
  constructor
  · intro h
    by_cases h1 : (z.2 : ℝ) ≤ -1
    · exact Or.inl h1
    · exact Or.inr (by by_contra h2; exact h ⟨by linarith, by linarith⟩)
  · rintro (h | h)
    · exact fun ⟨h1, _⟩ => absurd h1 (by linarith)
    · exact fun ⟨_, h2⟩ => absurd h2 (by linarith)

private theorem continuous_core_radius :
    Continuous fun z : cylinderTubeSystem.core => ((z.1 : TubeDomain).2 : ℝ) :=
  continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)

private theorem isClosed_core_upper : IsClosed {z : cylinderTubeSystem.core | (1 : ℝ) ≤ (z.1.2 : ℝ)} :=
  isClosed_Ici.preimage (f := fun z : cylinderTubeSystem.core => (z.1.2 : ℝ)) continuous_core_radius

private theorem isClosed_core_lower : IsClosed {z : cylinderTubeSystem.core | (z.1.2 : ℝ) ≤ -1} :=
  isClosed_Iic.preimage (f := fun z : cylinderTubeSystem.core => (z.1.2 : ℝ)) continuous_core_radius

private theorem eq_compl_of_core {z : cylinderTubeSystem.core} :
    ((z.1.2 : ℝ) ≤ -1) ↔ ¬ (1 ≤ (z.1.2 : ℝ)) := by
  constructor
  · intro h hge
    linarith
  · intro hlt
    rcases (mem_cylinderTubeSystem_core_iff z.1).mp z.2 with h1 | h2
    · exact h1
    · exact absurd h2 hlt

private theorem eq_not_lower_of_core {z : cylinderTubeSystem.core} :
    (1 ≤ (z.1.2 : ℝ)) ↔ ¬ ((z.1.2 : ℝ) ≤ -1) := by
  constructor
  · intro h hle
    linarith
  · intro h
    by_contra hlt
    exact h ((eq_compl_of_core (z := z)).mpr hlt)

private theorem isOpen_core_lower : IsOpen {z : cylinderTubeSystem.core | (z.1.2 : ℝ) ≤ -1} := by
  have hset : {z : cylinderTubeSystem.core | (z.1.2 : ℝ) ≤ -1} =
      {z : cylinderTubeSystem.core | (1 : ℝ) ≤ (z.1.2 : ℝ)}ᶜ := by
    ext w
    exact eq_compl_of_core
  rw [hset]
  exact isClosed_core_upper.isOpen_compl

private theorem isOpen_core_upper : IsOpen {z : cylinderTubeSystem.core | 1 ≤ (z.1.2 : ℝ)} := by
  have hset : {z : cylinderTubeSystem.core | (1 : ℝ) ≤ (z.1.2 : ℝ)} =
      {z : cylinderTubeSystem.core | (z.1.2 : ℝ) ≤ -1}ᶜ := by
    ext w
    exact eq_not_lower_of_core
  rw [hset]
  exact isClosed_core_lower.isOpen_compl

private def lowerPoint (z : TubeDomain) : ThreeBall :=
  ⟨(-(z.2 : ℝ) / 2) • (z.1 : ThreeSpace),
    mem_threeBall_of_norm_le (by
      rw [norm_smul, norm_eq_one_of_mem_sphere z.1, mul_one, Real.norm_eq_abs]
      have := radius_abs_le_two z
      rw [abs_div, abs_neg, abs_two]
      linarith)⟩

private def upperPoint (z : TubeDomain) : ThreeBall :=
  ⟨((z.2 : ℝ) / 2) • (z.1 : ThreeSpace),
    mem_threeBall_of_norm_le (by
      rw [norm_smul, norm_eq_one_of_mem_sphere z.1, mul_one, Real.norm_eq_abs]
      have := radius_abs_le_two z
      rw [abs_div, abs_two]
      linarith)⟩

private def coreInclusionMap (z : cylinderTubeSystem.core) : ThreeBall ⊕ ThreeBall :=
  if (z.1.2 : ℝ) ≤ -1 then Sum.inl (lowerPoint z.1) else Sum.inr (upperPoint z.1)

private theorem coreInclusionMap_lower {z : cylinderTubeSystem.core}
    (h : (z.1.2 : ℝ) ≤ -1) : coreInclusionMap z = Sum.inl (lowerPoint z.1) :=
  dite_eq_left h

private theorem coreInclusionMap_upper {z : cylinderTubeSystem.core}
    (h : ¬ (z.1.2 : ℝ) ≤ -1) : coreInclusionMap z = Sum.inr (upperPoint z.1) :=
  dite_eq_right h

private theorem continuous_lowerPoint :
    Continuous fun z : cylinderTubeSystem.core => lowerPoint z.1 :=
  Continuous.subtype_mk (f := fun z : cylinderTubeSystem.core => (-(z.1.2 : ℝ) / 2) • (z.1.1 : ThreeSpace))
    (by fun_prop) _

private theorem continuous_upperPoint :
    Continuous fun z : cylinderTubeSystem.core => upperPoint z.1 :=
  Continuous.subtype_mk (f := fun z : cylinderTubeSystem.core => ((z.1.2 : ℝ) / 2) • (z.1.1 : ThreeSpace))
    (by fun_prop) _

private theorem continuous_coreInclusionMap : Continuous coreInclusionMap := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases h : (z.1.2 : ℝ) ≤ -1
  · refine (continuous_inl.comp continuous_lowerPoint).continuousAt.congr ?_
    filter_upwards [isOpen_core_lower.mem_nhds h] with w hw
    exact (coreInclusionMap_lower hw).symm
  · have hmem : z ∈ {w : cylinderTubeSystem.core | 1 ≤ (w.1.2 : ℝ)} :=
      (eq_not_lower_of_core (z := z)).mpr h
    refine (continuous_inr.comp continuous_upperPoint).continuousAt.congr ?_
    filter_upwards [isOpen_core_upper.mem_nhds hmem] with w hw
    exact (coreInclusionMap_upper ((eq_not_lower_of_core (z := w)).mp hw)).symm


private theorem isCompact_core : IsCompact cylinderTubeSystem.core := by
  have hclosed : IsClosed cylinderTubeSystem.core := by
    have hset : cylinderTubeSystem.core =
        {z : TubeDomain | (z.2 : ℝ) ≤ -1} ∪ {z : TubeDomain | 1 ≤ (z.2 : ℝ)} := by
      ext z
      exact mem_cylinderTubeSystem_core_iff z
    rw [hset]
    exact (isClosed_Iic.preimage (f := fun z : TubeDomain => (z.2 : ℝ))
        (continuous_subtype_val.comp continuous_snd)).union
      (isClosed_Ici.preimage (f := fun z : TubeDomain => (z.2 : ℝ))
        (continuous_subtype_val.comp continuous_snd))
  exact hclosed.isCompact

private theorem coreInclusionMap_injective_lower (a b : cylinderTubeSystem.core)
    (ha : (a.1.2 : ℝ) ≤ -1) (hb : (b.1.2 : ℝ) ≤ -1)
    (hab : coreInclusionMap a = coreInclusionMap b) : a = b := by
  have hv : (-(a.1.2 : ℝ) / 2) • (a.1.1 : ThreeSpace) =
      (-(b.1.2 : ℝ) / 2) • (b.1.1 : ThreeSpace) := by
    have hab' := hab
    rw [coreInclusionMap_lower ha, coreInclusionMap_lower hb] at hab'
    exact congrArg Subtype.val (Sum.inl_injective hab')
  have hnorm : ‖(-(a.1.2 : ℝ) / 2) • (a.1.1 : ThreeSpace)‖ =
      ‖(-(b.1.2 : ℝ) / 2) • (b.1.1 : ThreeSpace)‖ := congrArg norm hv
  rw [norm_smul, norm_smul, norm_eq_one_of_mem_sphere a.1.1,
    norm_eq_one_of_mem_sphere b.1.1, mul_one, mul_one, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < -(a.1.2 : ℝ) / 2),
    abs_of_pos (by linarith : (0 : ℝ) < -(b.1.2 : ℝ) / 2)] at hnorm
  have ht : (a.1.2 : ℝ) = (b.1.2 : ℝ) := by linarith
  have hc : (-(a.1.2 : ℝ) / 2) ≠ 0 := by linarith
  have hy : (a.1.1 : ThreeSpace) = (b.1.1 : ThreeSpace) := by
    have hinj : Function.Injective (fun v : ThreeSpace => (-(a.1.2 : ℝ) / 2) • v) := by
      intro u v huv
      have h := congrArg (fun w : ThreeSpace => (-(a.1.2 : ℝ) / 2)⁻¹ • w) huv
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_smul, inv_mul_cancel₀ hc, one_smul] at h
      exact h
    exact hinj (by simpa [← hnorm] using hv)
  exact Subtype.ext (Prod.ext (Subtype.ext hy) (Subtype.ext ht))

private theorem coreInclusionMap_injective_upper (a b : cylinderTubeSystem.core)
    (ha : 1 ≤ (a.1.2 : ℝ)) (hb : 1 ≤ (b.1.2 : ℝ))
    (hab : coreInclusionMap a = coreInclusionMap b) : a = b := by
  have hna : ¬ (a.1.2 : ℝ) ≤ -1 := by linarith
  have hnb : ¬ (b.1.2 : ℝ) ≤ -1 := by linarith
  have hv : ((a.1.2 : ℝ) / 2) • (a.1.1 : ThreeSpace) =
      ((b.1.2 : ℝ) / 2) • (b.1.1 : ThreeSpace) := by
    have hab' := hab
    rw [coreInclusionMap_upper hna, coreInclusionMap_upper hnb] at hab'
    exact congrArg Subtype.val (Sum.inr_injective hab')
  have hnorm : ‖((a.1.2 : ℝ) / 2) • (a.1.1 : ThreeSpace)‖ =
      ‖((b.1.2 : ℝ) / 2) • (b.1.1 : ThreeSpace)‖ := congrArg norm hv
  rw [norm_smul, norm_smul, norm_eq_one_of_mem_sphere a.1.1,
    norm_eq_one_of_mem_sphere b.1.1, mul_one, mul_one, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < (a.1.2 : ℝ) / 2),
    abs_of_pos (by linarith : (0 : ℝ) < (b.1.2 : ℝ) / 2)] at hnorm
  have ht : (a.1.2 : ℝ) = (b.1.2 : ℝ) := by linarith
  have hc : ((a.1.2 : ℝ) / 2) ≠ 0 := by linarith
  have hy : (a.1.1 : ThreeSpace) = (b.1.1 : ThreeSpace) := by
    have hinj : Function.Injective (fun v : ThreeSpace => ((a.1.2 : ℝ) / 2) • v) := by
      intro u v huv
      have h := congrArg (fun w : ThreeSpace => ((a.1.2 : ℝ) / 2)⁻¹ • w) huv
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_smul, inv_mul_cancel₀ hc, one_smul] at h
      exact h
    exact hinj (by simpa [← hnorm] using hv)
  exact Subtype.ext (Prod.ext (Subtype.ext hy) (Subtype.ext ht))

private theorem injective_coreInclusionMap : Injective coreInclusionMap := by
  intro z w hzw
  rcases (mem_cylinderTubeSystem_core_iff z.1).mp z.2 with hz | hz
  · rcases (mem_cylinderTubeSystem_core_iff w.1).mp w.2 with hw | hw
    · exact coreInclusionMap_injective_lower z w hz hw hzw
    · have h := hzw
      rw [coreInclusionMap_lower hz, coreInclusionMap_upper (by linarith)] at h
      exact absurd h Sum.inl_ne_inr
  · rcases (mem_cylinderTubeSystem_core_iff w.1).mp w.2 with hw | hw
    · have h := hzw
      rw [coreInclusionMap_upper (by linarith), coreInclusionMap_lower hw] at h
      exact absurd h Sum.inr_ne_inl
    · exact coreInclusionMap_injective_upper z w hz hw hzw

private theorem isEmbedding_coreInclusionMap : Topology.IsEmbedding coreInclusionMap := by
  have : CompactSpace ↥(cylinderTubeSystem.core) := isCompact_iff_compactSpace.mp isCompact_core
  exact (continuous_coreInclusionMap.isClosedEmbedding injective_coreInclusionMap).isEmbedding

private def halfPoint (y : ThreeBall) : ThreeBall :=
  ⟨(1/2 : ℝ) • (y : ThreeSpace),
    mem_threeBall_of_norm_le (by
      rw [norm_smul]
      norm_num
      linarith [norm_le_one_of_mem_closedBall y])⟩

private theorem continuous_halfPoint : Continuous halfPoint :=
  Continuous.subtype_mk (f := fun y : ThreeBall => (1/2 : ℝ) • (y : ThreeSpace)) (by fun_prop) _

private theorem injective_halfPoint : Injective halfPoint := by
  have hinj : Function.Injective (fun w : ThreeSpace => (1/2 : ℝ) • w) := by
    intro p q hpq
    have h := congrArg (fun w : ThreeSpace => (2 : ℝ) • w) hpq
    rw [smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h
    simpa using h
  intro u v huv
  exact Subtype.ext (hinj (congrArg Subtype.val huv))

private theorem isEmbedding_halfPoint : Topology.IsEmbedding halfPoint :=
  (continuous_halfPoint.isClosedEmbedding injective_halfPoint).isEmbedding

private def capMap (side : Bool) : C(ThreeBall, ThreeBall ⊕ ThreeBall) :=
  match side with
  | false => ⟨fun y => Sum.inl (halfPoint y), continuous_inl.comp continuous_halfPoint⟩
  | true => ⟨fun y => Sum.inr (halfPoint y), continuous_inr.comp continuous_halfPoint⟩

private theorem capMap_false_apply (y : ThreeBall) :
    capMap false y = Sum.inl (halfPoint y) := rfl

private theorem capMap_true_apply (y : ThreeBall) :
    capMap true y = Sum.inr (halfPoint y) := rfl

private theorem isEmbedding_capMap (side : Bool) : Topology.IsEmbedding (capMap side) := by
  cases side
  · change Topology.IsEmbedding (fun y : ThreeBall => Sum.inl (halfPoint y))
    exact (Topology.IsEmbedding.inl (X := ThreeBall) (Y := ThreeBall)).comp isEmbedding_halfPoint
  · change Topology.IsEmbedding (fun y : ThreeBall => Sum.inr (halfPoint y))
    exact (Topology.IsEmbedding.inr (X := ThreeBall) (Y := ThreeBall)).comp isEmbedding_halfPoint

private theorem halfPoint_inl_mem_range (v : ThreeBall) (hv : ‖(v : ThreeSpace)‖ ≤ 1 / 2) :
    Sum.inl v ∈ Set.range (capMap false) := by
  refine ⟨⟨(2 : ℝ) • (v : ThreeSpace), mem_threeBall_of_norm_le (by
    rw [norm_smul]
    norm_num
    linarith)⟩, ?_⟩
  simp only [capMap_false_apply, Sum.inl.injEq]
  exact Subtype.ext (by
    rw [halfPoint, Subtype.coe_mk, smul_smul]
    norm_num)

private theorem halfPoint_inr_mem_range (v : ThreeBall) (hv : ‖(v : ThreeSpace)‖ ≤ 1 / 2) :
    Sum.inr v ∈ Set.range (capMap true) := by
  refine ⟨⟨(2 : ℝ) • (v : ThreeSpace), mem_threeBall_of_norm_le (by
    rw [norm_smul]
    norm_num
    linarith)⟩, ?_⟩
  simp only [capMap_true_apply, Sum.inr.injEq]
  exact Subtype.ext (by
    rw [halfPoint, Subtype.coe_mk, smul_smul]
    norm_num)

private theorem half_le_norm_of_mem_range_coreInclusionMap {v : ThreeBall}
    (hv : Sum.inl v ∈ Set.range coreInclusionMap) : 1 / 2 ≤ ‖(v : ThreeSpace)‖ := by
  obtain ⟨z, hz⟩ := hv
  by_cases h : (z.1.2 : ℝ) ≤ -1
  · rw [coreInclusionMap_lower h] at hz
    have hval : lowerPoint z.1 = v := Sum.inl_injective hz
    have hnorm : ‖(v : ThreeSpace)‖ = -(z.1.2 : ℝ) / 2 := by
      rw [← hval, lowerPoint, norm_smul, norm_eq_one_of_mem_sphere z.1.1, mul_one,
        Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < -(z.1.2 : ℝ) / 2)]
    rw [hnorm]
    linarith
  · rw [coreInclusionMap_upper h] at hz
    exact absurd hz Sum.inr_ne_inl

private def normalizedSpherePoint (v : ThreeSpace) (h : ‖v‖ ≠ 0) : Sphere 2 :=
  ⟨‖v‖⁻¹ • v, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ h⟩

private theorem normalizedSpherePoint_coe (v : ThreeSpace) (h : ‖v‖ ≠ 0) :
    ((normalizedSpherePoint v h : Sphere 2) : ThreeSpace) = ‖v‖⁻¹ • v := rfl

private theorem mem_range_coreInclusionMap_of_half_le_norm (v : ThreeSpace)
    (hv : 1 / 2 ≤ ‖v‖) (hv1 : ‖v‖ ≤ 1) :
    Sum.inl (⟨v, mem_threeBall_of_norm_le hv1⟩ : ThreeBall) ∈
      Set.range coreInclusionMap := by
  have hpos : ‖v‖ ≠ 0 := by linarith
  have htmem : (-2 * ‖v‖) ∈ Set.Icc (-2 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hcore : (normalizedSpherePoint v hpos, ⟨-2 * ‖v‖, htmem⟩) ∈ cylinderTubeSystem.core := by
    rw [mem_cylinderTubeSystem_core_iff]
    exact Or.inl (by linarith)
  refine ⟨⟨(normalizedSpherePoint v hpos, ⟨-2 * ‖v‖, htmem⟩), hcore⟩, ?_⟩
  rw [coreInclusionMap_lower (z := ⟨(normalizedSpherePoint v hpos, ⟨-2 * ‖v‖, htmem⟩), hcore⟩)
    (by simp only; linarith)]
  congr 1
  exact Subtype.ext (by
    rw [lowerPoint, Subtype.coe_mk, normalizedSpherePoint_coe]
    rw [show -(-2 * ‖v‖) / 2 = ‖v‖ by ring]
    rw [smul_smul, mul_inv_cancel₀ hpos, one_smul])

private theorem cylinderTubeSystem_boundarySphere (b : cylinderTubeSystem.Boundary) (y : Sphere 2) :
    cylinderTubeSystem.boundarySphere b y = (y, TubeSystem.boundaryLevel b.2) := by
  simp only [TubeSystem.boundarySphere, cylinderTubeSystem, ContinuousMap.coe_comp,
    ContinuousMap.coe_mk, Function.comp_apply]
  rw [ContinuousMap.id_apply]

private theorem cylinderTubeSystem_coreBoundarySphere_coe (b : cylinderTubeSystem.Boundary)
    (y : Sphere 2) :
    ((cylinderTubeSystem.coreBoundarySphere b y : cylinderTubeSystem.core) : TubeDomain) =
      (y, TubeSystem.boundaryLevel b.2) := by
  simp only [TubeSystem.coreBoundarySphere, Subtype.coe_mk, ContinuousMap.coe_mk]
  exact cylinderTubeSystem_boundarySphere b y

private theorem coreBoundarySphere_false_coe (y : Sphere 2) :
    ((cylinderTubeSystem.coreBoundarySphere (PUnit.unit, false) y : cylinderTubeSystem.core) :
      TubeDomain) = (y, ⟨-1, by norm_num⟩) := by
  rw [cylinderTubeSystem_coreBoundarySphere_coe]
  exact Prod.ext rfl (Subtype.ext rfl)

private theorem coreBoundarySphere_true_coe (y : Sphere 2) :
    ((cylinderTubeSystem.coreBoundarySphere (PUnit.unit, true) y : cylinderTubeSystem.core) :
      TubeDomain) = (y, ⟨1, by norm_num⟩) := by
  rw [cylinderTubeSystem_coreBoundarySphere_coe]
  exact Prod.ext rfl (Subtype.ext rfl)

private theorem coreInclusionMap_boundary_false (y : Sphere 2) :
    coreInclusionMap (cylinderTubeSystem.coreBoundarySphere (PUnit.unit, false) y) =
      Sum.inl (halfPoint (sphereToThreeBall y)) := by
  have hle : (((cylinderTubeSystem.coreBoundarySphere (PUnit.unit, false) y :
      cylinderTubeSystem.core)).1.2 : ℝ) ≤ -1 := by
    rw [coreBoundarySphere_false_coe y]
  rw [coreInclusionMap_lower hle]
  congr 1
  refine Subtype.ext ?_
  simp only [lowerPoint, halfPoint, Subtype.coe_mk, coreBoundarySphere_false_coe y,
    sphereToThreeBall, ContinuousMap.coe_mk]
  norm_num

private theorem coreInclusionMap_boundary_true (y : Sphere 2) :
    coreInclusionMap (cylinderTubeSystem.coreBoundarySphere (PUnit.unit, true) y) =
      Sum.inr (halfPoint (sphereToThreeBall y)) := by
  have hnot : ¬ (((cylinderTubeSystem.coreBoundarySphere (PUnit.unit, true) y :
      cylinderTubeSystem.core)).1.2 : ℝ) ≤ -1 := by
    rw [coreBoundarySphere_true_coe y]
    norm_num
  rw [coreInclusionMap_upper hnot]
  rfl

private theorem mem_range_coreInclusionMap_inr_of_half_le_norm (v : ThreeSpace)
    (hv : 1 / 2 ≤ ‖v‖) (hv1 : ‖v‖ ≤ 1) :
    Sum.inr (⟨v, mem_threeBall_of_norm_le hv1⟩ : ThreeBall) ∈
      Set.range coreInclusionMap := by
  have hpos : ‖v‖ ≠ 0 := by linarith
  have htmem : (2 * ‖v‖) ∈ Set.Icc (-2 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hcore : (normalizedSpherePoint v hpos, ⟨2 * ‖v‖, htmem⟩) ∈ cylinderTubeSystem.core := by
    rw [mem_cylinderTubeSystem_core_iff]
    exact Or.inr (by linarith)
  refine ⟨⟨(normalizedSpherePoint v hpos, ⟨2 * ‖v‖, htmem⟩), hcore⟩, ?_⟩
  rw [coreInclusionMap_upper (z := ⟨(normalizedSpherePoint v hpos, ⟨2 * ‖v‖, htmem⟩), hcore⟩)
    (by simp only; linarith)]
  congr 1
  refine Subtype.ext ?_
  rw [upperPoint, Subtype.coe_mk, normalizedSpherePoint_coe,
    show (2 * ‖v‖) / 2 = ‖v‖ by ring]
  rw [smul_smul, mul_inv_cancel₀ hpos, one_smul]

def twoBallCapping : Capping cylinderTubeSystem (ThreeBall ⊕ ThreeBall) where
  coreInclusion := ⟨coreInclusionMap, continuous_coreInclusionMap⟩
  coreEmbedding := isEmbedding_coreInclusionMap
  cap := fun b => capMap b.2
  capEmbedding := fun b => isEmbedding_capMap b.2
  attaching := fun _ => Homeomorph.refl (Sphere 2)
  boundary_eq := by
    rintro ⟨⟨⟩, side⟩ y
    cases side
    · change capMap false (sphereToThreeBall y) =
        coreInclusionMap (cylinderTubeSystem.coreBoundarySphere (PUnit.unit, false) y)
      rw [capMap_false_apply, coreInclusionMap_boundary_false]
    · change capMap true (sphereToThreeBall y) =
        coreInclusionMap (cylinderTubeSystem.coreBoundarySphere (PUnit.unit, true) y)
      rw [capMap_true_apply, coreInclusionMap_boundary_true]
  exhaustive := by
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rcases x with v | v
    · by_cases hv : ‖(v : ThreeSpace)‖ ≤ 1 / 2
      · exact Or.inr (Set.mem_iUnion.mpr ⟨(PUnit.unit, false),
          halfPoint_inl_mem_range v hv⟩)
      · have hle1 : ‖(v : ThreeSpace)‖ ≤ 1 := norm_le_one_of_mem_closedBall v
        have hv' : 1 / 2 ≤ ‖(v : ThreeSpace)‖ := by linarith
        refine Or.inl ?_
        have hmem := mem_range_coreInclusionMap_of_half_le_norm (v : ThreeSpace) hv' hle1
        have hval : (⟨(v : ThreeSpace), mem_threeBall_of_norm_le hle1⟩ : ThreeBall) = v :=
          Subtype.ext rfl
        rwa [hval] at hmem
    · by_cases hv : ‖(v : ThreeSpace)‖ ≤ 1 / 2
      · exact Or.inr (Set.mem_iUnion.mpr ⟨(PUnit.unit, true),
          halfPoint_inr_mem_range v hv⟩)
      · have hle1 : ‖(v : ThreeSpace)‖ ≤ 1 := norm_le_one_of_mem_closedBall v
        have hv' : 1 / 2 ≤ ‖(v : ThreeSpace)‖ := by linarith
        refine Or.inl ?_
        have hmem := mem_range_coreInclusionMap_inr_of_half_le_norm (v : ThreeSpace) hv' hle1
        have hval : (⟨(v : ThreeSpace), mem_threeBall_of_norm_le hle1⟩ : ThreeBall) = v :=
          Subtype.ext rfl
        rwa [hval] at hmem
  core_cap_intersection := by
    rintro ⟨⟨⟩, side⟩
    cases side
    · ext x
      constructor
      · rintro ⟨hcore, hcap⟩
        obtain ⟨y, hy⟩ := hcap
        have hxe : x = Sum.inl (halfPoint y) := by rw [← hy, capMap_false_apply]
        subst hxe
        have hhalf : 1 / 2 ≤ ‖(halfPoint y : ThreeSpace)‖ :=
          half_le_norm_of_mem_range_coreInclusionMap hcore
        have hle : ‖(halfPoint y : ThreeSpace)‖ ≤ 1 / 2 := by
          rw [halfPoint, norm_smul]
          norm_num
          linarith [norm_le_one_of_mem_closedBall y]
        have hnorm : ‖(halfPoint y : ThreeSpace)‖ = 1 / 2 := le_antisymm hle hhalf
        have hy1 : ‖(y : ThreeSpace)‖ = 1 := by
          rw [halfPoint, norm_smul] at hnorm
          norm_num at hnorm
          linarith [norm_le_one_of_mem_closedBall y]
        refine ⟨⟨y, Metric.mem_sphere.mpr ?_⟩, ?_⟩
        · rw [dist_eq_norm, sub_zero]
          exact hy1
        · simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
          rw [coreInclusionMap_boundary_false]
          rfl
      · rintro ⟨y, rfl⟩
        constructor
        · exact ⟨_, rfl⟩
        · simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
          rw [coreInclusionMap_boundary_false]
          refine halfPoint_inl_mem_range _ ?_
          rw [halfPoint, norm_smul]
          norm_num
          linarith [norm_le_one_of_mem_closedBall (sphereToThreeBall y)]
    · ext x
      constructor
      · rintro ⟨hcore, hcap⟩
        obtain ⟨y, hy⟩ := hcap
        have hxe : x = Sum.inr (halfPoint y) := by rw [← hy, capMap_true_apply]
        subst hxe
        obtain ⟨z, hz⟩ := hcore
        change coreInclusionMap z = Sum.inr (halfPoint y) at hz
        by_cases h : (z.1.2 : ℝ) ≤ -1
        · rw [coreInclusionMap_lower h] at hz
          exact absurd hz Sum.inl_ne_inr
        · rw [coreInclusionMap_upper h] at hz
          have hval : upperPoint z.1 = halfPoint y := Sum.inr_injective hz
          have hge : (1 : ℝ) ≤ (z.1.2 : ℝ) := by
            rcases (mem_cylinderTubeSystem_core_iff z.1).mp z.2 with h1 | h2
            · exact absurd h1 h
            · exact h2
          have hnorm : ‖(halfPoint y : ThreeSpace)‖ = (z.1.2 : ℝ) / 2 := by
            rw [← hval, upperPoint, norm_smul, norm_eq_one_of_mem_sphere z.1.1, mul_one,
              Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < (z.1.2 : ℝ) / 2)]
          have hhalf : 1 / 2 ≤ ‖(halfPoint y : ThreeSpace)‖ := by
            rw [hnorm]
            linarith
          have hle : ‖(halfPoint y : ThreeSpace)‖ ≤ 1 / 2 := by
            rw [halfPoint, norm_smul]
            norm_num
            linarith [norm_le_one_of_mem_closedBall y]
          have heq : ‖(halfPoint y : ThreeSpace)‖ = 1 / 2 := le_antisymm hle hhalf
          have hy1 : ‖(y : ThreeSpace)‖ = 1 := by
            rw [halfPoint, norm_smul] at heq
            norm_num at heq
            linarith [norm_le_one_of_mem_closedBall y]
          refine ⟨⟨y, Metric.mem_sphere.mpr ?_⟩, ?_⟩
          · rw [dist_eq_norm, sub_zero]
            exact hy1
          · simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
            rw [coreInclusionMap_boundary_true]
            rfl
      · rintro ⟨y, rfl⟩
        constructor
        · exact ⟨_, rfl⟩
        · simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
          rw [coreInclusionMap_boundary_true]
          refine halfPoint_inr_mem_range _ ?_
          rw [halfPoint, norm_smul]
          norm_num
          linarith [norm_le_one_of_mem_closedBall (sphereToThreeBall y)]
  cap_disjoint := by
    rintro ⟨⟨⟩, s⟩ ⟨⟨⟩, s'⟩ hne
    cases s <;> cases s'
    · exact absurd rfl hne
    · rw [Set.disjoint_left]
      rintro x ⟨y, hy⟩ ⟨y', hy'⟩
      rw [capMap_false_apply] at hy
      rw [capMap_true_apply] at hy'
      exact Sum.inl_ne_inr (hy.trans hy'.symm)
    · rw [Set.disjoint_left]
      rintro x ⟨y, hy⟩ ⟨y', hy'⟩
      rw [capMap_true_apply] at hy
      rw [capMap_false_apply] at hy'
      exact Sum.inr_ne_inl (hy.trans hy'.symm)
    · exact absurd rfl hne

def twoBallCutCap :
    CutCapTopology TubeDomain ThreeBall ThreeBall (ThreeBall ⊕ ThreeBall) where
  tubes := cylinderTubeSystem
  capping := twoBallCapping
  presentation := Homeomorph.refl _
  nontrivial := Or.inl ⟨PUnit.unit⟩

theorem twoBallCutCap_capRetained : twoBallCutCap.capRetained (PUnit.unit, false) := by
  intro y
  exact ⟨halfPoint y, rfl⟩

theorem twoBallCutCap_capDiscarded : twoBallCutCap.capDiscarded (PUnit.unit, true) := by
  intro y
  exact ⟨halfPoint y, rfl⟩

theorem twoBallCutCap_cap_retained_and_discarded :
    twoBallCutCap.capRetained (PUnit.unit, false) ∧
      twoBallCutCap.capDiscarded (PUnit.unit, true) :=
  ⟨twoBallCutCap_capRetained, twoBallCutCap_capDiscarded⟩

theorem twoBallCutCap_boundary_retained_and_discarded :
    (∀ z : Sphere 2, twoBallCutCap.tubes.coreBoundarySphere (PUnit.unit, false) z ∈
        twoBallCutCap.retainedCore) ∧
      (∀ z : Sphere 2, twoBallCutCap.tubes.coreBoundarySphere (PUnit.unit, true) z ∉
        twoBallCutCap.retainedCore) :=
  ⟨fun z => twoBallCutCap.capRetained_coreBoundarySphere_mem_retainedCore _
      twoBallCutCap_capRetained z,
    fun z => twoBallCutCap.capDiscarded_coreBoundarySphere_not_mem_retainedCore _
      twoBallCutCap_capDiscarded z⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
