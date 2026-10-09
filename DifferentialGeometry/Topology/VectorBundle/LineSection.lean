import DifferentialGeometry.Bundle.OrthonormalFrame
import DifferentialGeometry.Topology.VectorBundle.FrameTrivialization
import DifferentialGeometry.Topology.VectorBundle.ClosedDiscCompact
import DifferentialGeometry.Topology.VectorBundle.UnitOrientation
import Mathlib.Topology.Connected.Clopen

/-!
# Smooth unit sections in rank-one bundles

A continuous unit section of an actual smooth rank-one Riemannian bundle is smooth. Locally it
agrees with the smooth unit frame through its value, since the other unit vector has negative
inner product. This supplies the regularity step in LFR51-T1 without a supplied smooth frame.
-/

set_option autoImplicit false

noncomputable section

open Bundle Module Filter Set
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Topology.VectorBundle

section Continuous

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {B : Type*} [TopologicalSpace B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]

private theorem sphere_projection_open :
    IsOpenMap (fun z : {z : TotalSpace F V // ‖z.2‖ = 1} => z.val.proj) := by
  intro O hO
  apply isOpen_iff_mem_nhds.mpr
  rintro b ⟨z, hz, rfl⟩
  have hv : Orthonormal ℝ (fun i : Fin 1 => z.val.2) :=
    orthonormal_subsingleton_iff.mpr (fun i => z.property)
  obtain ⟨U, hU, hb, e, he, hon, heq⟩ :=
    exists_continuous_orthonormal_sections (F := F) (V := V) z.val.proj
      (fun i : Fin 1 => z.val.2) hv
  let es : U → {z : TotalSpace F V // ‖z.2‖ = 1} :=
    fun x => ⟨⟨x.val, e 0 x.val⟩, (hon x.val x.property).norm_eq_one 0⟩
  have hes : Continuous es :=
    (continuousOn_iff_continuous_domRestrict.mp (he 0)).subtype_mk
      (fun x => (hon x.val x.property).norm_eq_one 0)
  have hbase : IsOpen (Subtype.val '' (es ⁻¹' O)) :=
    hU.isOpenMap_subtype_val (es ⁻¹' O) (hO.preimage hes)
  have hx : z.val.proj ∈ Subtype.val '' (es ⁻¹' O) := by
    refine ⟨⟨z.val.proj, hb⟩, ?_, rfl⟩
    have hpoint : es ⟨z.val.proj, hb⟩ = z := by
      apply Subtype.ext
      change (⟨z.val.proj, e 0 z.val.proj⟩ : TotalSpace F V) = z.val
      rw [heq 0]
    rw [mem_preimage, hpoint]
    exact hz
  apply mem_of_superset (hbase.mem_nhds hx)
  rintro x ⟨u, hu, rfl⟩
  exact ⟨es u, hu, rfl⟩

variable [FiniteDimensional ℝ F] [CompactSpace B] [T2Space B] [ConnectedSpace B]

private theorem continuous_unit_section_of_not_preconnected (hF : finrank ℝ F = 1)
    (hn : ¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1}) :
    ∃ s : ∀ b, V b, Continuous (fun b => (⟨b, s b⟩ : TotalSpace F V)) ∧
      ∀ b, ‖s b‖ = 1 := by
  classical
  let S := {z : TotalSpace F V // ‖z.2‖ = 1}
  let p : S → B := fun z => z.val.proj
  let τ : S → S := fun z => ⟨⟨z.val.proj, -z.val.2⟩, by simpa using z.property⟩
  have hpc : Continuous p := (FiberBundle.continuous_proj F V).comp continuous_subtype_val
  have hpo : IsOpenMap p := sphere_projection_open
  let sphereCompact : CompactSpace S :=
    isCompact_iff_compactSpace.mp (isCompact_sphereBundle (F := F) (V := V) 1)
  have hclosed : IsClosedMap p := hpc.isClosedMap
  have hnot : ¬ PreconnectedSpace S := fun h => hn (isPreconnected_iff_preconnectedSpace.mpr h)
  have hnc : ¬ ∀ K : Set S, IsClopen K → K = ∅ ∨ K = univ :=
    fun h => hnot (preconnectedSpace_iff_clopen.mpr h)
  push Not at hnc
  obtain ⟨K, hK, hne, hnu⟩ := hnc
  have hsurj (A : Set S) (hA : IsClopen A) (ha : A.Nonempty) : p '' A = univ := by
    have hc : IsClopen (p '' A) := ⟨hclosed A hA.isClosed, hpo A hA.isOpen⟩
    exact (isClopen_iff.mp hc).resolve_left (ha.image p).ne_empty
  have hfiber (x y : S) (h : p y = p x) : y = x ∨ y = τ x := by
    rcases x with ⟨⟨b, u⟩, hu⟩
    rcases y with ⟨⟨a, v⟩, hv⟩
    change a = b at h
    subst a
    have hr : finrank ℝ (V b) = 1 :=
      (RankOneQuotient.finrank_fiber (F := F) (V := V) b).trans hF
    rcases RankOneQuotient.eq_or_eq_neg_of_finrank_eq_one hr hu hv with hh | hh
    · left
      change v = u at hh
      subst v
      rfl
    · right
      change v = -u at hh
      subst v
      rfl
  have hinj : Function.Injective (fun x : K => p x.val) := by
    intro x y hxy
    obtain ⟨z, hz, hzp⟩ := (hsurj Kᶜ hK.compl (Set.nonempty_compl.mpr hnu)).symm ▸
      (mem_univ (p x.val))
    have hzx : z ≠ x.val := fun hh => hz (hh ▸ x.property)
    have hzτ : z = τ x.val := (hfiber x.val z hzp).resolve_left hzx
    rcases hfiber x.val y.val hxy.symm with hy | hy
    · exact Subtype.ext hy.symm
    · exact False.elim (hz (by rw [hzτ, ← hy]; exact y.property))
  have hs : Function.Surjective (fun x : K => p x.val) := by
    intro b
    obtain ⟨x, hx, hpx⟩ := (hsurj K hK hne).symm ▸
      (mem_univ b)
    exact ⟨⟨x, hx⟩, hpx⟩
  let hp : IsHomeomorph (fun x : K => p x.val) :=
    ⟨hpc.comp continuous_subtype_val, hpo.comp hK.isOpen.isOpenMap_subtype_val, hinj, hs⟩
  let e := hp.homeomorph (fun x : K => p x.val)
  let s : B → S := fun b => (e.symm b).val
  have hsproj (b : B) : (s b).val.proj = b := e.apply_symm_apply b
  let σ : ∀ b, V b := fun b => cast (congrArg V (hsproj b)) (s b).val.2
  have hsval (b : B) : (⟨b, σ b⟩ : TotalSpace F V) = (s b).val :=
    TotalSpace.mk_cast (hsproj b) (s b).val.2
  refine ⟨σ, ?_, ?_⟩
  · have hc : Continuous (fun b => (s b).val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp e.symm.continuous)
    exact hc.congr (fun b => (hsval b).symm)
  · intro b
    change ‖(⟨b, σ b⟩ : TotalSpace F V).2‖ = 1
    rw [hsval]
    exact (s b).property

end Continuous

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V IB] [IsContMDiffRiemannianBundle IB ∞ F V]

omit [FiniteDimensional ℝ F] in
theorem contMDiff_unit_section (hF : finrank ℝ F = 1) (s : ∀ b, V b)
    (hs : Continuous (fun b => (⟨b, s b⟩ : TotalSpace F V))) (hu : ∀ b, ‖s b‖ = 1) :
    ContMDiff IB (IB.prod 𝓘(ℝ, F)) ∞ (fun b => (⟨b, s b⟩ : TotalSpace F V)) := by
  let bundleContinuousMetric : IsContinuousRiemannianBundle F V := by
    obtain ⟨g, hg, heq⟩ := IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := IB) (n := ∞) (F := F) (E := V)
    exact ⟨g, hg.continuous, heq⟩
  intro b
  have hv : Orthonormal ℝ (fun i : Fin 1 => s b) :=
    orthonormal_subsingleton_iff.mpr (fun i => hu b)
  obtain ⟨U, hU, hb, e, he, hon, heq⟩ :=
    exists_contMDiff_orthonormal_sections (I := IB) (F := F) (V := V) (m := ∞) b
      (fun i : Fin 1 => s b) hv
  have hsm := (he 0).contMDiffAt (hU.mem_nhds hb)
  have hinner : ContinuousAt (fun x => ⟪s x, e 0 x⟫_ℝ) b :=
    hs.continuousAt.inner_bundle hsm.continuousAt
  have hpos : 0 < ⟪s b, e 0 b⟫_ℝ := by
    rw [heq 0, real_inner_self_eq_norm_sq, hu, one_pow]
    exact zero_lt_one
  apply hsm.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hb, hinner.eventually (lt_mem_nhds hpos)] with x hx hp
  have hex : ‖e 0 x‖ = 1 := (hon x hx).norm_eq_one 0
  have hrank : finrank ℝ (V x) = 1 := (finrank_fiber_eq (F := F) (V := V) x).trans hF
  rcases RankOneQuotient.eq_or_eq_neg_of_finrank_eq_one hrank hex (hu x) with hh | hh
  · exact congrArg (fun v => (⟨x, v⟩ : TotalSpace F V)) hh
  · have hn : ⟪s x, e 0 x⟫_ℝ = -1 := by
      rw [hh, inner_neg_left, real_inner_self_eq_norm_sq, hex, one_pow]
    rw [hn] at hp
    norm_num at hp

theorem exists_smooth_unit_section_of_sphere_not_preconnected
    [CompactSpace B] [T2Space B] [ConnectedSpace B] (hF : finrank ℝ F = 1)
    (hn : ¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1}) :
    ∃ s : ∀ b, V b,
      ContMDiff IB (IB.prod 𝓘(ℝ, F)) ∞ (fun b => (⟨b, s b⟩ : TotalSpace F V)) ∧
      ∀ b, ‖s b‖ = 1 := by
  let bundleContinuousMetric : IsContinuousRiemannianBundle F V := by
    obtain ⟨g, hg, heq⟩ := IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := IB) (n := ∞) (F := F) (E := V)
    exact ⟨g, hg.continuous, heq⟩
  obtain ⟨s, hs, hu⟩ := continuous_unit_section_of_not_preconnected hF hn
  exact ⟨s, contMDiff_unit_section hF s hs hu, hu⟩

theorem exists_line_trivialization_of_sphere_not_preconnected
    [CompactSpace B] [T2Space B] [ConnectedSpace B] (hF : finrank ℝ F = 1)
    (hn : ¬ IsPreconnected {z : TotalSpace F V | ‖z.2‖ = 1}) :
    ∃ s : ∀ b, V b,
      ∃ Φ : TotalSpace (EuclideanSpace ℝ (Fin 1))
        (Trivial B (EuclideanSpace ℝ (Fin 1))) ≃ₘ⟮
          IB.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)), IB.prod 𝓘(ℝ, F)⟯ TotalSpace F V,
        (∀ z, Φ z = ⟨z.proj, z.2 0 • s z.proj⟩) ∧
        (∀ z, ‖(Φ z).2‖ = ‖z.2‖) ∧ ∀ b, ‖s b‖ = 1 := by
  obtain ⟨s, hs, hu⟩ := exists_smooth_unit_section_of_sphere_not_preconnected (IB := IB) hF hn
  have hon (b : B) : Orthonormal ℝ (fun i : Fin 1 => s b) :=
    orthonormal_subsingleton_iff.mpr (fun i => hu b)
  obtain ⟨Φ, hΦ, hnorm⟩ := exists_normPreserving_trivialization_of_orthonormal
    (IB := IB) hF (fun i : Fin 1 => s) (fun i => hs) hon
  refine ⟨s, Φ, ?_, hnorm, hu⟩
  intro z
  simpa only [Fin.sum_univ_one] using hΦ z.proj z.2

end DifferentialGeometry.Topology.VectorBundle
