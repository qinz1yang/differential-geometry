import DifferentialGeometry.Topology.Manifold.OneManifold.HalfChartAtlasBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.ImmersedParamBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.IntervalOrCircle
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential

/-!
# Compact smooth one-dimensional domains: finitely many arcs AND loops (lane B-BCF134; D74-9, K0)

Review 74, D74-9: the shared `K₃` kernel outputs a compact smooth one-dimensional domain of the base
`Bs` WITH its circle components and finite component parametrizations; the closed route keeps whole
circle components (ZSP04), the boundary route excludes them in its own binding
(`no_closed_base_component_BCF`), never in the kernel.

* `SmoothCompactOneDomain_BCF Bs`: a carrier `⊆ Bs`, finitely many smooth regular embedded arcs
  `[0, 1] → H` and finitely many smooth regular `1`-periodic loops, pairwise disjoint, covering the
  carrier; arc interiors and loop ranges are relatively open in `Bs`; the relative frontier of the
  carrier in `Bs` is exactly the set of arc endpoints.
* `exists_smoothCompactOneDomain_BCF`: a COMPACT `T` with a half-chart cover
  (`HalfChartCover_BCF Bs T`) is the carrier of such a domain. Route: the half charts make `↥T` a
  compact smooth one-manifold with boundary (`HalfChartAtlasBCF`); the tree's classification
  `finite_connectedComponents_and_Icc_or_circle` gives finitely many components, each diffeomorphic
  to `[0, 1]` or to the circle; the inclusion into `H` is an injective immersion
  (`mfderiv_val_injective_BCF`), so the parametrizations are smooth and regular
  (`ImmersedParamBCF`); interior points of the manifold are the relative interior points of `T` in
  `Bs` (`isInteriorPoint_iff_BCF`).
* `segmentDomain_BCF`: the inhabitant `[0, 1] ⊆ ℝ` (one arc, no loop).
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **A compact smooth one-dimensional domain of `Bs`** with finitely many arc AND loop components. -/
structure SmoothCompactOneDomain_BCF (Bs : Set H) where
  /-- The carrier. -/
  carrier : Set H
  /-- The number of arc (interval) components. -/
  m : ℕ
  /-- The number of loop (circle) components. -/
  l : ℕ
  /-- The arcs, parametrized on `[0, 1]`. -/
  arc : Fin m → ℝ → H
  /-- The loops, `1`-periodic. -/
  loop : Fin l → ℝ → H
  arc_smooth : ∀ k, ContDiffOn ℝ ∞ (arc k) (Icc 0 1)
  arc_injOn : ∀ k, InjOn (arc k) (Icc 0 1)
  arc_deriv : ∀ k, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (arc k) (Icc 0 1) t ≠ 0
  loop_smooth : ∀ j, ContDiff ℝ ∞ (loop j)
  loop_periodic : ∀ j, Periodic (loop j) 1
  loop_injOn : ∀ j, InjOn (loop j) (Ico 0 1)
  loop_deriv : ∀ j t, deriv (loop j) t ≠ 0
  arc_disjoint : Pairwise (Disjoint on fun k => arc k '' Icc 0 1)
  loop_disjoint : Pairwise (Disjoint on fun j => range (loop j))
  arc_loop_disjoint : ∀ k j, Disjoint (arc k '' Icc 0 1) (range (loop j))
  carrier_eq : carrier = (⋃ k, arc k '' Icc 0 1) ∪ ⋃ j, range (loop j)
  subset_base : carrier ⊆ Bs
  arc_interior_relOpen : ∀ k, ∃ G : Set H, IsOpen G ∧ G ∩ Bs = arc k '' Ioo 0 1
  loop_relOpen : ∀ j, ∃ G : Set H, IsOpen G ∧ G ∩ Bs = range (loop j)
  relFrontier_eq : carrier \ Subtype.val '' interior (Subtype.val ⁻¹' carrier : Set Bs) =
    ⋃ k, ({arc k 0, arc k 1} : Set H)

namespace SmoothCompactOneDomain_BCF

variable {Bs : Set H} (D : SmoothCompactOneDomain_BCF Bs)

/-- The carrier is compact. -/
theorem isCompact_carrier_BCF : IsCompact D.carrier := by
  rw [D.carrier_eq]
  refine (isCompact_iUnion fun k => isCompact_Icc.image_of_continuousOn
    (D.arc_smooth k).continuousOn).union (isCompact_iUnion fun j => ?_)
  rw [← (D.loop_periodic j).image_Icc one_pos 0]
  exact isCompact_Icc.image (D.loop_smooth j).continuous

/-- Arc endpoints are distinct. -/
theorem arc_zero_ne_one_BCF (k : Fin D.m) : D.arc k 0 ≠ D.arc k 1 := fun h =>
  zero_ne_one (D.arc_injOn k (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) h)

end SmoothCompactOneDomain_BCF

omit [NormedSpace ℝ H] in
/-- An open subset `Z` of `T` inside the relative interior of `T` in `Bs` is relatively open in `Bs`. -/
theorem relOpen_of_subset_relInterior_BCF {Bs T : Set H} {Z : Set T} (hZ : IsOpen Z)
    (hrel : Subtype.val '' Z ⊆ Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs)) :
    ∃ G : Set H, IsOpen G ∧ G ∩ Bs = Subtype.val '' Z := by
  obtain ⟨G₁, hG₁, hG₁Z⟩ := isOpen_induced_iff.mp hZ
  have hloc : ∀ z ∈ Subtype.val '' Z, ∃ O : Set H, IsOpen O ∧ z ∈ O ∧ O ∩ Bs ⊆ T := fun z hz =>
    (mem_image_interior_preimage_val_iff.mp (hrel hz)).2
  choose O hO hzO hOT using hloc
  refine ⟨G₁ ∩ ⋃ z, ⋃ hz : z ∈ Subtype.val '' Z, O z hz,
    hG₁.inter (isOpen_iUnion fun z => isOpen_iUnion fun hz => hO z hz), ?_⟩
  ext w
  constructor
  · rintro ⟨⟨hwG, hwO⟩, hwB⟩
    obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp hwO
    have hwT : w ∈ T := hOT z hz ⟨hwz, hwB⟩
    have : (⟨w, hwT⟩ : T) ∈ Z := hG₁Z ▸ hwG
    exact ⟨⟨w, hwT⟩, this, rfl⟩
  · rintro ⟨⟨w', hw'T⟩, hw'Z, rfl⟩
    have hw : w' ∈ Subtype.val '' Z := ⟨⟨w', hw'T⟩, hw'Z, rfl⟩
    refine ⟨⟨?_, mem_iUnion₂.mpr ⟨w', hw, hzO w' hw⟩⟩,
      (mem_image_interior_preimage_val_iff.mp (hrel hw)).1⟩
    have : (⟨w', hw'T⟩ : T) ∈ Subtype.val ⁻¹' G₁ := hG₁Z.symm ▸ hw'Z
    exact this

section Components

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) ∞ M]

/-- The interior points of `[0, 1]` (as a manifold with boundary) are the points of `(0, 1)`. -/
theorem interior_Icc_BCF : (𝓡∂ 1).interior (Icc (0 : ℝ) 1) = {p | p.val ∈ Ioo (0 : ℝ) 1} := by
  ext p
  constructor
  · intro hp
    have hpb : p ∉ (𝓡∂ 1).boundary (Icc (0 : ℝ) 1) := fun hb =>
      (𝓡∂ 1).disjoint_interior_boundary.ne_of_mem hp hb rfl
    rw [boundary_Icc] at hpb
    have h0 : p ≠ ⊥ := fun h => hpb (Or.inl h)
    have h1 : p ≠ ⊤ := fun h => hpb (Or.inr h)
    refine ⟨lt_of_le_of_ne p.2.1 fun h => h0 (Subtype.ext h.symm),
      lt_of_le_of_ne p.2.2 fun h => h1 (Subtype.ext h)⟩
  · intro hp
    exact Icc_isInteriorPoint_interior hp

/-- A component diffeomorphic to the circle has no boundary point. -/
theorem boundary_eq_empty_of_circle_BCF {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 1) N] (ψ : Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ N) :
    (𝓡∂ 1).boundary N = ∅ := by
  rw [← ψ.image_boundary (by simp), ModelWithCorners.Boundaryless.boundary_eq_empty, image_empty]

/-- Under a diffeomorphism `[0, 1] ≃ N`, the boundary points of `N` are the images of `0` and `1`. -/
theorem mem_boundary_iff_of_Icc_BCF {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 1) N]
    (φ : Icc (0 : ℝ) 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ N) {p : N} :
    p ∈ (𝓡∂ 1).boundary N ↔ φ.symm p = ⊥ ∨ φ.symm p = ⊤ := by
  rw [← φ.image_boundary (by simp), boundary_Icc]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa using hs
  · intro h
    exact ⟨φ.symm p, h, by simp⟩

/-- Under a diffeomorphism `[0, 1] ≃ N`, the interior points of `N` are the images of `(0, 1)`. -/
theorem mem_interior_iff_of_Icc_BCF {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 1) N]
    (φ : Icc (0 : ℝ) 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ N) {p : N} :
    p ∈ (𝓡∂ 1).interior N ↔ (φ.symm p).val ∈ Ioo (0 : ℝ) 1 := by
  rw [← φ.image_interior (by simp), interior_Icc_BCF]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa using hs
  · intro h
    exact ⟨φ.symm p, h, by simp⟩

/-- `projIcc 0 1 0 = ⊥` and `projIcc 0 1 1 = ⊤`. -/
theorem projIcc_zero_one_BCF :
    projIcc (0 : ℝ) 1 zero_le_one 0 = ⊥ ∧ projIcc (0 : ℝ) 1 zero_le_one 1 = ⊤ :=
  ⟨Subtype.ext (by simp), Subtype.ext (by simp)⟩

end Components

/-- **The core of the shared `K₃` kernel (D74-9, K0)**: a compact `T` with a half-chart cover is the
carrier of a compact smooth one-dimensional domain of `Bs`, with interval AND circle components. -/
theorem exists_smoothCompactOneDomain_BCF {Bs T : Set H} (A : HalfChartCover_BCF Bs T)
    (hT : IsCompact T) : ∃ D : SmoothCompactOneDomain_BCF Bs, D.carrier = T := by
  classical
  let _ : ChartedSpace (EuclideanHalfSpace 1) T := A.chartedSpace_BCF
  have hA : ∀ e ∈ atlas (EuclideanHalfSpace 1) T, ∃ (d : HalfChart_BCF Bs T) (y₀ : T),
      e = d.toChart y₀ := A.mem_atlas_BCF
  have : IsManifold (𝓡∂ 1) ∞ T := isManifold_of_halfCharts_BCF hA
  have : CompactSpace T := isCompact_iff_compactSpace.mp hT
  obtain ⟨hfin, hcls⟩ := Manifold.OneManifold.finite_connectedComponents_and_Icc_or_circle (M := T)
  have hsurj : Surjective (ConnectedComponents.mk : T → ConnectedComponents T) :=
    ConnectedComponents.surjective_coe
  choose rep hrep using hsurj
  set U : ConnectedComponents T → TopologicalSpace.Opens T :=
    fun c => Manifold.OneManifold.componentOpens (rep c) with hU
  have memU_iff : ∀ (c : ConnectedComponents T) (y : T), y ∈ U c ↔
      (y : ConnectedComponents T) = c := fun c y => by
    change y ∈ connectedComponent (rep c) ↔ _
    rw [← ConnectedComponents.coe_eq_coe' (α := T), hrep c]
  have memU : ∀ y : T, y ∈ U (y : ConnectedComponents T) := fun y => (memU_iff _ y).mpr rfl
  -- the inclusion of a component into `H` is an injective immersion
  have hval := contMDiff_val_BCF hA
  have hιs : ∀ c, ContMDiff (𝓡∂ 1) 𝓘(ℝ, H) ∞ (fun p : U c => ((p : T) : H)) := fun c =>
    hval.comp contMDiff_subtype_val
  have hιi : ∀ c, Injective (fun p : U c => ((p : T) : H)) := fun c p q h =>
    Subtype.ext (Subtype.ext h)
  have hιd : ∀ c (p : U c), Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, H) (fun p : U c => ((p : T) : H)) p) :=
    fun c p => by
      have h := Manifold.mfderiv_restrict_open (𝓡∂ 1) 𝓘(ℝ, H) (U c) (Subtype.val : T → H) hval p
      change Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ, H) ((Subtype.val : T → H) ∘ (Subtype.val : U c → T)) p)
      rw [h]
      exact mfderiv_val_injective_BCF hA p.val
  -- interior points of `T` are relative interior points of `T` in `Bs`
  have hrelInt : ∀ y : T, y ∈ (𝓡∂ 1).interior T →
      (y : H) ∈ Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs) := fun y hy =>
    (isInteriorPoint_iff_BCF hA).mp hy
  -- disjointness of components
  have hdisjU : ∀ c c' : ConnectedComponents T, c ≠ c' →
      Disjoint (Subtype.val '' (U c : Set T)) (Subtype.val '' (U c' : Set T)) := by
    intro c c' hcc'
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
    have hy'y : y' = y := Subtype.ext hyy'
    subst hy'y
    exact hcc' (((memU_iff c y').mp hy).symm.trans ((memU_iff c' y').mp hy'))
  -- arc and loop components
  set P : ConnectedComponents T → Prop :=
    fun c => Nonempty (U c ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) with hP
  have hcirc : ∀ c, ¬ P c → Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ U c) := fun c h =>
    (hcls (rep c)).resolve_left h
  have : Finite (ConnectedComponents T) := hfin
  set eA := (Finite.equivFin {c // P c}).symm with heA
  set eL := (Finite.equivFin {c // ¬ P c}).symm with heL
  let φ : ∀ c : {c // P c}, Icc (0 : ℝ) 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ U c.1 := fun c => (Classical.choice c.2).symm
  let ψ : ∀ c : {c // ¬ P c}, Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ U c.1 := fun c => Classical.choice (hcirc c.1 c.2)
  let arc : Fin (Nat.card {c // P c}) → ℝ → H := fun k t =>
    (((φ (eA k)) (projIcc 0 1 zero_le_one t) : T) : H)
  let loop : Fin (Nat.card {c // ¬ P c}) → ℝ → H := fun j t =>
    (((ψ (eL j)) (AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ))) : T) : H)
  -- images
  have harc_img : ∀ k, arc k '' Icc 0 1 = Subtype.val '' (U (eA k).1 : Set T) := by
    intro k
    ext y
    constructor
    · rintro ⟨t, -, rfl⟩
      exact ⟨((φ (eA k)) (projIcc 0 1 zero_le_one t) : T), ((φ (eA k)) _).2, rfl⟩
    · rintro ⟨y', hy', rfl⟩
      refine ⟨((φ (eA k)).symm ⟨y', hy'⟩).val, ((φ (eA k)).symm ⟨y', hy'⟩).2, ?_⟩
      change (((φ (eA k)) (projIcc 0 1 zero_le_one ((φ (eA k)).symm ⟨y', hy'⟩).val) : T) : H) = y'
      rw [projIcc_val, Diffeomorph.apply_symm_apply]
  have harc_ioo : ∀ k, arc k '' Ioo 0 1 =
      Subtype.val '' ((U (eA k).1 : Set T) ∩ (𝓡∂ 1).interior T) := by
    intro k
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hp := (mem_interior_iff_of_Icc_BCF (φ (eA k))
        (p := (φ (eA k)) (projIcc 0 1 zero_le_one t))).mpr
        (by rw [Diffeomorph.symm_apply_apply, projIcc_of_mem _ (Ioo_subset_Icc_self ht)]; exact ht)
      rw [ModelWithCorners.interior_open] at hp
      exact ⟨((φ (eA k)) (projIcc 0 1 zero_le_one t) : T), ⟨((φ (eA k)) _).2, hp⟩, rfl⟩
    · rintro ⟨y', ⟨hy'U, hy'I⟩, rfl⟩
      have hp : (⟨y', hy'U⟩ : U (eA k).1) ∈ (𝓡∂ 1).interior (U (eA k).1) := by
        rw [ModelWithCorners.interior_open]
        exact hy'I
      have ht := (mem_interior_iff_of_Icc_BCF (φ (eA k))).mp hp
      refine ⟨((φ (eA k)).symm ⟨y', hy'U⟩).val, ht, ?_⟩
      change (((φ (eA k)) (projIcc 0 1 zero_le_one ((φ (eA k)).symm ⟨y', hy'U⟩).val) : T) : H) = y'
      rw [projIcc_val, Diffeomorph.apply_symm_apply]
  have hloop_img : ∀ j, range (loop j) = Subtype.val '' (U (eL j).1 : Set T) := by
    intro j
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨((ψ (eL j)) (AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ))) : T),
        ((ψ (eL j)) _).2, rfl⟩
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective
        (AddCircle.diffeomorphCircle.symm ((ψ (eL j)).symm ⟨y', hy'⟩))
      refine ⟨t, ?_⟩
      change (((ψ (eL j)) (AddCircle.diffeomorphCircle ((t : ℝ) : AddCircle (1 : ℝ))) : T) : H) = y'
      have ht' : ((t : ℝ) : AddCircle (1 : ℝ)) =
          AddCircle.diffeomorphCircle.symm ((ψ (eL j)).symm ⟨y', hy'⟩) := ht
      rw [ht', Diffeomorph.apply_symm_apply, Diffeomorph.apply_symm_apply]
  have hloop_int : ∀ j, (U (eL j).1 : Set T) ⊆ (𝓡∂ 1).interior T := by
    intro j y hy
    have hb := boundary_eq_empty_of_circle_BCF (ψ (eL j))
    have hp : (⟨y, hy⟩ : U (eL j).1) ∈ (𝓡∂ 1).interior (U (eL j).1) := by
      rw [← (𝓡∂ 1).compl_boundary, hb]
      exact Set.notMem_empty _
    rw [ModelWithCorners.interior_open] at hp
    exact hp
  -- the relative frontier
  have hfront : T \ Subtype.val '' interior (Subtype.val ⁻¹' T : Set Bs) =
      ⋃ k, ({arc k 0, arc k 1} : Set H) := by
    ext y
    constructor
    · rintro ⟨hyT, hyI⟩
      set q : T := ⟨y, hyT⟩ with hq
      have hqb : q ∈ (𝓡∂ 1).boundary T := by
        rw [← (𝓡∂ 1).compl_interior]
        exact fun hqi => hyI (hrelInt q hqi)
      set c : ConnectedComponents T := (q : ConnectedComponents T) with hc
      by_cases hPc : P c
      · set k := eA.symm ⟨c, hPc⟩ with hk
        have hek : eA k = ⟨c, hPc⟩ := by rw [hk, Equiv.apply_symm_apply]
        have hpb : (⟨q, hek ▸ memU q⟩ : U (eA k).1) ∈ (𝓡∂ 1).boundary (U (eA k).1) := by
          rw [ModelWithCorners.boundary_open]
          exact hqb
        rcases (mem_boundary_iff_of_Icc_BCF (φ (eA k))).mp hpb with h0 | h1
        · refine mem_iUnion.mpr ⟨k, Or.inl ?_⟩
          change y = (((φ (eA k)) (projIcc 0 1 zero_le_one 0) : T) : H)
          rw [projIcc_zero_one_BCF.1, ← h0, Diffeomorph.apply_symm_apply]
        · refine mem_iUnion.mpr ⟨k, Or.inr ?_⟩
          change y = (((φ (eA k)) (projIcc 0 1 zero_le_one 1) : T) : H)
          rw [projIcc_zero_one_BCF.2, ← h1, Diffeomorph.apply_symm_apply]
      · set j := eL.symm ⟨c, hPc⟩ with hj
        have hej : eL j = ⟨c, hPc⟩ := by rw [hj, Equiv.apply_symm_apply]
        have hpb : (⟨q, hej ▸ memU q⟩ : U (eL j).1) ∈ (𝓡∂ 1).boundary (U (eL j).1) := by
          rw [ModelWithCorners.boundary_open]
          exact hqb
        rw [boundary_eq_empty_of_circle_BCF (ψ (eL j))] at hpb
        exact absurd hpb (Set.notMem_empty _)
    · intro hy
      obtain ⟨k, hk⟩ := mem_iUnion.mp hy
      have hend : ∃ s : Icc (0 : ℝ) 1, (s = ⊥ ∨ s = ⊤) ∧ y = (((φ (eA k)) s : T) : H) := by
        rcases hk with rfl | rfl
        · exact ⟨⊥, Or.inl rfl, by
            change (((φ (eA k)) (projIcc 0 1 zero_le_one 0) : T) : H) = _
            rw [projIcc_zero_one_BCF.1]⟩
        · exact ⟨⊤, Or.inr rfl, by
            change (((φ (eA k)) (projIcc 0 1 zero_le_one 1) : T) : H) = _
            rw [projIcc_zero_one_BCF.2]⟩
      obtain ⟨s, hs, rfl⟩ := hend
      have hpb : (φ (eA k)) s ∈ (𝓡∂ 1).boundary (U (eA k).1) :=
        (mem_boundary_iff_of_Icc_BCF (φ (eA k))).mpr (by rw [Diffeomorph.symm_apply_apply]; exact hs)
      rw [ModelWithCorners.boundary_open] at hpb
      refine ⟨((φ (eA k)) s : T).2, fun hrel => ?_⟩
      have hint := (isInteriorPoint_iff_BCF hA (y := ((φ (eA k)) s : T))).mpr hrel
      exact (𝓡∂ 1).disjoint_interior_boundary.ne_of_mem hint hpb rfl
  -- the carrier
  have hcarrier : T = (⋃ k, arc k '' Icc 0 1) ∪ ⋃ j, range (loop j) := by
    ext y
    constructor
    · intro hyT
      set q : T := ⟨y, hyT⟩
      by_cases hPc : P (q : ConnectedComponents T)
      · refine Or.inl (mem_iUnion.mpr ⟨eA.symm ⟨_, hPc⟩, ?_⟩)
        rw [harc_img, Equiv.apply_symm_apply]
        exact ⟨q, memU q, rfl⟩
      · refine Or.inr (mem_iUnion.mpr ⟨eL.symm ⟨_, hPc⟩, ?_⟩)
        rw [hloop_img, Equiv.apply_symm_apply]
        exact ⟨q, memU q, rfl⟩
    · rintro (hy | hy)
      · obtain ⟨k, t, -, rfl⟩ := mem_iUnion.mp hy
        exact ((φ (eA k)) (projIcc 0 1 zero_le_one t) : T).2
      · obtain ⟨j, t, rfl⟩ := mem_iUnion.mp hy
        exact ((ψ (eL j)) (AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ))) : T).2
  refine ⟨{
    carrier := T
    m := Nat.card {c // P c}
    l := Nat.card {c // ¬ P c}
    arc := arc
    loop := loop
    arc_smooth := fun k => arc_contDiffOn_BCF _ (φ (eA k)) (hιs _)
    arc_injOn := fun k => arc_injOn_BCF _ (φ (eA k)) (hιi _)
    arc_deriv := fun k t ht => arc_derivWithin_ne_zero_BCF _ (φ (eA k)) (hιs _) (hιd _) ht
    loop_smooth := fun j => loop_contDiff_BCF _ (ψ (eL j)) (hιs _)
    loop_periodic := fun j => loop_periodic_BCF (fun p : U (eL j).1 => ((p : T) : H)) (ψ (eL j))
    loop_injOn := fun j => loop_injOn_BCF _ (ψ (eL j)) (hιi _)
    loop_deriv := fun j t => loop_deriv_ne_zero_BCF _ (ψ (eL j)) (hιs _) (hιd _) t
    arc_disjoint := fun k k' hkk' => by
      rw [Function.onFun, harc_img, harc_img]
      exact hdisjU _ _ fun h => hkk' (eA.injective (Subtype.ext h))
    loop_disjoint := fun j j' hjj' => by
      rw [Function.onFun, hloop_img, hloop_img]
      exact hdisjU _ _ fun h => hjj' (eL.injective (Subtype.ext h))
    arc_loop_disjoint := fun k j => by
      rw [harc_img, hloop_img]
      exact hdisjU _ _ fun h => (eL j).2 (h ▸ (eA k).2)
    carrier_eq := hcarrier
    subset_base := A.subset_base_BCF
    arc_interior_relOpen := fun k => by
      rw [harc_ioo]
      exact relOpen_of_subset_relInterior_BCF ((U (eA k).1).isOpen.inter
        ((𝓡∂ 1).isOpen_interior (n := ∞) (by simp)))
        (by rintro _ ⟨y, hy, rfl⟩; exact hrelInt y hy.2)
    loop_relOpen := fun j => by
      rw [hloop_img]
      exact relOpen_of_subset_relInterior_BCF (U (eL j).1).isOpen
        (by rintro _ ⟨y, hy, rfl⟩; exact hrelInt y (hloop_int j hy))
    relFrontier_eq := hfront }, rfl⟩

end DifferentialGeometry.Topology
