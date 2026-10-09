import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeBaseAtlasEIM
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base
import DifferentialGeometry.Topology.Manifold.OneManifold.IntervalOrCircle
import DifferentialGeometry.Topology.Manifold.OneManifold.SmoothCompactOneDomainBCF
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# E2: the finite interval / circle components of a compact smooth domain (lane S-EDGE-INT, G1)

Draft 74, package E2 (`finite_interval_circle_components74`). For a smooth one-manifold `Base`
(model `𝓡 1`, Hausdorff) and a compact set `C` with the local defining-function data of
`EdgeBundle.cbase_domain`, the connected components of `C` are finitely many arcs and loops:

* `exists_components_generic_EIM`: on ANY compact manifold-with-boundary structure on `↥C` for which
  the inclusion is an immersion and the boundary is the frontier, an equivalence
  `(Fin m ⊕ Fin l) ≃ ActualComponent C` (no empty component, no repetition), smooth embeddings
  `a i : [0, 1] → Base` and `c j : S¹ → Base` with range EXACTLY the component, and the endpoint
  equivalence `(Fin m × Bool) ≃ frontier C` with `ε (i, b) = a i (iccEnd b)`. Route: the tree's
  classification of compact one-manifolds (`finite_connectedComponents_and_Icc_or_circle`) applied
  to the components, diffeomorphisms transported along the open inclusions; the arcs are immersions
  because the tree's `IsImmersion.comp_of_smoothBoundary` composes the open inclusion with the
  immersion `↥C → Base` of `EdgeBaseAtlasEIM.lean`.
* `finite_interval_circle_components_EIM`: the hypotheses reduced to the data of
  `EdgeBundle.cbase_domain` (the half-line atlas of `EdgeBaseAtlasEIM.lean`).
* `EdgeBundle.finite_interval_circle_components_EIM`: the statement for the edge bundle (E2 row).

Template: `OneManifold/SmoothCompactOneDomainBCF.lean` (the same assembly for subsets of a normed
space).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Manifold.OneManifold

namespace GC.GraphManifold.Assembly.FC39P0

section Embeddings

variable {Base : Type*} [TopologicalSpace Base] [T2Space Base]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) Base] [IsManifold (𝓡 1) ∞ Base] {C : Set Base}
  [ChartedSpace (EuclideanHalfSpace 1) C] [IsManifold (𝓡∂ 1) ∞ C]

omit [IsManifold (𝓡 1) ∞ Base] in
/-- **An arc of the half-line manifold `↥C`**: the composite of a diffeomorphism `[0, 1] ≃ U` onto
an open piece of `↥C` with the inclusion into `Base` is a smooth embedding. -/
theorem isSmoothEmbedding_arc_EIM
    (hι : Manifold.IsImmersion (𝓡∂ 1) (𝓡 1) ∞ (Subtype.val : C → Base))
    (U : TopologicalSpace.Opens C) (φ : Icc (0 : ℝ) 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ U) :
    Manifold.IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ (fun t => (((φ t : U) : C) : Base)) := by
  have h1 : Manifold.IsImmersion (𝓡∂ 1) (𝓡∂ 1) ∞ (Subtype.val : U → C) :=
    Manifold.IsImmersion.of_opens U
  have h2 := Manifold.IsImmersion.comp_of_smoothBoundary h1 hι
  have h3 := Manifold.IsImmersion.precomp_diffeomorph h2 φ
  have hcont : Continuous (fun t => (((φ t : U) : C) : Base)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp φ.continuous)
  have hinj : Injective (fun t => (((φ t : U) : C) : Base)) := fun s t h =>
    φ.injective (Subtype.ext (Subtype.ext h))
  exact ⟨h3, (hcont.isClosedEmbedding hinj).isEmbedding⟩

/-- **A loop of the half-line manifold `↥C`**: the composite of a diffeomorphism `S¹ ≃ U` onto an
open piece of `↥C` with the inclusion into `Base` is a smooth embedding. -/
theorem isSmoothEmbedding_loop_EIM
    (hι : Manifold.IsImmersion (𝓡∂ 1) (𝓡 1) ∞ (Subtype.val : C → Base))
    (U : TopologicalSpace.Opens C) (ψ : Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ U) :
    Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (fun z => (((ψ z : U) : C) : Base)) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have h1 : Manifold.IsImmersion (𝓡∂ 1) (𝓡∂ 1) ∞ (Subtype.val : U → C) :=
    Manifold.IsImmersion.of_opens U
  have hιs : ContMDiff (𝓡∂ 1) (𝓡 1) ∞ (Subtype.val : C → Base) := hι.contMDiff
  have hvs : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ (Subtype.val : U → C) := contMDiff_subtype_val
  have hcomp : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z => (((ψ z : U) : C) : Base)) :=
    hιs.comp (hvs.comp ψ.contMDiff)
  have hinj : ∀ z, Injective (mfderiv (𝓡 1) (𝓡 1) (fun z => (((ψ z : U) : C) : Base)) z) := by
    intro z
    have hψd : MDifferentiableAt (𝓡 1) (𝓡∂ 1) ψ z := (ψ.contMDiff z).mdifferentiableAt hn
    have hvd : MDifferentiableAt (𝓡∂ 1) (𝓡∂ 1) (Subtype.val : U → C) (ψ z) :=
      (hvs (ψ z)).mdifferentiableAt hn
    have hιd : MDifferentiableAt (𝓡∂ 1) (𝓡 1) (Subtype.val : C → Base) ((ψ z : U) : C) :=
      (hιs _).mdifferentiableAt hn
    have hc : mfderiv (𝓡 1) (𝓡 1) (fun z => (((ψ z : U) : C) : Base)) z =
        (mfderiv (𝓡∂ 1) (𝓡 1) (Subtype.val : C → Base) ((ψ z : U) : C)).comp
          ((mfderiv (𝓡∂ 1) (𝓡∂ 1) (Subtype.val : U → C) (ψ z)).comp
            (mfderiv (𝓡 1) (𝓡∂ 1) ψ z)) := by
      have := mfderiv_comp z hιd (hvd.comp z hψd)
      rw [mfderiv_comp z hvd hψd] at this
      exact this
    have hinv : Injective (mfderiv (𝓡 1) (𝓡∂ 1) ψ z) := by
      obtain ⟨e, he⟩ := ψ.isInvertible_mfderiv (x := z) (by simp)
      rw [← he]
      exact e.injective
    rw [hc]
    exact (hι.mfderiv_injective hn _).comp ((h1.mfderiv_injective hn _).comp hinv)
  have himm := DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv hn hcomp hinj
  have hcont : Continuous (fun z => (((ψ z : U) : C) : Base)) := hcomp.continuous
  have hinj' : Injective (fun z => (((ψ z : U) : C) : Base)) := fun s t h =>
    ψ.injective (Subtype.ext (Subtype.ext h))
  exact ⟨himm, (hcont.isClosedEmbedding hinj').isEmbedding⟩

end Embeddings

section Components

theorem iccEnd_false_eq_bot_EIM : iccEnd false = (⊥ : Icc (0 : ℝ) 1) := by
  ext
  simp [iccEnd]

theorem iccEnd_true_eq_top_EIM : iccEnd true = (⊤ : Icc (0 : ℝ) 1) := by
  ext
  simp [iccEnd]

theorem iccEnd_injective_EIM : Injective iccEnd := by
  intro b b' h
  have h' := congrArg Subtype.val h
  cases b <;> cases b' <;> simp [iccEnd] at h' ⊢

variable {Base : Type*} [TopologicalSpace Base] [T2Space Base]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) Base] [IsManifold (𝓡 1) ∞ Base] {C : Set Base}
  [ChartedSpace (EuclideanHalfSpace 1) C] [IsManifold (𝓡∂ 1) ∞ C] [CompactSpace C]

/-- **Components of a compact half-line manifold inside a one-manifold** (generic form): the
components of `↥C` are finitely many arcs and loops, registered by an equivalence with the actual
components of `C`, with smooth embedded parametrizations and the endpoint equivalence. -/
theorem exists_components_generic_EIM
    (hι : Manifold.IsImmersion (𝓡∂ 1) (𝓡 1) ∞ (Subtype.val : C → Base))
    (hbd : ∀ y : C, (𝓡∂ 1).IsBoundaryPoint y ↔ (y : Base) ∈ frontier C) :
    ∃ (m l : ℕ) (e : (Fin m ⊕ Fin l) ≃ ActualComponent C) (a : Fin m → Icc (0 : ℝ) 1 → Base)
      (c : Fin l → Circle → Base) (ε : (Fin m × Bool) ≃ {x : Base // x ∈ frontier C}),
      (∀ i, Manifold.IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ (a i)) ∧
      (∀ i, range (a i) = (e (Sum.inl i)).1) ∧
      (∀ j, Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (c j)) ∧
      (∀ j, range (c j) = (e (Sum.inr j)).1) ∧
      ∀ i b, (ε (i, b)).1 = a i (iccEnd b) := by
  classical
  have hCclosed : IsClosed C := (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  obtain ⟨hfin, hcls⟩ := finite_connectedComponents_and_Icc_or_circle (M := C)
  have hsurj : Surjective (ConnectedComponents.mk : C → ConnectedComponents C) :=
    ConnectedComponents.surjective_coe
  choose rep hrep using hsurj
  let U : ConnectedComponents C → TopologicalSpace.Opens C := fun c => componentOpens (rep c)
  have memU_iff : ∀ (c : ConnectedComponents C) (y : C),
      y ∈ U c ↔ (y : ConnectedComponents C) = c := by
    intro c y
    change y ∈ connectedComponent (rep c) ↔ _
    rw [← ConnectedComponents.coe_eq_coe' (α := C), hrep c]
  have memU : ∀ y : C, y ∈ U (y : ConnectedComponents C) := fun y => (memU_iff _ y).mpr rfl
  have : Finite (ConnectedComponents C) := hfin
  -- the registry of components
  let toAC : ConnectedComponents C → ActualComponent C := fun c =>
    ⟨Subtype.val '' (U c : Set C), (rep c).1, (rep c).2, by
      rw [connectedComponentIn_eq_image (rep c).2]
      rfl⟩
  have hbij : Bijective toAC := by
    constructor
    · intro c c' h
      have h1 : Subtype.val '' (U c : Set C) = Subtype.val '' (U c' : Set C) :=
        congrArg Subtype.val h
      have h2 : (U c : Set C) = U c' := Subtype.val_injective.image_injective h1
      have h3 : rep c ∈ U c' := by
        have hm : rep c ∈ (U c : Set C) := (memU_iff c (rep c)).mpr (hrep c)
        rw [h2] at hm
        exact hm
      exact ((hrep c).symm.trans ((memU_iff c' (rep c)).mp h3))
    · rintro ⟨S, x, hx, hS⟩
      refine ⟨(⟨x, hx⟩ : C), Subtype.ext ?_⟩
      change Subtype.val '' (U (⟨x, hx⟩ : C) : Set C) = S
      rw [hS, connectedComponentIn_eq_image hx]
      congr 1
      change connectedComponent (rep (⟨x, hx⟩ : C)) = connectedComponent (⟨x, hx⟩ : C)
      rw [← ConnectedComponents.coe_eq_coe, hrep]
  -- arcs and loops
  let P : ConnectedComponents C → Prop := fun c =>
    Nonempty (U c ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1)
  have hcirc : ∀ c, ¬ P c → Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ U c) := fun c h =>
    (hcls (rep c)).resolve_left h
  let eA := (Finite.equivFin {c // P c}).symm
  let eL := (Finite.equivFin {c // ¬ P c}).symm
  let φ : ∀ c : {c // P c}, Icc (0 : ℝ) 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ U c.1 := fun c =>
    (Classical.choice c.2).symm
  let ψ : ∀ c : {c // ¬ P c}, Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ U c.1 := fun c =>
    Classical.choice (hcirc c.1 c.2)
  let a : Fin (Nat.card {c // P c}) → Icc (0 : ℝ) 1 → Base := fun k t =>
    (((φ (eA k)) t : U (eA k).1) : C).val
  let loop : Fin (Nat.card {c // ¬ P c}) → Circle → Base := fun j z =>
    (((ψ (eL j)) z : U (eL j).1) : C).val
  let e : (Fin (Nat.card {c // P c}) ⊕ Fin (Nat.card {c // ¬ P c})) ≃ ActualComponent C :=
    ((Equiv.sumCongr eA eL).trans (Equiv.sumCompl P)).trans (Equiv.ofBijective toAC hbij)
  have he_inl : ∀ k, (e (Sum.inl k)).1 = Subtype.val '' (U (eA k).1 : Set C) := fun k => rfl
  have he_inr : ∀ j, (e (Sum.inr j)).1 = Subtype.val '' (U (eL j).1 : Set C) := fun j => rfl
  have harc_range : ∀ k, range (a k) = (e (Sum.inl k)).1 := by
    intro k
    rw [he_inl]
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨((φ (eA k)) t : C), ((φ (eA k)) t).2, rfl⟩
    · rintro ⟨y', hy', rfl⟩
      exact ⟨(φ (eA k)).symm ⟨y', hy'⟩, by
        change ((((φ (eA k)) ((φ (eA k)).symm ⟨y', hy'⟩) : U (eA k).1) : C) : Base) = y'
        rw [Diffeomorph.apply_symm_apply]⟩
  have hloop_range : ∀ j, range (loop j) = (e (Sum.inr j)).1 := by
    intro j
    rw [he_inr]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨((ψ (eL j)) z : C), ((ψ (eL j)) z).2, rfl⟩
    · rintro ⟨y', hy', rfl⟩
      exact ⟨(ψ (eL j)).symm ⟨y', hy'⟩, by
        change ((((ψ (eL j)) ((ψ (eL j)).symm ⟨y', hy'⟩) : U (eL j).1) : C) : Base) = y'
        rw [Diffeomorph.apply_symm_apply]⟩
  -- the endpoints
  have harc_end : ∀ k (b : Bool), ((φ (eA k)).symm ((φ (eA k)) (iccEnd b))) = iccEnd b :=
    fun k b => Diffeomorph.symm_apply_apply _ _
  have hend_mem : ∀ k b, a k (iccEnd b) ∈ frontier C := by
    intro k b
    have hpb : (φ (eA k)) (iccEnd b) ∈ (𝓡∂ 1).boundary (U (eA k).1) := by
      rw [DifferentialGeometry.Topology.mem_boundary_iff_of_Icc_BCF (φ (eA k)),
        harc_end k b]
      cases b
      · exact Or.inl iccEnd_false_eq_bot_EIM
      · exact Or.inr iccEnd_true_eq_top_EIM
    rw [ModelWithCorners.boundary_open] at hpb
    exact (hbd _).mp hpb
  let f : Fin (Nat.card {c // P c}) × Bool → {x : Base // x ∈ frontier C} := fun p =>
    ⟨a p.1 (iccEnd p.2), hend_mem p.1 p.2⟩
  have hf_inj : Injective f := by
    rintro ⟨k, b⟩ ⟨k', b'⟩ h
    have h1 : a k (iccEnd b) = a k' (iccEnd b') :=
      congrArg (Subtype.val : {x : Base // x ∈ frontier C} → Base) h
    have hk : k = k' := by
      have hmem : a k (iccEnd b) ∈ (e (Sum.inl k)).1 := by
        rw [← harc_range]
        exact mem_range_self _
      have hmem' : a k (iccEnd b) ∈ (e (Sum.inl k')).1 := by
        rw [← harc_range, h1]
        exact mem_range_self _
      have := ActualComponent.eq_of_mem hmem hmem'
      exact Sum.inl_injective (e.injective this)
    subst hk
    have hemb := (isSmoothEmbedding_arc_EIM hι (U (eA k).1) (φ (eA k))).isEmbedding.injective h1
    exact Prod.ext rfl (iccEnd_injective_EIM hemb)
  have hf_surj : Surjective f := by
    rintro ⟨x, hx⟩
    have hxC : x ∈ C := hCclosed.frontier_subset hx
    set q : C := ⟨x, hxC⟩ with hq
    have hqb : (𝓡∂ 1).IsBoundaryPoint q := (hbd q).mpr hx
    by_cases hPc : P (q : ConnectedComponents C)
    · set k := eA.symm ⟨(q : ConnectedComponents C), hPc⟩ with hk
      have hek : (eA k).1 = (q : ConnectedComponents C) := by rw [hk, Equiv.apply_symm_apply]
      have hqU : q ∈ U (eA k).1 := by rw [hek]; exact memU q
      have hpb : (⟨q, hqU⟩ : U (eA k).1) ∈ (𝓡∂ 1).boundary (U (eA k).1) := by
        rw [ModelWithCorners.boundary_open]
        exact hqb
      rcases (DifferentialGeometry.Topology.mem_boundary_iff_of_Icc_BCF (φ (eA k))).mp hpb with
        h0 | h1
      · refine ⟨(k, false), Subtype.ext ?_⟩
        have hp : (φ (eA k)) ⊥ = ⟨q, hqU⟩ := by rw [← h0, Diffeomorph.apply_symm_apply]
        change ((((φ (eA k)) (iccEnd false) : U (eA k).1) : C) : Base) = x
        rw [iccEnd_false_eq_bot_EIM, hp]
      · refine ⟨(k, true), Subtype.ext ?_⟩
        have hp : (φ (eA k)) ⊤ = ⟨q, hqU⟩ := by rw [← h1, Diffeomorph.apply_symm_apply]
        change ((((φ (eA k)) (iccEnd true) : U (eA k).1) : C) : Base) = x
        rw [iccEnd_true_eq_top_EIM, hp]
    · exfalso
      obtain ⟨ψc⟩ := hcirc _ hPc
      have hpb : (⟨q, memU q⟩ : U (q : ConnectedComponents C)) ∈
          (𝓡∂ 1).boundary (U (q : ConnectedComponents C)) := by
        rw [ModelWithCorners.boundary_open]
        exact hqb
      rw [DifferentialGeometry.Topology.boundary_eq_empty_of_circle_BCF ψc] at hpb
      exact notMem_empty _ hpb
  exact ⟨_, _, e, a, loop, Equiv.ofBijective f ⟨hf_inj, hf_surj⟩,
    fun i => isSmoothEmbedding_arc_EIM hι _ (φ (eA i)), harc_range,
    fun j => isSmoothEmbedding_loop_EIM hι _ (ψ (eL j)), hloop_range, fun i b => rfl⟩

end Components

section Final

variable {Base : Type*} [TopologicalSpace Base] [T2Space Base]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) Base] [IsManifold (𝓡 1) ∞ Base] {C : Set Base}

/-- **E2 (`finite_interval_circle_components74`)**: the finite interval / circle components of a
compact smooth domain of a one-manifold, with smooth embedded parametrizations of range exactly
the component and the endpoint equivalence with the frontier. -/
theorem finite_interval_circle_components_EIM (hC : IsCompact C)
    (hdom : ∀ c ∈ frontier C, ∃ U : TopologicalSpace.Opens Base, c ∈ U ∧ ∃ φ : Base → ℝ,
      ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ φ U ∧ φ c = 0 ∧ mfderiv (𝓡 1) 𝓘(ℝ, ℝ) φ c ≠ 0 ∧
        C ∩ U = {c' | c' ∈ U ∧ 0 ≤ φ c'}) :
    ∃ (m l : ℕ) (e : (Fin m ⊕ Fin l) ≃ ActualComponent C) (a : Fin m → Icc (0 : ℝ) 1 → Base)
      (c : Fin l → Circle → Base) (ε : (Fin m × Bool) ≃ {x : Base // x ∈ frontier C}),
      (∀ i, Manifold.IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ (a i)) ∧
      (∀ i, range (a i) = (e (Sum.inl i)).1) ∧
      (∀ j, Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (c j)) ∧
      (∀ j, range (c j) = (e (Sum.inr j)).1) ∧
      ∀ i b, (ε (i, b)).1 = a i (iccEnd b) := by
  have hadapt : ∀ x : C, ∃ ψ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1)),
      ψ ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Base ∧ (x : Base) ∈ ψ.source ∧
        ∀ y ∈ ψ.source, (y ∈ C ↔ 0 ≤ ψ y 0) := fun x => exists_adaptedChart_EIM hdom x.2
  let _ := chartedSpace_EIM hadapt
  have _ : IsManifold (𝓡∂ 1) ∞ C := isManifold_EIM hadapt
  have _ : CompactSpace C := isCompact_iff_compactSpace.mp hC
  exact exists_components_generic_EIM (isImmersion_val_EIM hadapt)
    (fun y => isBoundaryPoint_iff_frontier_EIM hadapt)

end Final

section Bundle

universe u

variable {W : GC.Endpoint.CompactCarrier.{u}}

/-- **E2 for the edge bundle**: the interval and circle components of `C₂ = P.cbase` with their
smooth parametrizations, the component equivalence (`ActualComponent`) and the endpoint equivalence
(`EdgeEnd`). -/
theorem EdgeBundle.finite_interval_circle_components_EIM (P : EdgeBundle W) :
    ∃ (m l : ℕ) (e : (Fin m ⊕ Fin l) ≃ P.EdgeBaseComponent)
      (a : Fin m → Icc (0 : ℝ) 1 → P.Base) (c : Fin l → Circle → P.Base)
      (ε : (Fin m × Bool) ≃ P.EdgeEnd),
      (∀ i, Manifold.IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ (a i)) ∧
      (∀ i, range (a i) = (e (Sum.inl i)).1) ∧
      (∀ j, Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (c j)) ∧
      (∀ j, range (c j) = (e (Sum.inr j)).1) ∧
      ∀ i b, (ε (i, b)).1 = a i (iccEnd b) :=
  _root_.GC.GraphManifold.Assembly.FC39P0.finite_interval_circle_components_EIM P.cbase_compact
    P.cbase_domain

end Bundle

end GC.GraphManifold.Assembly.FC39P0
