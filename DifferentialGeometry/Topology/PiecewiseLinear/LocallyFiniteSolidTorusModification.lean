/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CommonCircleSolidTorusTransport
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSupportedModification
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusOpenNeighborhood

open Set Topology Filter Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isParametrizedSolidTorusTransport_of_image_eq_self
    {P : Geometry.SimplicialComplex ℝ E} (hPfin : P.faces.Finite)
    (hP : IsCombinatorialManifoldWithBoundary 3 P)
    {f : (Fin 3 → ℝ) × ℝ → E}
    (hsolid : IsTopologicalSolidTorus P.space)
    (hf : IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) P.space)
    (hends : ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = f (x, 1))
    {g : E → E} (himage : g '' P.space = P.space) :
    IsParametrizedSolidTorusTransport g P.space := by
  refine ⟨P, P, f, f, hPfin, hPfin, hP, hP, rfl, himage.symm,
    hsolid, ?_, hf, ?_, hends, hends⟩
  · rwa [himage]
  · rwa [himage]

variable [FiniteDimensional ℝ E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) E] [HasGroupoid E (plGroupoid 3)]

structure SupportedSolidTorusPLHomeomorphSystem (D : CompactCoreExhaustion E)
    extends SupportedPLHomeomorphSystem (n := 3) D where
  torus : ℕ → Geometry.SimplicialComplex ℝ E
  parametrization : ℕ → (Fin 3 → ℝ) × ℝ → E
  finite_torus : ∀ i, (torus i).faces.Finite
  isManifold_torus : ∀ i, IsCombinatorialManifoldWithBoundary 3 (torus i)
  torus_subset_shell : ∀ i, (torus i).space ⊆ interior (D.core (i + 1)) \ D.core i
  support_subset_interior_torus : ∀ i, support i ⊆ interior (torus i).space
  isTopologicalSolidTorus_torus : ∀ i, IsTopologicalSolidTorus (torus i).space
  isCylindricalDiagram_parametrization : ∀ i,
    IsCylindricalDiagram (parametrization i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (torus i).space
  parametrization_eq_ends : ∀ i x, x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) →
    parametrization i (x, 0) = parametrization i (x, 1)

namespace SupportedSolidTorusPLHomeomorphSystem

variable {D : CompactCoreExhaustion E}

omit [FiniteDimensional ℝ E] [HasGroupoid E (plGroupoid 3)] in
theorem point_mem_interior_torus (S : SupportedSolidTorusPLHomeomorphSystem D) (i : ℕ) :
    S.point i ∈ interior (S.torus i).space :=
  S.support_subset_interior_torus i (S.toSupportedPLHomeomorphSystem.point_mem_support i)

omit [FiniteDimensional ℝ E] [HasGroupoid E (plGroupoid 3)] in
theorem image_torus (S : SupportedSolidTorusPLHomeomorphSystem D) (i : ℕ) :
    S.step i '' (S.torus i).space = (S.torus i).space :=
  image_eq_of_homeomorph_eqOn_compl_of_subset (S.step i)
    (S.eqOn_compl i) ((S.support_subset_interior_torus i).trans interior_subset)

omit [FiniteDimensional ℝ E] [HasGroupoid E (plGroupoid 3)] in
theorem isParametrizedSolidTorusTransport_step
    (S : SupportedSolidTorusPLHomeomorphSystem D) (i : ℕ) :
    IsParametrizedSolidTorusTransport (S.step i) (S.torus i).space :=
  isParametrizedSolidTorusTransport_of_image_eq_self (S.finite_torus i)
    (S.isManifold_torus i) (S.isTopologicalSolidTorus_torus i)
    (S.isCylindricalDiagram_parametrization i) (S.parametrization_eq_ends i)
    (S.image_torus i)

omit [FiniteDimensional ℝ E] [HasGroupoid E (plGroupoid 3)] in
theorem pairwise_disjoint_torus (S : SupportedSolidTorusPLHomeomorphSystem D) :
    Pairwise (fun i j => Disjoint (S.torus i).space (S.torus j).space) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact (S.torus_subset_shell j hxj).2
      (D.monotone_core (Nat.succ_le_iff.mpr hij')
        (interior_subset (S.torus_subset_shell i hxi).1))
  · exact (S.torus_subset_shell i hxi).2
      (D.monotone_core (Nat.succ_le_iff.mpr hji')
        (interior_subset (S.torus_subset_shell j hxj).1))

omit [FiniteDimensional ℝ E] [HasGroupoid E (plGroupoid 3)] in
theorem locallyFinite_torus (S : SupportedSolidTorusPLHomeomorphSystem D) :
    LocallyFinite (fun i => (S.torus i).space) := by
  intro x
  obtain ⟨k, hxk⟩ := D.exists_mem_core x
  refine ⟨D.core (k + 1), D.core_succ_mem_nhds k hxk, (Set.finite_Iic k).subset ?_⟩
  intro i hi
  by_contra hik
  have hki : k + 1 ≤ i := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hik)
  obtain ⟨y, hyT, hycore⟩ := hi
  exact (S.torus_subset_shell i hyT).2 (D.monotone_core hki hycore)

end SupportedSolidTorusPLHomeomorphSystem

open Classical in
theorem CompactCoreExhaustion.exists_supportedSolidTorusPLHomeomorphSystem
    (D : CompactCoreExhaustion E) (hdim : Module.finrank ℝ E = 3)
    (hstrict : ∀ i, (interior (D.core (i + 1)) \ D.core i).Nonempty) :
    Nonempty (SupportedSolidTorusPLHomeomorphSystem D) := by
  have hopen (i : ℕ) : IsOpen (interior (D.core (i + 1)) \ D.core i) :=
    isOpen_interior.sdiff (D.isCompact_core i).isClosed
  have htorus (i : ℕ) :
      ∃ (N : Geometry.SimplicialComplex ℝ E) (f : (Fin 3 → ℝ) × ℝ → E),
        N.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 N ∧
        N.space ⊆ interior (D.core (i + 1)) \ D.core i ∧
        (interior N.space).Nonempty ∧ IsTopologicalSolidTorus N.space ∧
        IsCylindricalDiagram f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) N.space ∧
        ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = f (x, 1) :=
    exists_parametrized_solid_torus_complex_subset_open hdim (hopen i) (hstrict i)
  choose N f hNfin hNman hNshell hNint hNsolid hf hends using htorus
  choose p hp using hNint
  have hmove (i : ℕ) :
      ∃ (C : Set E) (h : E ≃ₜ E),
        IsCompact C ∧ C ⊆ interior (N i).space \ D.core i ∧
        IsPL 3 3 h ∧ IsPL 3 3 h.symm ∧ h (p i) ≠ p i ∧
        EqOn h id Cᶜ := by
    have hpD : p i ∉ D.core i :=
      (hNshell i (interior_subset (hp i))).2
    obtain ⟨C, h, hC, hCU, hh, hh', hne, hfix, -, -, -⟩ :=
      exists_isPL_homeomorph_moves_point_dist_lt_eqOn (n := 3) (by omega)
        (D.isCompact_core i).isClosed isOpen_interior (hp i) hpD
        (by norm_num : (0 : ℝ) < 1)
    exact ⟨C, h, hC, hCU, hh, hh', hne, hfix⟩
  choose C h hC hCU hh hh' hne hfix using hmove
  let S : SupportedSolidTorusPLHomeomorphSystem D :=
    { support := C
      point := p
      step := h
      isCompact_support := hC
      support_subset_shell := fun i x hx =>
        hNshell i (interior_subset ((hCU i hx).1))
      isPL_step := hh
      moves_point := hne
      eqOn_compl := hfix
      torus := N
      parametrization := f
      finite_torus := hNfin
      isManifold_torus := hNman
      torus_subset_shell := hNshell
      support_subset_interior_torus := fun i x hx => (hCU i hx).1
      isTopologicalSolidTorus_torus := hNsolid
      isCylindricalDiagram_parametrization := hf
      parametrization_eq_ends := hends }
  exact ⟨S⟩

open Classical in
theorem exists_noncompact_infinite_solid_torus_supported_PL_modification_three :
    ∃ (G : Set (EuclideanSpace ℝ (Fin 3)))
        (T : LocallyFinitePieceTower 3 (EuclideanSpace ℝ (Fin 3)) Set.univ)
        (D : CompactCoreExhaustion (EuclideanSpace ℝ (Fin 3)))
        (S : SupportedSolidTorusPLHomeomorphSystem D),
      G.Nonempty ∧ IsCompact G ∧
      (∀ i, IsCombinatorialManifoldWithBoundary 3 (T.piece i).piece.complex) ∧
      G ⊆ D.core 0 ∧
      LocallyFinite (fun i => (S.torus i).space) ∧
      Pairwise (fun i j => Disjoint (S.torus i).space (S.torus j).space) ∧
      (∀ i, IsParametrizedSolidTorusTransport (S.step i) (S.torus i).space) ∧
      LocallyFinite S.support ∧ Function.Injective S.point ∧
      (∀ i, S.step i ≠ Homeomorph.refl (EuclideanSpace ℝ (Fin 3))) ∧
      (∀ i, S.toSupportedPLHomeomorphSystem.toCompatibleExhaustion.stage (i + 1) ≠
        S.toSupportedPLHomeomorphSystem.toCompatibleExhaustion.stage i) ∧
      IsPL 3 3 S.toSupportedPLHomeomorphSystem.toCompatibleExhaustion.limitHomeomorph ∧
      (∀ i, S.toSupportedPLHomeomorphSystem.toCompatibleExhaustion.limitHomeomorph
        (S.point i) ≠ S.point i) ∧
      (∀ i, EqOn (S.step i) id G) ∧
      EqOn S.toSupportedPLHomeomorphSystem.toCompatibleExhaustion.limitHomeomorph id G ∧
      (∀ C : Set (EuclideanSpace ℝ (Fin 3)), IsCompact C →
        ∀ᶠ i in atTop,
          EqOn S.toSupportedPLHomeomorphSystem.toCompatibleExhaustion.limitHomeomorph
            (S.toSupportedPLHomeomorphSystem.toCompatibleExhaustion.stage i) C) := by
  let E := EuclideanSpace ℝ (Fin 3)
  let e : E := EuclideanSpace.single (0 : Fin 3) 1
  let G : Set E := segment ℝ 0 e
  have hG : IsCompact G := by
    change IsCompact (segment ℝ (0 : E) e)
    rw [← convexHull_pair]
    exact (Set.toFinite {0, e}).isCompact_convexHull ℝ
  have hGne : G.Nonempty := ⟨0, left_mem_segment ℝ 0 e⟩
  obtain ⟨T, hT⟩ :=
    exists_locallyFinitePieceTower_of_isOpen (m := 2) (X := E) isOpen_univ
  obtain ⟨offset, hGcore⟩ := T.compact_subset_compactCoreExhaustion_core hG
  let D := T.compactCoreExhaustion offset
  have hD0 : (D.core 0).Nonempty := hGne.mono hGcore
  have hstrict (i : ℕ) : (interior (D.core (i + 1)) \ D.core i).Nonempty :=
    D.shell_nonempty hD0 i
  let S := Classical.choice
    (D.exists_supportedSolidTorusPLHomeomorphSystem
      (by simp only [E, finrank_euclideanSpace, Fintype.card_fin]) hstrict)
  let H := S.toSupportedPLHomeomorphSystem
  refine ⟨G, T, D, S, hGne, hG, hT, hGcore, S.locallyFinite_torus,
    S.pairwise_disjoint_torus, S.isParametrizedSolidTorusTransport_step,
    H.locallyFinite_support, H.injective_point, H.step_ne_refl,
    H.stage_succ_ne_stage, H.toCompatibleExhaustion.isPL_limitHomeomorph,
    H.limitHomeomorph_moves_point, ?_, ?_, ?_⟩
  · intro i x hx
    exact H.fixes_core i (D.monotone_core (Nat.zero_le i) (hGcore hx))
  · intro x hx
    rw [H.toCompatibleExhaustion.limitHomeomorph_eq_stage (hGcore hx)]
    rfl
  · intro C hC
    exact H.toCompatibleExhaustion.eventually_eqOn_limitHomeomorph_of_isCompact hC

end DifferentialGeometry.Topology.PiecewiseLinear
