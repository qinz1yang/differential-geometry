/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SlabWedgeConjugation
import DifferentialGeometry.Topology.PiecewiseLinear.SlabWedgeEndpointHomotopy

/-!
# Chart conjugates of endpoint-moving slab wedge homotopies
-/

open Set Topology ContinuousMap
open scoped Manifold

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem conjugateMap_id (e : _root_.OpenPartialHomeomorph X Y) :
    e.conjugateMap id = id := by
  funext x
  by_cases hx : x ∈ e.source
  · rw [e.conjugateMap_of_mem id hx, id_eq, e.left_inv hx]
    rfl
  · rw [e.conjugateMap_of_notMem id hx]
    rfl

theorem continuous_conjugateMap_family [T2Space X]
    (e : _root_.OpenPartialHomeomorph X Y) {H : unitInterval × Y → Y}
    (hH : Continuous H) (hmap : ∀ t, MapsTo (fun y => H (t, y)) e.target e.target)
    {C : Set Y} (hC : IsCompact C) (hCt : C ⊆ e.target)
    (hfix : ∀ t, EqOn (fun y => H (t, y)) id Cᶜ) :
    Continuous (fun z : unitInterval × X =>
      e.conjugateMap (fun y => H (z.1, y)) z.2) := by
  have hclosed : IsClosed (e.symm '' C) :=
    (hC.image_of_continuousOn (e.continuousOn_symm.mono hCt)).isClosed
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z.2 ∈ e.source
  · have harg : ContinuousAt (fun w : unitInterval × X => (w.1, e w.2)) z :=
      continuousAt_fst.prodMk ((e.continuousAt hz).comp continuousAt_snd)
    have hmid : ContinuousAt (fun w : unitInterval × X => H (w.1, e w.2)) z :=
      hH.continuousAt.comp' harg
    have houtComp := ContinuousAt.comp
      (f := fun w : unitInterval × X => H (w.1, e w.2))
      (e.continuousAt_symm (hmap z.1 (e.map_source hz))) hmid
    apply houtComp.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.preimage_mem_nhds (e.open_source.mem_nhds hz)] with w hw
    rw [e.conjugateMap_of_mem _ hw]
    rfl
  · have hzC : z.2 ∉ e.symm '' C := by
      rintro ⟨y, hy, hyeq⟩
      exact hz (hyeq ▸ e.map_target (hCt hy))
    apply continuousAt_snd.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.preimage_mem_nhds
      (hclosed.isOpen_compl.mem_nhds hzC)] with w hw
    exact e.conjugateMap_eqOn_compl (hfix w.1) hw

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem convex_bufferedSlabWedgeSupport (c ρ : ℝ) :
    Convex ℝ (bufferedSlabWedgeSupport c ρ) := by
  have hbox : Convex ℝ (slabWedgeSupport (c + 2 * ρ)) :=
    (convex_Icc (0 : ℝ) (c + 2 * ρ)).prod
      ((convex_Icc (-(c + 2 * ρ)) (c + 2 * ρ)).prod
        (convex_Icc (-(c + 2 * ρ)) (c + 2 * ρ)))
  have hset : bufferedSlabWedgeSupport c ρ =
      (fun p : ℝ × ℝ × ℝ => p + (ρ, 0, 0)) ⁻¹' slabWedgeSupport (c + 2 * ρ) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro hp
      exact ⟨p + (ρ, 0, 0), hp, by simp⟩
  rw [hset]
  exact hbox.translate_preimage_left (ρ, 0, 0)

theorem mapsTo_positiveBufferedWedgeHomotopy_support (c ρ : ℝ) (t : unitInterval) :
    MapsTo (fun p => positiveBufferedWedgeHomotopy c ρ (t, p))
      (bufferedSlabWedgeSupport c ρ) (bufferedSlabWedgeSupport c ρ) := by
  intro p hp
  apply (convex_bufferedSlabWedgeSupport c ρ).add_smul_sub_mem hp
  · exact mapsTo_of_injective_eqOn_compl
      (positiveBufferedWedgePushHomeomorph c ρ).injective
      (eqOn_positiveBufferedWedgePush_id_compl_support c ρ) hp
  · exact t.property

theorem mapsTo_negativeBufferedWedgeHomotopy_support (c ρ : ℝ) (t : unitInterval) :
    MapsTo (fun p => negativeBufferedWedgeHomotopy c ρ (t, p))
      (bufferedSlabWedgeSupport c ρ) (bufferedSlabWedgeSupport c ρ) := by
  intro p hp
  apply (convex_bufferedSlabWedgeSupport c ρ).add_smul_sub_mem hp
  · exact mapsTo_of_injective_eqOn_compl
      (negativeBufferedWedgePushHomeomorph c ρ).injective
      (eqOn_negativeBufferedWedgePush_id_compl_support c ρ) hp
  · exact t.property

theorem mapsTo_positiveBufferedWedgeHomotopy_target {c ρ : ℝ}
    {T : Set (ℝ × ℝ × ℝ)} (hsupport : bufferedSlabWedgeSupport c ρ ⊆ T)
    (t : unitInterval) :
    MapsTo (fun p => positiveBufferedWedgeHomotopy c ρ (t, p)) T T := by
  intro p hp
  by_cases hpC : p ∈ bufferedSlabWedgeSupport c ρ
  · exact hsupport (mapsTo_positiveBufferedWedgeHomotopy_support c ρ t hpC)
  · simpa only [positiveBufferedWedgeHomotopy_eq_of_not_mem_support c ρ t hpC] using hp

theorem mapsTo_negativeBufferedWedgeHomotopy_target {c ρ : ℝ}
    {T : Set (ℝ × ℝ × ℝ)} (hsupport : bufferedSlabWedgeSupport c ρ ⊆ T)
    (t : unitInterval) :
    MapsTo (fun p => negativeBufferedWedgeHomotopy c ρ (t, p)) T T := by
  intro p hp
  by_cases hpC : p ∈ bufferedSlabWedgeSupport c ρ
  · exact hsupport (mapsTo_negativeBufferedWedgeHomotopy_support c ρ t hpC)
  · simpa only [negativeBufferedWedgeHomotopy_eq_of_not_mem_support c ρ t hpC] using hp

noncomputable def positiveBufferedSlabWedgeConjugate {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c ρ : ℝ) : M → M :=
  E.conjugateMap (e.conjugateMap (positiveBufferedWedgePush c ρ))

noncomputable def negativeBufferedSlabWedgeConjugate {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c ρ : ℝ) : M → M :=
  E.conjugateMap (e.conjugateMap (negativeBufferedWedgePush c ρ))

noncomputable def positiveBufferedSlabWedgeConjugateHomotopy {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c ρ : ℝ) (z : unitInterval × M) : M :=
  E.conjugateMap
    (fun y => e.conjugateMap
      (fun p => positiveBufferedWedgeHomotopy c ρ (z.1, p)) y) z.2

noncomputable def negativeBufferedSlabWedgeConjugateHomotopy {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c ρ : ℝ) (z : unitInterval × M) : M :=
  E.conjugateMap
    (fun y => e.conjugateMap
      (fun p => negativeBufferedWedgeHomotopy c ρ (z.1, p)) y) z.2

def bufferedSlabWedgeChartSupport {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c ρ : ℝ) : Set M :=
  E.symm '' (e.symm '' bufferedSlabWedgeSupport c ρ)

theorem continuous_positiveBufferedSlabWedgeConjugateHomotopy
    {M : Type u} [TopologicalSpace M] [T2Space M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (hesrc : e.source ⊆ E.target) {c ρ : ℝ}
    (hsupport : bufferedSlabWedgeSupport c ρ ⊆ e.target) :
    Continuous (positiveBufferedSlabWedgeConjugateHomotopy E e c ρ) := by
  let C := bufferedSlabWedgeSupport c ρ
  let H : unitInterval × (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ := fun z =>
    positiveBufferedWedgeHomotopy c ρ z
  let K : unitInterval × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun z =>
    e.conjugateMap (fun p => H (z.1, p)) z.2
  have hCcompact : IsCompact C := isCompact_bufferedSlabWedgeSupport c ρ
  have hHC : ∀ t, EqOn (fun p => H (t, p)) id Cᶜ :=
    fun t p hp => positiveBufferedWedgeHomotopy_eq_of_not_mem_support c ρ t hp
  have hHmap : ∀ t, MapsTo (fun p => H (t, p)) e.target e.target :=
    fun t => mapsTo_positiveBufferedWedgeHomotopy_target hsupport t
  have hKcont : Continuous K :=
    e.continuous_conjugateMap_family (positiveBufferedWedgeHomotopy c ρ).continuous_toFun
      hHmap hCcompact hsupport hHC
  have hCinner : IsCompact (e.symm '' C) :=
    hCcompact.image_of_continuousOn (e.continuousOn_symm.mono hsupport)
  have hCinnerTarget : e.symm '' C ⊆ E.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact hesrc (e.map_target (hsupport hp))
  have hKfix : ∀ t, EqOn (fun y => K (t, y)) id (e.symm '' C)ᶜ :=
    fun t => e.conjugateMap_eqOn_compl (hHC t)
  have hKmap : ∀ t, MapsTo (fun y => K (t, y)) E.target E.target := by
    intro t y hy
    change K (t, y) ∈ E.target
    by_cases hye : y ∈ e.source
    · rw [show K (t, y) = e.symm (H (t, e y)) by
        exact e.conjugateMap_of_mem _ hye]
      exact hesrc (e.map_target (hHmap t (e.map_source hye)))
    · rw [show K (t, y) = y by exact e.conjugateMap_of_notMem _ hye]
      exact hy
  exact E.continuous_conjugateMap_family hKcont hKmap hCinner hCinnerTarget hKfix

theorem continuous_negativeBufferedSlabWedgeConjugateHomotopy
    {M : Type u} [TopologicalSpace M] [T2Space M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (hesrc : e.source ⊆ E.target) {c ρ : ℝ}
    (hsupport : bufferedSlabWedgeSupport c ρ ⊆ e.target) :
    Continuous (negativeBufferedSlabWedgeConjugateHomotopy E e c ρ) := by
  let C := bufferedSlabWedgeSupport c ρ
  let H : unitInterval × (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ := fun z =>
    negativeBufferedWedgeHomotopy c ρ z
  let K : unitInterval × EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun z =>
    e.conjugateMap (fun p => H (z.1, p)) z.2
  have hCcompact : IsCompact C := isCompact_bufferedSlabWedgeSupport c ρ
  have hHC : ∀ t, EqOn (fun p => H (t, p)) id Cᶜ :=
    fun t p hp => negativeBufferedWedgeHomotopy_eq_of_not_mem_support c ρ t hp
  have hHmap : ∀ t, MapsTo (fun p => H (t, p)) e.target e.target :=
    fun t => mapsTo_negativeBufferedWedgeHomotopy_target hsupport t
  have hKcont : Continuous K :=
    e.continuous_conjugateMap_family (negativeBufferedWedgeHomotopy c ρ).continuous_toFun
      hHmap hCcompact hsupport hHC
  have hCinner : IsCompact (e.symm '' C) :=
    hCcompact.image_of_continuousOn (e.continuousOn_symm.mono hsupport)
  have hCinnerTarget : e.symm '' C ⊆ E.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact hesrc (e.map_target (hsupport hp))
  have hKfix : ∀ t, EqOn (fun y => K (t, y)) id (e.symm '' C)ᶜ :=
    fun t => e.conjugateMap_eqOn_compl (hHC t)
  have hKmap : ∀ t, MapsTo (fun y => K (t, y)) E.target E.target := by
    intro t y hy
    change K (t, y) ∈ E.target
    by_cases hye : y ∈ e.source
    · rw [show K (t, y) = e.symm (H (t, e y)) by
        exact e.conjugateMap_of_mem _ hye]
      exact hesrc (e.map_target (hHmap t (e.map_source hye)))
    · rw [show K (t, y) = y by exact e.conjugateMap_of_notMem _ hye]
      exact hy
  exact E.continuous_conjugateMap_family hKcont hKmap hCinner hCinnerTarget hKfix

theorem positiveBufferedSlabWedgeConjugateHomotopy_zero
    {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c ρ : ℝ) (x : M) :
    positiveBufferedSlabWedgeConjugateHomotopy E e c ρ (0, x) = x := by
  rw [positiveBufferedSlabWedgeConjugateHomotopy]
  have hinner : e.conjugateMap (fun p => positiveBufferedWedgeHomotopy c ρ (0, p)) = id := by
    convert e.conjugateMap_id using 2
    funext p
    simp
  rw [hinner, E.conjugateMap_id]
  rfl

theorem negativeBufferedSlabWedgeConjugateHomotopy_zero
    {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c ρ : ℝ) (x : M) :
    negativeBufferedSlabWedgeConjugateHomotopy E e c ρ (0, x) = x := by
  rw [negativeBufferedSlabWedgeConjugateHomotopy]
  have hinner : e.conjugateMap (fun p => negativeBufferedWedgeHomotopy c ρ (0, p)) = id := by
    convert e.conjugateMap_id using 2
    funext p
    simp
  rw [hinner, E.conjugateMap_id]
  rfl

theorem positiveBufferedSlabWedgeConjugateHomotopy_one
    {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c ρ : ℝ) (x : M) :
    positiveBufferedSlabWedgeConjugateHomotopy E e c ρ (1, x) =
      positiveBufferedSlabWedgeConjugate E e c ρ x := by
  simp only [positiveBufferedSlabWedgeConjugateHomotopy,
    positiveBufferedSlabWedgeConjugate]
  congr 2
  funext p
  simp

theorem negativeBufferedSlabWedgeConjugateHomotopy_one
    {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c ρ : ℝ) (x : M) :
    negativeBufferedSlabWedgeConjugateHomotopy E e c ρ (1, x) =
      negativeBufferedSlabWedgeConjugate E e c ρ x := by
  simp only [negativeBufferedSlabWedgeConjugateHomotopy,
    negativeBufferedSlabWedgeConjugate]
  congr 2
  funext p
  simp

theorem eqOn_positiveBufferedSlabWedgeConjugateHomotopy_id_compl_support
    {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c ρ : ℝ) (t : unitInterval) :
    EqOn (fun x => positiveBufferedSlabWedgeConjugateHomotopy E e c ρ (t, x)) id
      (bufferedSlabWedgeChartSupport E e c ρ)ᶜ := by
  exact E.conjugateMap_eqOn_compl
    (e.conjugateMap_eqOn_compl
      (fun p hp => positiveBufferedWedgeHomotopy_eq_of_not_mem_support c ρ t hp))

theorem eqOn_negativeBufferedSlabWedgeConjugateHomotopy_id_compl_support
    {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c ρ : ℝ) (t : unitInterval) :
    EqOn (fun x => negativeBufferedSlabWedgeConjugateHomotopy E e c ρ (t, x)) id
      (bufferedSlabWedgeChartSupport E e c ρ)ᶜ := by
  exact E.conjugateMap_eqOn_compl
    (e.conjugateMap_eqOn_compl
      (fun p hp => negativeBufferedWedgeHomotopy_eq_of_not_mem_support c ρ t hp))

theorem positiveBufferedWedgeHomotopy_mem_wedgeSlabBoundary_iff
    (c ρ : ℝ) (t : unitInterval) (p : ℝ × ℝ × ℝ) :
    positiveBufferedWedgeHomotopy c ρ (t, p) ∈ wedgeSlabBoundary c ↔
      p ∈ wedgeSlabBoundary c := by
  simp only [wedgeSlabBoundary, mem_ofPred_eq, positiveBufferedWedgeHomotopy_fst]

theorem negativeBufferedWedgeHomotopy_mem_wedgeSlabBoundary_iff
    (c ρ : ℝ) (t : unitInterval) (p : ℝ × ℝ × ℝ) :
    negativeBufferedWedgeHomotopy c ρ (t, p) ∈ wedgeSlabBoundary c ↔
      p ∈ wedgeSlabBoundary c := by
  simp only [wedgeSlabBoundary, mem_ofPred_eq, negativeBufferedWedgeHomotopy_fst]

theorem positiveBufferedSlabWedgeConjugateHomotopy_mem_boundary_iff
    {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (hesrc : e.source ⊆ E.target) {BdM : Set M} {Bd₁ : Set (EuclideanSpace ℝ (Fin 3))}
    {c ρ : ℝ} (hsupport : bufferedSlabWedgeSupport c ρ ⊆ e.target)
    (hbdE : ∀ x ∈ E.source, x ∈ BdM ↔ E x ∈ Bd₁)
    (hbde : ∀ y ∈ e.source, y ∈ Bd₁ ↔ e y ∈ wedgeSlabBoundary c)
    (t : unitInterval) (x : M) :
    positiveBufferedSlabWedgeConjugateHomotopy E e c ρ (t, x) ∈ BdM ↔ x ∈ BdM := by
  let H := fun p => positiveBufferedWedgeHomotopy c ρ (t, p)
  let K := e.conjugateMap H
  have hHmap : MapsTo H e.target e.target :=
    mapsTo_positiveBufferedWedgeHomotopy_target hsupport t
  have hKmap : MapsTo K E.target E.target := by
    intro y hy
    by_cases hye : y ∈ e.source
    · rw [show K y = e.symm (H (e y)) by exact e.conjugateMap_of_mem _ hye]
      exact hesrc (e.map_target (hHmap (e.map_source hye)))
    · rw [show K y = y by exact e.conjugateMap_of_notMem _ hye]
      exact hy
  exact E.conjugateMap_mem_iff hKmap hbdE
    (fun y hy => e.conjugateMap_mem_iff hHmap hbde
      (fun p _ => positiveBufferedWedgeHomotopy_mem_wedgeSlabBoundary_iff c ρ t p) y) x

theorem negativeBufferedSlabWedgeConjugateHomotopy_mem_boundary_iff
    {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (hesrc : e.source ⊆ E.target) {BdM : Set M} {Bd₁ : Set (EuclideanSpace ℝ (Fin 3))}
    {c ρ : ℝ} (hsupport : bufferedSlabWedgeSupport c ρ ⊆ e.target)
    (hbdE : ∀ x ∈ E.source, x ∈ BdM ↔ E x ∈ Bd₁)
    (hbde : ∀ y ∈ e.source, y ∈ Bd₁ ↔ e y ∈ wedgeSlabBoundary c)
    (t : unitInterval) (x : M) :
    negativeBufferedSlabWedgeConjugateHomotopy E e c ρ (t, x) ∈ BdM ↔ x ∈ BdM := by
  let H := fun p => negativeBufferedWedgeHomotopy c ρ (t, p)
  let K := e.conjugateMap H
  have hHmap : MapsTo H e.target e.target :=
    mapsTo_negativeBufferedWedgeHomotopy_target hsupport t
  have hKmap : MapsTo K E.target E.target := by
    intro y hy
    by_cases hye : y ∈ e.source
    · rw [show K y = e.symm (H (e y)) by exact e.conjugateMap_of_mem _ hye]
      exact hesrc (e.map_target (hHmap (e.map_source hye)))
    · rw [show K y = y by exact e.conjugateMap_of_notMem _ hye]
      exact hy
  exact E.conjugateMap_mem_iff hKmap hbdE
    (fun y hy => e.conjugateMap_mem_iff hHmap hbde
      (fun p _ => negativeBufferedWedgeHomotopy_mem_wedgeSlabBoundary_iff c ρ t p) y) x

open Classical in
theorem buffered_slab_wedge_conjugate_properties
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hE : E ∈ (plGroupoid 3).maximalAtlas M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hesrc : e.source ⊆ E.target) {c ρ : ℝ} {A B : Set (ℝ × ℝ × ℝ)}
    (hρ : 0 < ρ) (hsupport : bufferedSlabWedgeSupport c ρ ⊆ e.target)
    (hAfold : A ⊆ positiveSlabFold c) (hBfold : B ⊆ negativeSlabFold c)
    (hAtarget : A ⊆ e.target) (hBtarget : B ⊆ e.target) :
    IsCompact (bufferedSlabWedgeChartSupport E e c ρ) ∧
      IsPL 3 3 (positiveBufferedSlabWedgeConjugate E e c ρ) ∧
      IsPL 3 3 (negativeBufferedSlabWedgeConjugate E e c ρ) ∧
      Function.Injective (positiveBufferedSlabWedgeConjugate E e c ρ) ∧
      Function.Injective (negativeBufferedSlabWedgeConjugate E e c ρ) ∧
      EqOn (positiveBufferedSlabWedgeConjugate E e c ρ) id
        (bufferedSlabWedgeChartSupport E e c ρ)ᶜ ∧
      EqOn (negativeBufferedSlabWedgeConjugate E e c ρ) id
        (bufferedSlabWedgeChartSupport E e c ρ)ᶜ ∧
      MapsTo (positiveBufferedSlabWedgeConjugate E e c ρ)
        (bufferedSlabWedgeChartSupport E e c ρ)
        (bufferedSlabWedgeChartSupport E e c ρ) ∧
      MapsTo (negativeBufferedSlabWedgeConjugate E e c ρ)
        (bufferedSlabWedgeChartSupport E e c ρ)
        (bufferedSlabWedgeChartSupport E e c ρ) ∧
      Disjoint
        (positiveBufferedSlabWedgeConjugate E e c ρ '' slabWedgeChartSet E e A)
        (negativeBufferedSlabWedgeConjugate E e c ρ '' slabWedgeChartSet E e B) := by
  let C := bufferedSlabWedgeSupport c ρ
  let kp := e.conjugateMap (positiveBufferedWedgePush c ρ)
  let kn := e.conjugateMap (negativeBufferedWedgePush c ρ)
  let K := E.symm '' (e.symm '' C)
  let hp := E.conjugateMap kp
  let hn := E.conjugateMap kn
  have hCcompact : IsCompact C := isCompact_bufferedSlabWedgeSupport c ρ
  have hposFix : EqOn (positiveBufferedWedgePush c ρ) id Cᶜ :=
    eqOn_positiveBufferedWedgePush_id_compl_support c ρ
  have hnegFix : EqOn (negativeBufferedWedgePush c ρ) id Cᶜ :=
    eqOn_negativeBufferedWedgePush_id_compl_support c ρ
  have hposInj : Function.Injective (positiveBufferedWedgePush c ρ) := by
    intro x y hxy
    exact (positiveBufferedWedgePushHomeomorph c ρ).injective (by simpa using hxy)
  have hnegInj : Function.Injective (negativeBufferedWedgePush c ρ) := by
    intro x y hxy
    exact (negativeBufferedWedgePushHomeomorph c ρ).injective (by simpa using hxy)
  have hposC : MapsTo (positiveBufferedWedgePush c ρ) C C :=
    mapsTo_of_injective_eqOn_compl hposInj hposFix
  have hnegC : MapsTo (negativeBufferedWedgePush c ρ) C C :=
    mapsTo_of_injective_eqOn_compl hnegInj hnegFix
  have hposTarget : MapsTo (positiveBufferedWedgePush c ρ) e.target e.target := by
    intro p hpTarget
    by_cases hpC : p ∈ C
    · exact hsupport (hposC hpC)
    · simpa only [hposFix hpC, id_eq] using hpTarget
  have hnegTarget : MapsTo (negativeBufferedWedgePush c ρ) e.target e.target := by
    intro p hpTarget
    by_cases hpC : p ∈ C
    · exact hsupport (hnegC hpC)
    · simpa only [hnegFix hpC, id_eq] using hpTarget
  have hinnerSupport : e.symm '' C ⊆ E.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact hesrc (e.map_target (hsupport hp))
  have hinnerCompact : IsCompact (e.symm '' C) :=
    hCcompact.image_of_continuousOn (e.continuousOn_symm.mono hsupport)
  have hkpFix : EqOn kp id (e.symm '' C)ᶜ := e.conjugateMap_eqOn_compl hposFix
  have hknFix : EqOn kn id (e.symm '' C)ᶜ := e.conjugateMap_eqOn_compl hnegFix
  have hkpTarget : MapsTo kp E.target E.target := by
    intro p hpTarget
    by_cases hpC : p ∈ e.symm '' C
    · exact hinnerSupport (mapsTo_of_injective_eqOn_compl
        (e.injective_conjugateMap hposInj hposTarget) hkpFix hpC)
    · simpa only [hkpFix hpC, id_eq] using hpTarget
  have hknTarget : MapsTo kn E.target E.target := by
    intro p hpTarget
    by_cases hpC : p ∈ e.symm '' C
    · exact hinnerSupport (mapsTo_of_injective_eqOn_compl
        (e.injective_conjugateMap hnegInj hnegTarget) hknFix hpC)
    · simpa only [hknFix hpC, id_eq] using hpTarget
  have hkpPL : IsPiecewiseAffineOn kp univ :=
    isPiecewiseAffineOn_conjugateMap e he hei
      ((isPLHomeomorphOn_positiveBufferedWedgePush c ρ).isPiecewiseAffineOn.mono
        e.open_target (subset_univ _)) hposTarget hCcompact hsupport hposFix
  have hknPL : IsPiecewiseAffineOn kn univ :=
    isPiecewiseAffineOn_conjugateMap e he hei
      ((isPLHomeomorphOn_negativeBufferedWedgePush c ρ).isPiecewiseAffineOn.mono
        e.open_target (subset_univ _)) hnegTarget hCcompact hsupport hnegFix
  have hKcompact : IsCompact K :=
    hinnerCompact.image_of_continuousOn (E.continuousOn_symm.mono hinnerSupport)
  have hhpPL : IsPL 3 3 hp :=
    isPL_conjugateMap E hE hkpPL hkpTarget hinnerCompact hinnerSupport hkpFix
  have hhnPL : IsPL 3 3 hn :=
    isPL_conjugateMap E hE hknPL hknTarget hinnerCompact hinnerSupport hknFix
  have hhpInj : Function.Injective hp :=
    E.injective_conjugateMap (e.injective_conjugateMap hposInj hposTarget) hkpTarget
  have hhnInj : Function.Injective hn :=
    E.injective_conjugateMap (e.injective_conjugateMap hnegInj hnegTarget) hknTarget
  have hhpFix : EqOn hp id Kᶜ := E.conjugateMap_eqOn_compl hkpFix
  have hhnFix : EqOn hn id Kᶜ := E.conjugateMap_eqOn_compl hknFix
  have hposChart : e.symm '' A ⊆ E.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact hesrc (e.map_target (hAtarget hp))
  have hnegChart : e.symm '' B ⊆ E.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact hesrc (e.map_target (hBtarget hp))
  have hmodelDisj : Disjoint
      (positiveBufferedWedgePush c ρ '' A) (negativeBufferedWedgePush c ρ '' B) :=
    (disjoint_positive_negative_bufferedWedgePush_on_slabFold hρ).mono
      (image_mono hAfold) (image_mono hBfold)
  have hinnerDisj : Disjoint (kp '' (e.symm '' A)) (kn '' (e.symm '' B)) :=
    e.disjoint_conjugateMap_images hposTarget hnegTarget hAtarget hBtarget hmodelDisj
  have houterDisj : Disjoint
      (hp '' (E.symm '' (e.symm '' A))) (hn '' (E.symm '' (e.symm '' B))) :=
    E.disjoint_conjugateMap_images hkpTarget hknTarget hposChart hnegChart hinnerDisj
  change IsCompact K ∧ IsPL 3 3 hp ∧ IsPL 3 3 hn ∧ Function.Injective hp ∧
    Function.Injective hn ∧ EqOn hp id Kᶜ ∧ EqOn hn id Kᶜ ∧ MapsTo hp K K ∧
    MapsTo hn K K ∧ Disjoint
      (hp '' (E.symm '' (e.symm '' A))) (hn '' (E.symm '' (e.symm '' B)))
  exact ⟨hKcompact, hhpPL, hhnPL, hhpInj, hhnInj, hhpFix, hhnFix,
    mapsTo_of_injective_eqOn_compl hhpInj hhpFix,
    mapsTo_of_injective_eqOn_compl hhnInj hhnFix, houterDisj⟩

end DifferentialGeometry.Topology.PiecewiseLinear
