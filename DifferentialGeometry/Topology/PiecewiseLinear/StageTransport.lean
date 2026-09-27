/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CompactRelativeApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap
import DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyPolyhedral

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Composition

variable {p n m : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M₂]

theorem isPLOn_comp_isPLOn_of_mapsTo {F : EuclideanSpace ℝ (Fin p) → M₁} {v : M₁ → M₂}
    {S : Set (EuclideanSpace ℝ (Fin p))} {R : Set M₁} (hv : IsPLOn n m v R)
    (hF : IsPLOn p n F S) (hmap : MapsTo F S R) : IsPLOn p m (v ∘ F) S := by
  intro x hx
  obtain ⟨hFc, hFp⟩ := (StructureGroupoid.liftPropWithinAt_self_source).mp (hF x hx)
  set e := chartAt (EuclideanSpace ℝ (Fin n)) (F x)
  have hFpa : IsPiecewiseAffineWithinAt ((e : M₁ → EuclideanSpace ℝ (Fin n)) ∘ F) S x := hFp
  have hvx := hv (F x) (hmap hx)
  have hvpa : IsPiecewiseAffineWithinAt
      ((chartAt (EuclideanSpace ℝ (Fin m)) (v (F x))) ∘ v ∘ (e.symm))
      (e.symm ⁻¹' R) (((e : M₁ → EuclideanSpace ℝ (Fin n)) ∘ F) x) := hvx.prop
  have hcomp := IsPiecewiseAffineWithinAt.comp
    (f := (e : M₁ → EuclideanSpace ℝ (Fin n)) ∘ F) (x := x) (s := S) hvpa hFpa
  obtain ⟨O, hO, hxO, hOsub⟩ := mem_nhdsWithin.mp
    (hFc.preimage_mem_nhdsWithin (e.open_source.mem_nhds (mem_chart_source _ _)))
  have hlocal := hcomp.inter_of_mem_nhds (hO.mem_nhds hxO)
  have hsetEq : (S ∩ ((e : M₁ → EuclideanSpace ℝ (Fin n)) ∘ F) ⁻¹' (e.symm ⁻¹' R)) ∩ O
      = S ∩ O := by
    refine Subset.antisymm (inter_subset_inter_left _ inter_subset_left) ?_
    rintro z ⟨hzS, hzO⟩
    have hzsrc : F z ∈ e.source := hOsub ⟨hzO, hzS⟩
    refine ⟨⟨hzS, ?_⟩, hzO⟩
    change e.symm (e (F z)) ∈ R
    rw [e.left_inv hzsrc]
    exact hmap hzS
  rw [hsetEq] at hlocal
  have hcongr : IsPiecewiseAffineWithinAt
      ((chartAt (EuclideanSpace ℝ (Fin m)) (v (F x))) ∘ (v ∘ F)) (S ∩ O) x := by
    refine hlocal.congr fun z hz => ?_
    have hzsrc : F z ∈ e.source := hOsub ⟨hz.2, hz.1⟩
    simp only [Function.comp_apply, e.left_inv hzsrc]
  exact (StructureGroupoid.liftPropWithinAt_self_source).mpr
    ⟨hvx.continuousWithinAt.comp hFc hmap, hcongr.of_inter_of_mem_nhds (hO.mem_nhds hxO)⟩

end Composition

section PieceTransport

variable {n d m : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M₂]

theorem PLPieceIn.isPLOn_of_eqOn_comp_invFunOn {Y : Set M₁}
    (T : PLPieceIn (EuclideanSpace ℝ (Fin d)) n M₁ Y)
    {w : EuclideanSpace ℝ (Fin d) → M₂} (hw : IsPLOn d m w T.complex.space)
    {F : M₁ → M₂} (hF : EqOn F (w ∘ Function.invFunOn T.map T.complex.space) Y) :
    IsPLOn n m F Y := by
  classical
  intro x hx
  have hinv : MapsTo (Function.invFunOn T.map T.complex.space) Y T.complex.space :=
    fun _ hy => T.bijOn.surjOn.mapsTo_invFunOn hy
  set a := Function.invFunOn T.map T.complex.space
  set e := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hxe : x ∈ e.source := mem_chart_source _ _
  have hleft : e.symm (e x) = x := e.left_inv hxe
  have hmem : e x ∈ e.target ∩ e.symm ⁻¹' Y := by
    refine ⟨e.map_source hxe, ?_⟩
    change e.symm (e x) ∈ Y
    rw [hleft]
    exact hx
  have hsymm : IsPiecewiseAffineOn (a ∘ (e.symm : EuclideanSpace ℝ (Fin n) → M₁))
      (e.target ∩ e.symm ⁻¹' Y) := T.isPiecewiseAffineOn_chart_symm e (chart_mem_atlas _ _)
  have hac : ContinuousWithinAt a Y x := by
    have hcont := hsymm.continuousOn (e x) hmem
    have hecont : ContinuousWithinAt (e : M₁ → EuclideanSpace ℝ (Fin n)) (Y ∩ e.source) x :=
      (e.continuousOn x hxe).mono inter_subset_right
    have hmaps : MapsTo (e : M₁ → EuclideanSpace ℝ (Fin n)) (Y ∩ e.source)
        (e.target ∩ e.symm ⁻¹' Y) := by
      intro z hz
      refine ⟨e.map_source hz.2, ?_⟩
      change e.symm (e z) ∈ Y
      rw [e.left_inv hz.2]
      exact hz.1
    have hcomp := hcont.comp hecont hmaps
    have hc2 : ContinuousWithinAt a (Y ∩ e.source) x := by
      refine hcomp.congr (fun z hz => ?_) ?_
      · simp only [Function.comp_apply, e.left_inv hz.2]
      · simp only [Function.comp_apply, hleft]
    exact (continuousWithinAt_inter (e.open_source.mem_nhds hxe)).mp hc2
  have hFx : F x = w (a x) := hF hx
  have hwp : IsPiecewiseAffineWithinAt
      ((chartAt (EuclideanSpace ℝ (Fin m)) (F x)) ∘ w) T.complex.space (a x) := by
    rw [hFx]
    exact ((StructureGroupoid.liftPropWithinAt_self_source).mp (hw (a x) (hinv hx))).2
  have hpoint : (a ∘ (e.symm : EuclideanSpace ℝ (Fin n) → M₁)) (e x) = a x := by
    simp only [Function.comp_apply, hleft]
  have hwp' : IsPiecewiseAffineWithinAt
      ((chartAt (EuclideanSpace ℝ (Fin m)) (F x)) ∘ w) T.complex.space
      ((a ∘ (e.symm : EuclideanSpace ℝ (Fin n) → M₁)) (e x)) := by
    rw [hpoint]
    exact hwp
  have hcomp := IsPiecewiseAffineWithinAt.comp
    (f := a ∘ (e.symm : EuclideanSpace ℝ (Fin n) → M₁)) (x := e x)
    (s := e.target ∩ e.symm ⁻¹' Y) hwp' (hsymm (e x) hmem)
  have hsub : e.target ∩ e.symm ⁻¹' Y
      ⊆ (a ∘ (e.symm : EuclideanSpace ℝ (Fin n) → M₁)) ⁻¹' T.complex.space :=
    fun _ hz => hinv hz.2
  rw [inter_eq_left.mpr hsub] at hcomp
  have hcongr : IsPiecewiseAffineWithinAt
      ((chartAt (EuclideanSpace ℝ (Fin m)) (F x)) ∘ F ∘ (e.symm))
      (e.target ∩ e.symm ⁻¹' Y) (e x) := by
    refine hcomp.congr fun z hz => ?_
    simp only [Function.comp_apply, hF hz.2]
  have hFc : ContinuousWithinAt F Y x :=
    ((hw (a x) (hinv hx)).continuousWithinAt.comp hac hinv).congr (fun z hz => hF hz) (hF hx)
  rw [inter_comm] at hcongr
  exact ⟨hFc, hcongr.of_inter_of_mem_nhds (e.open_target.mem_nhds (e.map_source hxe))⟩

end PieceTransport

section ModelApproximation

variable {n m : ℕ} {N : Type*} [MetricSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [HasGroupoid N (plGroupoid m)]

omit [HasGroupoid N (plGroupoid m)] in
theorem exists_pos_forall_exists_isPLOn_dist_lt_eqOn_of_biUnion {ι : Type*}
    {C : ι → Set (EuclideanSpace ℝ (Fin n))} (hC : ∀ i, IsPolyhedron (C i))
    {Q : Set (EuclideanSpace ℝ (Fin n))} (hQ : IsPolyhedron Q)
    {f : EuclideanSpace ℝ (Fin n) → N} (s : Finset ι)
    (hf : ContinuousOn f (Q ∪ ⋃ i ∈ s, C i))
    (hchart : ∀ i ∈ s, ∃ e : OpenPartialHomeomorph N (EuclideanSpace ℝ (Fin m)),
      e ∈ (plGroupoid m).maximalAtlas N ∧ MapsTo f (C i) e.source)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ u : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m u Q →
      (∀ x ∈ Q, dist (u x) (f x) < η) →
        ∃ g : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m g (Q ∪ ⋃ i ∈ s, C i) ∧ EqOn g u Q ∧
          ∀ x ∈ Q ∪ ⋃ i ∈ s, C i, dist (g x) (f x) < ε := by
  classical
  induction s using Finset.induction_on generalizing ε with
  | empty =>
    refine ⟨ε, hε, fun u hu hclose => ⟨u, ?_, fun _ _ => rfl, ?_⟩⟩
    · simpa using hu
    · intro x hx
      exact hclose x (by simpa using hx)
  | insert j t hj ih =>
    have hset : Q ∪ ⋃ i ∈ insert j t, C i = C j ∪ (Q ∪ ⋃ i ∈ t, C i) := by
      rw [Finset.set_biUnion_insert, Set.union_left_comm]
    rw [hset] at hf ⊢
    set U := Q ∪ ⋃ i ∈ t, C i
    have hU : IsPolyhedron U := hQ.union (IsPolyhedron.finsetBiUnion t hC)
    obtain ⟨e, he, hemap⟩ := hchart j (Finset.mem_insert_self j t)
    have hQ' : IsPolyhedron (U ∩ C j) := hU.inter (hC j)
    obtain ⟨η₁, hη₁, hη₁prop⟩ :=
      exists_pos_forall_exists_isPLOn_dist_lt_eqOn_of_mapsTo_chart (hC j) (hC j).isCompact
        hQ' inter_subset_right (hf.mono subset_union_left) e he hemap hε
    obtain ⟨η₂, hη₂, hη₂prop⟩ :=
      ih (hf.mono subset_union_right) (fun i hi => hchart i (Finset.mem_insert_of_mem hi))
        (lt_min hε hη₁)
    refine ⟨η₂, hη₂, fun u hu hclose => ?_⟩
    obtain ⟨g₀, hg₀, hg₀Q, hg₀d⟩ := hη₂prop u hu hclose
    obtain ⟨g₁, hg₁, hg₁eq, hg₁d⟩ :=
      hη₁prop g₀ (hg₀.mono_of_isPolyhedron hQ' inter_subset_left)
        (fun x hx => lt_of_lt_of_le (hg₀d x hx.1) (min_le_right _ _))
    refine ⟨(C j).piecewise g₁ g₀, ?_, ?_, ?_⟩
    · exact hg₁.piecewise_of_isClosed hg₀ (hC j).isClosed hU.isClosed
        (fun x hx => hg₁eq ⟨hx.2, hx.1⟩)
    · intro x hx
      have hxU : x ∈ U := subset_union_left hx
      by_cases hxV : x ∈ C j
      · rw [Set.piecewise_eq_of_mem _ _ _ hxV, hg₁eq ⟨hxU, hxV⟩]
        exact hg₀Q hx
      · rw [Set.piecewise_eq_of_notMem _ _ _ hxV]
        exact hg₀Q hx
    · intro x hx
      by_cases hxV : x ∈ C j
      · rw [Set.piecewise_eq_of_mem _ _ _ hxV]
        exact hg₁d x hxV
      · rw [Set.piecewise_eq_of_notMem _ _ _ hxV]
        exact lt_of_lt_of_le (hg₀d x (hx.resolve_left hxV)) (min_le_left _ _)

theorem exists_pos_forall_exists_isPLOn_dist_lt_eqOn
    {P Q : Set (EuclideanSpace ℝ (Fin n))} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q)
    (hQP : Q ⊆ P) {f : EuclideanSpace ℝ (Fin n) → N} (hf : ContinuousOn f P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ u : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m u Q →
      (∀ x ∈ Q, dist (u x) (f x) < η) →
        ∃ g : EuclideanSpace ℝ (Fin n) → N, IsPLOn n m g P ∧ EqOn g u Q ∧
          ∀ x ∈ P, dist (g x) (f x) < ε := by
  obtain ⟨D, S, hD, hunion, hchart⟩ := exists_finsetBiUnion_eq_mapsTo_chart (m := m) hP hf
  have hQunion : Q ∪ ⋃ s ∈ S, D s = P := by
    rw [hunion]
    exact union_eq_self_of_subset_left hQP
  obtain ⟨η, hη, hηprop⟩ :=
    exists_pos_forall_exists_isPLOn_dist_lt_eqOn_of_biUnion hD hQ S
      (by rw [hQunion]; exact hf) hchart hε
  refine ⟨η, hη, fun u hu hclose => ?_⟩
  obtain ⟨g, hg, hgQ, hgd⟩ := hηprop u hu hclose
  rw [hQunion] at hg hgd
  exact ⟨g, hg, hgQ, hgd⟩

end ModelApproximation

namespace LocallyFinitePieceTower

section Stage

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [MetricSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
  {K : Set M₁}

private noncomputable def stagePiece (T : LocallyFinitePieceTower n M₁ K) (i : ℕ) :
    PLPieceIn (EuclideanSpace ℝ (Fin (T.piece i).ambientDim)) n M₁ (T.coreSpace i) :=
  (T.piece i).piece.restrict (T.core i) (T.core_le i)

theorem exists_isPLOn_coreSpace_eqOn_comp (T : LocallyFinitePieceTower n M₁ K) (i : ℕ)
    {w : EuclideanSpace ℝ (Fin (T.piece i).ambientDim) → M₂}
    (hw : IsPLOn (T.piece i).ambientDim n w (T.core i).space) :
    ∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace i) ∧
      ∀ y ∈ (T.core i).space, f ((T.piece i).piece.map y) = w y := by
  classical
  refine ⟨fun x => w (Function.invFunOn (T.piece i).piece.map (T.core i).space x), ?_, ?_⟩
  · exact (T.stagePiece i).isPLOn_of_eqOn_comp_invFunOn hw fun _ _ => rfl
  · intro y hy
    have hleft : Function.invFunOn (T.piece i).piece.map (T.core i).space
        ((T.piece i).piece.map y) = y := (T.stagePiece i).bijOn.injOn.leftInvOn_invFunOn hy
    simp only [hleft]

variable [HasGroupoid M₂ (plGroupoid n)]

theorem exists_isPLOn_dist_lt_coreSpace (T : LocallyFinitePieceTower n M₁ K) (i : ℕ)
    {h : M₁ → M₂} (hh : ContinuousOn h (T.coreSpace i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace i) ∧
      ∀ x ∈ T.coreSpace i, dist (f x) (h x) < ε := by
  classical
  have hfin : Finite (T.core i).faces := (T.core_faces_finite i).to_subtype
  have hP : IsPolyhedron (T.core i).space := PiecewiseLinear.isPolyhedron_space (T.core i)
  have hmaps : MapsTo (T.piece i).piece.map (T.core i).space (T.coreSpace i) :=
    (T.stagePiece i).bijOn.mapsTo
  have hcont : ContinuousOn (h ∘ (T.piece i).piece.map) (T.core i).space :=
    hh.comp (T.stagePiece i).continuousOn hmaps
  obtain ⟨w, hw, hwd⟩ := exists_isPLOn_dist_lt (m := n) hP hcont hε
  obtain ⟨f, hf, hfeq⟩ := T.exists_isPLOn_coreSpace_eqOn_comp i hw
  refine ⟨f, hf, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ :=
    (show x ∈ (T.piece i).piece.map '' (T.core i).space from hx)
  rw [hfeq y hy]
  exact hwd y hy

theorem exists_pos_forall_exists_isPLOn_eqOn_dist_lt_coreSpace_succ
    (T : LocallyFinitePieceTower n M₁ K) (i : ℕ) {h : M₁ → M₂}
    (hh : ContinuousOn h (T.coreSpace (i + 1))) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ g : M₁ → M₂, IsPLOn n n g (T.coreSpace i) →
      (∀ x ∈ T.coreSpace i, dist (g x) (h x) < η) →
        ∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace (i + 1)) ∧ EqOn f g (T.coreSpace i) ∧
          ∀ x ∈ T.coreSpace (i + 1), dist (f x) (h x) < ε := by
  classical
  have hfinP : Finite (T.core (i + 1)).faces := (T.core_faces_finite (i + 1)).to_subtype
  have hfinQ : Finite (T.coreImage i).faces := (T.coreImage_faces_finite i).to_subtype
  have hP : IsPolyhedron (T.core (i + 1)).space :=
    PiecewiseLinear.isPolyhedron_space (T.core (i + 1))
  have hQ : IsPolyhedron (T.coreImage i).space :=
    PiecewiseLinear.isPolyhedron_space (T.coreImage i)
  have hQP : (T.coreImage i).space ⊆ (T.core (i + 1)).space :=
    space_mono_of_faces_subset (T.coreImage_le i)
  have hQimg : (T.piece (i + 1)).piece.map '' (T.coreImage i).space = T.coreSpace i := by
    have hsig := (T.embed_isPLHomeomorphOn i).1.image_eq
    rw [← hsig, image_image]
    exact (show EqOn
      (fun y => (T.piece (i + 1)).piece.map (simplicialMap (T.core i) (T.embed i) y))
      (T.piece i).piece.map (T.core i).space from fun y hy => T.map_embed i y hy).image_eq
  have hmapsP : MapsTo (T.piece (i + 1)).piece.map (T.core (i + 1)).space
      (T.coreSpace (i + 1)) := (T.stagePiece (i + 1)).bijOn.mapsTo
  have hmapsQ : MapsTo (T.piece (i + 1)).piece.map (T.coreImage i).space (T.coreSpace i) := by
    intro y hy
    rw [← hQimg]
    exact mem_image_of_mem _ hy
  have hcont : ContinuousOn (h ∘ (T.piece (i + 1)).piece.map) (T.core (i + 1)).space :=
    hh.comp (T.stagePiece (i + 1)).continuousOn hmapsP
  obtain ⟨η, hη, hηprop⟩ :=
    exists_pos_forall_exists_isPLOn_dist_lt_eqOn (m := n) hP hQ hQP hcont hε
  refine ⟨η, hη, fun g hg hgd => ?_⟩
  have hmpQ : IsPLOn (T.piece (i + 1)).ambientDim n (T.piece (i + 1)).piece.map
      (T.coreImage i).space := by
    have h0 := (T.stagePiece (i + 1)).isPLOn_comp (f := id)
      hQ.isLocallyPolyhedral.isPiecewiseAffineOn_id (fun _ hy => hQP hy)
    exact h0
  have hu : IsPLOn (T.piece (i + 1)).ambientDim n (g ∘ (T.piece (i + 1)).piece.map)
      (T.coreImage i).space := isPLOn_comp_isPLOn_of_mapsTo hg hmpQ hmapsQ
  obtain ⟨w, hw, hweq, hwd⟩ :=
    hηprop (g ∘ (T.piece (i + 1)).piece.map) hu fun y hy => hgd _ (hmapsQ hy)
  obtain ⟨f, hf, hfeq⟩ := T.exists_isPLOn_coreSpace_eqOn_comp (i + 1) hw
  refine ⟨f, hf, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ :=
      (show x ∈ (T.piece (i + 1)).piece.map '' (T.coreImage i).space by rw [hQimg]; exact hx)
    have h1 : f ((T.piece (i + 1)).piece.map y) = w y := hfeq y (hQP hy)
    have h2 : w y = g ((T.piece (i + 1)).piece.map y) := hweq hy
    rw [h1, h2]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ :=
      (show x ∈ (T.piece (i + 1)).piece.map '' (T.core (i + 1)).space from hx)
    rw [hfeq y hy]
    exact hwd y hy

end Stage

end LocallyFinitePieceTower

section Obligation

def Moise352StageInjection (n : ℕ) : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [MetricSpace M₂] [SecondCountableTopology M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
    [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]
    {K : Set M₁} (T : LocallyFinitePieceTower n M₁ K),
    (∀ i, IsCombinatorialManifoldWithBoundary n (T.piece i).piece.complex) →
    ∀ {h : M₁ → M₂}, Topology.IsEmbedding (K.domRestrict h) →
      (∀ (f : M₁ → M₂), IsPLOn n n f (T.coreSpace 0) → ∀ {ε : ℝ}, 0 < ε →
          (∀ x ∈ T.coreSpace 0, dist (f x) (h x) < ε) →
          ∃ f' : M₁ → M₂, IsPLOn n n f' (T.coreSpace 0) ∧ InjOn f' (T.coreSpace 0) ∧
            ∀ x ∈ T.coreSpace 0, dist (f' x) (h x) < ε) ∧
        ∀ (i : ℕ) (g f : M₁ → M₂), IsPLHomeomorphInto n g (T.coreSpace i) →
          IsPLOn n n f (T.coreSpace (i + 1)) → EqOn f g (T.coreSpace i) →
          ∀ {ε : ℝ}, 0 < ε → (∀ x ∈ T.coreSpace (i + 1), dist (f x) (h x) < ε) →
            ∃ f' : M₁ → M₂, IsPLOn n n f' (T.coreSpace (i + 1)) ∧
              InjOn f' (T.coreSpace (i + 1)) ∧ EqOn f' g (T.coreSpace i) ∧
                ∀ x ∈ T.coreSpace (i + 1), dist (f' x) (h x) < ε

namespace LocallyFinitePieceTower

section Witness

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁] [MetricSpace M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
  {K : Set M₁}

theorem exists_isPLOn_injOn_eqOn_dist_lt_of_eqOn_of_subset
    (T : LocallyFinitePieceTower n M₁ K) {i : ℕ}
    (hsub : T.coreSpace (i + 1) ⊆ T.coreSpace i) {g f h : M₁ → M₂} {ε : ℝ}
    (hg : InjOn g (T.coreSpace i)) (hf : IsPLOn n n f (T.coreSpace (i + 1)))
    (hfg : EqOn f g (T.coreSpace i))
    (hd : ∀ x ∈ T.coreSpace (i + 1), dist (f x) (h x) < ε) :
    ∃ f' : M₁ → M₂, IsPLOn n n f' (T.coreSpace (i + 1)) ∧ InjOn f' (T.coreSpace (i + 1)) ∧
      EqOn f' g (T.coreSpace i) ∧ ∀ x ∈ T.coreSpace (i + 1), dist (f' x) (h x) < ε :=
  ⟨f, hf, fun _ hx _ hy hxy =>
    hg (hsub hx) (hsub hy) ((hfg (hsub hx)).symm.trans (hxy.trans (hfg (hsub hy)))), hfg, hd⟩

end Witness

section Reduction

variable {n : ℕ} {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁]
  [SecondCountableTopology M₁] [MetricSpace M₂] [SecondCountableTopology M₂]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₂]
  [HasGroupoid M₁ (plGroupoid n)] [HasGroupoid M₂ (plGroupoid n)]

theorem exists_isPLOn_injOn_dist_lt_coreSpace_zero
    (H : Moise352StageInjection.{u} n) {K : Set M₁} (T : LocallyFinitePieceTower n M₁ K)
    (hT : ∀ i, IsCombinatorialManifoldWithBoundary n (T.piece i).piece.complex)
    {h : M₁ → M₂} (hh : Topology.IsEmbedding (K.domRestrict h)) {φ : M₁ → ℝ}
    (hφ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ T.coreSpace 0, c ≤ φ x) :
    ∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace 0) ∧ InjOn f (T.coreSpace 0) ∧
      ∀ x ∈ T.coreSpace 0, dist (f x) (h x) < φ x := by
  obtain ⟨c, hc, hcle⟩ := hφ
  have hcont : ContinuousOn h (T.coreSpace 0) :=
    (continuousOn_iff_continuous_domRestrict.mpr hh.continuous).mono
      (T.core_space_subset_union 0)
  obtain ⟨f, hf, hfd⟩ := T.exists_isPLOn_dist_lt_coreSpace 0 hcont hc
  obtain ⟨f', hf', hinj', hd'⟩ := (H T hT hh).1 f hf hc hfd
  exact ⟨f', hf', hinj', fun x hx => lt_of_lt_of_le (hd' x hx) (hcle x hx)⟩

theorem exists_pos_forall_exists_isPLOn_injOn_eqOn_dist_lt_coreSpace_succ
    (H : Moise352StageInjection.{u} n) {K : Set M₁} (T : LocallyFinitePieceTower n M₁ K)
    (hT : ∀ i, IsCombinatorialManifoldWithBoundary n (T.piece i).piece.complex)
    {h : M₁ → M₂} (hh : Topology.IsEmbedding (K.domRestrict h)) (i : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ g : M₁ → M₂, IsPLHomeomorphInto n g (T.coreSpace i) →
      (∀ x ∈ T.coreSpace i, dist (g x) (h x) < η) →
        ∃ f : M₁ → M₂, IsPLOn n n f (T.coreSpace (i + 1)) ∧ InjOn f (T.coreSpace (i + 1)) ∧
          EqOn f g (T.coreSpace i) ∧ ∀ x ∈ T.coreSpace (i + 1), dist (f x) (h x) < ε := by
  have hcont : ContinuousOn h (T.coreSpace (i + 1)) :=
    (continuousOn_iff_continuous_domRestrict.mpr hh.continuous).mono
      (T.core_space_subset_union (i + 1))
  obtain ⟨η, hη, hηprop⟩ :=
    T.exists_pos_forall_exists_isPLOn_eqOn_dist_lt_coreSpace_succ i hcont hε
  refine ⟨η, hη, fun g hg hgd => ?_⟩
  obtain ⟨f, hf, hfeq, hfd⟩ := hηprop g hg.isPLOn hgd
  exact (H T hT hh).2 i g f hg hf hfeq hε hfd

end Reduction

end LocallyFinitePieceTower

end Obligation

end DifferentialGeometry.Topology.PiecewiseLinear
