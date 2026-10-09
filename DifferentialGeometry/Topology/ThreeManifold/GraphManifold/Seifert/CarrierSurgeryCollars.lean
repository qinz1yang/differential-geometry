import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter
import DifferentialGeometry.Topology.Manifold.CollarFamily

/-!
Uniform disjoint half collars for abstract torus surgery. Compact disjoint zero sections admit
one common positive shrink width, including collars retained at the external boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

universe u v

namespace GC.Seifert

private theorem surgeryContinuousHalfLift : Continuous halfSpaceOneLift := by
  have he : halfSpaceOneLift = fun t : ℝ =>
      halfSpaceOneHomeomorph.symm ⟨max 0 t, le_max_left 0 t⟩ :=
    funext halfSpaceOneLift_eq
  rw [he]
  exact halfSpaceOneHomeomorph.symm.continuous.comp
    ((continuous_const.max continuous_id).subtype_mk (fun t => le_max_left 0 t))

private def surgeryClampedHalfPoint (s : {r : ℝ // 0 ≤ r}) : EuclideanHalfSpace 1 :=
  halfSpaceOneLift (min (s : ℝ) (1 / 2))

private theorem surgeryClampedHalfPoint_coord (s : {r : ℝ // 0 ≤ r}) :
    (surgeryClampedHalfPoint s).1 0 = min (s : ℝ) (1 / 2) := by
  change max (min (s : ℝ) (1 / 2)) 0 = min (s : ℝ) (1 / 2)
  exact max_eq_left (le_min s.property (by norm_num))

private theorem surgeryClampedHalfPoint_continuous : Continuous surgeryClampedHalfPoint :=
  surgeryContinuousHalfLift.comp (continuous_subtype_val.min continuous_const)

private theorem surgeryClampedHalfPoint_zero :
    surgeryClampedHalfPoint 0 = halfZero := by
  change halfSpaceOneLift (min (0 : ℝ) (1 / 2)) = halfZero
  norm_num
  exact (halfSpaceOneLift_coord halfZero).trans rfl

theorem exists_disjoint_shrunk_halfCollars (C : CompactCarrier.{u})
    {ι : Type v} [Finite ι]
    (c : ι → PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hs : ∀ i, (c i).source = halfCollarSource)
    (hd : Pairwise fun i j => Disjoint
      (range fun t => c i (t, halfZero)) (range fun t => c j (t, halfZero))) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧ Pairwise fun i j =>
      Disjoint (shrinkHalfCollar hδ (c i)).target (shrinkHalfCollar hδ (c j)).target := by
  let f : ι → ULift.{u} Torus × {r : ℝ // 0 ≤ r} → C.Carrier :=
    fun i p => c i (p.1.down, surgeryClampedHalfPoint p.2)
  have hf : ∀ i, Continuous (f i) := by
    intro i
    apply (c i).toOpenPartialHomeomorph.continuousOn.comp_continuous
      ((continuous_uliftDown.comp continuous_fst).prodMk
        (surgeryClampedHalfPoint_continuous.comp continuous_snd))
    intro p
    change (p.1.down, surgeryClampedHalfPoint p.2) ∈ (c i).source
    rw [hs i]
    change (surgeryClampedHalfPoint p.2).1 0 < 1
    rw [surgeryClampedHalfPoint_coord]
    exact (min_le_right p.2.val (1 / 2)).trans_lt (by norm_num)
  have hzero : ∀ i (t : ULift.{u} Torus), f i (t, 0) = c i (t.down, halfZero) := by
    intro i t
    simp only [f, surgeryClampedHalfPoint_zero]
  have hrange : ∀ i, (range fun t : ULift.{u} Torus => c i (t.down, halfZero)) =
      range fun t : Torus => c i (t, halfZero) := by
    intro i
    ext x
    exact ⟨fun ⟨t, ht⟩ => ⟨t.down, ht⟩, fun ⟨t, ht⟩ => ⟨ULift.up t, ht⟩⟩
  have hd' : Pairwise fun i j => Disjoint
      (range fun t : ULift.{u} Torus => c i (t.down, halfZero))
      (range fun t : ULift.{u} Torus => c j (t.down, halfZero)) := by
    intro i j hij
    rw [hrange i, hrange j]
    exact hd hij
  obtain ⟨a, ha, hpair⟩ := Collar.disjointHalfCollarFamily hf hzero hd'
  let δ : ℝ := min a (1 / 2)
  have hδ : 0 < δ := lt_min ha (by norm_num)
  have hδ1 : δ ≤ 1 := (min_le_right a (1 / 2)).trans (by norm_num)
  have hsub : ∀ i, (shrinkHalfCollar hδ (c i)).target ⊆
      f i '' {p : ULift.{u} Torus × {r : ℝ // 0 ≤ r} | (p.2 : ℝ) < a} := by
    intro i y hy
    let p := (shrinkHalfCollar hδ (c i)).symm y
    have hp := (shrinkHalfCollar hδ (c i)).map_target' hy
    have hp1 : p.2.1 0 < 1 := by
      rwa [shrinkHalfCollar_source hδ hδ1 (hs i)] at hp
    let s := halfSpaceScale hδ p.2
    have hsa : s.1 0 < a := (halfSpaceScale_lt hδ hp1).trans_le (min_le_left a (1 / 2))
    have hslo : s.1 0 < 1 / 2 :=
      (halfSpaceScale_lt hδ hp1).trans_le (min_le_right a (1 / 2))
    refine ⟨(ULift.up p.1, ⟨s.1 0, s.2⟩), hsa, ?_⟩
    have he : surgeryClampedHalfPoint ⟨s.1 0, s.2⟩ = s := by
      unfold surgeryClampedHalfPoint
      rw [min_eq_left hslo.le]
      exact halfSpaceOneLift_coord s
    change c i (p.1, surgeryClampedHalfPoint ⟨s.1 0, s.2⟩) = y
    rw [he]
    exact (shrinkHalfCollar hδ (c i)).right_inv' hy
  exact ⟨δ, hδ, hδ1, fun i j hij => (hpair hij).mono (hsub i) (hsub j)⟩

end GC.Seifert

namespace GC.GraphManifold.TorusPairing

open GC.Seifert

variable {C : CompactCarrier.{u}}

theorem leftCollar_zero_range (P : TorusPairing C) (j : Fin P.count) :
    (range fun t => P.leftCollar j (t, halfZero)) = P.gluing.left j := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    change P.leftCollar j (t, halfZero) ∈ P.gluing.left j
    rw [P.left_zero]
    exact (P.leftParam j t).property
  · intro hx
    refine ⟨(P.leftParam j).symm ⟨x, hx⟩, ?_⟩
    change P.leftCollar j ((P.leftParam j).symm ⟨x, hx⟩, halfZero) = x
    rw [P.left_zero]
    exact congrArg Subtype.val ((P.leftParam j).apply_symm_apply ⟨x, hx⟩)

theorem rightCollar_zero_range (P : TorusPairing C) (j : Fin P.count) :
    (range fun t => P.rightCollar j (t, halfZero)) = P.gluing.right j := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    change P.rightCollar j (t, halfZero) ∈ P.gluing.right j
    rw [P.right_zero]
    exact (P.rightParam j t).property
  · intro hx
    refine ⟨(P.rightParam j).symm ⟨x, hx⟩, ?_⟩
    change P.rightCollar j ((P.rightParam j).symm ⟨x, hx⟩, halfZero) = x
    rw [P.right_zero]
    exact congrArg Subtype.val ((P.rightParam j).apply_symm_apply ⟨x, hx⟩)

def surgerySideCollar (P : TorusPairing C) :
    Fin P.count ⊕ Fin P.count → PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞ :=
  Sum.elim P.leftCollar P.rightCollar

theorem surgerySideCollar_source (P : TorusPairing C)
    (i : Fin P.count ⊕ Fin P.count) : (P.surgerySideCollar i).source = halfCollarSource := by
  cases i with
  | inl j => exact P.left_source j
  | inr j => exact P.right_source j

theorem surgerySideCollar_zero_disjoint (P : TorusPairing C) : Pairwise fun i j =>
    Disjoint (range fun t => P.surgerySideCollar i (t, halfZero))
      (range fun t => P.surgerySideCollar j (t, halfZero)) := by
  intro i j hij
  cases i with
  | inl a =>
    cases j with
    | inl b =>
      rw [surgerySideCollar, Sum.elim_inl, Sum.elim_inl,
        P.leftCollar_zero_range, P.leftCollar_zero_range]
      exact (P.gluing.disjoint_blocks a b (fun h => hij (congrArg Sum.inl h))).mono
        subset_union_left subset_union_left
    | inr b =>
      rw [surgerySideCollar, Sum.elim_inl, Sum.elim_inr,
        P.leftCollar_zero_range, P.rightCollar_zero_range]
      by_cases hab : a = b
      · subst b
        exact P.gluing.disjoint_left_right a
      · exact (P.gluing.disjoint_blocks a b hab).mono subset_union_left subset_union_right
  | inr a =>
    cases j with
    | inl b =>
      rw [surgerySideCollar, Sum.elim_inr, Sum.elim_inl,
        P.rightCollar_zero_range, P.leftCollar_zero_range]
      by_cases hab : a = b
      · subst b
        exact (P.gluing.disjoint_left_right a).symm
      · exact (P.gluing.disjoint_blocks a b hab).mono subset_union_right subset_union_left
    | inr b =>
      rw [surgerySideCollar, Sum.elim_inr, Sum.elim_inr,
        P.rightCollar_zero_range, P.rightCollar_zero_range]
      exact (P.gluing.disjoint_blocks a b (fun h => hij (congrArg Sum.inr h))).mono
        subset_union_right subset_union_right

def surgeryBoundaryCollar (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n) :
    (Fin P.count ⊕ Fin P.count) ⊕ Fin n → PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞ :=
  Sum.elim P.surgerySideCollar E.collar

theorem surgeryBoundaryCollar_source (P : TorusPairing C) {n : ℕ} (E : BoundaryTori C n)
    (i : (Fin P.count ⊕ Fin P.count) ⊕ Fin n) :
    (P.surgeryBoundaryCollar E i).source = halfCollarSource := by
  cases i with
  | inl j => exact P.surgerySideCollar_source j
  | inr j => exact E.source_eq j

private theorem surgerySideCollar_zero_subset (P : TorusPairing C)
    (i : Fin P.count ⊕ Fin P.count) :
    (range fun t => P.surgerySideCollar i (t, halfZero)) ⊆ ⋃ j, P.gluing.block j := by
  cases i with
  | inl j =>
    rw [surgerySideCollar, Sum.elim_inl, P.leftCollar_zero_range]
    exact (subset_union_left : P.gluing.left j ⊆ P.gluing.block j).trans
      (subset_iUnion_of_subset j subset_rfl)
  | inr j =>
    rw [surgerySideCollar, Sum.elim_inr, P.rightCollar_zero_range]
    exact (subset_union_right : P.gluing.right j ⊆ P.gluing.block j).trans
      (subset_iUnion_of_subset j subset_rfl)

private theorem surgeryExternal_zero_subset {n : ℕ} (E : BoundaryTori C n) (j : Fin n) :
    (range fun t => E.collar j (t, halfZero)) ⊆ E.image :=
  subset_iUnion_of_subset j subset_rfl

private theorem surgeryExternal_zero_target {n : ℕ} (E : BoundaryTori C n) (j : Fin n) :
    (range fun t => E.collar j (t, halfZero)) ⊆ (E.collar j).target := by
  rintro x ⟨t, rfl⟩
  apply (E.collar j).map_source'
  rw [E.source_eq]
  change (halfZero : EuclideanHalfSpace 1).1 0 < 1
  change (0 : ℝ) < 1
  norm_num

theorem exists_disjoint_surgeryBoundaryCollars (P : TorusPairing C) {n : ℕ}
    (E : BoundaryTori C n) (hd : Disjoint (⋃ j, P.gluing.block j) E.image) :
    ∃ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧ Pairwise fun i j =>
      Disjoint (shrinkHalfCollar hδ (P.surgeryBoundaryCollar E i)).target
        (shrinkHalfCollar hδ (P.surgeryBoundaryCollar E j)).target := by
  apply GC.Seifert.exists_disjoint_shrunk_halfCollars C (P.surgeryBoundaryCollar E)
    (P.surgeryBoundaryCollar_source E)
  intro i j hij
  cases i with
  | inl a =>
    cases j with
    | inl b =>
      exact P.surgerySideCollar_zero_disjoint (fun h => hij (congrArg Sum.inl h))
    | inr b =>
      exact hd.mono (P.surgerySideCollar_zero_subset a) (surgeryExternal_zero_subset E b)
  | inr a =>
    cases j with
    | inl b =>
      exact hd.symm.mono (surgeryExternal_zero_subset E a) (P.surgerySideCollar_zero_subset b)
    | inr b =>
      exact (E.disjoint (fun h => hij (congrArg Sum.inr h))).mono
        (surgeryExternal_zero_target E a) (surgeryExternal_zero_target E b)

end GC.GraphManifold.TorusPairing
