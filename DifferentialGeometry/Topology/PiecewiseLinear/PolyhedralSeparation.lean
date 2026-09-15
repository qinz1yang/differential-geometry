import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPiecewiseAffineOn.isPolyhedron_sublevel {f : E → ℝ} {P : Set E}
    (hf : IsPiecewiseAffineOn f P) (hP : IsPolyhedron P) (r : ℝ) :
    IsPolyhedron (P ∩ {x | f x ≤ r}) := by
  classical
  obtain ⟨K, hKfinite, hKspace⟩ := hP.exists_simplicialComplex
  let _ : Finite K.faces := hKfinite.to_subtype
  obtain ⟨R, hR, hRfinite, hAff⟩ :=
    (hKspace.symm ▸ hf).exists_isSubdivision_affineOn_faces K
  let _ : Finite R.faces := hRfinite.to_subtype
  choose A hA using hAff
  have heq : P ∩ {x | f x ≤ r} =
      ⋃ s : R.faces, convexHull ℝ ((s : Finset E) : Set E) ∩ {x | A s s.property x ≤ r} := by
    ext x
    constructor
    · rintro ⟨hxP, hfx⟩
      obtain ⟨s, hs, hxs⟩ := R.mem_space_iff.mp ((hR.space_eq.trans hKspace).symm ▸ hxP)
      exact mem_iUnion.mpr ⟨⟨s, hs⟩, hxs, by simpa only [mem_ofPred_eq, hA s hs hxs] using hfx⟩
    · intro hx
      obtain ⟨s, hxs, hfx⟩ := mem_iUnion.mp hx
      exact ⟨(hR.space_eq.trans hKspace) ▸ R.convexHull_subset_space s.property hxs,
        by simpa only [mem_ofPred_eq, ← hA s s.property hxs] using hfx⟩
  rw [heq]
  exact IsPolyhedron.iUnion fun s =>
    ((isHPolytope_convexHull_of_affineIndependent _ (R.indep s.property)).inter_affine_le
      (A s s.property) r).isPolyhedron

theorem IsHPolytope.exists_nonneg_piecewiseAffine_zero_set {P : Set E} (hP : IsHPolytope P) :
    ∃ f : E → ℝ, IsPiecewiseAffineOn f univ ∧ (∀ x, 0 ≤ f x) ∧
      ∀ x, f x = 0 ↔ x ∈ P := by
  classical
  obtain ⟨-, ι, hι, l, c, rfl⟩ := hP
  let _ : Fintype ι := Fintype.ofFinite ι
  have hfinite : ∀ s : Finset ι, ∃ f : E → ℝ, IsPiecewiseAffineOn f univ ∧
      (∀ x, 0 ≤ f x) ∧ ∀ x, f x = 0 ↔ ∀ i ∈ s, l i x ≤ c i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨fun _ => 0, isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E 0) isOpen_univ,
          fun _ => le_rfl, ?_⟩
        intro x
        simp
    | @insert i s hi ih =>
        obtain ⟨f, hf, hf0, hfzero⟩ := ih
        let A : E →ᵃ[ℝ] ℝ := (l i).toAffineMap - AffineMap.const ℝ E (c i)
        refine ⟨fun x => max (f x) (A x), hf.max
          (isPiecewiseAffineOn_of_affine A isOpen_univ), fun x => (hf0 x).trans (le_max_left _ _), ?_⟩
        intro x
        have hAx : A x = l i x - c i := rfl
        constructor
        · intro hx j hj
          have hzero : f x = 0 := le_antisymm (hx ▸ le_max_left _ _) (hf0 x)
          rcases Finset.mem_insert.mp hj with rfl | hj
          · have hle : A x ≤ 0 := hx ▸ le_max_right _ _
            linarith
          · exact (hfzero x).mp hzero j hj
        · intro hx
          have hz := (hfzero x).mpr fun j hj => hx j (Finset.mem_insert_of_mem hj)
          have hle : A x ≤ 0 := by rw [hAx]; exact sub_nonpos.mpr (hx i (Finset.mem_insert_self _ _))
          change max (f x) (A x) = 0
          rw [hz, max_eq_left hle]
  obtain ⟨f, hf, hf0, hfzero⟩ := hfinite Finset.univ
  exact ⟨f, hf, hf0, fun x => by simpa only [mem_ofPred_eq, Finset.mem_univ, forall_const] using hfzero x⟩

theorem IsPolyhedron.exists_nonneg_piecewiseAffine_zero_set {P : Set E} (hP : IsPolyhedron P) :
    ∃ f : E → ℝ, IsPiecewiseAffineOn f univ ∧ (∀ x, 0 ≤ f x) ∧
      ∀ x, f x = 0 ↔ x ∈ P := by
  classical
  obtain ⟨ι, hι, C, hC, rfl⟩ := hP
  let _ : Fintype ι := Fintype.ofFinite ι
  have hfinite : ∀ s : Finset ι, ∃ f : E → ℝ, IsPiecewiseAffineOn f univ ∧
      (∀ x, 0 ≤ f x) ∧ ∀ x, f x = 0 ↔ x ∈ ⋃ i ∈ s, C i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨fun _ => 1, isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E 1) isOpen_univ,
          fun _ => zero_le_one, ?_⟩
        intro x
        simp
    | @insert i s hi ih =>
        obtain ⟨f, hf, hf0, hfzero⟩ := ih
        obtain ⟨g, hg, hg0, hgzero⟩ := (hC i).exists_nonneg_piecewiseAffine_zero_set
        refine ⟨fun x => min (f x) (g x), hf.min hg, fun x => le_min (hf0 x) (hg0 x), ?_⟩
        intro x
        change min (f x) (g x) = 0 ↔ _
        have hz : min (f x) (g x) = 0 ↔ f x = 0 ∨ g x = 0 := by
          rcases le_total (f x) (g x) with hle | hle
          · rw [min_eq_left hle]
            exact ⟨Or.inl, fun h => h.elim id (fun hgzero => le_antisymm (hgzero ▸ hle) (hf0 x))⟩
          · rw [min_eq_right hle]
            exact ⟨Or.inr, fun h => h.elim (fun hfzero => le_antisymm (hfzero ▸ hle) (hg0 x)) id⟩
        rw [hz, hfzero, hgzero]
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_union]
        exact or_comm
  obtain ⟨f, hf, hf0, hfzero⟩ := hfinite Finset.univ
  exact ⟨f, hf, hf0, fun x => by simpa only [Finset.mem_univ, iUnion_true] using hfzero x⟩

theorem exists_isPolyhedron_neighborhood_sdiff {C A U : Set E}
    (hC : IsPolyhedron C) (hA : IsPolyhedron A) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ N : Set E, IsPolyhedron N ∧ C \ A ⊆ interior N ∧ N ⊆ U ∧ N ∩ A = C ∩ A := by
  obtain ⟨P, hP, hCP, hPU⟩ := exists_isPolyhedron_neighborhood hC.isCompact hU hCU
  obtain ⟨f, hf, hf0, hfzero⟩ := hC.exists_nonneg_piecewiseAffine_zero_set
  obtain ⟨g, hg, hg0, hgzero⟩ := hA.exists_nonneg_piecewiseAffine_zero_set
  let N := P ∩ {x | f x - g x ≤ 0}
  have hdiff : IsPiecewiseAffineOn (fun x => f x - g x) P := by
    have h := hf.add (hg.affine_comp (-AffineMap.id ℝ ℝ))
    exact (show IsPiecewiseAffineOn (fun x => f x - g x) univ from h).mono_of_isPolyhedron hP
      (subset_univ P)
  refine ⟨N, hdiff.isPolyhedron_sublevel hP 0, ?_, inter_subset_left.trans hPU, ?_⟩
  · have hfcont : Continuous f := continuousOn_univ.mp hf.continuousOn
    have hgcont : Continuous g := continuousOn_univ.mp hg.continuousOn
    have hopen : IsOpen (interior P ∩ {x | f x - g x < 0}) :=
      isOpen_interior.inter (isOpen_lt
        (hfcont.sub hgcont)
        continuous_const)
    have hsub : interior P ∩ {x | f x - g x < 0} ⊆ N :=
      fun x hx => ⟨interior_subset hx.1, (show f x - g x < 0 from hx.2).le⟩
    intro x hx
    apply interior_maximal hsub hopen
    have hfz := (hfzero x).mpr hx.1
    have hgpos : 0 < g x := lt_of_le_of_ne (hg0 x) (fun heq => hx.2 ((hgzero x).mp heq.symm))
    exact ⟨hCP hx.1, by change f x - g x < 0; linarith⟩
  · ext x
    constructor
    · rintro ⟨⟨_, hle⟩, hxA⟩
      have hgzero' := (hgzero x).mpr hxA
      refine ⟨(hfzero x).mp (le_antisymm ?_ (hf0 x)), hxA⟩
      change f x - g x ≤ 0 at hle
      linarith
    · rintro ⟨hxC, hxA⟩
      exact ⟨⟨interior_subset (hCP hxC), by
        change f x - g x ≤ 0
        rw [(hfzero x).mpr hxC, (hgzero x).mpr hxA, sub_self]⟩, hxA⟩

end DifferentialGeometry.Topology.PiecewiseLinear
