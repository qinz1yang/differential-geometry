import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph
import Mathlib.Topology.Algebra.AffineSubspace
import Mathlib.Topology.MetricSpace.Contracting

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsPiecewiseAffineWithinAt.affine_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {s : Set E} {x : E}
    (hf : IsPiecewiseAffineWithinAt f s x) (A : F →ᵃ[ℝ] G) :
    IsPiecewiseAffineWithinAt (A ∘ f) s x := by
  obtain ⟨ι, hι, C, B, hC, hCx⟩ := hf
  refine ⟨ι, hι, C, fun i => A.comp (B i), fun i => ⟨(hC i).1, (hC i).2.1, ?_⟩, hCx⟩
  intro y hy
  change A (f y) = A (B i y)
  rw [(hC i).2.2 hy]

theorem IsPiecewiseAffineOn.affine_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) (A : F →ᵃ[ℝ] G) : IsPiecewiseAffineOn (A ∘ f) s :=
  fun x hx => (hf x hx).affine_comp A

theorem IsPiecewiseAffineWithinAt.prod_mk {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {g : E → G} {s : Set E} {x : E}
    (hf : IsPiecewiseAffineWithinAt f s x) (hg : IsPiecewiseAffineWithinAt g s x) :
    IsPiecewiseAffineWithinAt (fun y => (f y, g y)) s x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  obtain ⟨κ, hκ, D, B, hD, hDx⟩ := hg
  have := hι
  have := hκ
  refine ⟨ι × κ, inferInstance, fun p => C p.1 ∩ D p.2, fun p => (A p.1).prod (B p.2),
    fun p => ⟨(hC p.1).1.inter (hD p.2).1, inter_subset_left.trans (hC p.1).2.1, ?_⟩, ?_⟩
  · intro y hy
    exact Prod.ext ((hC p.1).2.2 hy.1) ((hD p.2).2.2 hy.2)
  · have heq : (⋃ p : ι × κ, C p.1 ∩ D p.2) = (⋃ i, C i) ∩ ⋃ j, D j := by
      ext y
      simp
    rw [heq]
    exact Filter.inter_mem hCx hDx

theorem IsPiecewiseAffineOn.prod_mk {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {g : E → G} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) (hg : IsPiecewiseAffineOn g s) :
    IsPiecewiseAffineOn (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prod_mk (hg x hx)

theorem IsPiecewiseAffineOn.add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {s : Set E} (hf : IsPiecewiseAffineOn f s) (hg : IsPiecewiseAffineOn g s) :
    IsPiecewiseAffineOn (fun x => f x + g x) s :=
  (hf.prod_mk hg).affine_comp ((LinearMap.fst ℝ F F + LinearMap.snd ℝ F F).toAffineMap)

theorem IsHPolytope.inter_affine_le [FiniteDimensional ℝ E] {C : Set E} (hC : IsHPolytope C)
    (A : E →ᵃ[ℝ] ℝ) (r : ℝ) : IsHPolytope (C ∩ {x | A x ≤ r}) := by
  obtain ⟨hCc, ι, hι, l, c, rfl⟩ := hC
  have := hι
  refine ⟨hCc.inter_right (isClosed_le A.continuous_of_finiteDimensional continuous_const),
    Unit ⊕ ι, inferInstance, Sum.elim (fun _ => A.linear) l,
    Sum.elim (fun _ => r - A 0) c, ?_⟩
  ext x
  have hAx : A x = A.linear x + A 0 := by simpa using A.map_vadd 0 x
  simp only [mem_inter_iff, mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr, forall_const]
  constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨by rw [hAx] at h₁; linarith, h₀⟩
  · rintro ⟨h₁, h₀⟩
    exact ⟨h₀, by rw [hAx]; linarith⟩

theorem isPiecewiseAffineOn_max :
    IsPiecewiseAffineOn (fun p : ℝ × ℝ => max p.1 p.2) univ := by
  intro p _
  obtain ⟨Q, hQ, _, hQp⟩ := exists_isHPolytope_subset_mem_nhds (x := p) (U := univ) Filter.univ_mem
  let A : (ℝ × ℝ) →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ).toAffineMap
  refine ⟨Bool, inferInstance,
    (fun b => if b then Q ∩ {z | (-A) z ≤ 0} else Q ∩ {z | A z ≤ 0}),
    (fun b => if b then (LinearMap.fst ℝ ℝ ℝ).toAffineMap else (LinearMap.snd ℝ ℝ ℝ).toAffineMap),
    ?_, ?_⟩
  · intro b
    cases b with
    | false =>
      refine ⟨hQ.inter_affine_le A 0, subset_univ _, ?_⟩
      rintro z ⟨_, hz⟩
      change z.1 - z.2 ≤ 0 at hz
      exact max_eq_right (by linarith)
    | true =>
      refine ⟨hQ.inter_affine_le (-A) 0, subset_univ _, ?_⟩
      rintro z ⟨_, hz⟩
      change -(z.1 - z.2) ≤ 0 at hz
      exact max_eq_left (by linarith)
  · apply mem_nhdsWithin_of_mem_nhds
    apply Filter.mem_of_superset hQp
    intro z hz
    rcases le_total z.1 z.2 with h | h
    · exact mem_iUnion.mpr ⟨false, hz, show A z ≤ 0 by change z.1 - z.2 ≤ 0; linarith⟩
    · exact mem_iUnion.mpr ⟨true, hz, show (-A) z ≤ 0 by change -(z.1 - z.2) ≤ 0; linarith⟩

theorem IsPiecewiseAffineOn.max [FiniteDimensional ℝ E] {f g : E → ℝ} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) (hg : IsPiecewiseAffineOn g s) :
    IsPiecewiseAffineOn (fun x => max (f x) (g x)) s := by
  have h := isPiecewiseAffineOn_max.comp (hf.prod_mk hg)
  rw [preimage_univ, inter_univ] at h
  exact h.congr fun _ _ => rfl

theorem IsPiecewiseAffineOn.min [FiniteDimensional ℝ E] {f g : E → ℝ} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) (hg : IsPiecewiseAffineOn g s) :
    IsPiecewiseAffineOn (fun x => min (f x) (g x)) s := by
  have h := ((hf.affine_comp (-AffineMap.id ℝ ℝ)).max (hg.affine_comp (-AffineMap.id ℝ ℝ))).affine_comp
    (-AffineMap.id ℝ ℝ)
  change IsPiecewiseAffineOn (fun x => -Max.max (-f x) (-g x)) s at h
  refine h.congr fun x _ => ?_
  change Min.min (f x) (g x) = -Max.max (-f x) (-g x)
  rcases le_total (f x) (g x) with hle | hle
  · rw [min_eq_left hle, max_eq_left (neg_le_neg hle), neg_neg]
  · rw [min_eq_right hle, max_eq_right (neg_le_neg hle), neg_neg]

theorem isPLHomeomorphOn_id_add_of_lipschitz [FiniteDimensional ℝ E] {f : E → E} {k : NNReal}
    (hf : IsPiecewiseAffineOn f univ) (hlip : LipschitzWith k f) (hk : k < 1) :
    IsPLHomeomorphOn (fun x => x + f x) univ univ := by
  have hcon : ∀ y : E, ContractingWith k (fun x => y - f x) := by
    intro y
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun x z => ?_⟩
    have heq : (y - f x) - (y - f z) = -(f x - f z) := by abel
    rw [dist_eq_norm, heq, norm_neg]
    simpa only [dist_eq_norm] using hlip.dist_le_mul x z
  have hbij : Function.Bijective (fun x => x + f x) := by
    constructor
    · intro x y hxy
      change x + f x = y + f y at hxy
      apply (hcon (x + f x)).fixedPoint_unique'
      · change x + f x - f x = x
        abel
      · change x + f x - f y = y
        rw [hxy]
        abel
    · intro y
      let x := ContractingWith.fixedPoint (fun z => y - f z) (hcon y)
      refine ⟨x, ?_⟩
      exact eq_sub_iff_add_eq.mp (hcon y).fixedPoint_isFixedPt.symm
  let g := Equiv.ofBijective (fun x => x + f x) hbij
  have hkpos : (0 : ℝ) < 1 - k := sub_pos.mpr hk
  have hginv : LipschitzWith (⟨1 / (1 - k), by positivity⟩ : NNReal) g.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have hy : g.symm y + f (g.symm y) = y := g.apply_symm_apply y
    have hz : g.symm z + f (g.symm z) = z := g.apply_symm_apply z
    have heq : g.symm y - g.symm z = (y - z) - (f (g.symm y) - f (g.symm z)) := by
      calc g.symm y - g.symm z =
          ((g.symm y + f (g.symm y)) - (g.symm z + f (g.symm z))) -
            (f (g.symm y) - f (g.symm z)) := by abel
        _ = (y - z) - (f (g.symm y) - f (g.symm z)) := by rw [hy, hz]
    have htriangle := norm_sub_le (y - z) (f (g.symm y) - f (g.symm z))
    rw [← heq] at htriangle
    have hfbound := hlip.dist_le_mul (g.symm y) (g.symm z)
    simp only [dist_eq_norm] at hfbound ⊢
    change ‖g.symm y - g.symm z‖ ≤ 1 / (1 - (k : ℝ)) * ‖y - z‖
    calc ‖g.symm y - g.symm z‖ ≤ ‖y - z‖ / (1 - k) := (le_div_iff₀ hkpos).mpr (by nlinarith)
      _ = 1 / (1 - (k : ℝ)) * ‖y - z‖ := by ring
  let e : E ≃ₜ E :=
    { toEquiv := g
      continuous_toFun := continuous_id.add hlip.continuous
      continuous_invFun := hginv.continuous }
  have hpl : IsPiecewiseAffineOn (fun x => x + f x) univ :=
    (isPiecewiseAffineOn_id isOpen_univ).add hf
  have hplinv : IsPiecewiseAffineOn e.symm univ :=
    IsPiecewiseAffineOn.symm (e := e.toOpenPartialHomeomorph) hpl
  have hbijSet : BijOn (fun x => x + f x) univ univ := by
    refine ⟨mapsTo_univ _ _, fun x _ y _ hxy => hbij.1 hxy, fun y _ => ?_⟩
    obtain ⟨x, hx⟩ := hbij.2 y
    exact ⟨x, mem_univ _, hx⟩
  refine ⟨hbijSet, hpl, hplinv.congr fun y hy => ?_⟩
  apply hbij.1
  exact (hbijSet.invOn_invFunOn.2 hy).trans (g.apply_symm_apply y).symm

theorem interior_eq_empty_of_affineSubspace_ne_top (s : AffineSubspace ℝ E) (hs : s ≠ ⊤) :
    interior (s : Set E) = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hxs : x ∈ s := interior_subset hx
  have hcont : ContinuousAt (fun v : E => v + x) (0 : E) := by fun_prop
  have hpre : (fun v : E => v + x) ⁻¹' (s : Set E) ∈ 𝓝 (0 : E) :=
    hcont.preimage_mem_nhds
      (by simpa only [zero_add] using mem_interior_iff_mem_nhds.mp hx)
  have hdir : (s.direction : Set E) ∈ 𝓝 (0 : E) := by
    apply Filter.mem_of_superset hpre
    intro v hv
    change v ∈ s.direction
    have hmem := AffineSubspace.vsub_mem_direction hv hxs
    simpa only [vsub_eq_sub, add_sub_cancel_right] using hmem
  exact hs ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x, hxs⟩).mp
    (s.direction.eq_top_of_nonempty_interior' ⟨0, mem_interior_iff_mem_nhds.mpr hdir⟩))

theorem exists_mem_ball_notMem_affineSubspaces [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]
    (s : ι → AffineSubspace ℝ E) (hs : ∀ i, s i ≠ ⊤) {x : E} {ε : ℝ} (hε : 0 < ε) :
    ∃ y : E, dist y x < ε ∧ ∀ i, y ∉ s i := by
  classical
  have hclosed : ∀ i, IsClosed (s i : Set E) := fun i =>
    ((s i).isClosed_direction_iff).mp ((s i).direction.closed_of_finiteDimensional)
  have hint : interior (⋃ i, (s i : Set E)) = ∅ :=
    interior_iUnion_eq_empty_of_finite hclosed fun i =>
      interior_eq_empty_of_affineSubspace_ne_top (s i) (hs i)
  by_contra h
  have hsub : ball x ε ⊆ ⋃ i, (s i : Set E) := by
    intro y hy
    by_contra hyS
    apply h
    exact ⟨y, hy, fun i hi => hyS (mem_iUnion.mpr ⟨i, hi⟩)⟩
  have hx : x ∈ interior (⋃ i, (s i : Set E)) :=
    interior_maximal hsub isOpen_ball (mem_ball_self hε)
  rw [hint] at hx
  exact hx

theorem isPLHomeomorphOn_add_const [FiniteDimensional ℝ E] (a : E) :
    IsPLHomeomorphOn (fun x => x + a) univ univ := by
  have hbij : BijOn (fun x : E => x + a) univ univ :=
    ⟨mapsTo_univ _ _, fun _ _ _ _ h => add_right_cancel h,
      fun y _ => ⟨y - a, mem_univ _, sub_add_cancel _ _⟩⟩
  refine ⟨hbij, ?_, ?_⟩
  · exact isPiecewiseAffineOn_of_affine (AffineMap.id ℝ E + AffineMap.const ℝ E a) isOpen_univ
  · have hpl : IsPiecewiseAffineOn (fun y : E => y - a) univ :=
      isPiecewiseAffineOn_of_affine (AffineMap.id ℝ E - AffineMap.const ℝ E a) isOpen_univ
    refine hpl.congr fun y hy => ?_
    exact eq_sub_iff_add_eq.mpr (hbij.invOn_invFunOn.2 hy)

open Classical in
theorem exists_small_translation_transverse_faces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E, ‖a‖ < ε ∧ IsPLHomeomorphOn (fun x => x + a) univ univ ∧
      ∀ s ∈ K.faces, ∀ t ∈ L.faces,
        ((fun x => x + a) '' convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
          vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
  let I := {p : K.faces × L.faces //
    vectorSpan ℝ (p.1.val : Set E) ⊔ vectorSpan ℝ (p.2.val : Set E) ≠ ⊤}
  let B : I → AffineSubspace ℝ E := fun p =>
    AffineSubspace.mk' (p.val.2.val.centroid ℝ id - p.val.1.val.centroid ℝ id)
      (vectorSpan ℝ (p.val.1.val : Set E) ⊔ vectorSpan ℝ (p.val.2.val : Set E))
  have hB : ∀ p, B p ≠ ⊤ := by
    intro p h
    apply p.property
    have hdir := congrArg AffineSubspace.direction h
    simpa only [B, AffineSubspace.direction_mk', AffineSubspace.direction_top] using hdir
  obtain ⟨a, ha, havoid⟩ := exists_mem_ball_notMem_affineSubspaces B hB (x := 0) hε
  refine ⟨a, by simpa only [dist_zero_right] using ha, isPLHomeomorphOn_add_const a, ?_⟩
  intro s hs t ht hinter
  by_contra hdir
  let p : I := ⟨(⟨s, hs⟩, ⟨t, ht⟩), hdir⟩
  obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := hinter
  have hsC : s.centroid ℝ id ∈ affineSpan ℝ (s : Set E) :=
    convexHull_subset_affineSpan _ (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs))
  have htC : t.centroid ℝ id ∈ affineSpan ℝ (t : Set E) :=
    convexHull_subset_affineSpan _ (t.centroid_mem_convexHull (L.nonempty_of_mem_faces ht))
  have hxdir : x - s.centroid ℝ id ∈ vectorSpan ℝ (s : Set E) := by
    simpa only [vsub_eq_sub, direction_affineSpan] using
      AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ hx) hsC
  have hydir : x + a - t.centroid ℝ id ∈ vectorSpan ℝ (t : Set E) := by
    simpa only [vsub_eq_sub, direction_affineSpan] using
      AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ hy) htC
  apply havoid p
  change a ∈ AffineSubspace.mk' (t.centroid ℝ id - s.centroid ℝ id)
    (vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E))
  rw [AffineSubspace.mem_mk', vsub_eq_sub]
  have heq : a - (t.centroid ℝ id - s.centroid ℝ id) =
      (x + a - t.centroid ℝ id) - (x - s.centroid ℝ id) := by abel
  rw [heq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right hydir) (Submodule.mem_sup_left hxdir)

end DifferentialGeometry.Topology.PiecewiseLinear
