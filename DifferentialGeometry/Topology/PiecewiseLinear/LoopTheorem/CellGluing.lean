import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskUnion
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem exists_boundaryParam_paths_of_isCutPair_union
    {P R T : Set (EuclideanSpace ℝ (Fin 2))}
    {a b : EuclideanSpace ℝ (Fin 2)}
    (hR : Schoenflies.IsArcBetween R a b)
    (hT : Schoenflies.IsArcBetween T a b)
    (hinter : R ∩ T = {a, b}) (hfront : frontier P = R ∪ T) :
    ∃ (a' b' : frontier P) (ρ : Path a' b') (κ : Path b' a')
        (e : loopCircle ≃ₜ frontier P),
      Set.range (fun t => ((ρ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = R ∧
        Set.range (fun t => ((κ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = T ∧
          ∀ θ, e θ = pathToCircle (ρ.trans κ) θ := by
  have haR := hR.left_mem
  have hbR := hR.right_mem
  obtain ⟨f, hfc, hfi, hfimage, hf0, hf1⟩ := hR
  obtain ⟨g, hgc, hgi, hgimage, hg0, hg1⟩ := hT.reverse
  have ha : a ∈ frontier P := by
    rw [hfront]
    exact Or.inl haR
  have hb : b ∈ frontier P := by
    rw [hfront]
    exact Or.inl hbR
  let a' : frontier P := ⟨a, ha⟩
  let b' : frontier P := ⟨b, hb⟩
  have hfmem (t : unitInterval) : f t ∈ frontier P := by
    rw [hfront]
    apply Or.inl
    rw [← hfimage]
    exact ⟨t, t.property, rfl⟩
  have hgmem (t : unitInterval) : g t ∈ frontier P := by
    rw [hfront]
    apply Or.inr
    rw [← hgimage]
    exact ⟨t, t.property, rfl⟩
  let ρ : Path a' b' :=
    { toFun := fun t => ⟨f t, hfmem t⟩
      continuous_toFun := hfc.domRestrict.subtype_mk _
      source' := Subtype.ext hf0
      target' := Subtype.ext hf1 }
  let κ : Path b' a' :=
    { toFun := fun t => ⟨g t, hgmem t⟩
      continuous_toFun := hgc.domRestrict.subtype_mk _
      source' := Subtype.ext hg0
      target' := Subtype.ext hg1 }
  have hrangeρ : Set.range (fun t : unitInterval => ρ t) =
      {x : frontier P | (x : EuclideanSpace ℝ (Fin 2)) ∈ R} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      change f t ∈ R
      rw [← hfimage]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      change (x : EuclideanSpace ℝ (Fin 2)) ∈ R at hx
      rw [← hfimage] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, Subtype.ext htx⟩
  have hrangeκ : Set.range (fun t : unitInterval => κ t) =
      {x : frontier P | (x : EuclideanSpace ℝ (Fin 2)) ∈ T} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      change g t ∈ T
      rw [← hgimage]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      change (x : EuclideanSpace ℝ (Fin 2)) ∈ T at hx
      rw [← hgimage] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, Subtype.ext htx⟩
  have hmid : f 1 = g 0 := hf1.trans hg0.symm
  have hclose : g 1 = f 0 := hg1.trans hf0.symm
  have hmeet : ∀ z ∈ f '' Set.Icc 0 1, z ∈ g '' Set.Icc 0 1 →
      z = f 0 ∨ z = f 1 := by
    intro z hzR hzT
    rw [hfimage] at hzR
    rw [hgimage] at hzT
    have hz : z ∈ ({a, b} : Set (EuclideanSpace ℝ (Fin 2))) :=
      hinter ▸ ⟨hzR, hzT⟩
    rcases hz with rfl | rfl
    · exact Or.inl hf0.symm
    · exact Or.inr hf1.symm
  have hloop : Schoenflies.IsLoop (Schoenflies.concatenate f g) :=
    Schoenflies.IsLoop.concatenate hfc hfi hgc hgi hmid hclose hmeet
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (((ρ.trans κ) ⟨t, ht⟩ : frontier P) : EuclideanSpace ℝ (Fin 2)) =
        Schoenflies.concatenate f g t := by
    rw [Path.trans_apply]
    split_ifs with htHalf
    · change t ≤ 1 / 2 at htHalf
      change f (2 * t) = Schoenflies.concatenate f g t
      rw [Schoenflies.concatenate, if_pos htHalf]
    · change ¬t ≤ 1 / 2 at htHalf
      change g (2 * t - 1) = Schoenflies.concatenate f g t
      rw [Schoenflies.concatenate, if_neg htHalf]
  let p : Path a' a' := ρ.trans κ
  let F : loopCircle → frontier P := pathToCircle p
  have hFcontinuous : Continuous F := by
    simpa [F] using (pathToCircle p).continuous
  have hFinjective : Function.Injective F := by
    intro θ η hθη
    let t := AddCircle.equivIco (1 : ℝ) 0 θ
    let s := AddCircle.equivIco (1 : ℝ) 0 η
    have htCircle : (((t : ℝ) : loopCircle)) = θ := by
      simp [t]
    have hsCircle : (((s : ℝ) : loopCircle)) = η := by
      simp [s]
    have htIco : (t : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
      simpa [t] using t.property
    have hsIco : (s : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
      simpa [s] using s.property
    have htI : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨htIco.1, htIco.2.le⟩
    have hsI : (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨hsIco.1, hsIco.2.le⟩
    have hpEq : p ⟨t, htI⟩ = p ⟨s, hsI⟩ := by
      calc
        p ⟨t, htI⟩ = pathToCircle p ((t : ℝ) : loopCircle) :=
          (pathToCircle_coe p ⟨t, htI⟩).symm
        _ = pathToCircle p θ := congrArg (pathToCircle p) htCircle
        _ = pathToCircle p η := hθη
        _ = pathToCircle p ((s : ℝ) : loopCircle) :=
          congrArg (pathToCircle p) hsCircle.symm
        _ = p ⟨s, hsI⟩ := pathToCircle_coe p ⟨s, hsI⟩
    have hreal : Schoenflies.concatenate f g t = Schoenflies.concatenate f g s := by
      rw [← hline t htI, ← hline s hsI]
      exact congrArg Subtype.val hpEq
    have hts : (t : ℝ) = s := hloop.injOn htIco hsIco hreal
    calc
      θ = ((t : ℝ) : loopCircle) := htCircle.symm
      _ = ((s : ℝ) : loopCircle) := congrArg (fun x : ℝ => (x : loopCircle)) hts
      _ = η := hsCircle
  have hpRange : Set.range (fun t : unitInterval => p t) = Set.univ := by
    rw [show p = ρ.trans κ from rfl, Path.trans_range, hrangeρ, hrangeκ]
    ext x
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (congrArg (fun S : Set (EuclideanSpace ℝ (Fin 2)) =>
      (x : EuclideanSpace ℝ (Fin 2)) ∈ S) hfront).mp x.property
  have hFsurjective : Function.Surjective F := by
    intro x
    have hx : x ∈ Set.range p := by rw [hpRange]; exact Set.mem_univ x
    obtain ⟨t, rfl⟩ := hx
    exact ⟨((t : unitInterval).val : loopCircle), pathToCircle_coe p t⟩
  let e₀ : loopCircle ≃ frontier P := Equiv.ofBijective F ⟨hFinjective, hFsurjective⟩
  let e : loopCircle ≃ₜ frontier P :=
    Continuous.homeoOfEquivCompactToT2 (f := e₀) hFcontinuous
  refine ⟨a', b', ρ, κ, e, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      change f t ∈ R
      rw [← hfimage]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      rw [← hfimage] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, htx⟩
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      change g t ∈ T
      rw [← hgimage]
      exact ⟨t, t.property, rfl⟩
    · intro hx
      rw [← hgimage] at hx
      obtain ⟨t, ht, htx⟩ := hx
      exact ⟨⟨t, ht⟩, htx⟩
  · intro θ
    rfl

private theorem IsPLOn.comp_isPiecewiseAffineOn
    {n m p : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    {f : EuclideanSpace ℝ (Fin n) → M}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin n)}
    {P : Set (EuclideanSpace ℝ (Fin n))} {Q : Set (EuclideanSpace ℝ (Fin p))}
    (hf : IsPLOn n m f P) (hg : IsPiecewiseAffineOn g Q) (hmap : MapsTo g Q P) :
    IsPLOn p m (f ∘ g) Q := by
  intro x hx
  have hfx :=
    (StructureGroupoid.liftPropWithinAt_self_source).mp
      (hf (g x) (hmap hx))
  apply (StructureGroupoid.liftPropWithinAt_self_source).mpr
  refine ⟨hfx.1.comp (hg x hx).continuousWithinAt hmap, ?_⟩
  have hcomp := hfx.2.comp (hg x hx)
  have hQP : Q ∩ g ⁻¹' P = Q := inter_eq_left.mpr hmap
  rw [hQP] at hcomp
  exact IsPiecewiseAffineWithinAt.congr hcomp fun _ _ => rfl

open Classical in
private theorem isPLOn_piecewise_of_isClosed
    {n m : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
    {f g : EuclideanSpace ℝ (Fin n) → M}
    {P Q : Set (EuclideanSpace ℝ (Fin n))}
    (hf : IsPLOn n m f P) (hg : IsPLOn n m g Q)
    (hP : IsClosed P) (hQ : IsClosed Q) (hfg : EqOn f g (P ∩ Q)) :
    IsPLOn n m (P.piecewise f g) (P ∪ Q) := by
  let h := P.piecewise f g
  have hPf : EqOn h f P := P.piecewise_eqOn f g
  have hQg : EqOn h g Q := by
    intro x hx
    by_cases hxP : x ∈ P
    · change P.piecewise f g x = g x
      rw [P.piecewise_eq_of_mem f g hxP, hfg ⟨hxP, hx⟩]
    · change P.piecewise f g x = g x
      exact P.piecewise_eq_of_notMem f g hxP
  intro x hx
  by_cases hxP : x ∈ P
  · have hhP : IsPLWithinAt n m h P x :=
      piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
        (hf x hxP) hPf hxP
    by_cases hxQ : x ∈ Q
    · have hhQ : IsPLWithinAt n m h Q x :=
        piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
          (hg x hxQ) hQg hxQ
      have hhP' :=
        (StructureGroupoid.liftPropWithinAt_self_source).mp hhP
      have hhQ' :=
        (StructureGroupoid.liftPropWithinAt_self_source).mp hhQ
      apply (StructureGroupoid.liftPropWithinAt_self_source).mpr
      exact ⟨hhP'.1.union hhQ'.1, hhP'.2.union hhQ'.2⟩
    · have hset : (fun y => y ∈ P) =ᶠ[𝓝 x] (fun y => y ∈ P ∪ Q) := by
        filter_upwards [hQ.isOpen_compl.mem_nhds hxQ] with y hy
        apply propext
        exact ⟨Or.inl, fun h => h.resolve_right hy⟩
      exact (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set hset).mp hhP
  · have hxQ : x ∈ Q := hx.resolve_left hxP
    have hhQ : IsPLWithinAt n m h Q x :=
      piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_of_mem
        (hg x hxQ) hQg hxQ
    have hset : (fun y => y ∈ Q) =ᶠ[𝓝 x] (fun y => y ∈ P ∪ Q) := by
      filter_upwards [hP.isOpen_compl.mem_nhds hxP] with y hy
      apply propext
      exact ⟨Or.inr, fun h => h.resolve_left hy⟩
    exact (piecewiseAffineProperty_localInvariantProp.liftPropWithinAt_congr_set hset).mp hhQ

open Classical in
theorem exists_complementary_frontier_arcs_of_isPLBall_union_between
    {C D : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsPLBall 2 C) (hD : IsPLBall 2 D) (hI : IsPLBall 1 (C ∩ D))
    {p q : EuclideanSpace ℝ (Fin 2)}
    (hIpq : Schoenflies.IsArcBetween (C ∩ D) p q)
    (hIC : C ∩ D ⊆ frontier C) (hID : C ∩ D ⊆ frontier D) :
    ∃ A B : Set (EuclideanSpace ℝ (Fin 2)),
      Schoenflies.IsCutPair (frontier C) p q (C ∩ D) A ∧
      Schoenflies.IsCutPair (frontier D) p q (C ∩ D) B ∧
      IsPLBall 1 A ∧ IsPLBall 1 B ∧ frontier (C ∪ D) = A ∪ B := by
  obtain ⟨A, hcutC, -, hA⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere hC.isPLSphere_frontier hIpq hIC
  obtain ⟨B, hcutD, -, hB⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere hD.isPLSphere_frontier hIpq hID
  have hCclosed : IsClosed C := hC.isPolyhedron.isClosed
  have hDclosed : IsClosed D := hD.isPolyhedron.isClosed
  have hAfront : A ⊆ frontier (C ∪ D) := by
    have hAdiff : A \ {p, q} ⊆ frontier (C ∪ D) := by
      intro x hx
      have hxfrontC : x ∈ frontier C := hcutC.snd_subset hx.1
      have hxC : x ∈ C := hCclosed.frontier_subset hxfrontC
      have hxnotI : x ∉ C ∩ D := by
        intro hxI
        have hxpair : x ∈ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) := by
          rw [← hcutC.inter_eq]
          exact ⟨hxI, hx.1⟩
        exact hx.2 hxpair
      have hxnotD : x ∉ D := fun hxD => hxnotI ⟨hxC, hxD⟩
      apply (mem_frontier_iff_notMem_interior
        (show x ∈ C ∪ D from Or.inl hxC)).mpr
      intro hxint
      have hxside : x ∈ D ∪ interior C := by
        apply hDclosed.interior_union_left
        rwa [union_comm]
      rcases hxside with hxD | hxintC
      · exact hxnotD hxD
      · exact (mem_frontier_iff_notMem_interior hxC).mp hxfrontC hxintC
    calc
      A ⊆ closure (A \ {p, q}) := hA.subset_closure_sdiff_finite (Set.toFinite {p, q})
      _ ⊆ closure (frontier (C ∪ D)) := closure_mono hAdiff
      _ = frontier (C ∪ D) := isClosed_frontier.closure_eq
  have hBfront : B ⊆ frontier (C ∪ D) := by
    have hBdiff : B \ {p, q} ⊆ frontier (C ∪ D) := by
      intro x hx
      have hxfrontD : x ∈ frontier D := hcutD.snd_subset hx.1
      have hxD : x ∈ D := hDclosed.frontier_subset hxfrontD
      have hxnotI : x ∉ C ∩ D := by
        intro hxI
        have hxpair : x ∈ ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) := by
          rw [← hcutD.inter_eq]
          exact ⟨hxI, hx.1⟩
        exact hx.2 hxpair
      have hxnotC : x ∉ C := fun hxC => hxnotI ⟨hxC, hxD⟩
      apply (mem_frontier_iff_notMem_interior
        (show x ∈ C ∪ D from Or.inr hxD)).mpr
      intro hxint
      have hxside : x ∈ C ∪ interior D := hCclosed.interior_union_left hxint
      rcases hxside with hxC | hxintD
      · exact hxnotC hxC
      · exact (mem_frontier_iff_notMem_interior hxD).mp hxfrontD hxintD
    calc
      B ⊆ closure (B \ {p, q}) := hB.subset_closure_sdiff_finite (Set.toFinite {p, q})
      _ ⊆ closure (frontier (C ∪ D)) := closure_mono hBdiff
      _ = frontier (C ∪ D) := isClosed_frontier.closure_eq
  have hinterAB : A ∩ B = ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) := by
    apply Subset.antisymm
    · intro x hx
      have hxC : x ∈ C := hCclosed.frontier_subset (hcutC.snd_subset hx.1)
      have hxD : x ∈ D := hDclosed.frontier_subset (hcutD.snd_subset hx.2)
      rw [← hcutC.inter_eq]
      exact ⟨⟨hxC, hxD⟩, hx.1⟩
    · intro x hx
      have hxA : x ∈ (C ∩ D) ∩ A := hcutC.inter_eq.symm.subset hx
      have hxB : x ∈ (C ∩ D) ∩ B := hcutD.inter_eq.symm.subset hx
      exact ⟨hxA.2, hxB.2⟩
  have hcutAB : Schoenflies.IsCutPair (A ∪ B) p q A B :=
    ⟨hcutC.snd, hcutD.snd, rfl, hinterAB⟩
  have hABsphere : IsPLSphere 1 (A ∪ B) :=
    isPLSphere_one_of_isCutPair hcutAB hA hB
  have hCDball : IsPLBall 2 (C ∪ D) :=
    (isPLBall_union_and_finite_frontier_inter hC hD hI hIC hID).1
  have hfrontierEq : A ∪ B = frontier (C ∪ D) :=
    DifferentialGeometry.Topology.PlanarJordan.eq_of_isJordanCurve_of_subset
      (isJordanCurve_of_isPLSphere_one hABsphere)
      (isJordanCurve_of_isPLSphere_one hCDball.isPLSphere_frontier)
      (union_subset hAfront hBfront)
  exact ⟨A, B, hcutC, hcutD, hA, hB, hfrontierEq.symm⟩

open Classical in
theorem exists_complementary_frontier_arcs_of_isPLBall_union
    {C D : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsPLBall 2 C) (hD : IsPLBall 2 D) (hI : IsPLBall 1 (C ∩ D))
    (hIC : C ∩ D ⊆ frontier C) (hID : C ∩ D ⊆ frontier D) :
    ∃ p q : EuclideanSpace ℝ (Fin 2), ∃ A B : Set (EuclideanSpace ℝ (Fin 2)),
      Schoenflies.IsCutPair (frontier C) p q (C ∩ D) A ∧
      Schoenflies.IsCutPair (frontier D) p q (C ∩ D) B ∧
      IsPLBall 1 A ∧ IsPLBall 1 B ∧ frontier (C ∪ D) = A ∪ B := by
  obtain ⟨p, q, hIpq⟩ := hI.isArc.exists_isArcBetween
  obtain ⟨A, B, hcutC, hcutD, hA, hB, hfront⟩ :=
    exists_complementary_frontier_arcs_of_isPLBall_union_between
      hC hD hI hIpq hIC hID
  exact ⟨p, q, A, B, hcutC, hcutD, hA, hB, hfront⟩

open Classical in
theorem IsPLHomeomorphOn.maps_arc_endpoints
    {A B : Set (EuclideanSpace ℝ (Fin 2))}
    {p q r s : EuclideanSpace ℝ (Fin 2)}
    (hA : IsPLBall 1 A) (hB : IsPLBall 1 B)
    (hApq : Schoenflies.IsArcBetween A p q)
    (hBrs : Schoenflies.IsArcBetween B r s)
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hg : IsPLHomeomorphOn g A B) :
    (g p = r ∧ g q = s) ∨ (g p = s ∧ g q = r) := by
  obtain ⟨α, hα, hα0, hα1⟩ :=
    exists_isPLHomeomorphOn_Icc_of_isArcBetween hA hApq
  obtain ⟨β, hβ, hβ0, hβ1⟩ :=
    exists_isPLHomeomorphOn_Icc_of_isArcBetween hB hBrs
  let k := Function.invFunOn β (Icc (0 : ℝ) 1) ∘ g ∘ α
  have hk : IsPLHomeomorphOn k (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
    (hα.trans hg).trans hβ.symm
  have hk0mem : k 0 ∈ Icc (0 : ℝ) 1 := hk.bijOn.mapsTo Schoenflies.zero_mem_I
  have hk1mem : k 1 ∈ Icc (0 : ℝ) 1 := hk.bijOn.mapsTo Schoenflies.one_mem_I
  have hβ0comp : β (k 0) = g (α 0) := by
    change β (Function.invFunOn β (Icc (0 : ℝ) 1) (g (α 0))) = g (α 0)
    exact hβ.bijOn.invOn_invFunOn.2 ((hα.trans hg).bijOn.mapsTo Schoenflies.zero_mem_I)
  have hβ1comp : β (k 1) = g (α 1) := by
    change β (Function.invFunOn β (Icc (0 : ℝ) 1) (g (α 1))) = g (α 1)
    exact hβ.bijOn.invOn_invFunOn.2 ((hα.trans hg).bijOn.mapsTo Schoenflies.one_mem_I)
  rcases hk.isPiecewiseAffineOn.continuousOn.strictMonoOn_of_injOn_Icc'
      (by norm_num : (0 : ℝ) ≤ 1) hk.bijOn.injOn with hmono | hanti
  · obtain ⟨t₀, ht₀, hkt₀⟩ := hk.bijOn.surjOn Schoenflies.zero_mem_I
    obtain ⟨t₁, ht₁, hkt₁⟩ := hk.bijOn.surjOn Schoenflies.one_mem_I
    have hk0 : k 0 = 0 := by
      apply le_antisymm
      · simpa only [hkt₀] using hmono.monotoneOn Schoenflies.zero_mem_I ht₀ ht₀.1
      · exact hk0mem.1
    have hk1 : k 1 = 1 := by
      apply le_antisymm hk1mem.2
      simpa only [hkt₁] using hmono.monotoneOn ht₁ Schoenflies.one_mem_I ht₁.2
    exact Or.inl ⟨by
      calc
        g p = g (α 0) := congrArg g hα0.symm
        _ = β (k 0) := hβ0comp.symm
        _ = β 0 := congrArg β hk0
        _ = r := hβ0, by
      calc
        g q = g (α 1) := congrArg g hα1.symm
        _ = β (k 1) := hβ1comp.symm
        _ = β 1 := congrArg β hk1
        _ = s := hβ1⟩
  · obtain ⟨t₀, ht₀, hkt₀⟩ := hk.bijOn.surjOn Schoenflies.zero_mem_I
    obtain ⟨t₁, ht₁, hkt₁⟩ := hk.bijOn.surjOn Schoenflies.one_mem_I
    have hk0 : k 0 = 1 := by
      apply le_antisymm hk0mem.2
      simpa only [hkt₁] using hanti.antitoneOn Schoenflies.zero_mem_I ht₁ ht₁.1
    have hk1 : k 1 = 0 := by
      apply le_antisymm
      · simpa only [hkt₀] using hanti.antitoneOn ht₀ Schoenflies.one_mem_I ht₀.2
      · exact hk1mem.1
    exact Or.inr ⟨by
      calc
        g p = g (α 0) := congrArg g hα0.symm
        _ = β (k 0) := hβ0comp.symm
        _ = β 1 := congrArg β hk0
        _ = s := hβ1, by
      calc
        g q = g (α 1) := congrArg g hα1.symm
        _ = β (k 1) := hβ1comp.symm
        _ = β 0 := congrArg β hk1
        _ = r := hβ0⟩

namespace SingularTwoCell

open Classical in
theorem exists_glue_of_isPLHomeomorphOn_boundary_arc
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D₁ D₂ : SingularTwoCell M)
    {A B : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) {a₀ a₁ : EuclideanSpace ℝ (Fin 2)}
    (hAarc : Schoenflies.IsArcBetween A a₀ a₁)
    (hAfront : A ⊆ frontier D₁.domain)
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hg : IsPLHomeomorphOn g A B) (hBfront : B ⊆ frontier D₂.domain)
    (hcompat : EqOn D₁ (D₂ ∘ g) A) :
    ∃ (D : SingularTwoCell M) (P Q : Set (EuclideanSpace ℝ (Fin 2)))
      (f₁ f₂ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      IsPLBall 2 P ∧ IsPLBall 2 Q ∧ IsPLBall 2 (P ∪ Q) ∧
      D.domain = P ∪ Q ∧ IsPLBall 1 (P ∩ Q) ∧
      P ∩ Q ⊆ frontier P ∧ P ∩ Q ⊆ frontier Q ∧
      IsPLHomeomorphOn f₁ P D₁.domain ∧
      IsPLHomeomorphOn f₂ Q D₂.domain ∧
      EqOn f₂ (g ∘ f₁) (P ∩ Q) ∧
      f₁ '' (P ∩ Q) = A ∧ f₂ '' (P ∩ Q) = B ∧
      EqOn D (D₁ ∘ f₁) P ∧ EqOn D (D₂ ∘ f₂) Q ∧
      ∃ p q : EuclideanSpace ℝ (Fin 2), ∃ R T : Set (EuclideanSpace ℝ (Fin 2)),
        Schoenflies.IsCutPair (frontier P) p q (P ∩ Q) R ∧
        Schoenflies.IsCutPair (frontier Q) p q (P ∩ Q) T ∧
        IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier D.domain = R ∪ T ∧
        f₁ p = a₀ ∧ f₁ q = a₁ ∧ f₂ p = g a₀ ∧ f₂ q = g a₁ := by
  obtain ⟨K, L, hKfin, hLfin, hK, hL, hKL, p, q, hpq, hinter, hSK, hSL⟩ :=
    exists_isPLBall_pair_with_segment_inter
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  let S := segment ℝ p q
  have hS : IsPLBall 1 S := isPLBall_segment hpq
  have hSarc : Schoenflies.IsArcBetween S p q := Schoenflies.isArcBetween_segment hpq
  obtain ⟨a, ha, ha₀, ha₁⟩ :=
    exists_isPLHomeomorphOn_of_isArcBetween hS hA hSarc hAarc
  have hSfrontK : S ⊆ frontier K.space := by
    rw [← boundaryComplex_space_eq_of_isPLBall_of_frontier K hK hK.isPLSphere_frontier rfl]
    exact hSK
  have hSfrontL : S ⊆ frontier L.space := by
    rw [← boundaryComplex_space_eq_of_isPLBall_of_frontier L hL hL.isPLSphere_frontier rfl]
    exact hSL
  obtain ⟨b₁, hb₁, hb₁a⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one
    hK.isPLSphere_frontier D₁.isPLSphere_frontier hSarc hSfrontK ha hAfront
  obtain ⟨f₁, hf₁, hf₁b⟩ := exists_isPLHomeomorphOn_of_frontier hK D₁.isPLBall_domain hb₁
  have hf₁a : EqOn f₁ a S := (hf₁b.mono hSfrontK).trans hb₁a
  have hga : IsPLHomeomorphOn (g ∘ a) S B := ha.trans hg
  obtain ⟨b₂, hb₂, hb₂ga⟩ := exists_isPLHomeomorphOn_eqOn_arc_of_isPLSphere_one
    hL.isPLSphere_frontier D₂.isPLSphere_frontier hSarc hSfrontL hga hBfront
  obtain ⟨f₂, hf₂, hf₂b⟩ := exists_isPLHomeomorphOn_of_frontier hL D₂.isPLBall_domain hb₂
  have hf₂ga : EqOn f₂ (g ∘ a) S := (hf₂b.mono hSfrontL).trans hb₂ga
  have hf₂f₁ : EqOn f₂ (g ∘ f₁) S := by
    intro x hx
    exact (hf₂ga hx).trans (congrArg g (hf₁a hx).symm)
  let F₁ := D₁.toFun ∘ f₁
  let F₂ := D₂.toFun ∘ f₂
  have hF₁ : IsPLOn 2 3 F₁ K.space :=
    D₁.isPLOn.comp_isPiecewiseAffineOn hf₁.isPiecewiseAffineOn hf₁.bijOn.mapsTo
  have hF₂ : IsPLOn 2 3 F₂ L.space :=
    D₂.isPLOn.comp_isPiecewiseAffineOn hf₂.isPiecewiseAffineOn hf₂.bijOn.mapsTo
  have hFcompat : EqOn F₁ F₂ (K.space ∩ L.space) := by
    rw [hinter]
    intro x hx
    change D₁ (f₁ x) = D₂ (f₂ x)
    rw [hf₂f₁ hx]
    exact hcompat (hf₁a hx ▸ ha.bijOn.mapsTo hx)
  let F := K.space.piecewise F₁ F₂
  have hF : IsPLOn 2 3 F (K.space ∪ L.space) :=
    isPLOn_piecewise_of_isClosed hF₁ hF₂ hK.isPolyhedron.isClosed
      hL.isPolyhedron.isClosed hFcompat
  let D : SingularTwoCell M :=
    { domain := K.space ∪ L.space
      isPLBall_domain := hKL
      toFun := F
      isPLOn := hF }
  refine ⟨D, K.space, L.space, f₁, f₂, hK, hL, hKL, rfl, hinter.symm ▸ hS,
    ?_, ?_, hf₁, hf₂, hinter.symm ▸ hf₂f₁, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hinter]
    exact hSfrontK
  · rw [hinter]
    exact hSfrontL
  · rw [hinter]
    calc
      f₁ '' S = a '' S := Set.image_congr hf₁a
      _ = A := ha.image_eq
  · rw [hinter]
    calc
      f₂ '' S = (g ∘ a) '' S := Set.image_congr hf₂ga
      _ = B := hga.image_eq
  · exact K.space.piecewise_eqOn F₁ F₂
  · intro x hx
    by_cases hxK : x ∈ K.space
    · rw [show D x = F₁ x from K.space.piecewise_eq_of_mem F₁ F₂ hxK]
      exact hFcompat ⟨hxK, hx⟩
    · exact K.space.piecewise_eq_of_notMem F₁ F₂ hxK
  · obtain ⟨R, T, hcutK, hcutL, hR, hT, hfront⟩ :=
      exists_complementary_frontier_arcs_of_isPLBall_union_between hK hL
        (hinter.symm ▸ hS) (by rw [hinter]; exact hSarc)
          (hinter.symm ▸ hSfrontK) (hinter.symm ▸ hSfrontL)
    refine ⟨p, q, R, T, hcutK, hcutL, hR, hT, hfront, ?_, ?_, ?_, ?_⟩
    · exact (hf₁a hSarc.left_mem).trans ha₀
    · exact (hf₁a hSarc.right_mem).trans ha₁
    · exact (hf₂ga hSarc.left_mem).trans (congrArg g ha₀)
    · exact (hf₂ga hSarc.right_mem).trans (congrArg g ha₁)

end SingularTwoCell

end DifferentialGeometry.Topology.PiecewiseLinear
