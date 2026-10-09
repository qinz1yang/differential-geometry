/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskUnion
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.External.Schoenflies.BoundaryContinuity2
import DifferentialGeometry.External.Schoenflies.MatchedArc

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem exists_boundaryParam_paths_of_isCutPair_union_with_endpoints
    {P R T : Set (EuclideanSpace ℝ (Fin 2))}
    {a b : EuclideanSpace ℝ (Fin 2)}
    (hR : Schoenflies.IsArcBetween R a b)
    (hT : Schoenflies.IsArcBetween T a b)
    (hinter : R ∩ T = {a, b}) (hfront : frontier P = R ∪ T) :
    ∃ (a' b' : frontier P) (ρ : Path a' b') (κ : Path b' a')
        (e : loopCircle ≃ₜ frontier P),
      Set.range (fun t => ((ρ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = R ∧
        Set.range (fun t => ((κ t : frontier P) : EuclideanSpace ℝ (Fin 2))) = T ∧
          (∀ θ, e θ = pathToCircle (ρ.trans κ) θ) ∧
            Function.Injective ρ ∧ Function.Injective κ ∧
              (a' : EuclideanSpace ℝ (Fin 2)) = a ∧
              (b' : EuclideanSpace ℝ (Fin 2)) = b := by
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
      rw [Schoenflies.concatenate, ite_eq_left htHalf]
    · change ¬t ≤ 1 / 2 at htHalf
      change g (2 * t - 1) = Schoenflies.concatenate f g t
      rw [Schoenflies.concatenate, ite_eq_right htHalf]
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
  refine ⟨a', b', ρ, κ, e, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
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
  · exact fun s t hst => Subtype.ext (hfi s.property t.property (congrArg Subtype.val hst))
  · exact fun s t hst => Subtype.ext (hgi s.property t.property (congrArg Subtype.val hst))

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
          (∀ θ, e θ = pathToCircle (ρ.trans κ) θ) ∧
            Function.Injective ρ ∧ Function.Injective κ := by
  obtain ⟨a', b', ρ, κ, e, hρ, hκ, he, hρi, hκi, -, -⟩ :=
    exists_boundaryParam_paths_of_isCutPair_union_with_endpoints hR hT hinter hfront
  exact ⟨a', b', ρ, κ, e, hρ, hκ, he, hρi, hκi⟩

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

theorem image_cutArc_eq_of_isPLHomeomorphOn
    {X Y S R A T : Set (EuclideanSpace ℝ (Fin 2))}
    {p q a b : EuclideanSpace ℝ (Fin 2)}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hX : IsPLBall 2 X) (hY : IsPLBall 2 Y) (hf : IsPLHomeomorphOn f X Y)
    (hcutX : Schoenflies.IsCutPair (frontier X) p q S R)
    (hfS : f '' S = A) (hfp : f p = a) (hfq : f q = b)
    (hcutY : Schoenflies.IsCutPair (frontier Y) a b A T) :
    f '' R = T := by
  have hfront : IsPLHomeomorphOn f (frontier X) (frontier Y) := by
    rw [← hf.image_frontier (by simp) hX.isPolyhedron.isClosed hY.isPolyhedron.isClosed]
    exact hf.restrict hX.isPLSphere_frontier.isPolyhedron
      hX.isPolyhedron.isClosed.frontier_subset
  have himage := hcutX.image hfront.isPiecewiseAffineOn.continuousOn hfront.bijOn.injOn
  rw [hfront.image_eq, hfS, hfp, hfq] at himage
  rcases DifferentialGeometry.Topology.PlanarJordan.eq_or_eq_of_isArcBetween_subset_isCutPair
    hcutY himage.snd himage.snd_subset with hbad | hgood
  · exact (himage.ne hbad.symm).elim
  · exact hgood

theorem frontier_middle_eq_union_seams
    {W U₁ U₂ U₃ A C : Set (EuclideanSpace ℝ (Fin 2))}
    (hcover : U₁ ∪ U₂ ∪ U₃ = W)
    (h₁closed : IsClosed U₁) (h₂closed : IsClosed U₂) (h₃closed : IsClosed U₃)
    (hinter₁₂ : U₁ ∩ U₂ = A) (hinter₂₃ : U₂ ∩ U₃ = C)
    (hA₂ : A ⊆ frontier U₂) (hC₂ : C ⊆ frontier U₂) :
    frontier U₂ = (U₂ ∩ frontier W) ∪ A ∪ C := by
  have hU₂W : U₂ ⊆ W := by
    intro x hx
    rw [← hcover]
    exact Or.inl (Or.inr hx)
  apply Subset.antisymm
  · intro x hx
    have hxU₂ : x ∈ U₂ := h₂closed.frontier_subset hx
    by_cases hxW : x ∈ frontier W
    · exact Or.inl (Or.inl ⟨hxU₂, hxW⟩)
    by_cases hxA : x ∈ A
    · exact Or.inl (Or.inr hxA)
    by_cases hxC : x ∈ C
    · exact Or.inr hxC
    exfalso
    have hxint : x ∈ interior W := by
      by_contra hxint
      exact hxW ((mem_frontier_iff_notMem_interior (hU₂W hxU₂)).mpr hxint)
    have hxU₁ : x ∉ U₁ := fun h => hxA (hinter₁₂ ▸ ⟨h, hxU₂⟩)
    have hxU₃ : x ∉ U₃ := fun h => hxC (hinter₂₃ ▸ ⟨hxU₂, h⟩)
    have hopen : IsOpen (interior W ∩ (U₁ ∪ U₃)ᶜ) :=
      isOpen_interior.inter (h₁closed.union h₃closed).isOpen_compl
    have hmem : x ∈ interior W ∩ (U₁ ∪ U₃)ᶜ := by
      refine ⟨hxint, ?_⟩
      simp only [mem_compl_iff, mem_union, not_or]
      exact ⟨hxU₁, hxU₃⟩
    have hsub : interior W ∩ (U₁ ∪ U₃)ᶜ ⊆ U₂ := by
      rintro y ⟨hyW, hy⟩
      simp only [mem_compl_iff, mem_union, not_or] at hy
      have hycover : y ∈ U₁ ∪ U₂ ∪ U₃ := by
        rw [hcover]
        exact interior_subset hyW
      rcases hycover with (hy₁ | hy₂) | hy₃
      · exact (hy.1 hy₁).elim
      · exact hy₂
      · exact (hy.2 hy₃).elim
    exact (mem_frontier_iff_notMem_interior hxU₂).mp hx
      (interior_maximal hsub hopen hmem)
  · refine union_subset (union_subset ?_ hA₂) hC₂
    rintro x ⟨hxU₂, hxW⟩
    refine (mem_frontier_iff_notMem_interior hxU₂).mpr ?_
    intro hxint
    exact (mem_frontier_iff_notMem_interior (hU₂W hxU₂)).mp hxW
      (interior_mono hU₂W hxint)

theorem isCutPair_snd_eq_of_union_eq
    {J T A C S : Set (EuclideanSpace ℝ (Fin 2))} {r s : EuclideanSpace ℝ (Fin 2)}
    (hcut : Schoenflies.IsCutPair J r s C S) (hJ : J = T ∪ A ∪ C)
    (hmeet : C ∩ (T ∪ A) ⊆ {r, s}) (hr : r ∈ T) (hs : s ∈ T) :
    S = T ∪ A := by
  apply Subset.antisymm
  · intro x hxS
    have hxJ : x ∈ J := hcut.snd_subset hxS
    rw [hJ] at hxJ
    rcases hxJ with hxTA | hxC
    · exact hxTA
    · have hxpair : x ∈ ({r, s} : Set (EuclideanSpace ℝ (Fin 2))) :=
        hcut.inter_eq.subset ⟨hxC, hxS⟩
      rcases hxpair with rfl | rfl
      · exact Or.inl hr
      · exact Or.inl hs
  · intro x hx
    have hxJ : x ∈ J := by
      rw [hJ]
      exact Or.inl hx
    rcases hcut.union_eq.symm.subset hxJ with hxC | hxS
    · have hxpair : x ∈ ({r, s} : Set (EuclideanSpace ℝ (Fin 2))) := hmeet ⟨hxC, hx⟩
      rcases hxpair with rfl | rfl
      · exact hcut.snd.left_mem
      · exact hcut.snd.right_mem
    · exact hxS

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
    IsPLOn.piecewise_of_isClosed hF₁ hF₂ hK.isPolyhedron.isClosed
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

open Classical in
theorem exists_cross_glue_of_isPLHomeomorphOn_disjoint_boundary_arcs_with_source_arcs
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D₁ D₂ D₃ : SingularTwoCell M) {D : SingularTwoCell M}
    {A C : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) (hAC : Disjoint A C)
    {a₀ a₁ : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hcover : D₁.domain ∪ D₂.domain ∪ D₃.domain = D.domain)
    (hinter₁₂ : D₁.domain ∩ D₂.domain = A)
    (hinter₂₃ : D₂.domain ∩ D₃.domain = C)
    (hAfront₂ : A ⊆ frontier D₂.domain)
    (hCfront₂ : C ⊆ frontier D₂.domain)
    (hcut₁ : Schoenflies.IsCutPair (frontier D₁.domain) a₀ a₁ A
      (D₁.domain ∩ frontier D.domain))
    (hcut₃ : Schoenflies.IsCutPair (frontier D₃.domain) (g a₀) (g a₁) C
      (D₃.domain ∩ frontier D.domain))
    (hg : IsPLHomeomorphOn g A C)
    (hcompat₁₂ : EqOn D₁ (D₂ ∘ g) A)
    (hcompat₂₃ : EqOn D₂ (D₃ ∘ g) A)
    (hfun₁ : D₁.toFun = D.toFun) (hfun₂ : D₂.toFun = D.toFun)
    (hfun₃ : D₃.toFun = D.toFun) :
    ∃ (H G : SingularTwoCell M)
      (P Q P' Q' : Set (EuclideanSpace ℝ (Fin 2)))
      (f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (A' : Set (EuclideanSpace ℝ (Fin 2))),
      IsPLBall 2 P ∧ IsPLBall 2 Q ∧ H.domain = P ∪ Q ∧
      IsPLHomeomorphOn f₁ P D₁.domain ∧
      IsPLHomeomorphOn f₂ Q D₂.domain ∧
      f₁ '' (P ∩ Q) = A ∧ f₂ '' (P ∩ Q) = C ∧
      EqOn H (D₁ ∘ f₁) P ∧ EqOn H (D₂ ∘ f₂) Q ∧
      A' = Function.invFunOn f₂ Q '' A ∧ IsPLBall 1 A' ∧ Disjoint A' (P ∩ Q) ∧
      A' ⊆ frontier H.domain ∧
      IsPLHomeomorphOn (g ∘ f₂) A' C ∧
      IsPLBall 2 P' ∧ IsPLBall 2 Q' ∧ G.domain = P' ∪ Q' ∧
      IsPLHomeomorphOn h P' H.domain ∧
      IsPLHomeomorphOn f₃ Q' D₃.domain ∧
      h '' (P' ∩ Q') = A' ∧ f₃ '' (P' ∩ Q') = C ∧
      EqOn G (H ∘ h) P' ∧ EqOn G (D₃ ∘ f₃) Q' ∧
      ∃ a b : EuclideanSpace ℝ (Fin 2),
      ∃ R T : Set (EuclideanSpace ℝ (Fin 2)),
        Schoenflies.IsCutPair (frontier P') a b (P' ∩ Q') R ∧
        Schoenflies.IsCutPair (frontier Q') a b (P' ∩ Q') T ∧
        IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier G.domain = R ∪ T ∧
        h a = Function.invFunOn f₂ Q a₀ ∧
        h b = Function.invFunOn f₂ Q a₁ ∧
        f₃ a = g a₀ ∧ f₃ b = g a₁ ∧
        ∃ (x y : M) (σ : Path x y) (ω : Path y x)
            (e : loopCircle ≃ₜ frontier G.domain),
          Set.range σ = G '' R ∧ Set.range ω = G '' T ∧
            (∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ) ∧
            G '' R = D '' ((D₁.domain ∪ D₂.domain) ∩ frontier D.domain) ∧
            G '' T = D '' (D₃.domain ∩ frontier D.domain) ∧
            ∃ (a' b' : frontier G.domain) (ρ : Path a' b') (κ : Path b' a'),
              Function.Injective ρ ∧ Function.Injective κ ∧
              Set.range (fun t => ((ρ t : frontier G.domain) :
                EuclideanSpace ℝ (Fin 2))) = R ∧
              Set.range (fun t => ((κ t : frontier G.domain) :
                EuclideanSpace ℝ (Fin 2))) = T ∧
              (∀ θ, e θ = pathToCircle (ρ.trans κ) θ) ∧
              ∃ (R₀ T₀ SH : Set (EuclideanSpace ℝ (Fin 2)))
                (pH qH : EuclideanSpace ℝ (Fin 2)),
                Schoenflies.IsCutPair (frontier P) pH qH (P ∩ Q) R₀ ∧
                Schoenflies.IsCutPair (frontier Q) pH qH (P ∩ Q) T₀ ∧
                Schoenflies.IsCutPair (frontier H.domain)
                  (Function.invFunOn f₂ Q a₀) (Function.invFunOn f₂ Q a₁) A' SH ∧
                R₀ ⊆ SH ∧ SH = R₀ ∪ (SH ∩ T₀) ∧ h '' R = SH ∧
                f₁ '' R₀ = D₁.domain ∩ frontier D.domain ∧
                f₂ '' (SH ∩ T₀) = D₂.domain ∩ frontier D.domain ∧
                f₃ '' T = D₃.domain ∩ frontier D.domain ∧
                f₁ pH = a₀ ∧ f₁ qH = a₁ ∧ f₂ pH = g a₀ ∧ f₂ qH = g a₁ ∧
                EqOn f₂ (g ∘ f₁) (P ∩ Q) ∧
                (a' : EuclideanSpace ℝ (Fin 2)) = a ∧
                (b' : EuclideanSpace ℝ (Fin 2)) = b := by
  obtain ⟨H, P, Q, f₁, f₂, hP, hQ, -, hHdomain, -, -, -, hf₁, hf₂, hf₂f₁,
    hf₁seam, hf₂seam, hH₁, hH₂, pH, qH, R₀, T₀, hcutP, hcutQ, hR₀, -, hfrontH,
    hf₁pH, hf₁qH, hf₂pH, hf₂qH⟩ :=
    D₁.exists_glue_of_isPLHomeomorphOn_boundary_arc D₂ hA hcut₁.fst hcut₁.fst_subset hg
      hCfront₂ hcompat₁₂
  let j := Function.invFunOn f₂ Q
  let A' := j '' A
  have hAD₂ : A ⊆ D₂.domain :=
    hAfront₂.trans D₂.isPLBall_domain.isPolyhedron.isClosed.frontier_subset
  have hjA : IsPLHomeomorphOn j A A' := by
    simpa only [j, A'] using hf₂.symm.restrict hA.isPolyhedron hAD₂
  have hA' : IsPLBall 1 A' := hA.of_isPLHomeomorphOn hjA
  have hA'arc : Schoenflies.IsArcBetween A' (j a₀) (j a₁) := by
    obtain ⟨α, hαc, hαi, hαimage, hα0, hα1⟩ := hcut₁.fst
    have hαA : ∀ t ∈ unitInterval, α t ∈ A := by
      intro t ht
      rw [← hαimage]
      exact ⟨t, ht, rfl⟩
    refine ⟨j ∘ α, hjA.isPiecewiseAffineOn.continuousOn.comp hαc hαA, ?_, ?_, ?_, ?_⟩
    · intro s hs t ht hst
      exact hαi hs ht (hjA.bijOn.injOn (hαA s hs) (hαA t ht) hst)
    · calc
        (j ∘ α) '' unitInterval = j '' (α '' unitInterval) := image_comp j α unitInterval
        _ = j '' A := congrArg (j '' ·) hαimage
        _ = A' := rfl
    · simp only [Function.comp_apply, hα0]
    · simp only [Function.comp_apply, hα1]
  have hjfront : j '' frontier D₂.domain = frontier Q := by
    simpa only [j] using hf₂.symm.image_frontier (by simp)
      D₂.isPLBall_domain.isPolyhedron.isClosed hQ.isPolyhedron.isClosed
  have hA'frontQ : A' ⊆ frontier Q := by
    rw [← hjfront]
    exact image_mono hAfront₂
  have hA'seam : Disjoint A' (P ∩ Q) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, hyA, rfl⟩ hxseam
    have hyD₂ : y ∈ D₂.domain := hAD₂ hyA
    have hf₂j : f₂ (j y) = y := hf₂.bijOn.invOn_invFunOn.2 hyD₂
    have hCmem : f₂ (j y) ∈ C := by
      rw [← hf₂seam]
      exact ⟨j y, hxseam, rfl⟩
    exact Set.disjoint_left.mp hAC hyA (hf₂j ▸ hCmem)
  have hA'T : A' ⊆ T₀ := by
    intro x hxA'
    have hxfront := hA'frontQ hxA'
    rw [← hcutQ.union_eq] at hxfront
    exact hxfront.resolve_left (Set.disjoint_left.mp hA'seam hxA')
  have hA'frontH : A' ⊆ frontier H.domain := by
    rw [hfrontH]
    exact hA'T.trans subset_union_right
  have hA'Q : A' ⊆ Q := by
    rintro x ⟨y, hyA, rfl⟩
    exact hf₂.bijOn.surjOn.mapsTo_invFunOn (hAD₂ hyA)
  have hf₂A'image : f₂ '' A' = A := by
    calc
      f₂ '' A' = f₂ '' (j '' A) := rfl
      _ = (f₂ ∘ j) '' A := (image_comp f₂ j A).symm
      _ = id '' A := Set.image_congr fun y hy =>
        hf₂.bijOn.invOn_invFunOn.2 (hAD₂ hy)
      _ = A := image_id A
  have hf₂A' : IsPLHomeomorphOn f₂ A' A := by
    have h := hf₂.restrict hA'.isPolyhedron hA'Q
    rwa [hf₂A'image] at h
  have hk : IsPLHomeomorphOn (g ∘ f₂) A' C := hf₂A'.trans hg
  have hcompatH₃ : EqOn H (D₃ ∘ (g ∘ f₂)) A' := by
    intro x hx
    calc
      H x = D₂ (f₂ x) := hH₂ (hA'Q hx)
      _ = D₃ (g (f₂ x)) := hcompat₂₃ (hf₂A'.bijOn.mapsTo hx)
      _ = (D₃ ∘ (g ∘ f₂)) x := rfl
  obtain ⟨G, P', Q', h, f₃, hP', hQ', -, hGdomain, -, -, -, hh, hf₃, -,
    hhseam, hf₃seam, hGH, hG₃, a, b, R', T', hcutP', hcutQ', hR', hT',
    hfrontG, hha, hhb, hf₃a, hf₃b⟩ :=
    H.exists_glue_of_isPLHomeomorphOn_boundary_arc D₃ hA' hA'arc hA'frontH hk
      hcut₃.fst_subset hcompatH₃
  have hCU₂ : C ⊆ D₂.domain := by
    rw [← hinter₂₃]
    exact inter_subset_left
  have hCU₃ : C ⊆ D₃.domain := by
    rw [← hinter₂₃]
    exact inter_subset_right
  have hR₀P : R₀ ⊆ P := hcutP.snd_subset.trans hP.isPolyhedron.isClosed.frontier_subset
  have hT₀Q : T₀ ⊆ Q := hcutQ.snd_subset.trans hQ.isPolyhedron.isClosed.frontier_subset
  have hR₀image : f₁ '' R₀ = D₁.domain ∩ frontier D.domain :=
    image_cutArc_eq_of_isPLHomeomorphOn hP D₁.isPLBall_domain hf₁ hcutP hf₁seam
      hf₁pH hf₁qH hcut₁
  have hfrontD₂ : frontier D₂.domain = (D₂.domain ∩ frontier D.domain) ∪ A ∪ C :=
    frontier_middle_eq_union_seams hcover D₁.isPLBall_domain.isPolyhedron.isClosed
      D₂.isPLBall_domain.isPolyhedron.isClosed D₃.isPLBall_domain.isPolyhedron.isClosed
      hinter₁₂ hinter₂₃ hAfront₂ hCfront₂
  obtain ⟨S₂, hcut₂, -, -⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere D₂.isPLSphere_frontier hcut₃.fst
      hCfront₂
  have hmeet : C ∩ ((D₂.domain ∩ frontier D.domain) ∪ A) ⊆ {g a₀, g a₁} := by
    rintro x ⟨hxC, hx⟩
    rcases hx with ⟨-, hxF⟩ | hxA
    · exact hcut₃.inter_eq.subset ⟨hxC, ⟨hCU₃ hxC, hxF⟩⟩
    · exact absurd hxA (Set.disjoint_right.mp hAC hxC)
  have hS₂eq : S₂ = (D₂.domain ∩ frontier D.domain) ∪ A :=
    isCutPair_snd_eq_of_union_eq hcut₂ hfrontD₂ hmeet
      ⟨hCU₂ hcut₃.fst.left_mem, hcut₃.snd.left_mem.2⟩
      ⟨hCU₂ hcut₃.fst.right_mem, hcut₃.snd.right_mem.2⟩
  have hT₀image : f₂ '' T₀ = S₂ :=
    image_cutArc_eq_of_isPLHomeomorphOn hQ D₂.isPLBall_domain hf₂ hcutQ hf₂seam
      hf₂pH hf₂qH hcut₂
  have hf₂jp : f₂ (j a₀) = a₀ := hf₂.bijOn.invOn_invFunOn.2 (hAD₂ hcut₁.fst.left_mem)
  have hf₂jq : f₂ (j a₁) = a₁ := hf₂.bijOn.invOn_invFunOn.2 (hAD₂ hcut₁.fst.right_mem)
  have hf₃aeq : f₃ a = g a₀ := by
    rw [hf₃a]
    exact congrArg g hf₂jp
  have hf₃beq : f₃ b = g a₁ := by
    rw [hf₃b]
    exact congrArg g hf₂jq
  have hT'image : f₃ '' T' = D₃.domain ∩ frontier D.domain :=
    image_cutArc_eq_of_isPLHomeomorphOn hQ' D₃.isPLBall_domain hf₃ hcutQ' hf₃seam
      hf₃aeq hf₃beq hcut₃
  obtain ⟨SH, hcutH, -, hSH⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere H.isPLSphere_frontier hA'arc
      hA'frontH
  have hR'image : h '' R' = SH :=
    image_cutArc_eq_of_isPLHomeomorphOn hP' H.isPLBall_domain hh hcutP' hhseam hha hhb
      hcutH
  have hR₀T₀ : R₀ ∩ T₀ = {pH, qH} := by
    apply Subset.antisymm
    · rintro x ⟨hxR, hxT⟩
      exact hcutP.inter_eq.subset ⟨⟨hR₀P hxR, hT₀Q hxT⟩, hxR⟩
    · rintro x (rfl | rfl)
      · exact ⟨hcutP.snd.left_mem, hcutQ.snd.left_mem⟩
      · exact ⟨hcutP.snd.right_mem, hcutQ.snd.right_mem⟩
  have hR₀SH : R₀ ⊆ SH := by
    have hsub : R₀ \ {pH, qH} ⊆ SH := by
      intro x hx
      have hxfront : x ∈ frontier H.domain := by
        rw [hfrontH]
        exact Or.inl hx.1
      rcases hcutH.union_eq.symm.subset hxfront with hxA' | hxSH
      · exact absurd (hR₀T₀.subset ⟨hx.1, hA'T hxA'⟩) hx.2
      · exact hxSH
    calc
      R₀ ⊆ closure (R₀ \ {pH, qH}) := hR₀.subset_closure_sdiff_finite (Set.toFinite _)
      _ ⊆ closure SH := closure_mono hsub
      _ = SH := hSH.isPolyhedron.isClosed.closure_eq
  have hA'char : ∀ x ∈ Q, f₂ x ∈ A → x ∈ A' := by
    intro x hxQ hxA
    have hxD₂ : f₂ x ∈ D₂.domain := hf₂.bijOn.mapsTo hxQ
    have hjx : j (f₂ x) ∈ Q := hf₂.bijOn.surjOn.mapsTo_invFunOn hxD₂
    have hfix : j (f₂ x) = x :=
      hf₂.bijOn.injOn hjx hxQ (hf₂.bijOn.invOn_invFunOn.2 hxD₂)
    have hmem : j (f₂ x) ∈ A' := mem_image_of_mem j hxA
    rwa [hfix] at hmem
  have hAF : A ∩ frontier D.domain ⊆ {a₀, a₁} := by
    rintro x ⟨hxA, hxF⟩
    refine hcut₁.inter_eq.subset ⟨hxA, ⟨?_, hxF⟩⟩
    rw [← hinter₁₂] at hxA
    exact hxA.1
  have hpF : a₀ ∈ D₂.domain ∩ frontier D.domain :=
    ⟨hAD₂ hcut₁.fst.left_mem, hcut₁.snd.left_mem.2⟩
  have hqF : a₁ ∈ D₂.domain ∩ frontier D.domain :=
    ⟨hAD₂ hcut₁.fst.right_mem, hcut₁.snd.right_mem.2⟩
  have hSHT₀image : f₂ '' (SH ∩ T₀) = D₂.domain ∩ frontier D.domain := by
    apply Subset.antisymm
    · rintro y ⟨x, ⟨hxSH, hxT₀⟩, rfl⟩
      have hmem : f₂ x ∈ S₂ := by
        rw [← hT₀image]
        exact mem_image_of_mem f₂ hxT₀
      rw [hS₂eq] at hmem
      rcases hmem with hgood | hxA
      · exact hgood
      · have hxpair : x ∈ ({j a₀, j a₁} : Set (EuclideanSpace ℝ (Fin 2))) :=
          hcutH.inter_eq.subset ⟨hA'char x (hT₀Q hxT₀) hxA, hxSH⟩
        rcases hxpair with rfl | rfl
        · rw [hf₂jp]
          exact hpF
        · rw [hf₂jq]
          exact hqF
    · intro y hy
      have hyT₀ : y ∈ f₂ '' T₀ := by
        rw [hT₀image, hS₂eq]
        exact Or.inl hy
      obtain ⟨x, hxT₀, hxy⟩ := hyT₀
      by_cases hxA' : x ∈ A'
      · have hyA : y ∈ A := by
          rw [← hf₂A'image]
          exact ⟨x, hxA', hxy⟩
        rcases hAF ⟨hyA, hy.2⟩ with rfl | rfl
        · exact ⟨j y, ⟨hcutH.snd.left_mem, hA'T (mem_image_of_mem j hyA)⟩, hf₂jp⟩
        · exact ⟨j y, ⟨hcutH.snd.right_mem, hA'T (mem_image_of_mem j hyA)⟩, hf₂jq⟩
      · refine ⟨x, ⟨?_, hxT₀⟩, hxy⟩
        have hxfront : x ∈ frontier H.domain := by
          rw [hfrontH]
          exact Or.inr hxT₀
        exact (hcutH.union_eq.symm.subset hxfront).resolve_left hxA'
  have hHR₀ : H '' R₀ = D '' (D₁.domain ∩ frontier D.domain) := by
    calc
      H '' R₀ = (D₁ ∘ f₁) '' R₀ := Set.image_congr (hH₁.mono hR₀P)
      _ = D₁ '' (f₁ '' R₀) := image_comp D₁ f₁ R₀
      _ = D₁ '' (D₁.domain ∩ frontier D.domain) := congrArg (D₁ '' ·) hR₀image
      _ = D '' (D₁.domain ∩ frontier D.domain) := by rw [hfun₁]
  have hHmid : H '' (SH ∩ T₀) = D '' (D₂.domain ∩ frontier D.domain) := by
    calc
      H '' (SH ∩ T₀) = (D₂ ∘ f₂) '' (SH ∩ T₀) :=
        Set.image_congr (hH₂.mono fun x hx => hT₀Q hx.2)
      _ = D₂ '' (f₂ '' (SH ∩ T₀)) := image_comp D₂ f₂ _
      _ = D₂ '' (D₂.domain ∩ frontier D.domain) := congrArg (D₂ '' ·) hSHT₀image
      _ = D '' (D₂.domain ∩ frontier D.domain) := by rw [hfun₂]
  have hSHsplit : SH = R₀ ∪ SH ∩ T₀ := by
    apply Subset.antisymm
    · intro x hx
      have hxfront : x ∈ frontier H.domain := hcutH.snd_subset hx
      rw [hfrontH] at hxfront
      rcases hxfront with hxR | hxT
      · exact Or.inl hxR
      · exact Or.inr ⟨hx, hxT⟩
    · exact union_subset hR₀SH fun x hx => hx.1
  have hHSH : H '' SH = D '' ((D₁.domain ∪ D₂.domain) ∩ frontier D.domain) := by
    rw [union_inter_distrib_right, image_union, hSHsplit, image_union]
    exact congrArg₂ (· ∪ ·) hHR₀ hHmid
  have hR'P' : R' ⊆ P' := hcutP'.snd_subset.trans hP'.isPolyhedron.isClosed.frontier_subset
  have hT'Q' : T' ⊆ Q' := hcutQ'.snd_subset.trans hQ'.isPolyhedron.isClosed.frontier_subset
  have hGR'image : G '' R' = D '' ((D₁.domain ∪ D₂.domain) ∩ frontier D.domain) := by
    calc
      G '' R' = (H ∘ h) '' R' := Set.image_congr (hGH.mono hR'P')
      _ = H '' (h '' R') := image_comp H h R'
      _ = H '' SH := congrArg (H '' ·) hR'image
      _ = D '' ((D₁.domain ∪ D₂.domain) ∩ frontier D.domain) := hHSH
  have hGT'image : G '' T' = D '' (D₃.domain ∩ frontier D.domain) := by
    calc
      G '' T' = (D₃ ∘ f₃) '' T' := Set.image_congr (hG₃.mono hT'Q')
      _ = D₃ '' (f₃ '' T') := image_comp D₃ f₃ T'
      _ = D₃ '' (D₃.domain ∩ frontier D.domain) := congrArg (D₃ '' ·) hT'image
      _ = D '' (D₃.domain ∩ frontier D.domain) := by rw [hfun₃]
  have hRT : R' ∩ T' = {a, b} := by
    apply Subset.antisymm
    · rintro x ⟨hxR, hxT⟩
      have hxP : x ∈ P' :=
        hP'.isPolyhedron.isClosed.frontier_subset (hcutP'.snd_subset hxR)
      have hxQ : x ∈ Q' :=
        hQ'.isPolyhedron.isClosed.frontier_subset (hcutQ'.snd_subset hxT)
      exact hcutP'.inter_eq.subset ⟨⟨hxP, hxQ⟩, hxR⟩
    · rintro x (rfl | rfl)
      · exact ⟨hcutP'.snd.left_mem, hcutQ'.snd.left_mem⟩
      · exact ⟨hcutP'.snd.right_mem, hcutQ'.snd.right_mem⟩
  obtain ⟨a', b', ρ, κ, e, hρrange, hκrange, he, hρinj, hκinj, ha'val, hb'val⟩ :=
    exists_boundaryParam_paths_of_isCutPair_union_with_endpoints
      hcutP'.snd hcutQ'.snd hRT hfrontG
  let σ : Path (G.boundary a') (G.boundary b') := ρ.map G.boundary.continuous
  let ω : Path (G.boundary b') (G.boundary a') := κ.map G.boundary.continuous
  have hσrange : Set.range σ = G '' R' := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨ρ t, ?_, rfl⟩
      rw [← hρrange]
      exact ⟨t, rfl⟩
    · rintro ⟨w, hwR, rfl⟩
      rw [← hρrange] at hwR
      obtain ⟨t, htw⟩ := hwR
      refine ⟨t, ?_⟩
      change G (ρ t) = G w
      exact congrArg G htw
  have hωrange : Set.range ω = G '' T' := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨κ t, ?_, rfl⟩
      rw [← hκrange]
      exact ⟨t, rfl⟩
    · rintro ⟨w, hwT, rfl⟩
      rw [← hκrange] at hwT
      obtain ⟨t, htw⟩ := hwT
      refine ⟨t, ?_⟩
      change G (κ t) = G w
      exact congrArg G htw
  have hboundaryParam : ∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ := by
    intro θ
    rw [he θ]
    obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ
    simp only [pathToCircle_coe]
    change ((ρ.trans κ).map G.boundary.continuous) t = (σ.trans ω) t
    rw [Path.map_trans]
  exact ⟨H, G, P, Q, P', Q', f₁, f₂, h, f₃, A', hP, hQ, hHdomain,
    hf₁, hf₂, hf₁seam, hf₂seam, hH₁, hH₂, rfl, hA', hA'seam, hA'frontH, hk,
    hP', hQ', hGdomain, hh, hf₃, hhseam, hf₃seam, hGH, hG₃,
    a, b, R', T', hcutP', hcutQ', hR', hT', hfrontG, hha, hhb, hf₃aeq, hf₃beq,
    G.boundary a', G.boundary b', σ, ω, e, hσrange, hωrange, hboundaryParam,
    hGR'image, hGT'image, a', b', ρ, κ, hρinj, hκinj, hρrange, hκrange, he,
    R₀, T₀, SH, pH, qH, hcutP, hcutQ, hcutH, hR₀SH, hSHsplit, hR'image,
    hR₀image, hSHT₀image, hT'image, hf₁pH, hf₁qH, hf₂pH, hf₂qH, hf₂f₁, ha'val, hb'val⟩

theorem exists_cross_glue_of_isPLHomeomorphOn_disjoint_boundary_arcs
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D₁ D₂ D₃ : SingularTwoCell M) {D : SingularTwoCell M}
    {A C : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) (hAC : Disjoint A C)
    {a₀ a₁ : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hcover : D₁.domain ∪ D₂.domain ∪ D₃.domain = D.domain)
    (hinter₁₂ : D₁.domain ∩ D₂.domain = A)
    (hinter₂₃ : D₂.domain ∩ D₃.domain = C)
    (hAfront₂ : A ⊆ frontier D₂.domain)
    (hCfront₂ : C ⊆ frontier D₂.domain)
    (hcut₁ : Schoenflies.IsCutPair (frontier D₁.domain) a₀ a₁ A
      (D₁.domain ∩ frontier D.domain))
    (hcut₃ : Schoenflies.IsCutPair (frontier D₃.domain) (g a₀) (g a₁) C
      (D₃.domain ∩ frontier D.domain))
    (hg : IsPLHomeomorphOn g A C)
    (hcompat₁₂ : EqOn D₁ (D₂ ∘ g) A)
    (hcompat₂₃ : EqOn D₂ (D₃ ∘ g) A)
    (hfun₁ : D₁.toFun = D.toFun) (hfun₂ : D₂.toFun = D.toFun)
    (hfun₃ : D₃.toFun = D.toFun) :
    ∃ (H G : SingularTwoCell M)
      (P Q P' Q' : Set (EuclideanSpace ℝ (Fin 2)))
      (f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (A' : Set (EuclideanSpace ℝ (Fin 2))),
      IsPLBall 2 P ∧ IsPLBall 2 Q ∧ H.domain = P ∪ Q ∧
      IsPLHomeomorphOn f₁ P D₁.domain ∧
      IsPLHomeomorphOn f₂ Q D₂.domain ∧
      f₁ '' (P ∩ Q) = A ∧ f₂ '' (P ∩ Q) = C ∧
      EqOn H (D₁ ∘ f₁) P ∧ EqOn H (D₂ ∘ f₂) Q ∧
      A' = Function.invFunOn f₂ Q '' A ∧ IsPLBall 1 A' ∧ Disjoint A' (P ∩ Q) ∧
      A' ⊆ frontier H.domain ∧
      IsPLHomeomorphOn (g ∘ f₂) A' C ∧
      IsPLBall 2 P' ∧ IsPLBall 2 Q' ∧ G.domain = P' ∪ Q' ∧
      IsPLHomeomorphOn h P' H.domain ∧
      IsPLHomeomorphOn f₃ Q' D₃.domain ∧
      h '' (P' ∩ Q') = A' ∧ f₃ '' (P' ∩ Q') = C ∧
      EqOn G (H ∘ h) P' ∧ EqOn G (D₃ ∘ f₃) Q' ∧
      ∃ a b : EuclideanSpace ℝ (Fin 2),
      ∃ R T : Set (EuclideanSpace ℝ (Fin 2)),
        Schoenflies.IsCutPair (frontier P') a b (P' ∩ Q') R ∧
        Schoenflies.IsCutPair (frontier Q') a b (P' ∩ Q') T ∧
        IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier G.domain = R ∪ T ∧
        h a = Function.invFunOn f₂ Q a₀ ∧
        h b = Function.invFunOn f₂ Q a₁ ∧
        f₃ a = g a₀ ∧ f₃ b = g a₁ ∧
        ∃ (x y : M) (σ : Path x y) (ω : Path y x)
            (e : loopCircle ≃ₜ frontier G.domain),
          Set.range σ = G '' R ∧ Set.range ω = G '' T ∧
            (∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ) ∧
            G '' R = D '' ((D₁.domain ∪ D₂.domain) ∩ frontier D.domain) ∧
            G '' T = D '' (D₃.domain ∩ frontier D.domain) ∧
            ∃ (a' b' : frontier G.domain) (ρ : Path a' b') (κ : Path b' a'),
              Function.Injective ρ ∧ Function.Injective κ ∧
              Set.range (fun t => ((ρ t : frontier G.domain) :
                EuclideanSpace ℝ (Fin 2))) = R ∧
              Set.range (fun t => ((κ t : frontier G.domain) :
                EuclideanSpace ℝ (Fin 2))) = T ∧
              ∀ θ, e θ = pathToCircle (ρ.trans κ) θ := by
  obtain ⟨H, G, P, Q, P', Q', f₁, f₂, h, f₃, A', hP, hQ, hHdomain,
    hf₁, hf₂, hf₁seam, hf₂seam, hH₁, hH₂, hA'def, hA', hA'seam, hA'frontH, hk,
    hP', hQ', hGdomain, hh, hf₃, hhseam, hf₃seam, hGH, hG₃,
    a, b, R', T', hcutP', hcutQ', hR', hT', hfrontG, hha, hhb, hf₃aeq, hf₃beq,
    x, y, σ, ω, e, hσrange, hωrange, hboundaryParam,
    hGR'image, hGT'image, a', b', ρ, κ, hρinj, hκinj, hρrange, hκrange, he, -⟩ :=
    D₁.exists_cross_glue_of_isPLHomeomorphOn_disjoint_boundary_arcs_with_source_arcs
      D₂ D₃ hA hAC hcover hinter₁₂ hinter₂₃ hAfront₂ hCfront₂ hcut₁ hcut₃ hg
      hcompat₁₂ hcompat₂₃ hfun₁ hfun₂ hfun₃
  exact ⟨H, G, P, Q, P', Q', f₁, f₂, h, f₃, A', hP, hQ, hHdomain,
    hf₁, hf₂, hf₁seam, hf₂seam, hH₁, hH₂, hA'def, hA', hA'seam, hA'frontH, hk,
    hP', hQ', hGdomain, hh, hf₃, hhseam, hf₃seam, hGH, hG₃,
    a, b, R', T', hcutP', hcutQ', hR', hT', hfrontG, hha, hhb, hf₃aeq, hf₃beq,
    x, y, σ, ω, e, hσrange, hωrange, hboundaryParam,
    hGR'image, hGT'image, a', b', ρ, κ, hρinj, hκinj, hρrange, hκrange, he⟩

end SingularTwoCell

theorem exists_three_segment_parameters_of_injective_param
    {S R T : Set (EuclideanSpace ℝ (Fin 2))}
    {p q : EuclideanSpace ℝ (Fin 2)}
    (f : ℝ → EuclideanSpace ℝ (Fin 2))
    (hfc : ContinuousOn f (Set.Icc 0 1)) (hfi : Set.InjOn f (Set.Icc 0 1))
    (hfimage : f '' Set.Icc 0 1 = S)
    (hR : Schoenflies.IsArcBetween R p q)
    (hRsub : R ⊆ S) (hsplit : S = R ∪ (S ∩ T))
    (hpT : p ∈ T) (hqT : q ∈ T) :
    ∃ t₁ t₂ : ℝ, f t₁ = p ∧ f t₂ = q ∧
      t₁ ∈ Set.Icc 0 1 ∧ t₂ ∈ Set.Icc 0 1 ∧ t₁ ≠ t₂ ∧
      ((t₁ < t₂ ∧
        (∀ t ∈ Set.Icc 0 t₁, f t ∈ T) ∧
        (∀ t ∈ Set.Icc t₁ t₂, f t ∈ R) ∧
        (∀ t ∈ Set.Icc t₂ 1, f t ∈ T)) ∨
       (t₂ < t₁ ∧
        (∀ t ∈ Set.Icc 0 t₂, f t ∈ T) ∧
        (∀ t ∈ Set.Icc t₂ t₁, f t ∈ R) ∧
        (∀ t ∈ Set.Icc t₁ 1, f t ∈ T))) := by
  have hS : Schoenflies.IsArcBetween S (f 0) (f 1) :=
    ⟨f, hfc, hfi, hfimage, rfl, rfl⟩
  have hpq : p ≠ q := by
    intro hpq
    obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hR
    exact zero_ne_one (hgi Schoenflies.zero_mem_I Schoenflies.one_mem_I
      (hg0.trans (hpq.trans hg1.symm)))
  have hpS : p ∈ S := hRsub hR.left_mem
  have hqS : q ∈ S := hRsub hR.right_mem
  rw [← hfimage] at hpS hqS
  obtain ⟨s, hs, hsp⟩ := hpS
  obtain ⟨t, ht, htq⟩ := hqS
  have hst : s ≠ t := by
    intro hst
    apply hpq
    rw [← hsp, hst, htq]
  have hB : Schoenflies.IsArcBetween (f '' Set.uIcc s t) p q := by
    have hB0 := Schoenflies.isArcBetween_subarc_of_injOn_I hfc hfi hs ht hst
    rw [hsp, htq] at hB0
    exact hB0
  have hBsub : f '' Set.uIcc s t ⊆ S := by
    intro x hx
    rw [← hfimage]
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨z, Set.uIcc_subset_Icc hs ht hz, rfl⟩
  have hReq : R = f '' Set.uIcc s t :=
    Schoenflies.IsArcBetween.eq_of_subset_arc hR hB hS hRsub hBsub
  have hmid : ∀ z ∈ Set.uIcc s t, f z ∈ R := by
    intro z hz
    rw [hReq]
    exact ⟨z, hz, rfl⟩
  have hout : ∀ z ∈ Set.Icc 0 1, z ∉ Set.uIcc s t → f z ∈ T := by
    intro z hzI hnot
    have hzS : f z ∈ S := by
      rw [← hfimage]
      exact ⟨z, hzI, rfl⟩
    rw [hsplit] at hzS
    rcases hzS with hzR | ⟨-, hzT⟩
    · rw [hReq] at hzR
      obtain ⟨w, hw, hfw⟩ := hzR
      have hwI : w ∈ Set.Icc 0 1 := Set.uIcc_subset_Icc hs ht hw
      have hzw : z = w := hfi hzI hwI hfw.symm
      exact (hnot (hzw ▸ hw)).elim
    · exact hzT
  rcases le_total s t with hstle | htsle
  · have hstlt : s < t := lt_of_le_of_ne hstle hst
    refine ⟨s, t, hsp, htq, hs, ht, hst,
      Or.inl ⟨hstlt, ?_, ?_, ?_⟩⟩
    · intro z hz
      by_cases hzs : z = s
      · rw [hzs, hsp]
        exact hpT
      · apply hout z ⟨hz.1, le_trans hz.2 (le_trans hstle ht.2)⟩
        rw [Set.uIcc_of_le hstle]
        intro hzst
        exact hzs (le_antisymm hz.2 hzst.1)
    · intro z hz
      apply hmid z
      rw [Set.uIcc_of_le hstle]
      exact hz
    · intro z hz
      by_cases hzt : z = t
      · rw [hzt, htq]
        exact hqT
      · apply hout z ⟨le_trans (le_trans hs.1 hstle) hz.1, hz.2⟩
        rw [Set.uIcc_of_le hstle]
        intro hzst
        exact hzt (le_antisymm hzst.2 hz.1)
  · have htslt : t < s := lt_of_le_of_ne htsle hst.symm
    refine ⟨s, t, hsp, htq, hs, ht, hst,
      Or.inr ⟨htslt, ?_, ?_, ?_⟩⟩
    · intro z hz
      by_cases hzt : z = t
      · rw [hzt, htq]
        exact hqT
      · apply hout z ⟨hz.1, le_trans hz.2 (le_trans htsle hs.2)⟩
        rw [Set.uIcc_of_ge htsle]
        intro hzts
        exact hzt (le_antisymm hz.2 hzts.1)
    · intro z hz
      apply hmid z
      rw [Set.uIcc_of_ge htsle]
      exact hz
    · intro z hz
      by_cases hzs : z = s
      · rw [hzs, hsp]
        exact hpT
      · apply hout z ⟨le_trans hs.1 hz.1, hz.2⟩
        rw [Set.uIcc_of_ge htsle]
        intro hzts
        exact hzs (le_antisymm hzts.2 hz.1)

theorem exists_three_segment_source_parameters
    {S R T : Set (EuclideanSpace ℝ (Fin 2))}
    {s₀ s₁ p q : EuclideanSpace ℝ (Fin 2)}
    (hS : Schoenflies.IsArcBetween S s₀ s₁)
    (hR : Schoenflies.IsArcBetween R p q)
    (hRsub : R ⊆ S) (hsplit : S = R ∪ (S ∩ T))
    (hpT : p ∈ T) (hqT : q ∈ T) :
    ∃ (f : ℝ → EuclideanSpace ℝ (Fin 2)) (t₁ t₂ : ℝ),
      ContinuousOn f (Set.Icc 0 1) ∧ Set.InjOn f (Set.Icc 0 1) ∧
      f '' Set.Icc 0 1 = S ∧ f 0 = s₀ ∧ f 1 = s₁ ∧ f t₁ = p ∧ f t₂ = q ∧
      t₁ ∈ Set.Icc 0 1 ∧ t₂ ∈ Set.Icc 0 1 ∧ t₁ ≠ t₂ ∧
      ((t₁ < t₂ ∧
        (∀ t ∈ Set.Icc 0 t₁, f t ∈ T) ∧
        (∀ t ∈ Set.Icc t₁ t₂, f t ∈ R) ∧
        (∀ t ∈ Set.Icc t₂ 1, f t ∈ T)) ∨
       (t₂ < t₁ ∧
        (∀ t ∈ Set.Icc 0 t₂, f t ∈ T) ∧
        (∀ t ∈ Set.Icc t₂ t₁, f t ∈ R) ∧
        (∀ t ∈ Set.Icc t₁ 1, f t ∈ T))) := by
  obtain ⟨f, hfc, hfi, hfimage, hf0, hf1⟩ := hS
  obtain ⟨t₁, t₂, h₁, h₂, ht₁, ht₂, hne, hparts⟩ :=
    exists_three_segment_parameters_of_injective_param f hfc hfi hfimage
      hR hRsub hsplit hpT hqT
  exact ⟨f, t₁, t₂, hfc, hfi, hfimage, hf0, hf1, h₁, h₂, ht₁, ht₂, hne, hparts⟩

theorem exists_cross_source_segment_equations
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D H G : SingularTwoCell M}
    {P Q P' Q' R T R₀ T₀ SH : Set (EuclideanSpace ℝ (Fin 2))}
    {pH qH s₀ s₁ a b : EuclideanSpace ℝ (Fin 2)}
    {f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hS : Schoenflies.IsArcBetween SH s₀ s₁)
    (hR₀ : Schoenflies.IsArcBetween R₀ pH qH)
    (hR₀sub : R₀ ⊆ SH) (hsplit : SH = R₀ ∪ (SH ∩ T₀))
    (hpH_T₀ : pH ∈ T₀) (hqH_T₀ : qH ∈ T₀)
    (hSHfront : SH ⊆ frontier H.domain)
    (hRimage : h '' R = SH) (hRsub : R ⊆ P')
    (haR : a ∈ R) (hbR : b ∈ R)
    (hha : h a = s₀) (hhb : h b = s₁)
    (hh : IsPLHomeomorphOn h P' H.domain)
    (hR₀P : R₀ ⊆ P) (hT₀Q : T₀ ⊆ Q)
    (hH₁ : EqOn H (D ∘ f₁) P) (hH₂ : EqOn H (D ∘ f₂) Q)
    (hGH : EqOn G (H ∘ h) P')
    (hTsub : T ⊆ Q') (hG₃ : EqOn G (D ∘ f₃) Q') :
    ∃ (ρ : ℝ → EuclideanSpace ℝ (Fin 2)) (t₁ t₂ : ℝ),
      ContinuousOn ρ (Set.Icc 0 1) ∧ Set.InjOn ρ (Set.Icc 0 1) ∧
      ρ '' Set.Icc 0 1 = R ∧
      ((ρ 0 = a ∧ ρ 1 = b) ∨ (ρ 0 = b ∧ ρ 1 = a)) ∧
      t₁ ∈ Set.Icc 0 1 ∧ t₂ ∈ Set.Icc 0 1 ∧ t₁ < t₂ ∧
      (∀ t ∈ Set.Icc 0 t₁, G (ρ t) = D (f₂ (h (ρ t)))) ∧
      (∀ t ∈ Set.Icc t₁ t₂, G (ρ t) = D (f₁ (h (ρ t)))) ∧
      (∀ t ∈ Set.Icc t₂ 1, G (ρ t) = D (f₂ (h (ρ t)))) ∧
      (∀ z ∈ T, G z = D (f₃ z)) := by
  obtain ⟨s, r₁, r₂, hsc, hsi, hsimage, hs0, hs1, hsr₁, hsr₂, hr₁, hr₂, hne,
    hparts⟩ := exists_three_segment_source_parameters hS hR₀ hR₀sub hsplit hpH_T₀ hqH_T₀
  have hsH : ∀ t ∈ Set.Icc (0 : ℝ) 1, s t ∈ H.domain := by
    intro t ht
    exact H.isPLBall_domain.isPolyhedron.isClosed.frontier_subset
      (hSHfront (hsimage ▸ Set.mem_image_of_mem s ht))
  let j := Function.invFunOn h P'
  have hjc : ContinuousOn j H.domain := by
    simpa only [j] using hh.symm.isPiecewiseAffineOn.continuousOn
  let ρ : ℝ → EuclideanSpace ℝ (Fin 2) := j ∘ s
  have hρc : ContinuousOn ρ (Set.Icc 0 1) := by
    exact hjc.comp hsc hsH
  have hρeq : ∀ t ∈ Set.Icc (0 : ℝ) 1, h (ρ t) = s t := by
    intro t ht
    change h (j (s t)) = s t
    exact hh.bijOn.invOn_invFunOn.2 (hsH t ht)
  have hρR : ∀ t ∈ Set.Icc (0 : ℝ) 1, ρ t ∈ R := by
    intro t ht
    have hst : s t ∈ h '' R := hRimage ▸ hsimage ▸ Set.mem_image_of_mem s ht
    obtain ⟨z, hzR, hzs⟩ := hst
    have hzP' : z ∈ P' := hRsub hzR
    have hzj : j (h z) = z := hh.bijOn.invOn_invFunOn.1 hzP'
    have hzt : ρ t = z := by
      calc
        ρ t = j (s t) := rfl
        _ = j (h z) := congrArg j hzs.symm
        _ = z := hzj
    exact hzt ▸ hzR
  have hρi : Set.InjOn ρ (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply hsi hx hy
    have h := congrArg h hxy
    rw [hρeq x hx, hρeq y hy] at h
    exact h
  have hρimage : ρ '' Set.Icc (0 : ℝ) 1 = R := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact hρR t ht
    · intro z hz
      have hzh : h z ∈ SH := hRimage ▸ Set.mem_image_of_mem h hz
      obtain ⟨t, ht, hst⟩ := hsimage ▸ hzh
      refine ⟨t, ht, ?_⟩
      have hzP' : z ∈ P' := hRsub hz
      have hzj : j (h z) = z := hh.bijOn.invOn_invFunOn.1 hzP'
      calc
        ρ t = j (s t) := rfl
        _ = j (h z) := congrArg j hst
        _ = z := hzj
  have hEqT : ∀ t ∈ Set.Icc (0 : ℝ) 1, s t ∈ T₀ →
      G (ρ t) = D (f₂ (h (ρ t))) := by
    intro t ht hT
    have hRP : ρ t ∈ P' := hRsub (hρR t ht)
    calc
      G (ρ t) = H (h (ρ t)) := by simpa only [Function.comp_apply] using hGH hRP
      _ = H (s t) := congrArg H (hρeq t ht)
      _ = D (f₂ (s t)) := hH₂ (hT₀Q hT)
      _ = D (f₂ (h (ρ t))) := congrArg (fun z => D (f₂ z)) (hρeq t ht).symm
  have hEqR : ∀ t ∈ Set.Icc (0 : ℝ) 1, s t ∈ R₀ →
      G (ρ t) = D (f₁ (h (ρ t))) := by
    intro t ht hR
    have hRP : ρ t ∈ P' := hRsub (hρR t ht)
    calc
      G (ρ t) = H (h (ρ t)) := by simpa only [Function.comp_apply] using hGH hRP
      _ = H (s t) := congrArg H (hρeq t ht)
      _ = D (f₁ (s t)) := hH₁ (hR₀P hR)
      _ = D (f₁ (h (ρ t))) := congrArg (fun z => D (f₁ z)) (hρeq t ht).symm
  have hEq3 : ∀ z ∈ T, G z = D (f₃ z) := by
    intro z hz
    simpa only [Function.comp_apply] using hG₃ (hTsub hz)
  have hja : j s₀ = a := by
    calc
      j s₀ = j (h a) := congrArg j hha.symm
      _ = a := hh.bijOn.invOn_invFunOn.1 (hRsub haR)
  have hjb : j s₁ = b := by
    calc
      j s₁ = j (h b) := congrArg j hhb.symm
      _ = b := hh.bijOn.invOn_invFunOn.1 (hRsub hbR)
  rcases hparts with hforward | hbackward
  · refine ⟨ρ, r₁, r₂, hρc, hρi, hρimage, ?_, hr₁, hr₂, hforward.1, ?_, ?_, ?_, hEq3⟩
    · left
      constructor
      · calc
          ρ 0 = j (s 0) := rfl
          _ = j s₀ := congrArg j hs0
          _ = a := hja
      · calc
          ρ 1 = j (s 1) := rfl
          _ = j s₁ := congrArg j hs1
          _ = b := hjb
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2, hr₁.2]⟩
      exact hEqT t htI (hforward.2.1 t ht)
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1, hr₁.1], by linarith [ht.2, hr₂.2]⟩
      exact hEqR t htI (hforward.2.2.1 t ht)
    · intro t ht
      exact hEqT t ⟨by linarith [ht.1, hr₂.1], by linarith [ht.2]⟩
        (hforward.2.2.2 t ht)
  · let ρ' : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => ρ (1 - t)
    have hrevmap : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 - t ∈ Set.Icc 0 1 := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hrevcont : ContinuousOn ρ' (Set.Icc (0 : ℝ) 1) := by
      dsimp [ρ']
      exact hρc.comp (continuousOn_const.sub continuousOn_id) hrevmap
    have hrevinj : Set.InjOn ρ' (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      have hxy' := hρi (hrevmap x hx) (hrevmap y hy) hxy
      linarith
    have hrevimage : ρ' '' Set.Icc (0 : ℝ) 1 = R := by
      apply Set.Subset.antisymm
      · rintro z ⟨t, ht, rfl⟩
        exact hρR (1 - t) (hrevmap t ht)
      · intro z hz
        rw [← hρimage] at hz
        obtain ⟨t, ht, hzt⟩ := hz
        refine ⟨1 - t, hrevmap t ht, ?_⟩
        dsimp [ρ']
        rw [show 1 - (1 - t) = t by ring, hzt]
    have hrev₁ : 1 - r₁ ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [hr₁.2], by linarith [hr₁.1]⟩
    have hrev₂ : 1 - r₂ ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [hr₂.2], by linarith [hr₂.1]⟩
    have hnewlt : 1 - r₁ < 1 - r₂ := by linarith [hbackward.1]
    refine ⟨ρ', 1 - r₁, 1 - r₂, hrevcont, hrevinj, hrevimage, ?_, hrev₁, hrev₂,
      hnewlt, ?_, ?_, ?_, hEq3⟩
    · right
      constructor
      · change ρ (1 - 0) = b
        rw [show 1 - (0 : ℝ) = 1 by norm_num, show ρ 1 = j (s 1) by rfl, hs1, hjb]
      · change ρ (1 - 1) = a
        rw [show 1 - (1 : ℝ) = 0 by norm_num, show ρ 0 = j (s 0) by rfl, hs0, hja]
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2, hrev₁.2]⟩
      have hz : 1 - t ∈ Set.Icc r₁ 1 := by
        exact ⟨by linarith [ht.2, hnewlt], by linarith [ht.1, hr₁.2]⟩
      exact hEqT (1 - t) (hrevmap t htI) (hbackward.2.2.2 _ hz)
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.1, hrev₁.1], by linarith [ht.2, hrev₂.2]⟩
      have hz : 1 - t ∈ Set.Icc r₂ r₁ := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      exact hEqR (1 - t) (hrevmap t htI) (hbackward.2.2.1 _ hz)
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1, hrev₂.1], by linarith [ht.2]⟩
      have hz : 1 - t ∈ Set.Icc 0 r₂ := by
        exact ⟨by linarith [ht.2, hr₂.1], by linarith [ht.1]⟩
      exact hEqT (1 - t) (hrevmap t htI) (hbackward.2.1 _ hz)

theorem exists_cross_source_segment_equations_with_source_data
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D D₁ D₂ H G : SingularTwoCell M}
    {P Q P' Q' R T R₀ T₀ SH : Set (EuclideanSpace ℝ (Fin 2))}
    {pH qH s₀ s₁ a b : EuclideanSpace ℝ (Fin 2)}
    {f₁ f₂ h f₃ g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hS : Schoenflies.IsArcBetween SH s₀ s₁)
    (hR₀ : Schoenflies.IsArcBetween R₀ pH qH)
    (hR₀sub : R₀ ⊆ SH) (hsplit : SH = R₀ ∪ (SH ∩ T₀))
    (hpH_T₀ : pH ∈ T₀) (hqH_T₀ : qH ∈ T₀)
    (hSHfront : SH ⊆ frontier H.domain)
    (hRimage : h '' R = SH) (hRsub : R ⊆ P')
    (haR : a ∈ R) (hbR : b ∈ R)
    (hha : h a = s₀) (hhb : h b = s₁)
    (hh : IsPLHomeomorphOn h P' H.domain)
    (hR₀P : R₀ ⊆ P) (hT₀Q : T₀ ⊆ Q)
    (hH₁ : EqOn H (D ∘ f₁) P) (hH₂ : EqOn H (D ∘ f₂) Q)
    (hGH : EqOn G (H ∘ h) P')
    (hseam : EqOn f₂ (g ∘ f₁) (P ∩ Q))
    (hR₀image : f₁ '' R₀ = D₁.domain ∩ frontier D.domain)
    (hSHT₀image : f₂ '' (SH ∩ T₀) = D₂.domain ∩ frontier D.domain)
    (hTsub : T ⊆ Q') (hG₃ : EqOn G (D ∘ f₃) Q') :
    ∃ (ρ : ℝ → EuclideanSpace ℝ (Fin 2)) (t₁ t₂ : ℝ),
      ContinuousOn ρ (Set.Icc 0 1) ∧ Set.InjOn ρ (Set.Icc 0 1) ∧
      ρ '' Set.Icc 0 1 = R ∧
      ((ρ 0 = a ∧ ρ 1 = b) ∨ (ρ 0 = b ∧ ρ 1 = a)) ∧
      t₁ ∈ Set.Icc 0 1 ∧ t₂ ∈ Set.Icc 0 1 ∧ t₁ < t₂ ∧
      (∀ t ∈ Set.Icc 0 t₁, G (ρ t) = D (f₂ (h (ρ t)))) ∧
      (∀ t ∈ Set.Icc t₁ t₂, G (ρ t) = D (f₁ (h (ρ t)))) ∧
      (∀ t ∈ Set.Icc t₂ 1, G (ρ t) = D (f₂ (h (ρ t)))) ∧
      (∀ z ∈ T, G z = D (f₃ z)) ∧
      (∀ t ∈ Set.Icc 0 t₁, f₂ (h (ρ t)) ∈ D₂.domain ∩ frontier D.domain) ∧
      (∀ t ∈ Set.Icc t₁ t₂, f₁ (h (ρ t)) ∈ D₁.domain ∩ frontier D.domain) ∧
      (∀ t ∈ Set.Icc t₂ 1, f₂ (h (ρ t)) ∈ D₂.domain ∩ frontier D.domain) ∧
      f₂ (h (ρ t₁)) = g (f₁ (h (ρ t₁))) ∧
      f₂ (h (ρ t₂)) = g (f₁ (h (ρ t₂))) := by
  obtain ⟨s, r₁, r₂, hsc, hsi, hsimage, hs0, hs1, hsr₁, hsr₂, hr₁, hr₂, hne,
    hparts⟩ := exists_three_segment_source_parameters hS hR₀ hR₀sub hsplit hpH_T₀ hqH_T₀
  have hsH : ∀ t ∈ Set.Icc (0 : ℝ) 1, s t ∈ H.domain := by
    intro t ht
    exact H.isPLBall_domain.isPolyhedron.isClosed.frontier_subset
      (hSHfront (hsimage ▸ Set.mem_image_of_mem s ht))
  let j := Function.invFunOn h P'
  have hjc : ContinuousOn j H.domain := by
    simpa only [j] using hh.symm.isPiecewiseAffineOn.continuousOn
  let ρ : ℝ → EuclideanSpace ℝ (Fin 2) := j ∘ s
  have hρc : ContinuousOn ρ (Set.Icc 0 1) := by
    exact hjc.comp hsc hsH
  have hρeq : ∀ t ∈ Set.Icc (0 : ℝ) 1, h (ρ t) = s t := by
    intro t ht
    change h (j (s t)) = s t
    exact hh.bijOn.invOn_invFunOn.2 (hsH t ht)
  have hρR : ∀ t ∈ Set.Icc (0 : ℝ) 1, ρ t ∈ R := by
    intro t ht
    have hst : s t ∈ h '' R := hRimage ▸ hsimage ▸ Set.mem_image_of_mem s ht
    obtain ⟨z, hzR, hzs⟩ := hst
    have hzP' : z ∈ P' := hRsub hzR
    have hzj : j (h z) = z := hh.bijOn.invOn_invFunOn.1 hzP'
    have hzt : ρ t = z := by
      calc
        ρ t = j (s t) := rfl
        _ = j (h z) := congrArg j hzs.symm
        _ = z := hzj
    exact hzt ▸ hzR
  have hρi : Set.InjOn ρ (Set.Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply hsi hx hy
    have h := congrArg h hxy
    rw [hρeq x hx, hρeq y hy] at h
    exact h
  have hρimage : ρ '' Set.Icc (0 : ℝ) 1 = R := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact hρR t ht
    · intro z hz
      have hzh : h z ∈ SH := hRimage ▸ Set.mem_image_of_mem h hz
      obtain ⟨t, ht, hst⟩ := hsimage ▸ hzh
      refine ⟨t, ht, ?_⟩
      have hzP' : z ∈ P' := hRsub hz
      have hzj : j (h z) = z := hh.bijOn.invOn_invFunOn.1 hzP'
      calc
        ρ t = j (s t) := rfl
        _ = j (h z) := congrArg j hst
        _ = z := hzj
  have hEqT : ∀ t ∈ Set.Icc (0 : ℝ) 1, s t ∈ T₀ →
      G (ρ t) = D (f₂ (h (ρ t))) := by
    intro t ht hT
    have hRP : ρ t ∈ P' := hRsub (hρR t ht)
    calc
      G (ρ t) = H (h (ρ t)) := by simpa only [Function.comp_apply] using hGH hRP
      _ = H (s t) := congrArg H (hρeq t ht)
      _ = D (f₂ (s t)) := hH₂ (hT₀Q hT)
      _ = D (f₂ (h (ρ t))) := congrArg (fun z => D (f₂ z)) (hρeq t ht).symm
  have hEqR : ∀ t ∈ Set.Icc (0 : ℝ) 1, s t ∈ R₀ →
      G (ρ t) = D (f₁ (h (ρ t))) := by
    intro t ht hR
    have hRP : ρ t ∈ P' := hRsub (hρR t ht)
    calc
      G (ρ t) = H (h (ρ t)) := by simpa only [Function.comp_apply] using hGH hRP
      _ = H (s t) := congrArg H (hρeq t ht)
      _ = D (f₁ (s t)) := hH₁ (hR₀P hR)
      _ = D (f₁ (h (ρ t))) := congrArg (fun z => D (f₁ z)) (hρeq t ht).symm
  have hEq3 : ∀ z ∈ T, G z = D (f₃ z) := by
    intro z hz
    simpa only [Function.comp_apply] using hG₃ (hTsub hz)
  have hSourceT : ∀ t ∈ Set.Icc (0 : ℝ) 1, s t ∈ T₀ →
      f₂ (h (ρ t)) ∈ D₂.domain ∩ frontier D.domain := by
    intro t ht hT
    have hSHt : s t ∈ SH := by
      rw [← hsimage]
      exact ⟨t, ht, rfl⟩
    have himage : f₂ (s t) ∈ D₂.domain ∩ frontier D.domain := by
      rw [← hSHT₀image]
      exact ⟨s t, ⟨hSHt, hT⟩, rfl⟩
    rw [hρeq t ht]
    exact himage
  have hSourceR : ∀ t ∈ Set.Icc (0 : ℝ) 1, s t ∈ R₀ →
      f₁ (h (ρ t)) ∈ D₁.domain ∩ frontier D.domain := by
    intro t ht hR
    have himage : f₁ (s t) ∈ D₁.domain ∩ frontier D.domain := by
      rw [← hR₀image]
      exact ⟨s t, hR, rfl⟩
    rw [hρeq t ht]
    exact himage
  have hseamAt : ∀ t ∈ Set.Icc (0 : ℝ) 1, s t ∈ R₀ → s t ∈ T₀ →
      f₂ (h (ρ t)) = g (f₁ (h (ρ t))) := by
    intro t ht hR hT
    have hP : h (ρ t) ∈ P := by
      rw [hρeq t ht]
      exact hR₀P hR
    have hQ : h (ρ t) ∈ Q := by
      rw [hρeq t ht]
      exact hT₀Q hT
    simpa only [Function.comp_apply] using hseam ⟨hP, hQ⟩
  have hja : j s₀ = a := by
    calc
      j s₀ = j (h a) := congrArg j hha.symm
      _ = a := hh.bijOn.invOn_invFunOn.1 (hRsub haR)
  have hjb : j s₁ = b := by
    calc
      j s₁ = j (h b) := congrArg j hhb.symm
      _ = b := hh.bijOn.invOn_invFunOn.1 (hRsub hbR)
  rcases hparts with hforward | hbackward
  · refine ⟨ρ, r₁, r₂, hρc, hρi, hρimage, ?_, hr₁, hr₂, hforward.1, ?_, ?_, ?_, hEq3,
      ?_, ?_, ?_, ?_, ?_⟩
    · left
      constructor
      · calc
          ρ 0 = j (s 0) := rfl
          _ = j s₀ := congrArg j hs0
          _ = a := hja
      · calc
          ρ 1 = j (s 1) := rfl
          _ = j s₁ := congrArg j hs1
          _ = b := hjb
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2, hr₁.2]⟩
      exact hEqT t htI (hforward.2.1 t ht)
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1, hr₁.1], by linarith [ht.2, hr₂.2]⟩
      exact hEqR t htI (hforward.2.2.1 t ht)
    · intro t ht
      exact hEqT t ⟨by linarith [ht.1, hr₂.1], by linarith [ht.2]⟩
        (hforward.2.2.2 t ht)
    · intro t ht
      exact hSourceT t ⟨by linarith [ht.1], by linarith [ht.2, hr₁.2]⟩
        (hforward.2.1 t ⟨ht.1, ht.2⟩)
    · intro t ht
      exact hSourceR t ⟨by linarith [ht.1, hr₁.1], by linarith [ht.2, hr₂.2]⟩
        (hforward.2.2.1 t ht)
    · intro t ht
      exact hSourceT t ⟨by linarith [ht.1, hr₂.1], by linarith [ht.2]⟩
        (hforward.2.2.2 t ht)
    · exact hseamAt r₁ ⟨hr₁.1, hr₁.2⟩
        (hforward.2.2.1 r₁ ⟨le_rfl, le_of_lt hforward.1⟩)
        (hforward.2.1 r₁ ⟨hr₁.1, le_rfl⟩)
    · exact hseamAt r₂ ⟨hr₂.1, hr₂.2⟩
        (hforward.2.2.1 r₂ ⟨le_of_lt hforward.1, le_rfl⟩)
        (hforward.2.2.2 r₂ ⟨le_rfl, hr₂.2⟩)
  · let ρ' : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => ρ (1 - t)
    have hrevmap : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 - t ∈ Set.Icc 0 1 := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hrevcont : ContinuousOn ρ' (Set.Icc (0 : ℝ) 1) := by
      dsimp [ρ']
      exact hρc.comp (continuousOn_const.sub continuousOn_id) hrevmap
    have hrevinj : Set.InjOn ρ' (Set.Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      have hxy' := hρi (hrevmap x hx) (hrevmap y hy) hxy
      linarith
    have hrevimage : ρ' '' Set.Icc (0 : ℝ) 1 = R := by
      apply Set.Subset.antisymm
      · rintro z ⟨t, ht, rfl⟩
        exact hρR (1 - t) (hrevmap t ht)
      · intro z hz
        rw [← hρimage] at hz
        obtain ⟨t, ht, hzt⟩ := hz
        refine ⟨1 - t, hrevmap t ht, ?_⟩
        dsimp [ρ']
        rw [show 1 - (1 - t) = t by ring, hzt]
    have hrev₁ : 1 - r₁ ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [hr₁.2], by linarith [hr₁.1]⟩
    have hrev₂ : 1 - r₂ ∈ Set.Icc (0 : ℝ) 1 := by
      exact ⟨by linarith [hr₂.2], by linarith [hr₂.1]⟩
    have hnewlt : 1 - r₁ < 1 - r₂ := by linarith [hbackward.1]
    refine ⟨ρ', 1 - r₁, 1 - r₂, hrevcont, hrevinj, hrevimage, ?_, hrev₁, hrev₂,
      hnewlt, ?_, ?_, ?_, hEq3, ?_, ?_, ?_, ?_, ?_⟩
    · right
      constructor
      · change ρ (1 - 0) = b
        rw [show 1 - (0 : ℝ) = 1 by norm_num, show ρ 1 = j (s 1) by rfl, hs1, hjb]
      · change ρ (1 - 1) = a
        rw [show 1 - (1 : ℝ) = 0 by norm_num, show ρ 0 = j (s 0) by rfl, hs0, hja]
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2, hrev₁.2]⟩
      have hz : 1 - t ∈ Set.Icc r₁ 1 := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      exact hEqT (1 - t) (hrevmap t htI) (hbackward.2.2.2 _ hz)
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.1, hrev₁.1], by linarith [ht.2, hrev₂.2]⟩
      have hz : 1 - t ∈ Set.Icc r₂ r₁ := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      exact hEqR (1 - t) (hrevmap t htI) (hbackward.2.2.1 _ hz)
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1, hrev₂.1], by linarith [ht.2]⟩
      have hz : 1 - t ∈ Set.Icc 0 r₂ := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      exact hEqT (1 - t) (hrevmap t htI) (hbackward.2.1 _ hz)
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.1], by linarith [ht.2, hr₁.1]⟩
      have hz : 1 - t ∈ Set.Icc r₁ 1 := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      exact hSourceT (1 - t) (hrevmap t htI) (hbackward.2.2.2 _ hz)
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by linarith [ht.1, hrev₁.1], by linarith [ht.2, hrev₂.2]⟩
      have hz : 1 - t ∈ Set.Icc r₂ r₁ := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      exact hSourceR (1 - t) (hrevmap t htI) (hbackward.2.2.1 _ hz)
    · intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1, hrev₂.1], by linarith [ht.2]⟩
      have hz : 1 - t ∈ Set.Icc 0 r₂ := by
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      exact hSourceT (1 - t) (hrevmap t htI) (hbackward.2.1 _ hz)
    · change f₂ (h (ρ (1 - (1 - r₁)))) = g (f₁ (h (ρ (1 - (1 - r₁)))))
      rw [show 1 - (1 - r₁) = r₁ by ring]
      exact hseamAt r₁ ⟨hr₁.1, hr₁.2⟩
        (hbackward.2.2.1 r₁ ⟨le_of_lt hbackward.1, le_rfl⟩)
        (hbackward.2.2.2 r₁ ⟨le_rfl, hr₁.2⟩)
    · change f₂ (h (ρ (1 - (1 - r₂)))) = g (f₁ (h (ρ (1 - (1 - r₂)))))
      rw [show 1 - (1 - r₂) = r₂ by ring]
      exact hseamAt r₂ ⟨hr₂.1, hr₂.2⟩
        (hbackward.2.2.1 r₂ ⟨le_rfl, le_of_lt hbackward.1⟩)
        (hbackward.2.1 r₂ ⟨hr₂.1, le_rfl⟩)

open Classical in
theorem exists_cross_glue_source_segments
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D₁ D₂ D₃ : SingularTwoCell M) {D : SingularTwoCell M}
    {A C : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) (hAC : Disjoint A C)
    {a₀ a₁ : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hcover : D₁.domain ∪ D₂.domain ∪ D₃.domain = D.domain)
    (hinter₁₂ : D₁.domain ∩ D₂.domain = A)
    (hinter₂₃ : D₂.domain ∩ D₃.domain = C)
    (hAfront₂ : A ⊆ frontier D₂.domain)
    (hCfront₂ : C ⊆ frontier D₂.domain)
    (hcut₁ : Schoenflies.IsCutPair (frontier D₁.domain) a₀ a₁ A
      (D₁.domain ∩ frontier D.domain))
    (hcut₃ : Schoenflies.IsCutPair (frontier D₃.domain) (g a₀) (g a₁) C
      (D₃.domain ∩ frontier D.domain))
    (hg : IsPLHomeomorphOn g A C)
    (hcompat₁₂ : EqOn D₁ (D₂ ∘ g) A)
    (hcompat₂₃ : EqOn D₂ (D₃ ∘ g) A)
    (hfun₁ : D₁.toFun = D.toFun)
    (hfun₂ : D₂.toFun = D.toFun)
    (hfun₃ : D₃.toFun = D.toFun) :
    ∃ (H G : SingularTwoCell M)
      (P Q P' Q' R T : Set (EuclideanSpace ℝ (Fin 2)))
      (f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (a b : EuclideanSpace ℝ (Fin 2))
      (ρ : ℝ → EuclideanSpace ℝ (Fin 2)) (t₁ t₂ : ℝ),
      IsPLBall 2 P ∧ IsPLBall 2 Q ∧ H.domain = P ∪ Q ∧
      IsPLHomeomorphOn f₁ P D₁.domain ∧ IsPLHomeomorphOn f₂ Q D₂.domain ∧
      EqOn H (D.toFun ∘ f₁) P ∧ EqOn H (D.toFun ∘ f₂) Q ∧
      IsPLBall 2 P' ∧ IsPLBall 2 Q' ∧ G.domain = P' ∪ Q' ∧
      IsPLHomeomorphOn h P' H.domain ∧ IsPLHomeomorphOn f₃ Q' D₃.domain ∧
      EqOn G (H.toFun ∘ h) P' ∧ EqOn G (D.toFun ∘ f₃) Q' ∧
      Schoenflies.IsCutPair (frontier P') a b (P' ∩ Q') R ∧
      Schoenflies.IsCutPair (frontier Q') a b (P' ∩ Q') T ∧
      IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier G.domain = R ∪ T ∧
      h a = Function.invFunOn f₂ Q a₀ ∧ h b = Function.invFunOn f₂ Q a₁ ∧
      f₃ a = g a₀ ∧ f₃ b = g a₁ ∧
      ContinuousOn ρ (Set.Icc 0 1) ∧ Set.InjOn ρ (Set.Icc 0 1) ∧
      ρ '' Set.Icc 0 1 = R ∧
      ((ρ 0 = a ∧ ρ 1 = b) ∨ (ρ 0 = b ∧ ρ 1 = a)) ∧
      t₁ ∈ Set.Icc 0 1 ∧ t₂ ∈ Set.Icc 0 1 ∧ t₁ < t₂ ∧
      (∀ t ∈ Set.Icc 0 t₁, G (ρ t) = D (f₂ (h (ρ t)))) ∧
      (∀ t ∈ Set.Icc t₁ t₂, G (ρ t) = D (f₁ (h (ρ t)))) ∧
      (∀ t ∈ Set.Icc t₂ 1, G (ρ t) = D (f₂ (h (ρ t)))) ∧
      (∀ z ∈ T, G z = D (f₃ z)) := by
  obtain ⟨H, P, Q, f₁, f₂, hP, hQ, -, hHdomain, -, -, -, hf₁, hf₂, -,
    hf₁seam, hf₂seam, hH₁, hH₂, pH, qH, R₀, T₀, hcutP, hcutQ, hR₀, -, hfrontH,
    hf₁pH, hf₁qH, hf₂pH, hf₂qH⟩ :=
    D₁.exists_glue_of_isPLHomeomorphOn_boundary_arc D₂ hA hcut₁.fst hcut₁.fst_subset hg
      hCfront₂ hcompat₁₂
  let j := Function.invFunOn f₂ Q
  let A' := j '' A
  have hAD₂ : A ⊆ D₂.domain :=
    hAfront₂.trans D₂.isPLBall_domain.isPolyhedron.isClosed.frontier_subset
  have hjA : IsPLHomeomorphOn j A A' := by
    simpa only [j, A'] using hf₂.symm.restrict hA.isPolyhedron hAD₂
  have hA' : IsPLBall 1 A' := hA.of_isPLHomeomorphOn hjA
  have hA'arc : Schoenflies.IsArcBetween A' (j a₀) (j a₁) := by
    obtain ⟨α, hαc, hαi, hαimage, hα0, hα1⟩ := hcut₁.fst
    have hαA : ∀ t ∈ unitInterval, α t ∈ A := by
      intro t ht
      rw [← hαimage]
      exact ⟨t, ht, rfl⟩
    refine ⟨j ∘ α, hjA.isPiecewiseAffineOn.continuousOn.comp hαc hαA, ?_, ?_, ?_, ?_⟩
    · intro s hs t ht hst
      exact hαi hs ht (hjA.bijOn.injOn (hαA s hs) (hαA t ht) hst)
    · calc
        (j ∘ α) '' unitInterval = j '' (α '' unitInterval) := image_comp j α unitInterval
        _ = j '' A := congrArg (j '' ·) hαimage
        _ = A' := rfl
    · simp only [Function.comp_apply, hα0]
    · simp only [Function.comp_apply, hα1]
  have hjfront : j '' frontier D₂.domain = frontier Q := by
    simpa only [j] using hf₂.symm.image_frontier (by simp)
      D₂.isPLBall_domain.isPolyhedron.isClosed hQ.isPolyhedron.isClosed
  have hA'frontQ : A' ⊆ frontier Q := by
    rw [← hjfront]
    exact image_mono hAfront₂
  have hA'seam : Disjoint A' (P ∩ Q) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, hyA, rfl⟩ hxseam
    have hyD₂ : y ∈ D₂.domain := hAD₂ hyA
    have hf₂j : f₂ (j y) = y := hf₂.bijOn.invOn_invFunOn.2 hyD₂
    have hCmem : f₂ (j y) ∈ C := by
      rw [← hf₂seam]
      exact ⟨j y, hxseam, rfl⟩
    exact Set.disjoint_left.mp hAC hyA (hf₂j ▸ hCmem)
  have hA'T : A' ⊆ T₀ := by
    intro x hxA'
    have hxfront := hA'frontQ hxA'
    rw [← hcutQ.union_eq] at hxfront
    exact hxfront.resolve_left (Set.disjoint_left.mp hA'seam hxA')
  have hA'frontH : A' ⊆ frontier H.domain := by
    rw [hfrontH]
    exact hA'T.trans subset_union_right
  have hA'Q : A' ⊆ Q := by
    rintro x ⟨y, hyA, rfl⟩
    exact hf₂.bijOn.surjOn.mapsTo_invFunOn (hAD₂ hyA)
  have hf₂A'image : f₂ '' A' = A := by
    calc
      f₂ '' A' = f₂ '' (j '' A) := rfl
      _ = (f₂ ∘ j) '' A := (image_comp f₂ j A).symm
      _ = id '' A := Set.image_congr fun y hy =>
        hf₂.bijOn.invOn_invFunOn.2 (hAD₂ hy)
      _ = A := image_id A
  have hf₂A' : IsPLHomeomorphOn f₂ A' A := by
    have h := hf₂.restrict hA'.isPolyhedron hA'Q
    rwa [hf₂A'image] at h
  have hk : IsPLHomeomorphOn (g ∘ f₂) A' C := hf₂A'.trans hg
  have hcompatH₃ : EqOn H (D₃ ∘ (g ∘ f₂)) A' := by
    intro x hx
    calc
      H x = D₂ (f₂ x) := hH₂ (hA'Q hx)
      _ = D₃ (g (f₂ x)) := hcompat₂₃ (hf₂A'.bijOn.mapsTo hx)
      _ = (D₃ ∘ (g ∘ f₂)) x := rfl
  obtain ⟨G, P', Q', h, f₃, hP', hQ', -, hGdomain, -, -, -, hh, hf₃, -,
    hhseam, hf₃seam, hGH, hG₃, a, b, R', T', hcutP', hcutQ', hR', hT',
    hfrontG, hha, hhb, hf₃a, hf₃b⟩ :=
    H.exists_glue_of_isPLHomeomorphOn_boundary_arc D₃ hA' hA'arc hA'frontH hk
      hcut₃.fst_subset hcompatH₃
  have hCU₂ : C ⊆ D₂.domain := by
    rw [← hinter₂₃]
    exact inter_subset_left
  have hCU₃ : C ⊆ D₃.domain := by
    rw [← hinter₂₃]
    exact inter_subset_right
  have hR₀P : R₀ ⊆ P := hcutP.snd_subset.trans hP.isPolyhedron.isClosed.frontier_subset
  have hT₀Q : T₀ ⊆ Q := hcutQ.snd_subset.trans hQ.isPolyhedron.isClosed.frontier_subset
  have hR₀image : f₁ '' R₀ = D₁.domain ∩ frontier D.domain :=
    image_cutArc_eq_of_isPLHomeomorphOn hP D₁.isPLBall_domain hf₁ hcutP hf₁seam
      hf₁pH hf₁qH hcut₁
  have hfrontD₂ : frontier D₂.domain = (D₂.domain ∩ frontier D.domain) ∪ A ∪ C :=
    frontier_middle_eq_union_seams hcover D₁.isPLBall_domain.isPolyhedron.isClosed
      D₂.isPLBall_domain.isPolyhedron.isClosed D₃.isPLBall_domain.isPolyhedron.isClosed
      hinter₁₂ hinter₂₃ hAfront₂ hCfront₂
  obtain ⟨S₂, hcut₂, -, -⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere D₂.isPLSphere_frontier hcut₃.fst
      hCfront₂
  have hmeet : C ∩ ((D₂.domain ∩ frontier D.domain) ∪ A) ⊆ {g a₀, g a₁} := by
    rintro x ⟨hxC, hx⟩
    rcases hx with ⟨-, hxF⟩ | hxA
    · exact hcut₃.inter_eq.subset ⟨hxC, ⟨hCU₃ hxC, hxF⟩⟩
    · exact absurd hxA (Set.disjoint_right.mp hAC hxC)
  have hS₂eq : S₂ = (D₂.domain ∩ frontier D.domain) ∪ A :=
    isCutPair_snd_eq_of_union_eq hcut₂ hfrontD₂ hmeet
      ⟨hCU₂ hcut₃.fst.left_mem, hcut₃.snd.left_mem.2⟩
      ⟨hCU₂ hcut₃.fst.right_mem, hcut₃.snd.right_mem.2⟩
  have hT₀image : f₂ '' T₀ = S₂ :=
    image_cutArc_eq_of_isPLHomeomorphOn hQ D₂.isPLBall_domain hf₂ hcutQ hf₂seam
      hf₂pH hf₂qH hcut₂
  have hf₂jp : f₂ (j a₀) = a₀ := hf₂.bijOn.invOn_invFunOn.2 (hAD₂ hcut₁.fst.left_mem)
  have hf₂jq : f₂ (j a₁) = a₁ := hf₂.bijOn.invOn_invFunOn.2 (hAD₂ hcut₁.fst.right_mem)
  have hf₃aeq : f₃ a = g a₀ := by
    rw [hf₃a]
    exact congrArg g hf₂jp
  have hf₃beq : f₃ b = g a₁ := by
    rw [hf₃b]
    exact congrArg g hf₂jq
  have hT'image : f₃ '' T' = D₃.domain ∩ frontier D.domain :=
    image_cutArc_eq_of_isPLHomeomorphOn hQ' D₃.isPLBall_domain hf₃ hcutQ' hf₃seam
      hf₃aeq hf₃beq hcut₃
  obtain ⟨SH, hcutH, -, hSH⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere H.isPLSphere_frontier hA'arc
      hA'frontH
  have hR'image : h '' R' = SH :=
    image_cutArc_eq_of_isPLHomeomorphOn hP' H.isPLBall_domain hh hcutP' hhseam hha hhb
      hcutH
  have hR₀T₀ : R₀ ∩ T₀ = {pH, qH} := by
    apply Subset.antisymm
    · rintro x ⟨hxR, hxT⟩
      exact hcutP.inter_eq.subset ⟨⟨hR₀P hxR, hT₀Q hxT⟩, hxR⟩
    · rintro x (rfl | rfl)
      · exact ⟨hcutP.snd.left_mem, hcutQ.snd.left_mem⟩
      · exact ⟨hcutP.snd.right_mem, hcutQ.snd.right_mem⟩
  have hR₀SH : R₀ ⊆ SH := by
    have hsub : R₀ \ {pH, qH} ⊆ SH := by
      intro x hx
      have hxfront : x ∈ frontier H.domain := by
        rw [hfrontH]
        exact Or.inl hx.1
      rcases hcutH.union_eq.symm.subset hxfront with hxA' | hxSH
      · exact absurd (hR₀T₀.subset ⟨hx.1, hA'T hxA'⟩) hx.2
      · exact hxSH
    calc
      R₀ ⊆ closure (R₀ \ {pH, qH}) := hR₀.subset_closure_sdiff_finite (Set.toFinite _)
      _ ⊆ closure SH := closure_mono hsub
      _ = SH := hSH.isPolyhedron.isClosed.closure_eq
  have hA'char : ∀ x ∈ Q, f₂ x ∈ A → x ∈ A' := by
    intro x hxQ hxA
    have hxD₂ : f₂ x ∈ D₂.domain := hf₂.bijOn.mapsTo hxQ
    have hjx : j (f₂ x) ∈ Q := hf₂.bijOn.surjOn.mapsTo_invFunOn hxD₂
    have hfix : j (f₂ x) = x :=
      hf₂.bijOn.injOn hjx hxQ (hf₂.bijOn.invOn_invFunOn.2 hxD₂)
    have hmem : j (f₂ x) ∈ A' := mem_image_of_mem j hxA
    rwa [hfix] at hmem
  have hAF : A ∩ frontier D.domain ⊆ {a₀, a₁} := by
    rintro x ⟨hxA, hxF⟩
    refine hcut₁.inter_eq.subset ⟨hxA, ⟨?_, hxF⟩⟩
    rw [← hinter₁₂] at hxA
    exact hxA.1
  have hpF : a₀ ∈ D₂.domain ∩ frontier D.domain :=
    ⟨hAD₂ hcut₁.fst.left_mem, hcut₁.snd.left_mem.2⟩
  have hqF : a₁ ∈ D₂.domain ∩ frontier D.domain :=
    ⟨hAD₂ hcut₁.fst.right_mem, hcut₁.snd.right_mem.2⟩
  have hSHT₀image : f₂ '' (SH ∩ T₀) = D₂.domain ∩ frontier D.domain := by
    apply Subset.antisymm
    · rintro y ⟨x, ⟨hxSH, hxT₀⟩, rfl⟩
      have hmem : f₂ x ∈ S₂ := by
        rw [← hT₀image]
        exact mem_image_of_mem f₂ hxT₀
      rw [hS₂eq] at hmem
      rcases hmem with hgood | hxA
      · exact hgood
      · have hxpair : x ∈ ({j a₀, j a₁} : Set (EuclideanSpace ℝ (Fin 2))) :=
          hcutH.inter_eq.subset ⟨hA'char x (hT₀Q hxT₀) hxA, hxSH⟩
        rcases hxpair with rfl | rfl
        · rw [hf₂jp]
          exact hpF
        · rw [hf₂jq]
          exact hqF
    · intro y hy
      have hyT₀ : y ∈ f₂ '' T₀ := by
        rw [hT₀image, hS₂eq]
        exact Or.inl hy
      obtain ⟨x, hxT₀, hxy⟩ := hyT₀
      by_cases hxA' : x ∈ A'
      · have hyA : y ∈ A := by
          rw [← hf₂A'image]
          exact ⟨x, hxA', hxy⟩
        rcases hAF ⟨hyA, hy.2⟩ with rfl | rfl
        · exact ⟨j y, ⟨hcutH.snd.left_mem, hA'T (mem_image_of_mem j hyA)⟩, hf₂jp⟩
        · exact ⟨j y, ⟨hcutH.snd.right_mem, hA'T (mem_image_of_mem j hyA)⟩, hf₂jq⟩
      · refine ⟨x, ⟨?_, hxT₀⟩, hxy⟩
        have hxfront : x ∈ frontier H.domain := by
          rw [hfrontH]
          exact Or.inr hxT₀
        exact (hcutH.union_eq.symm.subset hxfront).resolve_left hxA'
  have hHR₀ : H '' R₀ = D '' (D₁.domain ∩ frontier D.domain) := by
    calc
      H '' R₀ = (D₁ ∘ f₁) '' R₀ := Set.image_congr (hH₁.mono hR₀P)
      _ = D₁ '' (f₁ '' R₀) := image_comp D₁ f₁ R₀
      _ = D₁ '' (D₁.domain ∩ frontier D.domain) := congrArg (D₁ '' ·) hR₀image
      _ = D '' (D₁.domain ∩ frontier D.domain) := by rw [hfun₁]
  have hHmid : H '' (SH ∩ T₀) = D '' (D₂.domain ∩ frontier D.domain) := by
    calc
      H '' (SH ∩ T₀) = (D₂ ∘ f₂) '' (SH ∩ T₀) :=
        Set.image_congr (hH₂.mono fun x hx => hT₀Q hx.2)
      _ = D₂ '' (f₂ '' (SH ∩ T₀)) := image_comp D₂ f₂ _
      _ = D₂ '' (D₂.domain ∩ frontier D.domain) := congrArg (D₂ '' ·) hSHT₀image
      _ = D '' (D₂.domain ∩ frontier D.domain) := by rw [hfun₂]
  have hSHsplit : SH = R₀ ∪ SH ∩ T₀ := by
    apply Subset.antisymm
    · intro x hx
      have hxfront : x ∈ frontier H.domain := hcutH.snd_subset hx
      rw [hfrontH] at hxfront
      rcases hxfront with hxR | hxT
      · exact Or.inl hxR
      · exact Or.inr ⟨hx, hxT⟩
    · exact union_subset hR₀SH fun x hx => hx.1
  have hHSH : H '' SH = D '' ((D₁.domain ∪ D₂.domain) ∩ frontier D.domain) := by
    rw [union_inter_distrib_right, image_union, hSHsplit, image_union]
    exact congrArg₂ (· ∪ ·) hHR₀ hHmid
  have hR'P' : R' ⊆ P' := hcutP'.snd_subset.trans hP'.isPolyhedron.isClosed.frontier_subset
  have hT'Q' : T' ⊆ Q' := hcutQ'.snd_subset.trans hQ'.isPolyhedron.isClosed.frontier_subset
  have hH₁' : EqOn H (D.toFun ∘ f₁) P := by
    intro z hz
    simpa only [Function.comp_apply, hfun₁] using hH₁ hz
  have hH₂' : EqOn H (D.toFun ∘ f₂) Q := by
    intro z hz
    simpa only [Function.comp_apply, hfun₂] using hH₂ hz
  have hG₃' : EqOn G (D.toFun ∘ f₃) Q' := by
    intro z hz
    simpa only [Function.comp_apply, hfun₃] using hG₃ hz
  obtain ⟨ρ, t₁, t₂, hρc, hρi, hρimage, hρends, ht₁, ht₂, htlt,
    hρleft, hρmid, hρright, hT⟩ :=
    exists_cross_source_segment_equations (D := D) (H := H) (G := G)
      (P := P) (Q := Q) (P' := P') (Q' := Q') (R := R') (T := T')
      (R₀ := R₀) (T₀ := T₀) (SH := SH) (pH := pH) (qH := qH)
      (s₀ := j a₀) (s₁ := j a₁) (a := a) (b := b)
      (f₁ := f₁) (f₂ := f₂) (h := h) (f₃ := f₃)
      hcutH.snd hcutP.snd hR₀SH hSHsplit hcutQ.snd.left_mem hcutQ.snd.right_mem
      hcutH.snd_subset hR'image hR'P' hcutP'.snd.left_mem hcutP'.snd.right_mem
      hha hhb hh hR₀P hT₀Q hH₁' hH₂' hGH hT'Q' hG₃'
  exact ⟨H, G, P, Q, P', Q', R', T', f₁, f₂, h, f₃, a, b, ρ, t₁, t₂,
    hP, hQ, hHdomain, hf₁, hf₂, hH₁', hH₂', hP', hQ', hGdomain, hh, hf₃,
    hGH, hG₃', hcutP', hcutQ', hR', hT', hfrontG, hha, hhb, hf₃aeq, hf₃beq,
    hρc, hρi, hρimage, hρends, ht₁, ht₂, htlt, hρleft, hρmid, hρright, hT⟩

open Classical in
theorem exists_cross_glue_source_segments_with_source_data
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D₁ D₂ D₃ : SingularTwoCell M) {D : SingularTwoCell M}
    {A C : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) (hAC : Disjoint A C)
    {a₀ a₁ : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hcover : D₁.domain ∪ D₂.domain ∪ D₃.domain = D.domain)
    (hinter₁₂ : D₁.domain ∩ D₂.domain = A)
    (hinter₂₃ : D₂.domain ∩ D₃.domain = C)
    (hAfront₂ : A ⊆ frontier D₂.domain)
    (hCfront₂ : C ⊆ frontier D₂.domain)
    (hcut₁ : Schoenflies.IsCutPair (frontier D₁.domain) a₀ a₁ A
      (D₁.domain ∩ frontier D.domain))
    (hcut₃ : Schoenflies.IsCutPair (frontier D₃.domain) (g a₀) (g a₁) C
      (D₃.domain ∩ frontier D.domain))
    (hg : IsPLHomeomorphOn g A C)
    (hcompat₁₂ : EqOn D₁ (D₂ ∘ g) A)
    (hcompat₂₃ : EqOn D₂ (D₃ ∘ g) A)
    (hfun₁ : D₁.toFun = D.toFun)
    (hfun₂ : D₂.toFun = D.toFun)
    (hfun₃ : D₃.toFun = D.toFun) :
    ∃ (H G : SingularTwoCell M)
      (P Q P' Q' R T : Set (EuclideanSpace ℝ (Fin 2)))
      (f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (a b : EuclideanSpace ℝ (Fin 2))
      (ρ : ℝ → EuclideanSpace ℝ (Fin 2)) (t₁ t₂ : ℝ),
      IsPLBall 2 P ∧ IsPLBall 2 Q ∧ H.domain = P ∪ Q ∧
      IsPLHomeomorphOn f₁ P D₁.domain ∧ IsPLHomeomorphOn f₂ Q D₂.domain ∧
      EqOn H (D.toFun ∘ f₁) P ∧ EqOn H (D.toFun ∘ f₂) Q ∧
      IsPLBall 2 P' ∧ IsPLBall 2 Q' ∧ G.domain = P' ∪ Q' ∧
      IsPLHomeomorphOn h P' H.domain ∧ IsPLHomeomorphOn f₃ Q' D₃.domain ∧
      EqOn G (H.toFun ∘ h) P' ∧ EqOn G (D.toFun ∘ f₃) Q' ∧
      Schoenflies.IsCutPair (frontier P') a b (P' ∩ Q') R ∧
      Schoenflies.IsCutPair (frontier Q') a b (P' ∩ Q') T ∧
      IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier G.domain = R ∪ T ∧
      h a = Function.invFunOn f₂ Q a₀ ∧ h b = Function.invFunOn f₂ Q a₁ ∧
      f₃ a = g a₀ ∧ f₃ b = g a₁ ∧
      ContinuousOn ρ (Set.Icc 0 1) ∧ Set.InjOn ρ (Set.Icc 0 1) ∧
      ρ '' Set.Icc 0 1 = R ∧
      ((ρ 0 = a ∧ ρ 1 = b) ∨ (ρ 0 = b ∧ ρ 1 = a)) ∧
      t₁ ∈ Set.Icc 0 1 ∧ t₂ ∈ Set.Icc 0 1 ∧ t₁ < t₂ ∧
      (∀ t ∈ Set.Icc 0 t₁, G (ρ t) = D (f₂ (h (ρ t)))) ∧
      (∀ t ∈ Set.Icc t₁ t₂, G (ρ t) = D (f₁ (h (ρ t)))) ∧
      (∀ t ∈ Set.Icc t₂ 1, G (ρ t) = D (f₂ (h (ρ t)))) ∧
      (∀ z ∈ T, G z = D (f₃ z)) ∧
      (∀ t ∈ Set.Icc 0 t₁, f₂ (h (ρ t)) ∈ D₂.domain ∩ frontier D.domain) ∧
      (∀ t ∈ Set.Icc t₁ t₂, f₁ (h (ρ t)) ∈ D₁.domain ∩ frontier D.domain) ∧
      (∀ t ∈ Set.Icc t₂ 1, f₂ (h (ρ t)) ∈ D₂.domain ∩ frontier D.domain) ∧
      f₂ (h (ρ t₁)) = g (f₁ (h (ρ t₁))) ∧
      f₂ (h (ρ t₂)) = g (f₁ (h (ρ t₂))) ∧
      ∃ (x y : M) (σ : Path x y) (ω : Path y x)
          (e : loopCircle ≃ₜ frontier G.domain),
        Set.range σ = G '' R ∧ Set.range ω = G '' T ∧
          (∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ) ∧
          ∃ (a' b' : frontier G.domain) (ρG : Path a' b') (κG : Path b' a'),
            Function.Injective ρG ∧ Function.Injective κG ∧
            Set.range (fun t => ((ρG t : frontier G.domain) :
              EuclideanSpace ℝ (Fin 2))) = R ∧
            Set.range (fun t => ((κG t : frontier G.domain) :
              EuclideanSpace ℝ (Fin 2))) = T ∧
            ∀ θ, e θ = pathToCircle (ρG.trans κG) θ := by
  obtain ⟨H, G, P, Q, P', Q', f₁, f₂, h, f₃, A', hP, hQ, hHdomain,
    hf₁, hf₂, -, -, hH₁, hH₂, -, -, -, -, -, hP', hQ', hGdomain, hh, hf₃,
    -, -, hGH, hG₃, a, b, R, T, hcutP', hcutQ', hR, hT', hfrontG,
    hha, hhb, hf₃a, hf₃b, x, y, σ, ω, e, hσrange, hωrange, hparam, -, -,
    a', b', ρG, κG, hρGinj, hκGinj, hρGrange, hκGrange, he,
    R₀, T₀, SH, pH, qH, hcutP, hcutQ, hcutH, hR₀SH, hSHsplit, hRimage,
    hR₀image, hSHT₀image, -, -, -, -, -, hseam, -, -⟩ :=
    D₁.exists_cross_glue_of_isPLHomeomorphOn_disjoint_boundary_arcs_with_source_arcs
      D₂ D₃ hA hAC hcover hinter₁₂ hinter₂₃ hAfront₂ hCfront₂ hcut₁ hcut₃ hg
      hcompat₁₂ hcompat₂₃ hfun₁ hfun₂ hfun₃
  have hH₁' : EqOn H (D.toFun ∘ f₁) P := by
    intro z hz
    simpa only [Function.comp_apply, hfun₁] using hH₁ hz
  have hH₂' : EqOn H (D.toFun ∘ f₂) Q := by
    intro z hz
    simpa only [Function.comp_apply, hfun₂] using hH₂ hz
  have hG₃' : EqOn G (D.toFun ∘ f₃) Q' := by
    intro z hz
    simpa only [Function.comp_apply, hfun₃] using hG₃ hz
  obtain ⟨ρ, t₁, t₂, hρc, hρi, hρimage, hρends, ht₁, ht₂, htlt,
    hρleft, hρmid, hρright, hT, hsourceLeft, hsourceMid, hsourceRight,
    hseam₁, hseam₂⟩ :=
    exists_cross_source_segment_equations_with_source_data (D := D) (H := H) (G := G)
      (P := P) (Q := Q) (P' := P') (Q' := Q') (R := R) (T := T)
      (R₀ := R₀) (T₀ := T₀) (SH := SH) (pH := pH) (qH := qH)
      (a := a) (b := b) (f₁ := f₁) (f₂ := f₂) (h := h) (f₃ := f₃) (g := g)
      hcutH.snd hcutP.snd hR₀SH hSHsplit hcutQ.snd.left_mem hcutQ.snd.right_mem
      hcutH.snd_subset hRimage
      (hcutP'.snd_subset.trans hP'.isPolyhedron.isClosed.frontier_subset)
      hcutP'.snd.left_mem hcutP'.snd.right_mem hha hhb hh
      (hcutP.snd_subset.trans hP.isPolyhedron.isClosed.frontier_subset)
      (hcutQ.snd_subset.trans hQ.isPolyhedron.isClosed.frontier_subset)
      hH₁' hH₂' hGH hseam hR₀image hSHT₀image
      (hcutQ'.snd_subset.trans hQ'.isPolyhedron.isClosed.frontier_subset) hG₃'
  exact ⟨H, G, P, Q, P', Q', R, T, f₁, f₂, h, f₃, a, b, ρ, t₁, t₂,
    hP, hQ, hHdomain, hf₁, hf₂, hH₁', hH₂', hP', hQ', hGdomain, hh, hf₃,
    hGH, hG₃', hcutP', hcutQ', hR, hT', hfrontG, hha, hhb, hf₃a, hf₃b,
    hρc, hρi, hρimage, hρends, ht₁, ht₂, htlt, hρleft, hρmid, hρright, hT,
    hsourceLeft, hsourceMid, hsourceRight, hseam₁, hseam₂,
    x, y, σ, ω, e, hσrange, hωrange, hparam,
    a', b', ρG, κG, hρGinj, hκGinj, hρGrange, hκGrange, he⟩

end DifferentialGeometry.Topology.PiecewiseLinear
