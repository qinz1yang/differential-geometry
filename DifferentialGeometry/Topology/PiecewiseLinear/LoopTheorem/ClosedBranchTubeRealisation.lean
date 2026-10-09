/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeSquareLoop
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneSource
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchCaseOneTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_loopCircle_homeomorph_of_loop {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {S : Set X} (hS : IsCompact S) {m : X → Y}
    (hm : ContinuousOn m S) (hminj : InjOn m S) {γ : ℝ → Y} (hγ : ContinuousOn γ (Icc 0 1))
    (hγimg : γ '' Icc 0 1 = m '' S) (hγinj : InjOn γ (Ico 0 1)) (hγ01 : γ 0 = γ 1) :
    ∃ e : loopCircle ≃ₜ S, ∀ t ∈ Icc (0 : ℝ) 1, m (e (t : loopCircle)) = γ t := by
  have hγ01' : γ 0 = γ (0 + 1) := by rw [zero_add]; exact hγ01
  have hf₀c : Continuous (AddCircle.liftIco (1 : ℝ) 0 γ) :=
    AddCircle.liftIco_continuous hγ01' (by rw [zero_add]; exact hγ)
  have hf₀app : ∀ t ∈ Ico (0 : ℝ) 1, AddCircle.liftIco (1 : ℝ) 0 γ (t : loopCircle) = γ t :=
    fun t ht => AddCircle.liftIco_coe_apply (by rwa [zero_add])
  have hmemIco : ∀ z : loopCircle, (AddCircle.equivIco (1 : ℝ) 0 z : ℝ) ∈ Ico (0 : ℝ) 1 :=
    fun z => by simpa only [zero_add] using (AddCircle.equivIco (1 : ℝ) 0 z).2
  have hf₀val : ∀ z : loopCircle, AddCircle.liftIco (1 : ℝ) 0 γ z =
      γ (AddCircle.equivIco (1 : ℝ) 0 z : ℝ) := fun _ => rfl
  have hf₀mem : ∀ z : loopCircle, AddCircle.liftIco (1 : ℝ) 0 γ z ∈ m '' S := by
    intro z
    rw [← hγimg, hf₀val]
    exact mem_image_of_mem γ (Ico_subset_Icc_self (hmemIco z))
  have hf₀app1 : AddCircle.liftIco (1 : ℝ) 0 γ ((1 : ℝ) : loopCircle) = γ 1 := by
    rw [← hγ01, ← hf₀app 0 ⟨le_rfl, zero_lt_one⟩]
    congr 1
    rw [AddCircle.coe_period, QuotientAddGroup.mk_zero]
  let F : loopCircle → m '' S := fun z => ⟨AddCircle.liftIco (1 : ℝ) 0 γ z, hf₀mem z⟩
  have hFbij : Function.Bijective F := by
    refine ⟨fun z w h => (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext
      (hγinj (hmemIco z) (hmemIco w) (congrArg Subtype.val h))), fun y => ?_⟩
    · obtain ⟨t, ht, hty⟩ : (y : Y) ∈ γ '' Icc 0 1 := by
        rw [hγimg]
        exact y.2
      rcases eq_or_lt_of_le ht.2 with h1 | h1
      · refine ⟨((1 : ℝ) : loopCircle), Subtype.ext ?_⟩
        change AddCircle.liftIco (1 : ℝ) 0 γ ((1 : ℝ) : loopCircle) = y
        rw [hf₀app1, ← h1, hty]
      · exact ⟨(t : loopCircle), Subtype.ext ((hf₀app t ⟨ht.1, h1⟩).trans hty)⟩
  have hFc : Continuous (Equiv.ofBijective F hFbij) := hf₀c.subtype_mk _
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let H : S → m '' S := fun x => ⟨m x, mem_image_of_mem m x.2⟩
  have hHbij : Function.Bijective H := by
    refine ⟨fun x y h => Subtype.ext (hminj x.2 y.2 (congrArg Subtype.val h)), fun y => ?_⟩
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hHc : Continuous (Equiv.ofBijective H hHbij) := hm.domRestrict.subtype_mk _
  let eF := hFc.homeoOfEquivCompactToT2
  let eH := hHc.homeoOfEquivCompactToT2
  refine ⟨eF.trans eH.symm, fun t ht => ?_⟩
  have hkey : ∀ z : loopCircle, m ((eF.trans eH.symm) z) = AddCircle.liftIco (1 : ℝ) 0 γ z := by
    intro z
    have h := congrArg Subtype.val (eH.apply_symm_apply (eF z))
    exact h
  rw [hkey]
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · rw [h1, hf₀app1]
  · exact hf₀app t ⟨ht.1, h1⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isSourceTrackedBranchTube_of_cylinder {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [T2Space M] {D : SingularTwoCell M}
    {BdM B : Set M} (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {ι : M → E} (hιc : Continuous ι) (hι : Function.Injective ι)
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsCombinatorialManifold 3 L)
    {J : Set (EuclideanSpace ℝ (Fin 2))} (hJ : IsPLSphere 1 J)
    {τ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hτ : hD.IsBranchDeckInvolution c J τ)
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    {R Lc : Geometry.SimplicialComplex ℝ E} (hRfin : R.faces.Finite) (hRL : IsSubdivision R L)
    {Pc : Geometry.SimplicialComplex ℝ (ℝ × ℝ)} [Finite Pc.faces] (hPc : Pc.space = spliceSquare)
    {φ : (ℝ × ℝ) × ℝ → E} {u : ℝ × ℝ → ℝ × ℝ} {σ : Fin 4 → Fin 4}
    {α : Fin 4 → EuclideanSpace ℝ (Fin 2)} {v : Fin 4 → ℝ}
    (hcyl : IsCylindricalDiagram φ spliceSquare (derivedNeighborhood R Lc).space)
    (hu : IsPLHomeomorphOn u spliceSquare spliceSquare)
    (hseam : ∀ x ∈ spliceSquare, φ (x, 0) = φ (u x, 1)) (hu0 : u 0 = 0)
    (huσ : ∀ i, u (fourSpokeModelLeaf i) = fourSpokeModelLeaf (σ i))
    (hcore : φ '' (({0} : Set (ℝ × ℝ)) ×ˢ Icc (0 : ℝ) 1) =
      ι '' hD.singularSet.branchCarrier c)
    (hαJ : ∀ i, α i ∈ J) (hv : ∀ i, v i ∈ Icc (-1 : ℝ) 1)
    (hray : ∀ i, φ (fourSpokeModelLeaf i, 0) = ι (D (ρ (α i, v i))))
    (hbase : φ (0, 0) = ι (D (α 0))) (hα2 : α 2 = α 0) (hα1 : α 1 = τ (α 0))
    (hα3 : α 3 = α 1) (hv0 : 0 < v 0) (hv1 : 0 < v 1) (hv2 : v 2 < 0) (hv3 : v 3 < 0)
    (hmono : ∀ j, α j = τ (α (σ j)) ∧ (0 < v j ↔ 0 < v (σ j))) :
    IsSourceTrackedBranchTube hD c ι L J ρ (derivedNeighborhood R Lc) Pc φ u
      fourSpokeModelLeaf := by
  obtain ⟨hpre, -, -, hτmaps, -, hτfix, -, hDτ, hDiff⟩ := hτ
  have : Finite R.faces := hRfin.to_subtype
  have hrmem : ∀ i, fourSpokeModelLeaf i ∈ spliceSquare :=
    fun i => (fourSpokeModelLeaf_mem_spliceSquareBoundary i).1
  have hσinj : Function.Injective σ := by
    intro i j hij
    apply fourSpokeModelLeaf_injective
    apply hu.bijOn.injOn (hrmem i) (hrmem j)
    rw [huσ, huσ, hij]
  let σe : Fin 4 ≃ Fin 4 := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hσinj)
  have hσe : ∀ i, σ (σe.symm i) = i := fun i => σe.apply_symm_apply i
  have hvne : ∀ i, v i ≠ 0 := by
    intro i
    rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl
    · exact hv0.ne'
    · exact hv1.ne'
    · exact hv2.ne
    · exact hv3.ne
  have hαD : ∀ i, D (α i) = D (α 0) := by
    intro i
    rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl
    · rfl
    · rw [hα1, hDτ _ (hαJ 0)]
    · rw [hα2]
    · rw [hα3, hα1, hDτ _ (hαJ 0)]
  have hcont : ContinuousOn φ (spliceSquare ×ˢ Icc (0 : ℝ) 1) :=
    hcyl.isPiecewiseAffineOn.continuousOn
  have : Finite (hD.singularSet.branchComplex c).faces :=
    (hD.singularSet.branchComplex_faces_finite c).to_subtype
  have hScompact : IsCompact (hD.singularSet.branchComplex c).space :=
    (PiecewiseLinear.isPolyhedron_space (hD.singularSet.branchComplex c)).isCompact
  have hmcont : ContinuousOn (ι ∘ (hD.singularSet.branchPieceIn c).map)
      (hD.singularSet.branchComplex c).space :=
    hιc.comp_continuousOn (hD.singularSet.branchPieceIn c).continuousOn
  have hminj : InjOn (ι ∘ (hD.singularSet.branchPieceIn c).map)
      (hD.singularSet.branchComplex c).space :=
    hι.comp_injOn (hD.singularSet.branchPieceIn c).bijOn.injOn
  have hcarrier : (hD.singularSet.branchPieceIn c).map ''
      (hD.singularSet.branchComplex c).space = hD.singularSet.branchCarrier c :=
    (hD.singularSet.branchPieceIn c).bijOn.image_eq
  have hγc : ContinuousOn (fun t : ℝ => φ (0, t)) (Icc 0 1) :=
    hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      fun t ht => ⟨zero_mem_spliceSquare, ht⟩
  have hγimg : (fun t : ℝ => φ (0, t)) '' Icc 0 1 =
      (ι ∘ (hD.singularSet.branchPieceIn c).map) '' (hD.singularSet.branchComplex c).space := by
    rw [image_comp, hcarrier, ← hcore, singleton_prod, image_image]
  have hγinj : InjOn (fun t : ℝ => φ (0, t)) (Ico 0 1) := by
    intro s hs t ht hst
    rcases hcyl.eq_or_endpoints (0, s) ⟨zero_mem_spliceSquare, Ico_subset_Icc_self hs⟩ (0, t)
      ⟨zero_mem_spliceSquare, Ico_subset_Icc_self ht⟩ hst with h | h | h
    · exact congrArg Prod.snd h
    · exact absurd h.2 ht.2.ne
    · exact absurd h.1 hs.2.ne
  have hγ01 : φ (0, 0) = φ (0, 1) := by
    rw [hseam 0 zero_mem_spliceSquare, hu0]
  obtain ⟨e, he⟩ := exists_loopCircle_homeomorph_of_loop hScompact hmcont hminj hγc hγimg
    hγinj hγ01
  have hpD : ∀ x : hD.branchPreimage c,
      (hD.singularSet.branchPieceIn c).map (hD.branchProjection c x) = D x := by
    intro x
    have hx : D x ∈ (hD.singularSet.branchPieceIn c).map ''
        (hD.singularSet.branchPieceIn c).complex.space := by
      rw [(hD.singularSet.branchPieceIn c).bijOn.image_eq]
      exact x.2.2
    exact Function.invFunOn_eq hx
  let β : C(unitInterval, (hD.singularSet.branchComplex c).space) :=
    ⟨fun t => e ((t : ℝ) : loopCircle),
      e.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val)⟩
  have hβmap : ∀ t : unitInterval, ι ((hD.singularSet.branchPieceIn c).map (β t)) =
      φ (0, (t : ℝ)) := fun t => he t t.2
  have hmemJ : ∀ i, α i ∈ hD.branchPreimage c := fun i => hpre ▸ hαJ i
  have hβ0 : ∀ i, β 0 = hD.branchProjection c ⟨α i, hmemJ i⟩ := by
    intro i
    apply Subtype.ext
    apply (hD.singularSet.branchPieceIn c).bijOn.injOn (β 0).2
      (hD.branchProjection c ⟨α i, hmemJ i⟩).2
    apply hι
    rw [hβmap 0, hpD, hαD i, ← hbase]
    rfl
  have hlift : ∀ i, ∃ Γ : C(unitInterval, hD.branchPreimage c),
      hD.branchProjection c ∘ Γ = β ∧ Γ 0 = ⟨α i, hmemJ i⟩ := fun i =>
    (hD.branchProjection_isCoveringMap c).exists_path_lifts β ⟨α i, hmemJ i⟩ (hβ0 i)
  choose Γ hΓ hΓ0 using hlift
  have hΓD : ∀ i t, D (Γ i t : EuclideanSpace ℝ (Fin 2)) =
      (hD.singularSet.branchPieceIn c).map (β t) := by
    intro i t
    rw [← hpD, ← congrFun (hΓ i) t]
    rfl
  have hβ1 : β 1 = β 0 := by
    change e (((1 : unitInterval) : ℝ) : loopCircle) = e (((0 : unitInterval) : ℝ) : loopCircle)
    congr 1
    rw [Set.Icc.coe_one, Set.Icc.coe_zero, AddCircle.coe_period, QuotientAddGroup.mk_zero]
  have hend : ∀ i, (Γ i 1 : EuclideanSpace ℝ (Fin 2)) = τ (α i) := by
    intro i
    have hp1 : hD.branchProjection c (Γ i 1) = hD.branchProjection c (Γ i 0) := by
      have h1 := congrFun (hΓ i) 1
      have h0 := congrFun (hΓ i) 0
      simp only [Function.comp_apply] at h1 h0
      rw [h1, h0, hβ1]
    have hD1 : D (α i) = D (Γ i 1 : EuclideanSpace ℝ (Fin 2)) := by
      rw [← hpD, hp1, hΓ0 i]
      exact (hpD ⟨α i, hmemJ i⟩).symm
    rcases (hDiff (α i) (hαJ i) _ (hpre ▸ (Γ i 1).2)).mp hD1 with h | h
    · exfalso
      have hclosed : Γ i 1 = Γ i 0 := Subtype.ext (h.trans (congrArg Subtype.val (hΓ0 i)).symm)
      let Lf : ℝ → hD.branchPreimage c := fun t => Γ i (Set.projIcc 0 1 zero_le_one t)
      have hL01 : Lf 0 = Lf (0 + 1) := by
        simp only [Lf, zero_add, Set.projIcc_left, Set.projIcc_right]
        exact hclosed.symm
      have hLc : Continuous Lf := (Γ i).continuous.comp continuous_projIcc
      have hσ₀c : Continuous (AddCircle.liftIco (1 : ℝ) 0 Lf) :=
        AddCircle.liftIco_continuous hL01 hLc.continuousOn
      refine hD.not_exists_rightInverse_branchProjection_of_isPLSphere_one c hJ hpre
        ⟨⟨AddCircle.liftIco (1 : ℝ) 0 Lf ∘ e.symm, hσ₀c.comp e.symm.continuous⟩, fun y => ?_⟩
      have hmem : (AddCircle.equivIco (1 : ℝ) 0 (e.symm y) : ℝ) ∈ Ico (0 : ℝ) 1 := by
        simpa only [zero_add] using (AddCircle.equivIco (1 : ℝ) 0 (e.symm y)).2
      set t : ℝ := (AddCircle.equivIco (1 : ℝ) 0 (e.symm y) : ℝ) with ht
      have hty : ((t : ℝ) : loopCircle) = e.symm y := by
        rw [ht]
        exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (e.symm y)
      change hD.branchProjection c (AddCircle.liftIco (1 : ℝ) 0 Lf (e.symm y)) = y
      rw [← hty, AddCircle.liftIco_coe_apply (by rwa [zero_add])]
      have hproj := congrFun (hΓ i) (Set.projIcc 0 1 zero_le_one t)
      simp only [Function.comp_apply] at hproj
      change hD.branchProjection c (Γ i (Set.projIcc 0 1 zero_le_one t)) = y
      rw [hproj]
      change e (((Set.projIcc 0 1 zero_le_one t : unitInterval) : ℝ) : loopCircle) = y
      rw [Set.projIcc_of_mem zero_le_one (Ico_subset_Icc_self hmem), hty, e.apply_symm_apply]
    · exact h
  let a : Fin 4 → C(unitInterval, EuclideanSpace ℝ (Fin 2)) := fun i =>
    ⟨fun t => (Γ i t : EuclideanSpace ℝ (Fin 2)), continuous_subtype_val.comp (Γ i).continuous⟩
  let s : Fin 4 → C(unitInterval, ℝ) := fun i =>
    ⟨fun t => (1 - (t : ℝ)) * v i + (t : ℝ) * v (σe.symm i),
      ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
        (continuous_subtype_val.mul continuous_const)⟩
  have ha0 : ∀ i, a i 0 = α i := fun i => congrArg Subtype.val (hΓ0 i)
  have ha1 : ∀ i, a i 1 = τ (α i) := hend
  have hs0 : ∀ i, s i 0 = v i := fun i => by
    change (1 - ((0 : unitInterval) : ℝ)) * v i + ((0 : unitInterval) : ℝ) * v (σe.symm i) = v i
    rw [Set.Icc.coe_zero]
    ring
  have hs1 : ∀ i, s i 1 = v (σe.symm i) := fun i => by
    change (1 - ((1 : unitInterval) : ℝ)) * v i + ((1 : unitInterval) : ℝ) * v (σe.symm i) =
      v (σe.symm i)
    rw [Set.Icc.coe_one]
    ring
  have hsign : ∀ i, (0 < v i ↔ 0 < v (σe.symm i)) := fun i => by
    have h := (hmono (σe.symm i)).2
    rw [hσe] at h
    exact h.symm
  obtain ⟨g, w, hg, hgb, hw01, hw12, hw23, hw30, hgr⟩ := exists_spliceSquare_cyclic
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨R, Lc, hRfin, hRL, rfl⟩, ⟨g, w, hg, ?_, hw01, hw12, hw23, hw30,
    hgr⟩, ⟨e, a, s, fun i t => hpre ▸ (Γ i t).2, fun i t => ?_, fun i t => ?_, fun i t => ?_,
      fun i t ht => ?_, fun i j hij hs => ?_, ?_, ?_, ?_⟩⟩
  · rw [hPc]
    exact isPLBall_spliceSquare
  · exact (hL.of_isSubdivision hRL).isCombinatorialManifoldWithBoundary.derivedNeighborhood Lc
  · rw [hPc]
    exact hcyl
  · rw [hPc]
    exact hu
  · rw [hPc]
    exact hseam
  · rintro _ ⟨i, rfl⟩
    exact ⟨σ i, (huσ i).symm⟩
  · convert hgb using 2
    convert boundaryComplex_space_of_space_eq_spliceSquare Pc hPc using 3
  · have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    obtain ⟨hvi0, hvi1⟩ := hv i
    obtain ⟨hvj0, hvj1⟩ := hv (σe.symm i)
    have h1 := mul_nonneg (sub_nonneg.mpr ht1) (by linarith : (0 : ℝ) ≤ v i + 1)
    have h2 := mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ v (σe.symm i) + 1)
    have h3 := mul_nonneg (sub_nonneg.mpr ht1) (by linarith : (0 : ℝ) ≤ 1 - v i)
    have h4 := mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - v (σe.symm i))
    change (1 - (t : ℝ)) * v i + (t : ℝ) * v (σe.symm i) ∈ Icc (-1 : ℝ) 1
    constructor <;> nlinarith
  · have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    change (1 - (t : ℝ)) * v i + (t : ℝ) * v (σe.symm i) ≠ 0
    rcases lt_or_gt_of_ne (hvne i) with hneg | hpos
    · have hneg' : v (σe.symm i) < 0 := by
        rcases lt_or_gt_of_ne (hvne (σe.symm i)) with h | h
        · exact h
        · exact absurd ((hsign i).mpr h) (not_lt.mpr hneg.le)
      apply ne_of_lt
      rcases le_total (v i) (v (σe.symm i)) with hab | hab
      · have h5 : (t : ℝ) * (v (σe.symm i) - v i) ≤ v (σe.symm i) - v i := by nlinarith
        nlinarith
      · have h5 : (t : ℝ) * (v (σe.symm i) - v i) ≤ 0 := by nlinarith
        nlinarith
    · have hpos' : 0 < v (σe.symm i) := (hsign i).mp hpos
      apply ne_of_gt
      rcases le_total (v i) (v (σe.symm i)) with hab | hab
      · have h5 : 0 ≤ (t : ℝ) * (v (σe.symm i) - v i) := by nlinarith
        nlinarith
      · have h5 : v (σe.symm i) - v i ≤ (t : ℝ) * (v (σe.symm i) - v i) := by nlinarith
        nlinarith
  · change D (Γ i t : EuclideanSpace ℝ (Fin 2)) = _
    rw [hΓD]
    rfl
  · rcases ht with rfl | rfl
    · rw [ha0, hs0, Set.Icc.coe_zero]
      exact hray i
    · rw [ha1, hs1, Set.Icc.coe_one]
      have hj := hσe i
      set j := σe.symm i with hjdef
      have hseamj := hseam _ (hrmem j)
      rw [huσ, hj, hray j] at hseamj
      rw [← hseamj, (hmono j).1, hj]
  · rw [ha0, ha0] at hij
    rw [hs0, hs0] at hs
    have hA : α 0 ≠ α 1 := by
      rw [hα1]
      exact (hτfix _ (hαJ 0)).symm
    rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
      rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | exact absurd hij (by rw [hα2, hα3]; exact hA)
      | exact absurd hij (by rw [hα2]; exact hA)
      | exact absurd hij (by rw [hα3]; exact hA)
      | exact absurd hij hA
      | exact absurd hij (by rw [hα2, hα3]; exact hA.symm)
      | exact absurd hij (by rw [hα2]; exact hA.symm)
      | exact absurd hij (by rw [hα3]; exact hA.symm)
      | exact absurd hij hA.symm
      | exact absurd (hs.mp hv0) (not_lt.mpr hv2.le)
      | exact absurd (hs.mpr hv0) (not_lt.mpr hv2.le)
      | exact absurd (hs.mp hv1) (not_lt.mpr hv3.le)
      | exact absurd (hs.mpr hv1) (not_lt.mpr hv3.le)
  · rw [ha0, ha0, hα2]
  · rw [ha0, ha0, hα3]
  · rw [ha0, ha0, hα1]
    exact (hτfix _ (hαJ 0)).symm

end DifferentialGeometry.Topology.PiecewiseLinear
