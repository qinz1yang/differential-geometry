import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelSeamPiece
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelCutDataLift
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelAdapterNonsep
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyHalfCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutRaw

/-!
# Chapter-14 assembly, relative COMPARE: the generic tube cut

Lane ASM-L2e3, generic group (used by G5 SEP with two drilled carriers and by G6 NONSEP with one).
Data: a partial diffeomorphism `F : Q ⇀ W` (the fold off the caps, target the complement of a set
`Z`, the seam sphere), carrying the ports `R` of `Q` onto the ports `E` of `W`; a diffeomorphism `Ψ`
of `Q` fixed off a compact subset of the interior; `k` tubes `φ t` with pairwise disjoint closed unit
tubes; `m` drilled carriers `L j`, embedded by `η j` onto the piece `O j` of an open partition of `Q`
off the open unit tubes, with the radial collar `Γ t` of the tube `t` in its owner `L (o t)`; and a
plug piece `Pc` of `W` with its radial collars `lift t` inside the tubes, image the closed unit tubes
read through `Ψ⁻¹` and `F` together with `Z`.

`exists_rawGraphPresentation_of_tubeCut`: these data form a `RegularCutData W (E.shrink δ)` with the
`m + 1` pieces `Fin.cons Pc A` (`A j` the drilled carrier `L j` mapped by `F ∘ Ψ⁻¹ ∘ η j`), the `k`
seams `tubeSeam` of width `κ` (the plug collar shrunk by `2 κ / ν` on the side `true`, the drilled
collar shrunk by `2 κ` on the side `false`), the ports of `W` shrunk by one `δ` and lifted into the
drilled piece owning them; B3 (`exists_rawGraphPresentation_of_regularCutData`) then gives a raw
presentation of `W` from raw presentations of the pieces.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The zero section of a half collar consists of boundary points. -/
theorem isBoundaryPoint_halfCollarZero {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
    (ℓ : PartialDiffeomorph halfCollarModel J (Torus × EuclideanHalfSpace 1) N ∞)
    (hs : ℓ.source = halfCollarSource) (t : Torus) : J.IsBoundaryPoint (ℓ (t, halfZero)) := by
  have hmem : (t, halfZero) ∈ ℓ.source := hs ▸ zero_mem_halfCollarSource t
  exact ((ℓ.isLocalDiffeomorphAt halfCollarModel J ∞ hmem).isBoundaryPoint_iff (by simp)).mp
    (halfCollar_isBoundaryPoint_halfZero t)

/-- **The generic tube cut.** -/
theorem exists_rawGraphPresentation_of_tubeCut {W Q : CompactCarrier.{u}} {n : ℕ}
    (E : BoundaryTori W n) (hE : W.model.boundary W.Carrier = E.image)
    (R : BoundaryTori Q n) (hR : Q.model.boundary Q.Carrier = R.image)
    (F : PartialDiffeomorph Q.model W.model Q.Carrier W.Carrier ∞)
    (hRE : ∀ i p, p ∈ halfCollarSource → R.collar i p ∈ F.source →
      F (R.collar i p) = E.collar i p)
    (Z : Set W.Carrier) (hFt : F.target = Zᶜ)
    (Ψ : Q.Carrier ≃ₘ⟮Q.model, Q.model⟯ Q.Carrier) (K : Set Q.Carrier) (hK : IsCompact K)
    (hKI : K ⊆ Q.interior) (hΨK : ∀ x, x ∉ K → Ψ x = x) {k : ℕ}
    (φ : Fin k → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) Q.model
      (PlaneLift.{u} × Circle) Q.Carrier ∞)
    (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source)
    (hφI : ∀ t, (φ t).target ⊆ Q.interior)
    (hφd : Pairwise fun t t' =>
      Disjoint (φ t '' {p | ‖p.1.down‖ ≤ 1}) (φ t' '' {p | ‖p.1.down‖ ≤ 1}))
    {m : ℕ} (O : Fin m → Set Q.Carrier) (hOo : ∀ j, IsOpen (O j))
    (hOd : Pairwise (Disjoint on O)) (hOc : ∀ x, ∃ j, x ∈ O j)
    (L : Fin m → CompactCarrier.{u}) (hLk : ∀ j, (L j).kind = .withBoundary)
    (hLc : ∀ j, ConnectedSpace (L j).Carrier) (hLR : ∀ j, Nonempty (RawGraphPresentation (L j)))
    (η : ∀ j, (L j).Carrier → Q.Carrier)
    (hη : ∀ j, IsSmoothEmbedding (L j).model Q.model ∞ (η j))
    (hηb : ∀ j x, Bijective (mfderiv (L j).model Q.model (η j) x))
    (hηr : ∀ j, range (η j) = O j \ ⋃ t, φ t '' {p | ‖p.1.down‖ < 1})
    (o : Fin k → Fin m)
    (Γ : ∀ t, PartialDiffeomorph halfCollarModel (L (o t)).model
      (Torus × EuclideanHalfSpace 1) (L (o t)).Carrier ∞)
    (hΓs : ∀ t, (Γ t).source = halfCollarSource)
    (hΓ : ∀ t p, p ∈ halfCollarSource →
      η (o t) (Γ t p) = φ t (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (hLb : ∀ j, η j '' (L j).model.boundary (L j).Carrier ⊆ Q.model.boundary Q.Carrier ∪
      ⋃ t, range (fun τ : Torus => φ t (ULift.up (τ.1 : ℂ), τ.2)))
    (P : CompactCarrier.{u}) (hPR : Nonempty (RawGraphPresentation P)) (Pc : PieceFold W)
    (e : P.Carrier ≃ₘ⟮P.model, 𝓡∂ 3⟯ Pc.Piece) {ν : ℝ} (hν : 0 < ν)
    (lift : Fin k → PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) Pc.Piece ∞)
    (hls : ∀ t, (lift t).source = halfCollarSource)
    (hl : ∀ t p, p ∈ halfCollarSource → Pc.map (lift t p) =
      F (Ψ.symm (φ t (ULift.up ((1 - ν * p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))))
    (hPb : (𝓡∂ 3).boundary Pc.Piece ⊆ ⋃ t, range fun τ => lift t (τ, halfZero))
    (hPi : Injective Pc.map)
    (hPr : range Pc.map = F '' ((Ψ.symm '' ⋃ t, φ t '' {p | ‖p.1.down‖ ≤ 1}) ∩ F.source) ∪ Z)
    (hsrc : ∀ x, Ψ x ∉ ⋃ t, φ t '' {p | ‖p.1.down‖ < 1 - ν} → x ∈ F.source) :
    Nonempty (RawGraphPresentation W) := by
  /- the seams -/
  obtain ⟨κ, hκ, hκ1, hκν, hκ2, hw, σ, hσ, hσd⟩ := exists_tubeSeams F Ψ φ h3 hφI hφd hν hsrc
  /- the drilled pieces -/
  have hηO : ∀ j x, η j x ∈ O j ∧ η j x ∉ ⋃ t, φ t '' {p | ‖p.1.down‖ < 1} := fun j x => by
    have h := mem_range_self (f := η j) x
    rw [hηr j] at h
    exact h
  have hηs : ∀ j x, Ψ.symm (η j x) ∈ F.source := fun j x =>
    symm_mem_source_of_not_mem_tubes F Ψ φ hν hsrc (hηO j x).2
  have hA : ∀ j, ∃ (A : PieceFold W) (eA : (L j).Carrier ≃ₘ⟮(L j).model, 𝓡∂ 3⟯ A.Piece),
      (∀ x, A.map (eA x) = F (Ψ.symm (η j x))) ∧ Injective A.map := fun j => by
    have := hLc j
    exact exists_drilledPiece F Ψ (L j) (hLk j) (η j) (hη j) (hηb j) (hηs j)
  choose A eA hAm hAi using hA
  have hηinj : ∀ j, Injective (η j) := fun j => (hη j).isEmbedding.injective
  have hown_eq : ∀ {j j' : Fin m} (x : (L j).Carrier) (x' : (L j').Carrier),
      η j x = η j' x' → j = j' := fun x x' h =>
    eq_of_mem_openPartition hOd (hηO _ x).1 (h ▸ (hηO _ x').1)
  /- the shrunk ports -/
  let K' : Set Q.Carrier := K ∪ ⋃ t, φ t '' {p | ‖p.1.down‖ ≤ 1 + κ}
  have hK' : IsCompact K' :=
    hK.union (isCompact_iUnion fun t => isCompact_tubeImage (φ t) (h3 t) (by linarith))
  have hK'I : K' ⊆ Q.interior := by
    refine union_subset hKI (iUnion_subset fun t => ?_)
    rintro y ⟨p, hp, rfl⟩
    exact hφI t ((φ t).map_source (h3 t (show ‖p.1.down‖ ≤ 3 by
      linarith [show ‖p.1.down‖ ≤ 1 + κ from hp])))
  obtain ⟨δ, hδ, hδ1, own, hav, hown⟩ := exists_portShrink R hK' hK'I hOo hOd hOc
  have hport : ∀ i p, p ∈ halfCollarSource →
      Ψ ((R.shrink hδ hδ1).collar i p) = (R.shrink hδ hδ1).collar i p ∧
      Ψ.symm ((R.shrink hδ hδ1).collar i p) = (R.shrink hδ hδ1).collar i p ∧
      (∀ t, (R.shrink hδ hδ1).collar i p ∉ φ t '' {p | ‖p.1.down‖ ≤ 1 + κ}) ∧
      (R.shrink hδ hδ1).collar i p ∈ F.source ∧
      F ((R.shrink hδ hδ1).collar i p) = (E.shrink hδ hδ1).collar i p ∧
      ∃ w, η (own i) w = (R.shrink hδ hδ1).collar i p := by
    intro i p hp
    have h1 : (R.shrink hδ hδ1).collar i p ∉ K := fun h => hav i p hp (Or.inl h)
    have h2 : ∀ t, (R.shrink hδ hδ1).collar i p ∉ φ t '' {p | ‖p.1.down‖ ≤ 1 + κ} :=
      fun t h => hav i p hp (Or.inr (mem_iUnion.mpr ⟨t, h⟩))
    have hΨ := hΨK _ h1
    have hΨs : Ψ.symm ((R.shrink hδ hδ1).collar i p) = (R.shrink hδ hδ1).collar i p :=
      Ψ.injective ((Ψ.apply_symm_apply _).trans hΨ.symm)
    have hnot : (R.shrink hδ hδ1).collar i p ∉ ⋃ t, φ t '' {p | ‖p.1.down‖ < 1} := by
      intro h
      obtain ⟨t, q, hq, hqx⟩ := mem_iUnion.mp h
      exact h2 t ⟨q, show ‖q.1.down‖ ≤ 1 + κ by linarith [show ‖q.1.down‖ < 1 from hq], hqx⟩
    have hF : (R.shrink hδ hδ1).collar i p ∈ F.source := by
      have h := symm_mem_source_of_not_mem_tubes F Ψ φ hν hsrc hnot
      rwa [hΨs] at h
    refine ⟨hΨ, hΨs, h2, hF, R.shrink_collar_map E F F.source hRE hδ hδ1 i hp hF, ?_⟩
    have hmem : (R.shrink hδ hδ1).collar i p ∈ range (η (own i)) := by
      rw [hηr]
      exact ⟨hown i p hp, hnot⟩
    exact hmem
  /- the external lifts -/
  have hext : ∀ i, ((E.shrink hδ hδ1).collar i).target ⊆ range (A (own i)).map := by
    intro i y hy
    have hp := ((E.shrink hδ hδ1).collar i).map_target hy
    have hy' := ((E.shrink hδ hδ1).collar i).right_inv hy
    rw [(E.shrink hδ hδ1).source_eq i] at hp
    obtain ⟨-, hΨs, -, -, hFx, w, hw'⟩ := hport i _ hp
    refine ⟨eA (own i) w, ?_⟩
    rw [hAm, hw', hΨs, hFx]
    exact hy'
  have hℓ := fun i => (A (own i)).exists_halfCollarLift_of_injective (hAi (own i))
    ((E.shrink hδ hδ1).collar i) ((E.shrink hδ hδ1).source_eq i) (hext i)
  choose ℓ hℓs _ hℓv using hℓ
  /- plug against drilled pieces -/
  have hpd : ∀ j (w : (L j).Carrier) (q : Pc.Piece), Pc.map q = F (Ψ.symm (η j w)) →
      ∃ c τ, Pc.map q = (σ c).collar (τ, 0) := by
    intro j w q h
    have hq : Pc.map q ∈ range Pc.map := mem_range_self q
    rw [hPr] at hq
    rcases hq with ⟨y, ⟨hyΨ, hyF⟩, hyq⟩ | hZ
    · have hyy := F.toPartialEquiv.injOn hyF (hηs j w) (hyq.trans h)
      obtain ⟨z, hz, rfl⟩ := hyΨ
      have hzη : z = η j w := Ψ.symm.injective hyy
      obtain ⟨c, hzc⟩ := mem_iUnion.mp hz
      obtain ⟨τ, hτ⟩ := mem_range_torus_of_mem_closedTube (φ c) hzc (fun h' =>
        (hηO j w).2 (mem_iUnion.mpr ⟨c, hzη ▸ h'⟩))
      refine ⟨c, τ, ?_⟩
      rw [← hyq, hσ c, tubeSeamCollar_zero, ← hτ]
    · have ht : F (Ψ.symm (η j w)) ∈ F.target := F.map_source (hηs j w)
      rw [hFt, ← h] at ht
      exact (ht hZ).elim
  /- the regular cut -/
  refine exists_rawGraphPresentation_of_regularCutData (E := E.shrink hδ hδ1)
    { count := m + 1
      count_pos := Nat.succ_pos m
      piece := Fin.cons Pc A
      covers := ?_
      seamCount := k
      seam := σ
      seam_disjoint := hσd
      side := fun c b => cond b 0 (o c).succ
      lift := fun c b => match b with
        | true => shrinkHalfCollar (div_pos (mul_pos two_pos hκ) hν) (lift c)
        | false => drillSeamLift hκ (Γ c) (eA (o c))
      lift_source := ?_
      lift_eq := ?_
      externalOwner := fun i => (own i).succ
      externalLift := ℓ
      externalLift_source := hℓs
      externalLift_eq := hℓv
      boundary_exhausted := ?_
      overlap := ?_
      external_exhausted := by rw [BoundaryTori.shrink_image]; exact hE
      external_seam_disjoint := ?_ } ?_
  · -- covers
    refine eq_univ_of_forall fun y => ?_
    by_cases hyZ : y ∈ Z
    · have hy : y ∈ range Pc.map := by rw [hPr]; exact Or.inr hyZ
      exact mem_iUnion.mpr ⟨0, hy⟩
    have hyt : y ∈ F.target := by rw [hFt]; exact hyZ
    have hx := F.map_target hyt
    have hFx := F.right_inv hyt
    by_cases hz : Ψ (F.symm y) ∈ ⋃ t, φ t '' {p | ‖p.1.down‖ ≤ 1}
    · have hy : y ∈ range Pc.map := by
        rw [hPr]
        refine Or.inl ⟨F.symm y, ⟨⟨_, hz, Ψ.symm_apply_apply _⟩, hx⟩, hFx⟩
      exact mem_iUnion.mpr ⟨0, hy⟩
    · obtain ⟨j, hj⟩ := hOc (Ψ (F.symm y))
      have hmem : Ψ (F.symm y) ∈ range (η j) := by
        rw [hηr]
        refine ⟨hj, fun h => hz ?_⟩
        obtain ⟨t, p, hp, hpx⟩ := mem_iUnion.mp h
        exact mem_iUnion.mpr ⟨t, p, show ‖p.1.down‖ ≤ 1 from (show ‖p.1.down‖ < 1 from hp).le,
          hpx⟩
      obtain ⟨w, hw'⟩ := hmem
      refine mem_iUnion.mpr ⟨j.succ, eA j w, ?_⟩
      change (A j).map (eA j w) = y
      rw [hAm, hw', Ψ.symm_apply_apply]
      exact hFx
  · -- lift_source
    intro c b
    cases b
    · exact drillSeamLift_source hκ (hΓs c) (eA (o c)) hκ2
    · exact shrinkHalfCollar_source _ ((div_le_one hν).mpr hκν) (hls c)
  · -- lift_eq
    intro c b τ s hs hs1
    cases b
    · change (A (o c)).map (drillSeamLift hκ (Γ c) (eA (o c)) (τ, halfPoint s hs)) =
        (σ c).collar (τ, s)
      rw [hσ c]
      exact drillSeamLift_eq F Ψ (φ c) hκ (hΓ c) (eA (o c)) (A (o c)).map (hAm (o c)) hκ2 τ hs hs1
    · change Pc.map (shrinkHalfCollar (div_pos (mul_pos two_pos hκ) hν) (lift c)
        (τ, halfPoint s hs)) = (σ c).collar (τ, -s)
      rw [hσ c]
      exact tubeSeam_inner_lift F Ψ (φ c) hκ Pc.map (lift c) hν hκν (hl c) τ hs hs1
  · -- boundary_exhausted
    intro j
    refine Fin.cases ?_ (fun j' => ?_) j
    · change (𝓡∂ 3).boundary Pc.Piece = _
      ext q
      constructor
      · intro hq
        obtain ⟨c, τ, hτ⟩ := mem_iUnion.mp (hPb hq)
        refine Or.inl ⟨c, true, τ, rfl, ?_⟩
        change q = shrinkHalfCollar (div_pos (mul_pos two_pos hκ) hν) (lift c) (τ, halfZero)
        rw [shrinkHalfCollar_zero]
        exact hτ.symm
      · rintro (⟨c, b, τ, h, rfl⟩ | ⟨i, τ, h, rfl⟩)
        · cases b
          · exact absurd h (Fin.succ_ne_zero _)
          · exact isBoundaryPoint_halfCollarZero _
              (shrinkHalfCollar_source _ ((div_le_one hν).mpr hκν) (hls c)) τ
        · exact absurd h (Fin.succ_ne_zero _)
    · change (𝓡∂ 3).boundary (A j').Piece = _
      ext q
      constructor
      · intro hq
        have hx : (L j').model.IsBoundaryPoint ((eA j').symm q) := by
          rw [((eA j').isLocalDiffeomorph _).isBoundaryPoint_iff (by simp), (eA j').apply_symm_apply]
          exact hq
        rcases hLb j' ⟨_, hx, rfl⟩ with hb | ht
        · rw [hR] at hb
          obtain ⟨i, τ, hiτ⟩ := R.exists_shrink_zero_of_mem_image hδ hδ1 hb
          have hzero := zero_mem_halfCollarSource τ
          obtain ⟨-, hΨs, -, -, hFx, -⟩ := hport i _ hzero
          have hij : own i = j' :=
            eq_of_mem_openPartition hOd (hown i _ hzero) (hiτ ▸ (hηO j' _).1)
          subst hij
          refine Or.inr ⟨i, τ, rfl, ?_⟩
          change q = ℓ i (τ, halfZero)
          apply hAi (own i)
          rw [hℓv i _ hzero, ← hFx, ← (eA (own i)).apply_symm_apply q, hAm, hiτ, hΨs]
        · obtain ⟨c, τ, hτ⟩ := mem_iUnion.mp ht
          have hzero := zero_mem_halfCollarSource τ
          have hΓ0 : η (o c) (Γ c (τ, halfZero)) = η j' ((eA j').symm q) := by
            rw [hΓ c _ hzero, ← hτ]
            have h0 : (1 + (halfZero : EuclideanHalfSpace 1).val 0 / 2) • (τ.1 : ℂ) = (τ.1 : ℂ) := by
              change (1 + (0 : ℝ) / 2) • (τ.1 : ℂ) = (τ.1 : ℂ)
              rw [zero_div, add_zero, one_smul]
            change φ c (ULift.up ((1 + (halfZero : EuclideanHalfSpace 1).val 0 / 2) • (τ.1 : ℂ)), τ.2) =
              φ c (ULift.up (τ.1 : ℂ), τ.2)
            rw [h0]
          have hcj : o c = j' := hown_eq _ _ hΓ0
          subst hcj
          refine Or.inl ⟨c, false, τ, rfl, ?_⟩
          change q = drillSeamLift hκ (Γ c) (eA (o c)) (τ, halfZero)
          rw [drillSeamLift_zero, hηinj _ hΓ0, (eA (o c)).apply_symm_apply]
      · rintro (⟨c, b, τ, h, rfl⟩ | ⟨i, τ, h, rfl⟩)
        · cases b
          · have hcj : o c = j' := Fin.succ_injective _ h
            subst hcj
            exact isBoundaryPoint_halfCollarZero _ (drillSeamLift_source hκ (hΓs c) _ hκ2) τ
          · exact absurd h.symm (Fin.succ_ne_zero _)
        · have hij : own i = j' := Fin.succ_injective _ h
          subst hij
          exact isBoundaryPoint_halfCollarZero _ (hℓs i) τ
  · -- overlap
    intro j j'
    refine Fin.cases ?_ (fun j₁ => ?_) j <;> refine Fin.cases ?_ (fun j₂ => ?_) j' <;>
      intro q q' h
    · have hqq : q = q' := hPi h
      subst hqq
      exact Or.inl rfl
    · right
      change (A j₂).Piece at q'
      change Pc.map q = (A j₂).map q' at h
      rw [← (eA j₂).apply_symm_apply q', hAm] at h
      exact hpd j₂ _ q h
    · right
      change (A j₁).Piece at q
      have h' : Pc.map q' = (A j₁).map q := h.symm
      rw [← (eA j₁).apply_symm_apply q, hAm] at h'
      obtain ⟨c, τ, hc⟩ := hpd j₁ _ q' h'
      refine ⟨c, τ, ?_⟩
      change (A j₁).map q = _
      rw [← hc]
      exact h
    · left
      change (A j₁).Piece at q
      change (A j₂).Piece at q'
      change (A j₁).map q = (A j₂).map q' at h
      rw [← (eA j₁).apply_symm_apply q, ← (eA j₂).apply_symm_apply q', hAm, hAm] at h
      have hz := Ψ.symm.injective (F.toPartialEquiv.injOn (hηs _ _) (hηs _ _) h)
      have hjj : j₁ = j₂ := hown_eq _ _ hz
      subst hjj
      have hqq : q = q' := by
        rw [← (eA j₁).apply_symm_apply q, ← (eA j₁).apply_symm_apply q', hηinj _ hz]
      subst hqq
      rfl
  · -- external_seam_disjoint
    intro i c
    refine disjoint_left.mpr fun y hy hyc => ?_
    have hp := ((E.shrink hδ hδ1).collar i).map_target hy
    have hy' := ((E.shrink hδ hδ1).collar i).right_inv hy
    rw [(E.shrink hδ hδ1).source_eq i] at hp
    obtain ⟨hΨ, -, h2, hF, hFx, -⟩ := hport i _ hp
    rw [hσ c, ← hy', ← hFx] at hyc
    exact not_mem_tubeSeamCollar_target F Ψ φ hκ hκ1 c hF hΨ (h2 c) hyc
  · -- the pieces are raw
    intro j
    refine Fin.cases ?_ (fun j' => ?_) j
    · exact ⟨P, hPR, ⟨e⟩⟩
    · exact ⟨L j', hLR j', ⟨eA j'⟩⟩

end GC.GraphManifold.Assembly
