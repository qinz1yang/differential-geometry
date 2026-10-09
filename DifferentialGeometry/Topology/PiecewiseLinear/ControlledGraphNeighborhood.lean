/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnStability
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Statements
import DifferentialGeometry.Topology.PiecewiseLinear.Section34DeletedBalls
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ConfinedTubeCircleRemoval
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeMatchingLeaf
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingPackage
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexPreparation
import DifferentialGeometry.Topology.PiecewiseLinear.ControlledGraphCutFrame
import DifferentialGeometry.Topology.PiecewiseLinear.Moise341Producer

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U W : Set M₁} {h : M₁ → M₂}
  {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
  {Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem section34Marker_of_dist_lt
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hGp : ∀ w, IsPLHomeomorphInto 3 (G w) (Cp w))
    (hGdist : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w) (w : Section34VertexIndex 𝒦 𝒦') :
    h '' simplexBody 𝒦' w.1 ⊆ interior (G w '' Cp w) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, hkc, -⟩ := id hprep
  exact (image_mono (hkc w).2.1).trans ((section34MarkerConditions hprep hGp hGdist).1 w)

end Leaves

theorem controlledGraphNeighborhood (h341 : Moise341) :
    ControlledGraphNeighborhoodStatement.{u} := by
  intro M₁ M₂ _ _ _ _ _ _ _ _ _ U hU h hh Ea _ _ _ 𝒦 h𝒦 η H hH W hW hΓW hWU ψ hψc hψpos
  obtain ⟨-, hHsub, hHlf, -, -, hHchart⟩ := id hH
  obtain ⟨𝒦', src, srcBd, car, Q, ct, Sd, hframe, hN, hNW, hcarF, hcarS, hcarfib, hQint, hQH,
      hQsmall, hQsep, -, htorus⟩ :=
    exists_section34CutFrame hU hh 𝒦 h𝒦 η H hH hW hΓW hWU ψ hψc hψpos
  have hHfib : ∀ y ∈ h '' U, ∃ V ∈ 𝓝[h '' U] y,
      {t | ∃ w : Section34VertexIndex 𝒦 𝒦', car w = t ∧ (H t ∩ V).Nonempty}.Finite := by
    intro y hy
    obtain ⟨V, hV, hfin⟩ := hHlf y hy
    refine ⟨V, hV, hfin.subset ?_⟩
    rintro t ⟨w, hw, hmem⟩
    exact ⟨hw ▸ hcarF w, hmem⟩
  have hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite :=
    exists_nhds_finite_of_subset_carriers (h '' U) Q H car hQH
      (fun w => hHsub _ (hcarF w)) hcarfib hHfib
  have hQsub : ∀ w : Section34VertexIndex 𝒦 𝒦', Q w ⊆ h '' U := fun w =>
    (hQH w).trans (hHsub _ (hcarF w))
  have hQlfU : LocallyFinite fun w : Section34VertexIndex 𝒦 𝒦' =>
      {y : h '' U | (y : M₂) ∈ Q w} :=
    locallyFinite_subtype_of_subset_carriers (h '' U) Q H car hQH hcarfib hHfib
  obtain ⟨Cp, CpBd, Cc, CcBd, Kcore, ends, Sn, Tn, Aa, Ab₀, Ab₁, Bb, Bb₀, Bb₁, Bc, Bc₀, Bc₁, ε,
      hprep⟩ := exists_section34VertexPreparation hU hh hframe hN hQint fun w => by
    obtain ⟨c, hc, hcs⟩ := hHchart _ (hcarF w)
    exact ⟨c, hc, (((hQint w).trans interior_subset).trans (hQH w)).trans hcs⟩
  obtain ⟨-, -, hsubs, -, hcpcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnonadj, -⟩ := id hprep
  obtain ⟨Sp, Tp, cnt, Pg, G₁, hpack, hG₁dist⟩ :=
    exists_section34PiercingPackage h341 hU hh hframe hN hQsub hQlfU hprep
  obtain ⟨-, -, -, hSpdef, -, -, -, -, -, -, hGp₁, -⟩ := id hpack
  obtain ⟨hcore₁, hkdisj₁, -⟩ := section34MarkerConditions hprep hGp₁ hG₁dist
  have hSpK : ∀ w e, Disjoint (h '' Kcore w) (Sp e) := by
    intro w e
    rw [(hSpdef e).1]
    exact hkdisj₁ w e
  obtain ⟨G₂, cnt₂, Pg₂, hpack₂, hone, hoff₂, -⟩ :=
    exists_section34ConfinedTubePiercingConditions_count_eq_one hprep hpack
  obtain ⟨-, hGQ₂, -, -, -, -, -, -, -, -, hGp₂, -, -, hCpdisj₂, -, -, -, -, -, -, hLdisj₂,
    -⟩ := id hpack₂
  have hcore₂ : ∀ w, h '' Kcore w ⊆ interior (G₂ w '' Cp w) :=
    section34Core_of_eqOn_off_support G₂ hcpcell (fun w => (hsubs w).2.1) hGp₁ hGp₂ hcore₁
      hSpK hoff₂
  obtain ⟨Dv, DvBd, Dd, DdBd, hDvdef, hDv, hDd, hDmeet, hDdBd, hDmark, hDnbhd⟩ :=
    exists_section34DeletedBalls hU hh hframe hN hQlf hprep hpack₂ hone hcore₂
  have hDvP : ∀ w, Dv w ⊆ G₂ w '' Cp w := by
    intro w
    rw [hDvdef w]
    exact Set.sdiff_subset
  have hDvQ : ∀ w, Dv w ⊆ Q w := fun w =>
    (hDvP w).trans ((image_mono (hsubs w).2.1).trans (hGQ₂ w))
  have hDadj : ∀ w w', w ≠ w' → (Dv w ∩ Dv w').Nonempty → ∃ e : Section34EdgeIndex 𝒦 𝒦',
      (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1) := by
    intro w w' hne hmeet
    by_contra hcon
    obtain ⟨y, hy₁, hy₂⟩ := hmeet
    exact Set.disjoint_left.mp (hCpdisj₂ w w' (hnonadj w w' hne hcon)) (hDvP w hy₁)
      (hDvP w' hy₂)
  have hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d) := by
    intro e d hne
    rw [← hDmeet e, ← hDmeet d]
    exact (hLdisj₂ e d hne).mono (inter_subset_inter (hDvP _) (hDvP _))
      (inter_subset_inter (hDvP _) (hDvP _))
  obtain ⟨G, hG, hGD, hcompat, hmeet, hrim, hcert⟩ :=
    exists_section34EdgeMatching hU hh hframe hN hQsep hQlf htorus hprep hpack₂ Dv DvBd Dd
      DdBd hDvdef hDv hDd hDmeet hDdBd hDadj hDddisj hDvQ hDnbhd
  have hGQ : ∀ w, G w '' src (Section34Label.vertexBall w) ⊆ Q w := by
    intro w
    rw [hGD w]
    exact hDvQ w
  have hmarker : ∀ w, h '' simplexBody 𝒦' w.1 ⊆
      interior (G w '' src (Section34Label.vertexBall w)) := by
    intro w
    rw [hGD w]
    exact hDmark w
  have hGnbhd : (⋃ w, G w '' src (Section34Label.vertexBall w)) ∈
      nhdsSet (h '' graphSkeletonSpace 𝒦) := by
    have hEq : (⋃ w, G w '' src (Section34Label.vertexBall w)) = ⋃ w, Dv w :=
      iUnion_congr fun w => hGD w
    rw [hEq]
    exact hDnbhd
  obtain ⟨-, -, -, hcell, -, -, -, hLF, hcover, -, -, -, -, -, -, -, -, -, -, -, -, -,
      hsplit, -, -⟩ := id hframe
  obtain ⟨-, -, htor, -, -⟩ := id htorus
  have hCclosed : ∀ w, IsClosed (src (Section34Label.vertexBall w)) := fun w =>
    (hcell _).isCompact.isClosed
  have hDclosed : ∀ w, IsClosed (G w '' src (Section34Label.vertexBall w)) := fun w =>
    ((hcell _).isCompact.image_of_continuousOn (hG w).continuousOn).isClosed
  have hsub : ∀ w, src (Section34Label.vertexBall w) ⊆ U := fun w =>
    (subset_iUnion src (Section34Label.vertexBall w)).trans hcover.subset
  have hsrcLF : ∀ x ∈ ⋃ w, src (Section34Label.vertexBall w), ∃ V ∈ 𝓝 x,
      {w | (src (Section34Label.vertexBall w) ∩ V).Nonempty}.Finite := by
    intro x hx
    obtain ⟨w₀, hw₀⟩ := mem_iUnion.mp hx
    obtain ⟨V, hV, hfin⟩ := hLF x (hsub w₀ hw₀)
    refine ⟨V, hV, Set.Finite.of_finite_image (f := fun w =>
      (Section34Label.vertexBall w : Section34CutLabelOf 𝒦 𝒦'))
      (hfin.subset ?_) ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hw
    · intro a _ b _ hab
      simpa using hab
  have htgtLF : ∀ y ∈ ⋃ w, G w '' src (Section34Label.vertexBall w), ∃ V ∈ 𝓝 y,
      {w | (G w '' src (Section34Label.vertexBall w) ∩ V).Nonempty}.Finite := by
    refine exists_nhds_finite_of_subset_carriers (h '' U) _ H car
      (fun w => (hGQ w).trans (hQH w)) (fun w => hHsub _ (hcarF w)) hcarfib ?_
    intro y hy
    obtain ⟨V, hV, hfin⟩ := hHlf y hy
    refine ⟨V, hV, hfin.subset ?_⟩
    rintro t ⟨w, hw, hmem⟩
    exact ⟨hw ▸ hcarF w, hmem⟩
  obtain ⟨f₁, hf₁, hf₁G, hf₁im⟩ :=
    exists_isPLHomeomorphInto_dualCellPaste h (fun w => src (.vertexBall w)) G hCclosed
      hDclosed hG hcompat hmeet hsrcLF htgtLF
  have himg : ∀ w, f₁ '' src (Section34Label.vertexBall w) =
      G w '' src (Section34Label.vertexBall w) := fun w => (hf₁G w).image_eq
  have hfun : (fun w => f₁ '' src (Section34Label.vertexBall w)) =
      fun w => G w '' src (Section34Label.vertexBall w) := funext himg
  have hf₁Q : ∀ w, f₁ '' src (Section34Label.vertexBall w) ⊆ Q w := by
    intro w
    rw [himg w]
    exact hGQ w
  have hnbhd : f₁ '' section34CutNeighborhood src ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) := by
    have hrw : f₁ '' section34CutNeighborhood src =
        ⋃ w, G w '' src (Section34Label.vertexBall w) := hf₁im
    rw [hrw]
    exact hGnbhd
  have hmer : ∀ s : Section34SimplexIndex 𝒦 3,
      CarriesFundamentalGroupOnto (h '' simplexRim 𝒦 s.1)
        (section34FaceTorus (fun w => G w '' src (Section34Label.vertexBall w)) s) := by
    intro s
    obtain ⟨S₁, Te, Φ, -, -, hΦ, hS₁, hTe, h₁T, hT₂, hshell, hspine, hJe⟩ := hcert s
    exact carriesFundamentalGroupOnto_of_nestedSolidTorus
      ((hrim s).trans interior_subset) Φ hΦ hS₁ (htor s).1 hTe h₁T hT₂ hshell hspine hJe
  refine ⟨𝒦', src, srcBd, car, f₁, hframe, hN, hNW, hf₁, hnbhd, ?_, ?_, ?_, ?_, ?_, ?_,
    hcarF, hcarS, hcarfib, ?_⟩
  · intro x hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    refine hQsmall w x hw (f₁ x) (hf₁Q w ⟨x, hw, rfl⟩) (h x) ?_
    exact interior_subset (hQint w ⟨x, hw, rfl⟩)
  · intro w
    rw [himg w]
    exact hmarker w
  · intro e s hne
    obtain ⟨w, w', hww', hunion, hdisk⟩ := hsplit e
    have hwsub : src (Section34Label.splitDisk e) ⊆
        src (Section34Label.vertexBall w) := hdisk ▸ inter_subset_left
    have hw'sub : src (Section34Label.splitDisk e) ⊆
        src (Section34Label.vertexBall w') := hdisk ▸ inter_subset_right
    have hw : Section34Incident w.1 s.1 := by
      refine hQsep w s ?_
      obtain ⟨y, hy₁, hy₂⟩ := hne
      exact ⟨y, hf₁Q w (image_mono hwsub hy₁), hy₂⟩
    have hw' : Section34Incident w'.1 s.1 := by
      refine hQsep w' s ?_
      obtain ⟨y, hy₁, hy₂⟩ := hne
      exact ⟨y, hf₁Q w' (image_mono hw'sub hy₁), hy₂⟩
    have hkey : ((e.1 : Finset Ea) : Set Ea) ⊆ convexHull ℝ ((s.1 : Finset Ea) : Set Ea) := by
      rw [hunion]
      exact union_subset hw hw'
    exact hkey
  · intro w s hne
    obtain ⟨y, hy₁, hy₂⟩ := hne
    exact hQsep w s ⟨y, hf₁Q w hy₁, hy₂⟩
  · intro s
    rw [hfun]
    exact hrim s
  · intro s
    rw [hfun]
    exact hmer s
  · intro w
    refine union_subset ?_ ((hf₁Q w).trans (hQH w))
    exact fun y hy => hQH w (interior_subset (hQint w hy))

theorem controlledGraphNeighborhoodStatement : ControlledGraphNeighborhoodStatement.{u} :=
  controlledGraphNeighborhood moise341

end DifferentialGeometry.Topology.PiecewiseLinear
