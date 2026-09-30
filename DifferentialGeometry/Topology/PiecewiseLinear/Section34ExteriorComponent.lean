/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SplitDiskIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TerminalFaceBalls
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionSegmentStep
import DifferentialGeometry.Topology.PiecewiseLinear.TetrahedronStarComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem exists_mem_frontier_connectedComponentIn_of_joinedIn {X : Type*} [TopologicalSpace X]
    {A O : Set X} (hA : IsClosed A) {y z : X} (hy : y ∈ A) (hz : z ∉ interior A)
    (hyz : JoinedIn O y z) : (connectedComponentIn (A ∩ O) y ∩ frontier A).Nonempty := by
  obtain ⟨γ, hγ⟩ := hyz
  have hTc : IsCompact (Icc (0 : ℝ) 1 ∩ {s | γ.extend s ∉ interior A}) :=
    isCompact_Icc.inter_right (isOpen_interior.preimage γ.continuous_extend).isClosed_compl
  have hT1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 ∩ {s | γ.extend s ∉ interior A} := by
    refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
    change γ.extend 1 ∉ interior A
    rw [Path.extend_one]
    exact hz
  obtain ⟨τ, hτT, hτmin⟩ := hTc.exists_isLeast ⟨1, hT1⟩
  have hτ01 := hτT.1
  have hbefore : ∀ s, 0 ≤ s → s < τ → γ.extend s ∈ interior A := by
    intro s hs0 hsτ
    by_contra h
    exact absurd (hτmin ⟨⟨hs0, hsτ.le.trans hτ01.2⟩, h⟩) (not_le.mpr hsτ)
  have hA' : ∀ s ∈ Icc 0 τ, γ.extend s ∈ A := by
    rintro s ⟨hs0, hsτ⟩
    rcases hsτ.lt_or_eq with hlt | heq
    · exact interior_subset (hbefore s hs0 hlt)
    · rcases hs0.lt_or_eq with hpos | h0
      · have hcl : s ∈ closure (Ico 0 s) := by
          rw [closure_Ico hpos.ne]
          exact ⟨hs0, le_rfl⟩
        exact closure_minimal (fun r hr => show γ.extend r ∈ A from
          interior_subset (hbefore r hr.1 (hr.2.trans_le heq.le)))
          (hA.preimage γ.continuous_extend) hcl
      · rw [← h0, Path.extend_zero]
        exact hy
  have hfront : γ.extend τ ∈ frontier A := by
    rw [hA.frontier_eq]
    exact ⟨hA' τ ⟨hτ01.1, le_rfl⟩, hτT.2⟩
  refine ⟨γ.extend τ, ?_, hfront⟩
  have hconn : IsPreconnected (γ.extend '' Icc 0 τ) :=
    isPreconnected_Icc.image _ γ.continuous_extend.continuousOn
  have hsub : γ.extend '' Icc 0 τ ⊆ A ∩ O := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨hA' s hs, ?_⟩
    rw [Path.extend_apply γ ⟨hs.1, hs.2.trans hτ01.2⟩]
    exact hγ _
  have hy' : y ∈ γ.extend '' Icc 0 τ := ⟨0, ⟨le_rfl, hτ01.1⟩, Path.extend_zero γ⟩
  exact hconn.subset_connectedComponentIn hy' hsub ⟨τ, ⟨hτ01.1, le_rfl⟩, rfl⟩

theorem IsPLCellOn.isConnected_of_sdiff_subset {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {n : ℕ} {S B A : Set M}
    (hS : IsPLCellOn (n + 1) S B) (hSA : S \ B ⊆ A) (hAS : A ⊆ S) : IsConnected A := by
  obtain ⟨P, r, v, hr, hv, rfl, rfl⟩ := hS
  have hrP : r '' stdSimplexBoundary (n + 1) ⊆ P := by
    rintro _ ⟨z, hz, rfl⟩
    exact hr.bijOn.mapsTo hz.1
  have hconn : IsConnected (v '' (P \ r '' stdSimplexBoundary (n + 1))) :=
    (hr.isConnected_sdiff_image_stdSimplexBoundary (n := n)).image v
      (hv.continuousOn.mono sdiff_subset)
  have hcl := hr.closure_sdiff_image_stdSimplexBoundary (n := n)
  refine hconn.subset_closure ?_ (hAS.trans ?_)
  · rw [hv.injOn.image_sdiff_subset hrP]
    exact hSA
  · calc v '' P = v '' closure (P \ r '' stdSimplexBoundary (n + 1)) := by rw [hcl]
      _ ⊆ closure (v '' (P \ r '' stdSimplexBoundary (n + 1))) :=
        ContinuousOn.image_closure (by rw [hcl]; exact hv.continuousOn)

section Frames

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem src_vertexBall_inter_subset_srcBd (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    {w w' : Section34VertexIndex 𝒦 𝒦'} (hww : w ≠ w') :
    src (.vertexBall w) ∩ src (.vertexBall w') ⊆ srcBd (.vertexBall w) := by
  intro q hq
  obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hcut hww ⟨q, hq⟩
  obtain ⟨-, -, -, -, hbd, -⟩ := hcut
  rw [hbd]
  refine mem_iUnion₂.mpr ⟨.splitDisk e, ⟨?_, ?_⟩, he ▸ hq⟩
  · change src (.splitDisk e) ⊆ src (.vertexBall w)
    rw [he]
    exact inter_subset_left
  · simp

omit [FiniteDimensional ℝ Ea] in
theorem interior_image_vertexBall_inter_image_vertexBall
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    {w w' : Section34VertexIndex 𝒦 𝒦'} (hww : w ≠ w') :
    interior (f₁ '' src (.vertexBall w)) ∩ f₁ '' src (.vertexBall w') = ∅ := by
  obtain ⟨-, -, -, hcell, -⟩ := id hcut
  obtain ⟨-, -, hf₁, -⟩ := hgraph
  have hNV : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34Label.vertexBall v)) v
  have hcellw : IsPLCellOn 3 (src (.vertexBall w)) (srcBd (.vertexBall w)) :=
    hcell (.vertexBall w)
  have hint := (hcellw.image_boundary_interior (hf₁.mono_of_isPLCellOn hcellw (hNV w))).2
  rw [← hint]
  apply eq_empty_of_forall_notMem
  rintro _ ⟨⟨q, ⟨hqV, hqB⟩, rfl⟩, q', hq', hqq'⟩
  have hqq : q' = q := hf₁.injOn (hNV w' hq') (hNV w hqV) hqq'
  exact hqB (src_vertexBall_inter_subset_srcBd hcut hww ⟨hqV, hqq ▸ hq'⟩)

omit [FiniteDimensional ℝ Ea] in
theorem exists_mem_src_vertexBall_inter_of_subset_edge
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (e : Section34EdgeIndex 𝒦 𝒦')
    {u u' : Section34VertexIndex 𝒦 𝒦'} (hu : u.1 ⊆ e.1) (hu' : u'.1 ⊆ e.1) (huu : u ≠ u') :
    ∃ r ∈ src (.vertexBall u) ∩ src (.vertexBall u'),
      ∀ w'' : Section34VertexIndex 𝒦 𝒦', r ∈ src (.vertexBall w'') → w'' = u ∨ w'' = u' := by
  classical
  obtain ⟨-, -, -, hcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hve, hends, -, -⟩ :=
    id hcut
  have hkey : ∀ w'' : Section34VertexIndex 𝒦 𝒦', w''.1 ⊆ e.1 → w'' = u ∨ w'' = u' := by
    intro w'' hw''
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp u.2.2.1
    obtain ⟨q', hq'⟩ := Finset.card_eq_one.mp u'.2.2.1
    obtain ⟨q'', hq''⟩ := Finset.card_eq_one.mp w''.2.2.1
    have hqq : q ≠ q' := by
      intro hqq
      apply huu
      apply Subtype.ext
      rw [hq, hq', hqq]
    have hqe : q ∈ e.1 := hu (by rw [hq]; exact Finset.mem_singleton_self q)
    have hq'e : q' ∈ e.1 := hu' (by rw [hq']; exact Finset.mem_singleton_self q')
    have he2 : e.1 = {q, q'} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        rcases Finset.mem_insert.mp hz with hz | hz
        · rw [hz]
          exact hqe
        · rw [Finset.mem_singleton.mp hz]
          exact hq'e
      · rw [e.2.2.1, Finset.card_pair hqq]
    have hq''e : q'' ∈ e.1 := hw'' (by rw [hq'']; exact Finset.mem_singleton_self q'')
    rw [he2] at hq''e
    rcases Finset.mem_insert.mp hq''e with hz | hz
    · left
      apply Subtype.ext
      rw [hq'', hq, hz]
    · right
      apply Subtype.ext
      rw [hq'', hq', Finset.mem_singleton.mp hz]
  obtain ⟨w₁, w₂, hw₁₂, -, hsplit⟩ := hends e
  obtain ⟨r, hr⟩ := (hcell (.splitDisk e)).nonempty
  have hr' : r ∈ src (.vertexBall w₁) ∩ src (.vertexBall w₂) := hsplit ▸ hr
  have hsub : ∀ w'' : Section34VertexIndex 𝒦 𝒦', r ∈ src (.vertexBall w'') → w''.1 ⊆ e.1 :=
    fun w'' hw'' => hve w'' e ⟨r, hw'', hr⟩
  refine ⟨r, ?_, fun w'' hw'' => hkey w'' (hsub w'' hw'')⟩
  rcases hkey w₁ (hsub w₁ hr'.1) with h1 | h1 <;> rcases hkey w₂ (hsub w₂ hr'.2) with h2 | h2
  · exact absurd (h1.trans h2.symm) hw₁₂
  · rw [h1, h2] at hr'
    exact hr'
  · rw [h1, h2] at hr'
    exact ⟨hr'.2, hr'.1⟩
  · exact absurd (h1.trans h2.symm) hw₁₂

omit [FiniteDimensional ℝ Ea] in
open Classical in
theorem image_mem_connectedComponentIn_of_mem_segment
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    {t : Section34SimplexIndex 𝒦 4} {F : Set M₂}
    (hF : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 t.1 →
      f₁ '' (src (.vertexBall u) \ ⋃ (w' : Section34VertexIndex 𝒦 𝒦')
        (_ : Section34Incident w'.1 t.1), src (.vertexBall w')) ⊆ F)
    {a x : Ea} (hax : ({a, x} : Finset Ea) ∈ 𝒦.complex.faces) (hat : a ∈ t.1) (hxt : x ∉ t.1)
    {q : Ea} (hq : ({q} : Finset Ea) ∈ 𝒦'.complex.faces) (hqs : q ∈ segment ℝ a x)
    (hqa : q ≠ a) :
    h (𝒦.map q) ∈ connectedComponentIn F (h (𝒦.map x)) := by
  obtain ⟨-, hsubdiv, hmap, hcell, -⟩ := id hcut
  obtain ⟨-, -, hf₁, -, -, hcore, -⟩ := id hgraph
  obtain ⟨X, hX⟩ : ∃ X : Set M₁, X = ⋃ (w' : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident w'.1 t.1), src (.vertexBall w') := ⟨_, rfl⟩
  rw [← hX] at hF
  have hxa : x - a ≠ 0 := sub_ne_zero.mpr fun hxa => hxt (hxa ▸ hat)
  obtain ⟨g, hg⟩ := SeparatingDual.exists_eq_one (R := ℝ) hxa
  have hsegHull : segment ℝ a x = convexHull ℝ ((({a, x} : Finset Ea)) : Set Ea) := by
    rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair]
  have hΓ : ∀ τ : Finset Ea, convexHull ℝ (τ : Set Ea) ⊆ segment ℝ a x →
      simplexBody 𝒦' τ ⊆ graphSkeletonSpace 𝒦 := by
    intro τ hτ
    rintro _ ⟨r, hr, rfl⟩
    rw [hmap]
    exact mem_iUnion₂.mpr ⟨{a, x}, ⟨hax, Finset.card_le_two⟩, r, hsegHull ▸ hτ hr, rfl⟩
  have hsingle : ∀ r, r ∈ segment ℝ a x →
      convexHull ℝ (({r} : Finset Ea) : Set Ea) ⊆ segment ℝ a x := by
    intro r hr
    rw [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff]
    exact hr
  have hnotinc : ∀ r, r ∈ segment ℝ a x → r ≠ a →
      ¬ (({r} : Finset Ea) : Set Ea) ⊆ convexHull ℝ (t.1 : Set Ea) := by
    intro r hrs hra hinc
    have hrt : r ∈ convexHull ℝ (t.1 : Set Ea) := hinc (by simp)
    have hr2 : r ∈ convexHull ℝ ((({a, x} : Finset Ea)) : Set Ea) := hsegHull ▸ hrs
    have hint := 𝒦.complex.inter_subset_convexHull hax t.2.1 ⟨hr2, hrt⟩
    have hcap : ({a, x} : Finset Ea) ∩ t.1 = {a} := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hv | hv, hvt⟩
        · exact hv
        · exact absurd (hv ▸ hvt) hxt
      · rintro rfl
        exact ⟨Or.inl rfl, hat⟩
    rw [← Finset.coe_inter, hcap, Finset.coe_singleton, convexHull_singleton] at hint
    exact hra hint
  let vidx : ∀ r, ({r} : Finset Ea) ∈ 𝒦'.complex.faces → r ∈ segment ℝ a x →
      Section34VertexIndex 𝒦 𝒦' :=
    fun r hr hrs => ⟨{r}, hr, Finset.card_singleton r, hΓ {r} (hsingle r hrs)⟩
  have hbody : ∀ r (hr : ({r} : Finset Ea) ∈ 𝒦'.complex.faces) (hrs : r ∈ segment ℝ a x),
      h (𝒦.map r) ∈ h '' simplexBody 𝒦' (vidx r hr hrs).1 :=
    fun r hr hrs => ⟨𝒦.map r, ⟨r, subset_convexHull ℝ _
      (Finset.mem_coe.mpr (Finset.mem_singleton_self r)), by rw [hmap]⟩, rfl⟩
  have hNV : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34Label.vertexBall v)) v
  have hCX : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 t.1 →
      src (.vertexBall u) \ srcBd (.vertexBall u) ⊆ src (.vertexBall u) \ X := by
    rintro u hu q ⟨hqV, hqB⟩
    refine ⟨hqV, fun hqX => ?_⟩
    rw [hX] at hqX
    obtain ⟨w', hw', hqw'⟩ := mem_iUnion₂.mp hqX
    have hne : u ≠ w' := fun huw => hu (by rw [huw]; exact hw')
    exact hqB (src_vertexBall_inter_subset_srcBd hcut hne ⟨hqV, hqw'⟩)
  have hCconn : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 t.1 →
      IsConnected (src (.vertexBall u) \ X) := by
    intro u hu
    have hcellu : IsPLCellOn (2 + 1) (src (.vertexBall u)) (srcBd (.vertexBall u)) :=
      hcell (.vertexBall u)
    exact hcellu.isConnected_of_sdiff_subset (hCX u hu) sdiff_subset
  have hcore' : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 t.1 →
      h '' simplexBody 𝒦' u.1 ⊆ f₁ '' (src (.vertexBall u) \ X) := by
    intro u hu z hz
    have hzint := hcore u hz
    have hcellu : IsPLCellOn 3 (src (.vertexBall u)) (srcBd (.vertexBall u)) :=
      hcell (.vertexBall u)
    rw [← (hcellu.image_boundary_interior (hf₁.mono_of_isPLCellOn hcellu (hNV u))).2] at hzint
    exact image_mono (hCX u hu) hzint
  have hstep : ∀ (u u' : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦'),
      u.1 ⊆ e.1 → u'.1 ⊆ e.1 → u ≠ u' → ¬ Section34Incident u.1 t.1 →
      ¬ Section34Incident u'.1 t.1 → ∀ z ∈ h '' simplexBody 𝒦' u.1,
      ∀ z' ∈ h '' simplexBody 𝒦' u'.1, z ∈ connectedComponentIn F z' := by
    intro u u' e hu hu' huu hnu hnu' z hz z' hz'
    obtain ⟨r, ⟨hru, hru'⟩, hronly⟩ :=
      exists_mem_src_vertexBall_inter_of_subset_edge hcut e hu hu' huu
    have hrX : r ∉ X := by
      intro hrX
      rw [hX] at hrX
      obtain ⟨w', hw', hrw'⟩ := mem_iUnion₂.mp hrX
      rcases hronly w' hrw' with rfl | rfl
      · exact hnu hw'
      · exact hnu' hw'
    have hcont : ∀ v : Section34VertexIndex 𝒦 𝒦', ContinuousOn f₁ (src (.vertexBall v) \ X) :=
      fun v => hf₁.continuousOn.mono (sdiff_subset.trans (hNV v))
    have hm1 : f₁ r ∈ f₁ '' (src (.vertexBall u) \ X) := ⟨r, ⟨hru, hrX⟩, rfl⟩
    have hm2 : f₁ r ∈ f₁ '' (src (.vertexBall u') \ X) := ⟨r, ⟨hru', hrX⟩, rfl⟩
    have hS := IsPreconnected.union (f₁ r) hm1 hm2
      ((hCconn u hnu).image f₁ (hcont u)).isPreconnected
      ((hCconn u' hnu').image f₁ (hcont u')).isPreconnected
    exact hS.subset_connectedComponentIn (Or.inr (hcore' u' hnu' hz'))
      (union_subset (hF u hnu) (hF u' hnu')) (Or.inl (hcore' u hnu hz))
  have hsegK : segment ℝ a x ⊆ 𝒦'.complex.space := by
    rw [hsubdiv.space_eq, hsegHull]
    exact 𝒦.complex.convexHull_subset_space hax
  have hsegC : IsCompact (segment ℝ a x) := by
    rw [hsegHull]
    exact ({a, x} : Finset Ea).finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hVs : {r : Ea | ({r} : Finset Ea) ∈ 𝒦'.complex.faces ∧ r ∈ segment ℝ a x}.Finite := by
    refine (Set.Finite.preimage Finset.singleton_injective.injOn
      (𝒦'.finite_faces_inter_of_isCompact hsegC hsegK)).subset ?_
    rintro r ⟨hr, hrs⟩
    exact ⟨hr, r, by simp, hrs⟩
  have hgseg : ∀ r ∈ segment ℝ a x, ∃ l ∈ Icc (0 : ℝ) 1, r = a + l • (x - a) ∧ g (r - a) = l := by
    intro r hr
    rw [segment_eq_image'] at hr
    obtain ⟨l, hl, hrl⟩ := hr
    beta_reduce at hrl
    refine ⟨l, hl, hrl.symm, ?_⟩
    rw [← hrl, add_sub_cancel_left, map_smul, hg, smul_eq_mul, mul_one]
  have hgpos : ∀ r ∈ segment ℝ a x, r ≠ a → 0 < g (r - a) := by
    intro r hr hra
    obtain ⟨l, hl, hrl, hgl⟩ := hgseg r hr
    rw [hgl]
    rcases hl.1.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hra
      rw [hrl, ← heq, zero_smul, add_zero]
  have hx1 : ({x} : Finset Ea) ∈ 𝒦'.complex.faces :=
    hsubdiv.singleton_mem (𝒦.complex.down_closed hax
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self x)))
      (Finset.singleton_nonempty x))
  have hxs : x ∈ segment ℝ a x := right_mem_segment ℝ a x
  have hxa' : x ≠ a := fun hxa' => hxt (hxa' ▸ hat)
  have hxF : h (𝒦.map x) ∈ F :=
    hF (vidx x hx1 hxs) (hnotinc x hxs hxa')
      (hcore' (vidx x hx1 hxs) (hnotinc x hxs hxa') (hbody x hx1 hxs))
  have hmain : ∀ n : ℕ, ∀ r (hr : ({r} : Finset Ea) ∈ 𝒦'.complex.faces)
      (hrs : r ∈ segment ℝ a x), r ≠ a →
      {r' | (({r'} : Finset Ea) ∈ 𝒦'.complex.faces ∧ r' ∈ segment ℝ a x) ∧
        g (r - a) < g (r' - a)}.ncard ≤ n →
      h (𝒦.map r) ∈ connectedComponentIn F (h (𝒦.map x)) := by
    intro n
    induction n with
    | zero =>
      intro r hr hrs hra hcount
      by_cases hrx : r = x
      · rw [hrx]
        exact mem_connectedComponentIn hxF
      · exfalso
        obtain ⟨r', hpair, -, hr's, hlt⟩ :=
          𝒦.exists_pair_mem_faces_lt_of_mem_segment 𝒦' hsubdiv hax g hg hr hrs hrx
        have hr'1 : ({r'} : Finset Ea) ∈ 𝒦'.complex.faces :=
          𝒦'.complex.down_closed hpair (by simp) (Finset.singleton_nonempty r')
        have hfin : {r' | (({r'} : Finset Ea) ∈ 𝒦'.complex.faces ∧ r' ∈ segment ℝ a x) ∧
            g (r - a) < g (r' - a)}.Finite := hVs.subset fun r' hr' => hr'.1
        have hpos := (Set.ncard_pos hfin).mpr ⟨r', ⟨hr'1, hr's⟩, hlt⟩
        omega
    | succ n ih =>
      intro r hr hrs hra hcount
      by_cases hrx : r = x
      · rw [hrx]
        exact mem_connectedComponentIn hxF
      · obtain ⟨r', hpair, hr'r, hr's, hlt⟩ :=
          𝒦.exists_pair_mem_faces_lt_of_mem_segment 𝒦' hsubdiv hax g hg hr hrs hrx
        have hr'1 : ({r'} : Finset Ea) ∈ 𝒦'.complex.faces :=
          𝒦'.complex.down_closed hpair (by simp) (Finset.singleton_nonempty r')
        have hr'a : r' ≠ a := by
          intro hr'a
          have h0 : g (r' - a) = 0 := by rw [hr'a, sub_self, map_zero]
          have := hgpos r hrs hra
          linarith
        have hcount' : {r'' | (({r''} : Finset Ea) ∈ 𝒦'.complex.faces ∧
            r'' ∈ segment ℝ a x) ∧ g (r' - a) < g (r'' - a)}.ncard ≤ n := by
          have hssub : {r'' | (({r''} : Finset Ea) ∈ 𝒦'.complex.faces ∧
              r'' ∈ segment ℝ a x) ∧ g (r' - a) < g (r'' - a)} ⊂
              {r'' | (({r''} : Finset Ea) ∈ 𝒦'.complex.faces ∧ r'' ∈ segment ℝ a x) ∧
                g (r - a) < g (r'' - a)} := by
            refine ⟨fun r'' hr'' => ⟨hr''.1, hlt.trans hr''.2⟩, fun hsup => ?_⟩
            exact lt_irrefl _ (hsup ⟨⟨hr'1, hr's⟩, hlt⟩).2
          have := Set.ncard_lt_ncard hssub (hVs.subset fun r'' hr'' => hr''.1)
          omega
        have hIH := ih r' hr'1 hr's hr'a hcount'
        rw [connectedComponentIn_eq hIH]
        have hpairseg : convexHull ℝ (({r, r'} : Finset Ea) : Set Ea) ⊆ segment ℝ a x := by
          refine convexHull_min ?_ (convex_segment a x)
          rw [Finset.coe_insert, Finset.coe_singleton]
          exact insert_subset hrs (singleton_subset_iff.mpr hr's)
        let e : Section34EdgeIndex 𝒦 𝒦' :=
          ⟨{r, r'}, hpair, Finset.card_pair hr'r.symm, hΓ {r, r'} hpairseg⟩
        have hne : vidx r hr hrs ≠ vidx r' hr'1 hr's := by
          intro heq
          have := congrArg Subtype.val heq
          exact hr'r (Finset.singleton_injective this).symm
        exact hstep (vidx r hr hrs) (vidx r' hr'1 hr's) e
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self r {r'}))
          (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem
            (Finset.mem_singleton_self r')))
          hne (hnotinc r hrs hra) (hnotinc r' hr's hr'a) _ (hbody r hr hrs) _
          (hbody r' hr'1 hr's)
  exact hmain _ q hq hqs hqa le_rfl

open Classical in
theorem section34Exterior_component (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    {fbl : Section34SimplexIndex 𝒦 3 → Set M₂} (hfblc : ∀ s, IsClosed (fbl s))
    (hfblV : ∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
      ¬ Section34Incident w.1 s.1 → fbl s ∩ section34VertexBallImage src f₁ w = ∅)
    (hfblS : ∀ s : Section34SimplexIndex 𝒦 3,
      fbl s ⊆ h '' (𝒦.map '' ⋃ v ∈ s.1, openStar 𝒦.complex v))
    (t : Section34SimplexIndex 𝒦 4) (w : Section34VertexIndex 𝒦 𝒦')
    (hwt : ¬ Section34Incident w.1 t.1) {y : M₂} (hy : y ∈ h '' simplexBody 𝒦' w.1)
    (hyH : y ∈ H t.1) :
    y ∉ section34TetraObstacle (section34VertexBallImage src f₁) fbl t ∧
      (connectedComponentIn (H t.1 \ section34TetraObstacle (section34VertexBallImage src f₁)
        fbl t) y ∩ frontier (H t.1)).Nonempty := by
  obtain ⟨hK, hsubdiv, hmap, hcell, -⟩ := id hcut
  obtain ⟨hcarrier, hHU, -, -, hHcell, -⟩ := id hctrl
  obtain ⟨-, -, hf₁, -, -, hcore, -⟩ := id hgraph
  obtain ⟨Ob, hOb⟩ : ∃ Ob, Ob = section34TetraObstacle (section34VertexBallImage src f₁) fbl t :=
    ⟨_, rfl⟩
  rw [← hOb]
  have hNV : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34Label.vertexBall v)) v
  have hinc_trans : ∀ (w' : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
      Section34Incident w'.1 s.1 → Section34Incident s.1 t.1 → Section34Incident w'.1 t.1 :=
    fun w' s h1 h2 => h1.trans (convexHull_min h2 (convex_convexHull ℝ _))
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp w.2.2.1
  have hpw : p ∈ (w.1 : Set Ea) := by
    rw [hp]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
  have hyp : y = h (𝒦.map p) := by
    obtain ⟨_, ⟨p', hp', rfl⟩, rfl⟩ := hy
    rw [hp, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hp'
    rw [hp', hmap]
  have hyint : y ∈ interior (f₁ '' src (.vertexBall w)) := hcore w hy
  have hyOb : y ∉ Ob := by
    rw [hOb]
    rintro (hyV | hyF)
    · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hyV
      have hne : w ≠ x.1.2 := by
        intro hwx
        apply hwt
        rw [hwx, ← hx]
        exact x.2
      exact (eq_empty_iff_forall_notMem.mp
        (interior_image_vertexBall_inter_image_vertexBall hcut hgraph hne)) y ⟨hyint, hyx⟩
    · obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hyF
      have hns : ¬ Section34Incident w.1 s.1 := fun hws => hwt (hinc_trans w s hws hs)
      exact (eq_empty_iff_forall_notMem.mp (hfblV s w hns)) y ⟨hys, interior_subset hyint⟩
  refine ⟨hyOb, ?_⟩
  have hVfin : {w' : Section34VertexIndex 𝒦 𝒦' | Section34Incident w'.1 t.1}.Finite := by
    have htK : convexHull ℝ (t.1 : Set Ea) ⊆ 𝒦'.complex.space := by
      rw [hsubdiv.space_eq]
      exact 𝒦.complex.convexHull_subset_space t.2.1
    have hfin := 𝒦'.finite_faces_inter_of_isCompact
      (t.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)) htK
    refine Set.Finite.of_finite_image (f := fun w' : Section34VertexIndex 𝒦 𝒦' => w'.1)
      (hfin.subset ?_) Subtype.val_injective.injOn
    rintro _ ⟨w', hw', rfl⟩
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp w'.2.2.1
    have hqw : q ∈ (w'.1 : Set Ea) := by
      rw [hq]
      exact Finset.mem_coe.mpr (Finset.mem_singleton_self q)
    exact ⟨w'.2.1, q, subset_convexHull ℝ _ hqw,
      (show Section34Incident w'.1 t.1 from hw') hqw⟩
  have hPfin : {x : Section34PatchIndex 𝒦 𝒦' | x.1.1 = t}.Finite := by
    refine Set.Finite.of_finite_image (f := fun x : Section34PatchIndex 𝒦 𝒦' => x.1.2)
      (hVfin.subset ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      change Section34Incident x.1.2.1 t.1
      have hx' : x.1.1 = t := hx
      rw [← hx']
      exact x.2
    · intro x hx x' hx' hxx
      have h1 : x.1.1 = t := hx
      have h2 : x'.1.1 = t := hx'
      exact Subtype.ext (Prod.ext (h1.trans h2.symm) hxx)
  have hObc : IsClosed Ob := by
    rw [hOb]
    refine IsClosed.union ?_ ?_
    · exact hPfin.isClosed_biUnion fun x _ =>
        ((hcell (.vertexBall x.1.2)).isCompact.image_of_continuousOn
          (hf₁.continuousOn.mono (hNV _))).isClosed
    · exact (finite_setOf_section34Incident t).isClosed_biUnion fun s _ => hfblc s
  have : LocallyPathConnectedSpace M₂ :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M₂
  have hZo : IsOpen (connectedComponentIn Obᶜ y) := hObc.isOpen_compl.connectedComponentIn
  have hHc : IsClosed (H t.1) := (hHcell t.1 t.2.1).isCompact.isClosed
  by_cases hZH : connectedComponentIn Obᶜ y ⊆ interior (H t.1)
  · exfalso
    have hhU : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
    have hΦcont : ContinuousOn (fun z => h (𝒦.map z)) 𝒦.complex.space :=
      hhU.comp 𝒦.continuousOn fun z hz => 𝒦.bijOn.mapsTo hz
    have hΦinj : InjOn (fun z => h (𝒦.map z)) 𝒦.complex.space := by
      intro z hz z' hz' hzz
      have hinj := @hh.injective ⟨𝒦.map z, 𝒦.bijOn.mapsTo hz⟩ ⟨𝒦.map z', 𝒦.bijOn.mapsTo hz'⟩ hzz
      exact 𝒦.bijOn.injOn hz hz' (congrArg Subtype.val hinj)
    have hObOt : Ob ⊆ (fun z => h (𝒦.map z)) '' (⋃ v ∈ t.1, openStar 𝒦.complex v) := by
      rw [hOb]
      refine union_subset (iUnion₂_subset fun x hx => ?_) (iUnion₂_subset fun s hs => ?_)
      · have hinc : Section34Incident x.1.2.1 t.1 := by
          rw [← hx]
          exact x.2
        obtain ⟨q, hq⟩ := Finset.card_eq_one.mp x.1.2.2.2.1
        have hqw : q ∈ (x.1.2.1 : Set Ea) := by
          rw [hq]
          exact Finset.mem_coe.mpr (Finset.mem_singleton_self q)
        have hqt : q ∈ convexHull ℝ (t.1 : Set Ea) := hinc hqw
        obtain ⟨σ, hσ, hqσ⟩ :=
          exists_face_mem_openSimplex 𝒦.complex (𝒦.complex.convexHull_subset_space t.2.1 hqt)
        have hσt := face_subset_of_mem_openSimplex_of_mem_convexHull _ hσ t.2.1 hqσ hqt
        obtain ⟨a, haσ⟩ := 𝒦.complex.nonempty_of_mem_faces hσ
        have ha : ({a} : Finset Ea) ∈ 𝒦.complex.faces :=
          𝒦.complex.down_closed hσ (Finset.singleton_subset_iff.mpr haσ)
            (Finset.singleton_nonempty a)
        have hwa : (x.1.2.1 : Set Ea) ⊆ openStar 𝒦.complex a := by
          rw [hq, Finset.coe_singleton, singleton_subset_iff]
          exact ⟨𝒦.complex.convexHull_subset_space t.2.1 hqt,
            notMem_avoidingUnion_of_mem_openSimplex _ hσ hqσ haσ⟩
        have hsub := image_vertexBall_subset_image_openStar hh hcut hctrl hgraph x.1.2 ha hwa
        intro z hz
        obtain ⟨_, ⟨z', hz', rfl⟩, rfl⟩ := hsub hz
        exact ⟨z', mem_iUnion₂.mpr ⟨a, hσt haσ, hz'⟩, rfl⟩
      · intro z hz
        obtain ⟨_, ⟨z', hz', rfl⟩, rfl⟩ := hfblS s hz
        obtain ⟨v, hv, hz'v⟩ := mem_iUnion₂.mp hz'
        have hvt : v ∈ t.1 := mem_of_mem_convexHull_of_singleton_mem _
          (𝒦.complex.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hv)
            (Finset.singleton_nonempty v)) t.2.1 (hs (Finset.mem_coe.mpr hv))
        exact ⟨z', mem_iUnion₂.mpr ⟨v, hvt, hz'v⟩, rfl⟩
    have hK0 : ∀ z ∈ 𝒦.complex.space, z ∉ (⋃ v ∈ t.1, openStar 𝒦.complex v) →
        h (𝒦.map z) ∉ Ob := by
      intro z hz hzO hzOb
      obtain ⟨z', hz', hzz'⟩ := hObOt hzOb
      have hz'K : z' ∈ 𝒦.complex.space := by
        obtain ⟨v, -, hz'v⟩ := mem_iUnion₂.mp hz'
        exact hz'v.1
      have hzz := hΦinj hz'K hz hzz'
      rw [hzz] at hz'
      exact hzO hz'
    have hface0 : ∀ τ ∈ 𝒦.complex.faces, (∀ u ∈ τ, u ∉ t.1) →
        (fun z => h (𝒦.map z)) '' convexHull ℝ (τ : Set Ea) ⊆ Obᶜ := by
      rintro τ hτ hτt _ ⟨z, hz, rfl⟩
      refine hK0 z (𝒦.complex.convexHull_subset_space hτ hz) fun hzO => ?_
      obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hzO
      obtain ⟨ρ, hρ, hzρ⟩ := exists_face_mem_openSimplex 𝒦.complex hzv.1
      have hρτ := face_subset_of_mem_openSimplex_of_mem_convexHull _ hρ hτ hzρ hz
      have hvρ : v ∈ ρ := by
        by_contra hvρ
        exact hzv.2 (mem_iUnion₂.mpr ⟨ρ, ⟨hρ, hvρ⟩, openSimplex_subset_convexHull ρ hzρ⟩)
      exact hτt v (hρτ hvρ) hv
    have hfaceZ : ∀ τ ∈ 𝒦.complex.faces, (∀ u ∈ τ, u ∉ t.1) →
        ∀ z ∈ convexHull ℝ (τ : Set Ea), h (𝒦.map z) ∈ connectedComponentIn Obᶜ y →
        (fun z => h (𝒦.map z)) '' convexHull ℝ (τ : Set Ea) ⊆ connectedComponentIn Obᶜ y := by
      intro τ hτ hτt z hz hzZ
      have hconn : IsPreconnected ((fun z => h (𝒦.map z)) '' convexHull ℝ (τ : Set Ea)) :=
        (convex_convexHull ℝ _).isPreconnected.image _
          (hΦcont.mono (𝒦.complex.convexHull_subset_space hτ))
      rw [connectedComponentIn_eq hzZ]
      exact hconn.subset_connectedComponentIn ⟨z, hz, rfl⟩ (hface0 τ hτ hτt)
    have hG : ∀ τ ∈ 𝒦.complex.faces, ∀ u ∈ τ, ∀ u' ∈ τ, u ∉ t.1 → u' ∉ t.1 →
        u ∈ {u | h (𝒦.map u) ∈ connectedComponentIn Obᶜ y} →
        u' ∈ {u | h (𝒦.map u) ∈ connectedComponentIn Obᶜ y} := by
      intro τ hτ u hu u' hu' hut hu't huG
      have hτ₀ : τ.filter (· ∉ t.1) ∈ 𝒦.complex.faces :=
        𝒦.complex.down_closed hτ (Finset.filter_subset _ _)
          ⟨u, Finset.mem_filter.mpr ⟨hu, hut⟩⟩
      have hsubZ := hfaceZ _ hτ₀ (fun v hv => (Finset.mem_filter.mp hv).2) u
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hu, hut⟩))) huG
      exact hsubZ ⟨u', subset_convexHull ℝ _
        (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hu', hu't⟩)), rfl⟩
    obtain ⟨R, hR⟩ : ∃ R : Set Ea, ∀ z, z ∈ R ↔ z ∈ 𝒦.complex.space ∧
        ∃ τ ∈ 𝒦.complex.faces, z ∈ openSimplex τ ∧ ∃ u ∈ τ, u ∉ t.1 ∧
          u ∈ {u | h (𝒦.map u) ∈ connectedComponentIn Obᶜ y} :=
      ⟨{z | z ∈ 𝒦.complex.space ∧ ∃ τ ∈ 𝒦.complex.faces, z ∈ openSimplex τ ∧ ∃ u ∈ τ,
        u ∉ t.1 ∧ u ∈ {u | h (𝒦.map u) ∈ connectedComponentIn Obᶜ y}}, fun z => Iff.rfl⟩
    obtain ⟨hRt, hRo, hRc⟩ := 𝒦.isOpen_preimage_of_carrier_class t.2.1 hG hR
    obtain ⟨C, hRC, hCR, hCcl⟩ :=
      𝒦.exists_isClopen_of_isClopen_sdiff_convexHull hK t.2.1 t.2.2 hRt hRo hRc
    have hCint : ∀ z ∈ C, z ∈ 𝒦.complex.space → h (𝒦.map z) ∈ interior (H t.1) := by
      intro z hzC hzK
      rcases hCR hzC with hzR | hzt
      · obtain ⟨-, τ, hτ, hzτ, u, huτ, hut, huG⟩ := (hR z).mp hzR
        by_cases hτt : ∃ v ∈ τ, v ∈ t.1
        · obtain ⟨v, hvτ, hvt⟩ := hτt
          apply hcarrier t.1 t.2.1
          refine image_mono (image_openStar_subset_section34CarrierSupport hvt)
            ⟨𝒦.map z, ⟨z, ?_, rfl⟩, rfl⟩
          exact ⟨hzK, notMem_avoidingUnion_of_mem_openSimplex _ hτ hzτ hvτ⟩
        · have hτt' : ∀ v ∈ τ, v ∉ t.1 := fun v hv hvt => hτt ⟨v, hv, hvt⟩
          exact hZH (hfaceZ τ hτ hτt' u (subset_convexHull ℝ _ (Finset.mem_coe.mpr huτ)) huG
            ⟨z, openSimplex_subset_convexHull τ hzτ, rfl⟩)
      · obtain ⟨ρ, hρ, hzρ⟩ := exists_face_mem_openSimplex 𝒦.complex hzK
        have hρt := face_subset_of_mem_openSimplex_of_mem_convexHull _ hρ t.2.1 hzρ hzt
        obtain ⟨v, hv⟩ := 𝒦.complex.nonempty_of_mem_faces hρ
        apply hcarrier t.1 t.2.1
        refine image_mono (image_openStar_subset_section34CarrierSupport (hρt hv))
          ⟨𝒦.map z, ⟨z, ?_, rfl⟩, rfl⟩
        exact ⟨hzK, notMem_avoidingUnion_of_mem_openSimplex _ hρ hzρ hv⟩
    have hpK : p ∈ 𝒦.complex.space := by
      rw [← hsubdiv.space_eq]
      exact 𝒦'.complex.convexHull_subset_space w.2.1 (subset_convexHull ℝ _ hpw)
    have hpt : p ∉ convexHull ℝ (t.1 : Set Ea) := fun hpt => hwt fun z hz => by
      rw [hp, Finset.coe_singleton, mem_singleton_iff] at hz
      rw [hz]
      exact hpt
    obtain ⟨σ, hσ, hpσ⟩ := exists_face_mem_openSimplex 𝒦.complex hpK
    have hyZ : h (𝒦.map p) ∈ connectedComponentIn Obᶜ y := by
      rw [← hyp]
      exact mem_connectedComponentIn hyOb
    have hpR : p ∈ R := by
      refine (hR p).mpr ⟨hpK, σ, hσ, hpσ, ?_⟩
      by_cases hσt : ∃ v ∈ σ, v ∈ t.1
      · obtain ⟨a, haσ, hat⟩ := hσt
        obtain ⟨x, hxσ, hxt⟩ : ∃ x ∈ σ, x ∉ t.1 := by
          by_contra hcon
          apply hpt
          refine convexHull_mono (Finset.coe_subset.mpr fun v hv => ?_)
            (openSimplex_subset_convexHull σ hpσ)
          by_contra hvt
          exact hcon ⟨v, hv, hvt⟩
        have hσcard : σ.card ≤ 2 := by
          have hpΓ : 𝒦.map p ∈ graphSkeletonSpace 𝒦 := by
            apply w.2.2.2
            exact ⟨p, subset_convexHull ℝ _ hpw, by rw [hmap]⟩
          obtain ⟨e, ⟨he, he2⟩, p', hp', hpp'⟩ := mem_iUnion₂.mp hpΓ
          have hp'K : p' ∈ 𝒦.complex.space := 𝒦.complex.convexHull_subset_space he hp'
          have hpp : p' = p := 𝒦.bijOn.injOn hp'K hpK hpp'
          rw [hpp] at hp'
          exact (Finset.card_le_card
            (face_subset_of_mem_openSimplex_of_mem_convexHull _ hσ he hpσ hp')).trans he2
        have hxa : x ≠ a := fun hxa => hxt (hxa ▸ hat)
        have hσeq : σ = {a, x} := by
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro v hv
            rcases Finset.mem_insert.mp hv with hv | hv
            · rw [hv]
              exact haσ
            · rw [Finset.mem_singleton.mp hv]
              exact hxσ
          · rw [Finset.card_pair hxa.symm]
            exact hσcard
        have haxK : ({a, x} : Finset Ea) ∈ 𝒦.complex.faces := hσeq ▸ hσ
        have hps : p ∈ segment ℝ a x := by
          have hpσ' := openSimplex_subset_convexHull σ hpσ
          rwa [hσeq, Finset.coe_insert, Finset.coe_singleton, convexHull_pair] at hpσ'
        have hpa : p ≠ a := fun hpa =>
          hpt (hpa ▸ subset_convexHull ℝ _ (Finset.mem_coe.mpr hat))
        have hp1 : ({p} : Finset Ea) ∈ 𝒦'.complex.faces := by
          rw [← hp]
          exact w.2.1
        have hF : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 t.1 →
            f₁ '' (src (.vertexBall u) \ ⋃ (w' : Section34VertexIndex 𝒦 𝒦')
              (_ : Section34Incident w'.1 t.1), src (.vertexBall w')) ⊆ Obᶜ := by
          rintro u hu _ ⟨q, ⟨hqV, hqX⟩, rfl⟩ hqOb
          rw [hOb] at hqOb
          rcases hqOb with hqV' | hqF
          · obtain ⟨x', hx', q', hq', hqq'⟩ := mem_iUnion₂.mp hqV'
            have hqq : q' = q := hf₁.injOn (hNV _ hq') (hNV u hqV) hqq'
            apply hqX
            refine mem_iUnion₂.mpr ⟨x'.1.2, ?_, hqq ▸ hq'⟩
            rw [← hx']
            exact x'.2
          · obtain ⟨s, hs, hqs⟩ := mem_iUnion₂.mp hqF
            have hns : ¬ Section34Incident u.1 s.1 := fun hus => hu (hinc_trans u s hus hs)
            exact (eq_empty_iff_forall_notMem.mp (hfblV s u hns)) _ ⟨hqs, q, hqV, rfl⟩
        have hchain :=
          image_mem_connectedComponentIn_of_mem_segment hcut hgraph hF haxK hat hxt hp1 hps hpa
        refine ⟨x, hxσ, hxt, ?_⟩
        change h (𝒦.map x) ∈ connectedComponentIn Obᶜ y
        have hxF : h (𝒦.map x) ∈ Obᶜ := connectedComponentIn_nonempty_iff.mp ⟨_, hchain⟩
        rw [hyp, ← connectedComponentIn_eq hchain]
        exact mem_connectedComponentIn hxF
      · have hσt' : ∀ v ∈ σ, v ∉ t.1 := fun v hv hvt => hσt ⟨v, hv, hvt⟩
        obtain ⟨u, hu⟩ := 𝒦.complex.nonempty_of_mem_faces hσ
        refine ⟨u, hu, hσt' u hu, ?_⟩
        change h (𝒦.map u) ∈ connectedComponentIn Obᶜ y
        exact hfaceZ σ hσ hσt' p (openSimplex_subset_convexHull σ hpσ) hyZ
          ⟨u, subset_convexHull ℝ _ (Finset.mem_coe.mpr hu), rfl⟩
    let k : 𝒦.complex.space → U := fun z => ⟨𝒦.map z, 𝒦.bijOn.mapsTo z.2⟩
    have hk : IsEmbedding k := 𝒦.isEmbedding.codRestrict U fun z => 𝒦.bijOn.mapsTo z.2
    let E : 𝒦.complex.space → M₂ := U.domRestrict h ∘ k
    have hE : IsEmbedding E := hh.comp hk
    have hrange : H t.1 ⊆ range E := by
      intro z hz
      obtain ⟨u₀, hu₀U, rfl⟩ := hHU t.1 t.2.1 hz
      obtain ⟨z', hz'K, hz'u⟩ := 𝒦.bijOn.surjOn hu₀U
      exact ⟨⟨z', hz'K⟩, congrArg h hz'u⟩
    have hHpre : IsPreconnected (E ⁻¹' H t.1) := by
      rw [← hE.isInducing.isPreconnected_image, image_preimage_eq_of_subset hrange]
      exact (hHcell t.1 t.2.1).isConnected.isPreconnected
    have hpH : E ⟨p, hpK⟩ ∈ H t.1 := by
      change h (𝒦.map p) ∈ H t.1
      rw [← hyp]
      exact hyH
    have hEC : E ⁻¹' H t.1 ⊆ (Subtype.val : 𝒦.complex.space → Ea) ⁻¹' C :=
      hHpre.subset_isClopen hCcl ⟨⟨p, hpK⟩, hpH, hRC hpR⟩
    have hHint : H t.1 ⊆ interior (H t.1) := by
      intro z hz
      obtain ⟨⟨z', hz'K⟩, rfl⟩ := hrange hz
      exact hCint z' (hEC hz) hz'K
    obtain ⟨P, r, v, hr, hv, hS, hB⟩ := hHcell t.1 t.2.1
    have hx0 : (Pi.single (0 : Fin (3 + 1)) (1 : ℝ)) ∈ stdSimplexBoundary 3 :=
      ⟨Convexity.StdSimplex.single_mem_coordinateSet ℝ _, 1, by simp⟩
    have hb : v (r (Pi.single 0 1)) ∈ frontier (H t.1) := by
      rw [hB]
      exact ⟨_, ⟨_, hx0, rfl⟩, rfl⟩
    exact hb.2 (hHint (hHc.frontier_subset hb))
  · obtain ⟨z, hzZ, hzH⟩ := not_subset.mp hZH
    have hZpath : IsPathConnected (connectedComponentIn Obᶜ y) :=
      hZo.isConnected_iff_isPathConnected.mp (isConnected_connectedComponentIn_iff.mpr hyOb)
    have hjoin : JoinedIn Obᶜ y z :=
      (hZpath.joinedIn y (mem_connectedComponentIn hyOb) z hzZ).mono
        (connectedComponentIn_subset _ _)
    rw [sdiff_eq]
    exact exists_mem_frontier_connectedComponentIn_of_joinedIn hHc hyH hzH hjoin

theorem section34Exterior_of_subset (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    {fbl : Section34SimplexIndex 𝒦 3 → Set M₂} (hfblc : ∀ s, IsClosed (fbl s))
    (hfblH : ∀ (s : Section34SimplexIndex 𝒦 3) (t : Section34SimplexIndex 𝒦 4),
      Section34Incident s.1 t.1 → fbl s ⊆ interior (H t.1))
    (hfblV : ∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
      ¬ Section34Incident w.1 s.1 → fbl s ∩ section34VertexBallImage src f₁ w = ∅)
    (hfblS : ∀ s : Section34SimplexIndex 𝒦 3,
      fbl s ⊆ h '' (𝒦.map '' ⋃ v ∈ s.1, openStar 𝒦.complex v)) :
    Section34Exterior 𝒦 𝒦' h H (section34VertexBallImage src f₁) fbl :=
  ⟨fun t => section34TetraObstacle_subset_interior hh hcut hctrl hgraph t fun s hs => hfblH s t hs,
    (id hgraph).2.2.2.2.2.1,
    fun t w hwt _ hy hyH =>
      section34Exterior_component hh hcut hctrl hgraph hfblc hfblV hfblS t w hwt hy hyH⟩

end Frames

end DifferentialGeometry.Topology.PiecewiseLinear
