import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalSeamCrosscuts
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalAnnuli
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ReturningArcComponent
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnermostLateralCap
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskArcSide

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem IsCylindricalDiagram.seam_sides_of_subset_lateral
    {f : E × ℝ → F} {P Q : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (hQP : Q ⊆ P)
    (hJQ : J ⊆ f '' (Q ×ˢ Icc (0 : ℝ) 1)) {a : ℝ} (ha : 0 < a)
    (hseam : ∀ y ∈ J ∩ f '' (P ×ˢ ({1} : Set ℝ)),
      y ∈ closure (J ∩ f '' (P ×ˢ Ioo a 1)) ∧
      y ∈ closure (J \ f '' (P ×ˢ Icc a 1))) :
    ∀ y ∈ J ∩ f '' (Q ×ˢ ({1} : Set ℝ)),
      y ∈ closure (J ∩ f '' (Q ×ˢ Ioo a 1)) ∧
      y ∈ closure (J \ f '' (Q ×ˢ Icc a 1)) := by
  have hin : J ∩ f '' (P ×ˢ Ioo a 1) ⊆ J ∩ f '' (Q ×ˢ Ioo a 1) := by
    rintro y ⟨hyJ, x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hJQ hyJ
    have hzx' : z = x := by
      rcases hf.eq_or_endpoints z ⟨hQP hz.1, hz.2⟩ x
        ⟨hx.1, (ha.trans hx.2.1).le, hx.2.2.le⟩ hzx with h | h | h
      · exact h
      · exact (hx.2.2.ne h.2).elim
      · exact ((ha.trans hx.2.1).ne' h.2).elim
    exact ⟨hyJ, x, ⟨hzx' ▸ hz.1, hx.2⟩, rfl⟩
  have hout : J \ f '' (P ×ˢ Icc a 1) ⊆ J \ f '' (Q ×ˢ Icc a 1) :=
    sdiff_subset_sdiff_right (image_mono (prod_mono_left hQP))
  intro y hy
  obtain ⟨hyi, hyo⟩ := hseam y
    ⟨hy.1, image_mono (prod_mono_left hQP) hy.2⟩
  exact ⟨closure_mono hin hyi, closure_mono hout hyo⟩

theorem IsCylindricalDiagram.exists_empty_source_returning_bigon
    {f : E × ℝ → F} {P : Set E} {S J : Set F} {r : (Fin 3 → ℝ) → E}
    (hf : IsCylindricalDiagram f P S)
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    (hJ : IsPLSphere 1 J) (hJS : J ⊆ f '' ((r '' stdSimplexBoundary 2) ×ˢ Icc 0 1))
    (hseam : ∀ a ∈ Ioo (0 : ℝ) 1,
      ∀ y ∈ J ∩ f '' ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ)),
        y ∈ closure (J ∩ f '' ((r '' stdSimplexBoundary 2) ×ˢ Ioo a 1)) ∧
        y ∈ closure (J \ f '' ((r '' stdSimplexBoundary 2) ×ˢ Icc a 1)))
    {A₀ : Set (E × ℝ)} {γ : ℝ → E × ℝ}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A₀) {η : ℝ} (hη : η ∈ Ioo (0 : ℝ) 1)
    (hγside : A₀ ⊆ (r '' stdSimplexBoundary 2) ×ˢ Ioc η 1)
    (hγJ : MapsTo f A₀ J)
    (hγends : A₀ ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ)) = {γ 0, γ 1}) :
    ∃ (a : ℝ) (D A B : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ) (δ : ℝ → E × ℝ),
      a ∈ Ioo (0 : ℝ) η ∧ IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D ∧
      IsPLHomeomorphOn δ (Icc 0 1) A ∧ IsPLBall 1 B ∧
      D ⊆ (r '' stdSimplexBoundary 2) ×ˢ Ioc a 1 ∧
      q '' stdSimplexBoundary 2 = A ∪ B ∧
      D ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ)) = B ∧
      D ∩ f ⁻¹' J = A ∧ A ∩ B = {δ 0, δ 1} := by
  classical
  let Z := r '' stdSimplexBoundary 2
  have hZ : IsPLSphere 1 Z := hr.isPLSphere_image_stdSimplexBoundary
  have hZP : Z ⊆ P := (image_mono fun _ hx => hx.1).trans hr.image_eq.subset
  have hside := hf.restrict_base_of_eq_ends hZ.isPolyhedron hZP hends
  obtain ⟨a, L, ha, hLfin, hL, hcard, hreg, -, -⟩ :=
    hside.exists_finite_regular_slice hZ.isPolyhedron hJ
      (a := η / 4) (b := η / 2) (by linarith [hη.1]) (by linarith [hη.1])
      (by linarith [hη.2]) (Or.inl (by linarith [hη.1]))
  let _ : Finite L.faces := hLfin.to_subtype
  have ha0 : 0 < a := by linarith [ha.1, hη.1]
  have haη : a < η := by linarith [ha.2, hη.1]
  have ha1 : a < 1 := haη.trans hη.2
  have hγ0 : γ 0 ∈ A₀ := hγ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hγ1 : γ 1 ∈ A₀ := hγ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hγtop (t : ℝ) (ht : t = 0 ∨ t = 1) : γ t ∈ Z ×ˢ ({1} : Set ℝ) := by
    apply (hγends.symm.subset ?_).2
    rcases ht with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hmeet : (J ∩ f '' (Z ×ˢ ({1} : Set ℝ))).Nonempty :=
    ⟨f (γ 0), hγJ hγ0, γ 0, hγtop 0 (Or.inl rfl), rfl⟩
  obtain ⟨C, hCfin, hCdis, hcover, hC⟩ :=
    hside.exists_source_crosscut_partition_of_regular_upper_strip hZ.isPolyhedron hJ hJS L
      (by linarith [hη.1]) ha.1 ha.2 (by linarith [hη.2]) hL hcard hreg
      (hseam a ⟨ha0, ha1⟩) hmeet
  let _ : Finite C := hCfin.to_subtype
  have hcharts : ∀ T ∈ C, ∃ δ : ℝ → E × ℝ,
      IsPLHomeomorphOn δ (Icc 0 1) T ∧ T ∩ (Z ×ˢ ({a, 1} : Set ℝ)) = {δ 0, δ 1} := by
    intro T hTC
    obtain ⟨q, hq, hqb⟩ := hC T hTC
    obtain ⟨δ, hδ, hδb⟩ := exists_isPLHomeomorphOn_Icc_of_stdSimplex_one hq hqb
    exact ⟨δ, hδ, hδb.symm⟩
  have hsub : ∀ T ∈ C, T ⊆ (Z ×ˢ Icc a 1) ∩ f ⁻¹' J :=
    fun T hT x hx => hcover.subset (mem_sUnion.mpr ⟨T, hT, hx⟩)
  have hA₀C : A₀ ∈ C := by
    apply exists_member_eq_of_arc_between_partition_boundary_marks hCfin hCdis hcharts hγ
    · intro x hx
      exact hcover.symm.subset
        ⟨⟨(hγside hx).1, haη.le.trans (hγside hx).2.1.le, (hγside hx).2.2⟩, hγJ hx⟩
    · exact ⟨(hγtop 0 (Or.inl rfl)).1, Or.inr (hγtop 0 (Or.inl rfl)).2⟩
    · exact ⟨(hγtop 1 (Or.inr rfl)).1, Or.inr (hγtop 1 (Or.inr rfl)).2⟩
  choose δ hδ hδb using fun T : C => hcharts T.1 T.2
  have hendsC (T : C) : T.1 ∩ ((P ×ˢ ({a} : Set ℝ)) ∪ Z ×ˢ ({1} : Set ℝ)) =
      {δ T 0, δ T 1} := by
    rw [← hδb T]
    ext x
    constructor
    · rintro ⟨hxT, hx | hx⟩
      · exact ⟨hxT, (hsub T.1 T.2 hxT).1.1, Or.inl hx.2⟩
      · exact ⟨hxT, hx.1, Or.inr hx.2⟩
    · rintro ⟨hxT, hxZ, hx | hx⟩
      · exact ⟨hxT, Or.inl ⟨hZP hxZ, hx⟩⟩
      · exact ⟨hxT, Or.inr ⟨hxZ, hx⟩⟩
  have hreturn : ∃ T : C, Disjoint T.1 (P ×ˢ ({a} : Set ℝ)) := by
    refine ⟨⟨A₀, hA₀C⟩, disjoint_left.mpr ?_⟩
    intro x hx hxbase
    have ht : x.2 = a := hxbase.2
    linarith [(hγside hx).2.1]
  obtain ⟨T, D, B, q, hq, hB, hDZ, hqbd, hDtop, hDtrace, -⟩ :=
    exists_innermost_disk_of_lateral_arc_family hr ha1 hδ
      (fun T => (hsub T.1 T.2).trans inter_subset_left) hendsC
      (fun A B hne => hCdis A.2 B.2 (fun h => hne (Subtype.ext h))) hreturn
  have htrace : D ∩ f ⁻¹' J = T.1 := by
    have heq : (⋃ T : C, T.1) = (Z ×ˢ Icc a 1) ∩ f ⁻¹' J := by
      rw [← hcover]
      ext x
      simp
    rw [heq] at hDtrace
    refine (show D ∩ f ⁻¹' J = D ∩ ((Z ×ˢ Icc a 1) ∩ f ⁻¹' J) from ?_).trans hDtrace
    ext x
    exact ⟨fun h => ⟨h.1, ⟨(hDZ h.1).1, (hDZ h.1).2.1.le, (hDZ h.1).2.2⟩, h.2⟩,
      fun h => ⟨h.1, h.2.2⟩⟩
  have hTD : T.1 ⊆ D := htrace ▸ inter_subset_left
  have hTAB : T.1 ∩ B = {δ T 0, δ T 1} := by
    rw [← hδb T, ← hDtop]
    ext x
    constructor
    · rintro ⟨hxT, -, hxZ, hx1⟩
      exact ⟨hxT, hxZ, Or.inr hx1⟩
    · rintro ⟨hxT, hxZ, hxa | hx1⟩
      · exact ((hDZ (hTD hxT)).2.1.ne' hxa).elim
      · exact ⟨hxT, hTD hxT, hxZ, hx1⟩
  exact ⟨a, D, T.1, B, q, δ T, ⟨ha0, haη⟩, hq, hδ T, hB, hDZ,
    hqbd, hDtop, htrace, hTAB⟩

theorem IsCylindricalDiagram.exists_empty_returning_bigon
    {f : E × ℝ → F} {P : Set E} {S J : Set F} {r : (Fin 3 → ℝ) → E}
    (hf : IsCylindricalDiagram f P S)
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P)
    (hends : ∀ x ∈ P, f (x, 0) = f (x, 1))
    (hJ : IsPLSphere 1 J) (hJS : J ⊆ f '' ((r '' stdSimplexBoundary 2) ×ˢ Icc 0 1))
    (hseam : ∀ a ∈ Ioo (0 : ℝ) 1,
      ∀ y ∈ J ∩ f '' ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ)),
        y ∈ closure (J ∩ f '' ((r '' stdSimplexBoundary 2) ×ˢ Ioo a 1)) ∧
        y ∈ closure (J \ f '' ((r '' stdSimplexBoundary 2) ×ˢ Icc a 1)))
    {A₀ : Set (E × ℝ)} {γ : ℝ → E × ℝ}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A₀) {η : ℝ} (hη : η ∈ Ioo (0 : ℝ) 1)
    (hγside : A₀ ⊆ (r '' stdSimplexBoundary 2) ×ˢ Ioc η 1)
    (hγJ : MapsTo f A₀ J)
    (hγends : A₀ ∩ ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ)) = {γ 0, γ 1}) :
    ∃ (D : Set F) (q : (Fin 3 → ℝ) → F) (x y : F),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D ∧
      D ⊆ f '' ((r '' stdSimplexBoundary 2) ×ˢ Icc 0 1) ∧
      IsPLBall 1 (D ∩ J) ∧
      IsPLBall 1 (D ∩ f '' ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ))) ∧
      x ≠ y ∧ D ∩ (J ∩ f '' ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ))) = {x, y} ∧
      q '' stdSimplexBoundary 2 =
        (D ∩ J) ∪ (D ∩ f '' ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ))) := by
  obtain ⟨a, D, A, B, q, δ, ha, hq, hδ, hB, hDZ, hqbd, hDtop, hDJ, hAB⟩ :=
    hf.exists_empty_source_returning_bigon hr hends hJ hJS hseam hγ hη hγside hγJ hγends
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  have hZP : r '' stdSimplexBoundary 2 ⊆ P :=
    (image_mono fun _ hx => hx.1).trans hr.image_eq.subset
  have ha1 : a < 1 := ha.2.trans hη.2
  have hstrip := hf.isPLHomeomorphOn_strip hP.isPolyhedron ha.1.le le_rfl (Or.inl ha.1)
  have hDstrip : D ⊆ P ×ˢ Icc a 1 :=
    hDZ.trans (prod_mono hZP Ioc_subset_Icc_self)
  have hAD : A ⊆ D := hDJ ▸ inter_subset_left
  have hBD : B ⊆ D := hDtop ▸ inter_subset_left
  have hA : IsPLBall 1 A := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hδ
  have hD : IsPLBall 2 D := ⟨q, hq⟩
  have hmapD := hstrip.restrict hD.isPolyhedron hDstrip
  have hmapA := hstrip.restrict hA.isPolyhedron (hAD.trans hDstrip)
  have hmapB := hstrip.restrict hB.isPolyhedron (hBD.trans hDstrip)
  have htopstrip : (r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ) ⊆ P ×ˢ Icc a 1 :=
    fun _ h => ⟨hZP h.1, by rw [h.2]; exact ⟨ha1.le, le_rfl⟩⟩
  have htraceJ : f '' D ∩ J = f '' A := by rw [← image_inter_preimage, hDJ]
  have htraceTop : f '' D ∩ f '' ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ)) =
      f '' B := by
    rw [← hstrip.bijOn.injOn.image_inter hDstrip htopstrip, hDtop]
  have hδ0 : δ 0 ∈ A := hδ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
  have hδ1 : δ 1 ∈ A := hδ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hxy : f (δ 0) ≠ f (δ 1) := by
    intro h
    have hh := hmapA.bijOn.injOn hδ0 hδ1 h
    exact zero_ne_one (hδ.bijOn.injOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ hh)
  refine ⟨f '' D, f ∘ q, f (δ 0), f (δ 1), hq.trans hmapD, ?_, ?_, ?_, hxy, ?_, ?_⟩
  · exact image_mono (hDZ.trans (prod_mono_right
      (fun _ ht => ⟨ha.1.le.trans ht.1.le, ht.2⟩)))
  · rw [htraceJ]
    exact hA.of_isPLHomeomorphOn hmapA
  · rw [htraceTop]
    exact hB.of_isPLHomeomorphOn hmapB
  · have heq : f '' D ∩ (J ∩ f '' ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ))) =
        (f '' D ∩ J) ∩ (f '' D ∩ f '' ((r '' stdSimplexBoundary 2) ×ˢ ({1} : Set ℝ))) := by
      ext z
      simp only [mem_inter_iff]
      tauto
    rw [heq, htraceJ, htraceTop, ← hstrip.bijOn.injOn.image_inter
      (hAD.trans hDstrip) (hBD.trans hDstrip), hAB, image_pair]
  · rw [image_comp, hqbd, image_union, htraceJ, htraceTop]

end DifferentialGeometry.Topology.PiecewiseLinear
