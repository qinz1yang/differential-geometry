import DifferentialGeometry.Topology.Manifold.OneManifold.SmoothCompactOneDomainBCF

/-!
# Components of a compact one-dimensional set with half charts, WITHOUT a common base (lane S-BCF03)

`SmoothCompactOneDomain_BCF` (the shared `K₃` kernel) needs ONE one-dimensional base `Bs` in
which every half chart is relatively open: that is the right datum for the slim base, but not for a
curve `Γ` of a TWO-dimensional base with corners (the extension of a half chart beyond an endpoint
is not part of any natural one-dimensional base). The charts of `HalfChart_BCF.toChart` and their
coordinate changes do not use `Bs`; this file gives each chart its own base `T ∪ π '' W` and
records only what BCF03's partition needs (topological, no smoothness of the parametrizations):

* `HalfChart_BCF.ofData_BCF`: a half chart of `T` from raw data with `π '' W ⊆ O`
  (base `T ∪ π '' W`);
* `contDiffOn_transition_two_BCF`: smooth coordinate changes between half charts with different
  bases;
* **`exists_components_of_halfCharts_BCF`**: a compact `T ⊆ H` with a half chart at every point
  (each with its own base) is a finite disjoint union of arcs (injective, continuous on `[0, 1]`)
  and loops (continuous injective on the circle), each relatively open in `T`; the points whose
  chart coordinate vanishes are exactly the two endpoints of every arc and none on a loop.
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

open DifferentialGeometry.Topology.Manifold.OneManifold

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **A half chart from raw data** (base `T ∪ π '' W`, so `relOpen` and `mem` are automatic). -/
def HalfChart_BCF.ofData_BCF {T : Set H} (L : H →L[ℝ] ℝ) (κ : ℝ) (π : ℝ → H) (W V : Set ℝ)
    (O : Set H) (hW : IsOpen W) (hV : IsOpen V) (hVW : V ⊆ W) (hsm : ContDiffOn ℝ ∞ π W)
    (hcoord : ∀ t ∈ W, L (π t) + κ = t) (hπO : π '' W ⊆ O) (hO : IsOpen O)
    (hTO : T ∩ O = π '' (V ∩ Ici 0)) : HalfChart_BCF (T ∪ π '' W) T where
  L := L
  κ := κ
  π := π
  W := W
  V := V
  O := O
  isOpen_W := hW
  isOpen_V := hV
  V_subset := hVW
  smooth := hsm
  coord := hcoord
  mem := fun t ht => Or.inr ⟨t, ht, rfl⟩
  relOpen := ⟨O, hO, by
    ext z
    constructor
    · rintro ⟨hzO, hzB⟩
      rcases hzB with hzT | hzπ
      · obtain ⟨t, ht, rfl⟩ : z ∈ π '' (V ∩ Ici 0) := hTO ▸ ⟨hzT, hzO⟩
        exact ⟨t, hVW ht.1, rfl⟩
      · exact hzπ
    · rintro ⟨t, ht, rfl⟩
      exact ⟨hπO ⟨t, ht, rfl⟩, Or.inr ⟨t, ht, rfl⟩⟩⟩
  isOpen_O := hO
  inter_eq := hTO

namespace HalfChart_BCF

/-- **Smooth coordinate changes between half charts with different bases.** -/
theorem contDiffOn_transition_two_BCF {Bs Bs' T : Set H} (d : HalfChart_BCF Bs T)
    (d' : HalfChart_BCF Bs' T) (y₀ y₀' : T) :
    ContDiffOn ℝ ∞ ((𝓡∂ 1) ∘ ((d.toChart y₀).symm ≫ₕ d'.toChart y₀') ∘ (𝓡∂ 1).symm)
      ((𝓡∂ 1).symm ⁻¹' ((d.toChart y₀).symm ≫ₕ d'.toChart y₀').source ∩ range (𝓡∂ 1)) := by
  have hsingle : ContDiff ℝ ∞ (fun r : ℝ => EuclideanSpace.single (0 : Fin 1) r) := by
    have h : (fun r : ℝ => EuclideanSpace.single (0 : Fin 1) r) =
        fun r => r • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
      funext r
      ext i
      fin_cases i
      simp
    rw [h]
    exact contDiff_id.smul contDiff_const
  have hg : ContDiffOn ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin 1) =>
        EuclideanSpace.single (0 : Fin 1) (d'.L (d.π (x 0)) + d'.κ))
      {x | x 0 ∈ d.W} :=
    hsingle.comp_contDiffOn ((d'.L.contDiff.comp_contDiffOn d.contDiffOn_π_comp_BCF).add
      contDiffOn_const)
  refine (hg.mono ?_).congr ?_
  · rintro x ⟨hx, hxr⟩
    have h1 : ((𝓡∂ 1).symm x).val 0 ∈ d.V := hx.1
    rw [val_symm_of_mem_range_BCF hxr] at h1
    exact d.V_subset h1
  · rintro x ⟨hx, hxr⟩
    have hval := val_symm_of_mem_range_BCF hxr
    have htgt : (𝓡∂ 1).symm x ∈ (d.toChart y₀).target := hx.1
    have hz := d.toChart_symm_apply_val y₀ htgt
    rw [hval] at hz
    have hzO : (((d.toChart y₀).symm ((𝓡∂ 1).symm x) : T) : H) ∈ d'.O := hx.2
    have hnn := d'.coord_nonneg_BCF ((d.toChart y₀).symm ((𝓡∂ 1).symm x)).2 hzO
    rw [hz] at hnn
    change (𝓡∂ 1) (halfPt (d'.L (((d.toChart y₀).symm ((𝓡∂ 1).symm x) : T) : H) + d'.κ)) = _
    rw [hz, model_halfPt hnn]

end HalfChart_BCF

/-- **Components of a compact set with half charts (each with its own base).** -/
theorem exists_components_of_halfCharts_BCF {T : Set H} (hT : IsCompact T) (Bs : T → Set H)
    (d : ∀ y : T, HalfChart_BCF (Bs y) T) (hd : ∀ y : T, (y : H) ∈ (d y).O) :
    ∃ (n m : ℕ) (a : Fin n → ℝ → H) (l : Fin m → Circle → H),
      (∀ k, ContinuousOn (a k) (Icc 0 1) ∧ InjOn (a k) (Icc 0 1)) ∧
      (∀ j, Continuous (l j) ∧ Injective (l j)) ∧
      (∀ k k', k ≠ k' → Disjoint (a k '' Icc 0 1) (a k' '' Icc 0 1)) ∧
      (∀ j j', j ≠ j' → Disjoint (range (l j)) (range (l j'))) ∧
      (∀ k j, Disjoint (a k '' Icc 0 1) (range (l j))) ∧
      T = (⋃ k, a k '' Icc 0 1) ∪ ⋃ j, range (l j) ∧
      (∀ k, ∃ G : Set H, IsOpen G ∧ G ∩ T = a k '' Icc 0 1) ∧
      (∀ j, ∃ G : Set H, IsOpen G ∧ G ∩ T = range (l j)) ∧
      (∀ k, ∀ y : T, (y : H) ∈ a k '' Icc 0 1 →
        ((d y).L y + (d y).κ = 0 ↔ (y : H) = a k 0 ∨ (y : H) = a k 1)) ∧
      (∀ j, ∀ y : T, (y : H) ∈ range (l j) → 0 < (d y).L y + (d y).κ) := by
  classical
  let cs : ChartedSpace (EuclideanHalfSpace 1) T :=
    { atlas := range fun y : T => (d y).toChart y
      chartAt := fun y => (d y).toChart y
      mem_chart_source := hd
      chart_mem_atlas := fun y => ⟨y, rfl⟩ }
  let _ : ChartedSpace (EuclideanHalfSpace 1) T := cs
  have hA : ∀ e ∈ atlas (EuclideanHalfSpace 1) T, ∃ y : T, e = (d y).toChart y := by
    rintro e ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  have : IsManifold (𝓡∂ 1) ∞ T := by
    apply isManifold_of_contDiffOn
    intro e e' he he'
    obtain ⟨y, rfl⟩ := hA e he
    obtain ⟨y', rfl⟩ := hA e' he'
    exact (d y).contDiffOn_transition_two_BCF (d y') y y'
  have : CompactSpace T := isCompact_iff_compactSpace.mp hT
  obtain ⟨hfin, hcls⟩ := finite_connectedComponents_and_Icc_or_circle (M := T)
  have hsurj : Surjective (ConnectedComponents.mk : T → ConnectedComponents T) :=
    ConnectedComponents.surjective_coe
  choose rep hrep using hsurj
  set U : ConnectedComponents T → TopologicalSpace.Opens T :=
    fun c => componentOpens (rep c) with hU
  have memU_iff : ∀ (c : ConnectedComponents T) (y : T), y ∈ U c ↔
      (y : ConnectedComponents T) = c := fun c y => by
    change y ∈ connectedComponent (rep c) ↔ _
    rw [← ConnectedComponents.coe_eq_coe' (α := T), hrep c]
  have memU : ∀ y : T, y ∈ U (y : ConnectedComponents T) := fun y => (memU_iff _ y).mpr rfl
  -- the chart coordinate of a point decides interior / boundary
  have hcoord : ∀ y : T, (𝓡∂ 1).IsInteriorPoint y ↔ 0 < (d y).L y + (d y).κ := fun y => by
    have hmem : (d y).toChart y ∈ atlas (EuclideanHalfSpace 1) T :=
      chart_mem_atlas (EuclideanHalfSpace 1) y
    have hsrc : y ∈ ((d y).toChart y).source := mem_chart_source (EuclideanHalfSpace 1) y
    rw [isInteriorPoint_iff_coord_pos hmem hsrc, (d y).toChart_val_zero_BCF y (hd y)]
  have hnn : ∀ y : T, 0 ≤ (d y).L y + (d y).κ := fun y => (d y).coord_nonneg_BCF y.2 (hd y)
  have hdisjU : ∀ c c' : ConnectedComponents T, c ≠ c' →
      Disjoint (Subtype.val '' (U c : Set T)) (Subtype.val '' (U c' : Set T)) := by
    intro c c' hcc'
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
    have hy'y : y' = y := Subtype.ext hyy'
    subst hy'y
    exact hcc' (((memU_iff c y').mp hy).symm.trans ((memU_iff c' y').mp hy'))
  set P : ConnectedComponents T → Prop :=
    fun c => Nonempty (U c ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Icc (0 : ℝ) 1) with hP
  have hcirc : ∀ c, ¬ P c → Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ U c) := fun c h =>
    (hcls (rep c)).resolve_left h
  have : Finite (ConnectedComponents T) := hfin
  set eA := (Finite.equivFin {c // P c}).symm with heA
  set eL := (Finite.equivFin {c // ¬ P c}).symm with heL
  let φ : ∀ c : {c // P c}, Icc (0 : ℝ) 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ U c.1 :=
    fun c => (Classical.choice c.2).symm
  let ψ : ∀ c : {c // ¬ P c}, Circle ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ U c.1 :=
    fun c => Classical.choice (hcirc c.1 c.2)
  let arc : Fin (Nat.card {c // P c}) → ℝ → H := fun k t =>
    (((φ (eA k)) (projIcc 0 1 zero_le_one t) : T) : H)
  let loop : Fin (Nat.card {c // ¬ P c}) → Circle → H := fun j z =>
    (((ψ (eL j)) z : T) : H)
  have harc_img : ∀ k, arc k '' Icc 0 1 = Subtype.val '' (U (eA k).1 : Set T) := by
    intro k
    ext y
    constructor
    · rintro ⟨t, -, rfl⟩
      exact ⟨((φ (eA k)) (projIcc 0 1 zero_le_one t) : T), ((φ (eA k)) _).2, rfl⟩
    · rintro ⟨y', hy', rfl⟩
      refine ⟨((φ (eA k)).symm ⟨y', hy'⟩).val, ((φ (eA k)).symm ⟨y', hy'⟩).2, ?_⟩
      change (((φ (eA k)) (projIcc 0 1 zero_le_one ((φ (eA k)).symm ⟨y', hy'⟩).val) : T) : H) = y'
      rw [projIcc_val, Diffeomorph.apply_symm_apply]
  have hloop_img : ∀ j, range (loop j) = Subtype.val '' (U (eL j).1 : Set T) := by
    intro j
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨((ψ (eL j)) z : T), ((ψ (eL j)) z).2, rfl⟩
    · rintro ⟨y', hy', rfl⟩
      exact ⟨(ψ (eL j)).symm ⟨y', hy'⟩, by
        change (((ψ (eL j)) ((ψ (eL j)).symm ⟨y', hy'⟩) : T) : H) = y'
        rw [Diffeomorph.apply_symm_apply]⟩
  have hopen : ∀ c : ConnectedComponents T, ∃ G : Set H, IsOpen G ∧
      G ∩ T = Subtype.val '' (U c : Set T) := by
    intro c
    obtain ⟨G, hG, hGU⟩ := isOpen_induced_iff.mp (U c).isOpen
    refine ⟨G, hG, ?_⟩
    ext w
    constructor
    · rintro ⟨hwG, hwT⟩
      refine ⟨⟨w, hwT⟩, ?_, rfl⟩
      rw [← hGU] at *
      exact hwG
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ (U c : Set T) := hy
      rw [← hGU] at hy'
      exact ⟨hy', y.2⟩
  have hcarrier : T = (⋃ k, arc k '' Icc 0 1) ∪ ⋃ j, range (loop j) := by
    ext y
    constructor
    · intro hyT
      set q : T := ⟨y, hyT⟩
      by_cases hPc : P (q : ConnectedComponents T)
      · refine Or.inl (mem_iUnion.mpr ⟨eA.symm ⟨_, hPc⟩, ?_⟩)
        rw [harc_img, Equiv.apply_symm_apply]
        exact ⟨q, memU q, rfl⟩
      · refine Or.inr (mem_iUnion.mpr ⟨eL.symm ⟨_, hPc⟩, ?_⟩)
        rw [hloop_img, Equiv.apply_symm_apply]
        exact ⟨q, memU q, rfl⟩
    · rintro (hy | hy)
      · obtain ⟨k, t, -, rfl⟩ := mem_iUnion.mp hy
        exact ((φ (eA k)) (projIcc 0 1 zero_le_one t) : T).2
      · obtain ⟨j, z, rfl⟩ := mem_iUnion.mp hy
        exact ((ψ (eL j)) z : T).2
  refine ⟨Nat.card {c // P c}, Nat.card {c // ¬ P c}, arc, loop, ?_, ?_, ?_, ?_, ?_, hcarrier,
    ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨?_, ?_⟩
    · have h1 : Continuous fun t : ℝ => (φ (eA k)) (projIcc 0 1 zero_le_one t) :=
        (φ (eA k)).continuous.comp continuous_projIcc
      exact (continuous_subtype_val.comp (continuous_subtype_val.comp h1)).continuousOn
    · intro s hs t ht hst
      have h1 : (φ (eA k)) (projIcc 0 1 zero_le_one s) = (φ (eA k)) (projIcc 0 1 zero_le_one t) :=
        Subtype.ext (Subtype.ext hst)
      have h2 := (φ (eA k)).injective h1
      rw [projIcc_of_mem _ hs, projIcc_of_mem _ ht] at h2
      exact congrArg Subtype.val h2
  · intro j
    refine ⟨continuous_subtype_val.comp (continuous_subtype_val.comp (ψ (eL j)).continuous), ?_⟩
    intro z z' h
    exact (ψ (eL j)).injective (Subtype.ext (Subtype.ext h))
  · intro k k' hkk'
    rw [harc_img, harc_img]
    exact hdisjU _ _ fun h => hkk' (eA.injective (Subtype.ext h))
  · intro j j' hjj'
    rw [hloop_img, hloop_img]
    exact hdisjU _ _ fun h => hjj' (eL.injective (Subtype.ext h))
  · intro k j
    rw [harc_img, hloop_img]
    exact hdisjU _ _ fun h => (eL j).2 (h ▸ (eA k).2)
  · intro k
    rw [harc_img]
    exact hopen _
  · intro j
    rw [hloop_img]
    exact hopen _
  · intro k y hy
    rw [harc_img] at hy
    obtain ⟨y', hy'U, hy'⟩ := hy
    have hyy : y' = y := Subtype.ext hy'
    subst hyy
    have hmemU : y' ∈ U (eA k).1 := hy'U
    have hb : (𝓡∂ 1).IsInteriorPoint y' ↔ ¬ ((φ (eA k)).symm ⟨y', hmemU⟩ = ⊥ ∨
        (φ (eA k)).symm ⟨y', hmemU⟩ = ⊤) := by
      rw [← mem_boundary_iff_of_Icc_BCF (φ (eA k)) (p := ⟨y', hmemU⟩)]
      have h1 : ((⟨y', hmemU⟩ : U (eA k).1) ∈ (𝓡∂ 1).boundary (U (eA k).1)) ↔
          y' ∈ (𝓡∂ 1).boundary T := by
        rw [ModelWithCorners.boundary_open]
        exact Iff.rfl
      have h2 : (𝓡∂ 1).IsInteriorPoint y' ↔ y' ∈ (𝓡∂ 1).interior T := Iff.rfl
      rw [h1, h2, ← (𝓡∂ 1).compl_boundary]
      exact Iff.rfl
    have hz : (d y').L y' + (d y').κ = 0 ↔ ¬ (𝓡∂ 1).IsInteriorPoint y' := by
      rw [hcoord]
      constructor
      · intro h h2
        linarith
      · intro h
        exact le_antisymm (not_lt.mp fun h2 => h h2) (hnn y')
    rw [hz, hb, not_not]
    have h0 : (⊥ : Icc (0 : ℝ) 1) = projIcc 0 1 zero_le_one 0 := projIcc_zero_one_BCF.1.symm
    have h1 : (⊤ : Icc (0 : ℝ) 1) = projIcc 0 1 zero_le_one 1 := projIcc_zero_one_BCF.2.symm
    constructor
    · rintro (h | h)
      · left
        change (y' : H) = (((φ (eA k)) (projIcc 0 1 zero_le_one 0) : T) : H)
        rw [← h0, ← h, Diffeomorph.apply_symm_apply]
      · right
        change (y' : H) = (((φ (eA k)) (projIcc 0 1 zero_le_one 1) : T) : H)
        rw [← h1, ← h, Diffeomorph.apply_symm_apply]
    · rintro (h | h)
      · left
        have h2 : (⟨y', hmemU⟩ : U (eA k).1) = (φ (eA k)) (projIcc 0 1 zero_le_one 0) :=
          Subtype.ext (Subtype.ext h)
        rw [h2, Diffeomorph.symm_apply_apply, ← h0]
      · right
        have h2 : (⟨y', hmemU⟩ : U (eA k).1) = (φ (eA k)) (projIcc 0 1 zero_le_one 1) :=
          Subtype.ext (Subtype.ext h)
        rw [h2, Diffeomorph.symm_apply_apply, ← h1]
  · intro j y hy
    rw [hloop_img] at hy
    obtain ⟨y', hy'U, hy'⟩ := hy
    have hyy : y' = y := Subtype.ext hy'
    subst hyy
    have hb := boundary_eq_empty_of_circle_BCF (ψ (eL j))
    have hp : (⟨y', hy'U⟩ : U (eL j).1) ∈ (𝓡∂ 1).interior (U (eL j).1) := by
      rw [← (𝓡∂ 1).compl_boundary, hb]
      exact Set.notMem_empty _
    rw [ModelWithCorners.interior_open] at hp
    exact (hcoord y').mp hp

end DifferentialGeometry.Topology
