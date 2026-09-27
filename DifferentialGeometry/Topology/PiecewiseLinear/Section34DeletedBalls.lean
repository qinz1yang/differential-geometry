/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ConfinedTubePiercingConditions

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

theorem exists_section34DeletedBalls [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34ConfinedTubePiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Sp Tp cnt Pg G)
    (hone : ∀ e, cnt e = 1)
    (hcore : ∀ w, h '' Kcore w ⊆ interior (G w '' Cp w)) :
    ∃ (Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
      (Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂),
      (∀ w, Dv w = G w '' Cp w \
        ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
          interior (G (ends e).1 '' Cp (ends e).1)) ∧
        (∀ w, IsPLCellOn 3 (Dv w) (DvBd w)) ∧
        (∀ e, IsPLCellOn 2 (Dd e) (DdBd e)) ∧
        (∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e) ∧
        (∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2) ∧
        (∀ w, h '' simplexBody 𝒦' w.1 ⊆ interior (Dv w)) ∧
        (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦) := by
  let _ := hU
  let _ := hh
  let _ := hN
  let _ := hQlf
  let _ : T2Space M₁ := inferInstance
  let _ : SecondCountableTopology M₁ := inferInstance
  let _ : SecondCountableTopology M₂ := inferInstance
  let _ : HasGroupoid M₁ (plGroupoid 3) := inferInstance
  let _ : FiniteDimensional ℝ Ea := inferInstance
  obtain ⟨-, -, -, -, hCp, -, -, -, hends, -, -, -, -, -, hAa, hBb, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, hKc, hΓ, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, hbd, hAb, -, -, hGCp, -, -, -, -, -, hcnt, hPg, -, -, hover,
    hbody⟩ := hpack
  have hB : ∀ w, IsPLCellOn 3 (G w '' Cp w) (frontier (G w '' Cp w)) := by
    intro w
    have h1 := (hCp w).image (hGCp w)
    rw [h1.boundary_eq_frontier] at h1
    exact h1
  have hfr : ∀ w, frontier (G w '' Cp w) = G w '' CpBd w := fun w =>
    ((hCp w).image (hGCp w)).boundary_eq_frontier.symm
  have hfin : ∀ w, {e | (ends e).2 = w}.Finite := finite_splitDisk_of_section34CutFrame hframe
    (fun e => (ends e).2) (fun e => by rw [(hends e).2.2]; exact inter_subset_right)
  have hone' : ∀ e, 0 < cnt e := fun e => by rw [hone e]; exact zero_lt_one
  have hBC : ∀ e, frontier (G (ends e).2 '' Cp (ends e).2) ∩
      frontier (G (ends e).1 '' Cp (ends e).1) = Pg e 0 := by
    intro e
    have hAaC : Aa e ⊆ CpBd (ends e).1 := by rw [(hAa e).1]; exact inter_subset_left
    rw [hfr, hfr, inter_comm]
    apply Subset.antisymm
    · intro z hz
      have hz' := (hbd e hz).1
      have hzU : z ∈ ⋃ i < cnt e, Pg e i := by
        rw [← (hcnt e).2]
        exact ⟨image_mono sdiff_subset hz'.1, image_mono sdiff_subset hz'.2⟩
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hzU
      rw [hone e, Nat.lt_one_iff] at hi
      subst hi
      exact hzi
    · intro z hz
      obtain ⟨-, hsub⟩ := hPg e 0 (hone' e)
      exact ⟨image_mono (sdiff_subset.trans hAaC) (hsub hz).1,
        image_mono (sdiff_subset.trans (hBb e).1) (hsub hz).2⟩
  obtain ⟨s₀, hs₀⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hann : ∀ e, (∃ a ∈ Ab₀ e, a ∈ CpBd (ends e).1) ∧ ∃ b ∈ Ab₁ e, b ∈ CpBd (ends e).1 := by
    intro e
    obtain ⟨hAeq, φ, h0, h1⟩ := hAa e
    have hsub : Aa e ⊆ CpBd (ends e).1 := by rw [hAeq]; exact inter_subset_left
    let q₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 :=
      (⟨s₀, hs₀⟩, ⟨0, left_mem_Icc.mpr zero_le_one⟩)
    let q₁ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 × Icc (0 : ℝ) 1 :=
      (⟨s₀, hs₀⟩, ⟨1, right_mem_Icc.mpr zero_le_one⟩)
    refine ⟨⟨(φ q₀ : M₁), ?_, hsub (φ q₀).2⟩, ⟨(φ q₁ : M₁), ?_, hsub (φ q₁).2⟩⟩
    · rw [h0]
      exact ⟨φ q₀, ⟨q₀, rfl, rfl⟩, rfl⟩
    · rw [h1]
      exact ⟨φ q₁, ⟨q₁, rfl, rfl⟩, rfl⟩
  have hin : ∀ e, (frontier (G (ends e).1 '' Cp (ends e).1) ∩
      interior (G (ends e).2 '' Cp (ends e).2)).Nonempty := by
    intro e
    obtain ⟨⟨a, ha0, haC⟩, -⟩ := hann e
    refine ⟨G (ends e).1 a, ?_, (hAb e).1 (mem_image_of_mem _ ha0)⟩
    rw [hfr]
    exact mem_image_of_mem _ haC
  have hout : ∀ e, ¬ frontier (G (ends e).1 '' Cp (ends e).1) ⊆
      G (ends e).2 '' Cp (ends e).2 := by
    intro e hsub
    obtain ⟨-, b, hb1, hbC⟩ := hann e
    have hbf : G (ends e).1 b ∈ frontier (G (ends e).1 '' Cp (ends e).1) := by
      rw [hfr]
      exact mem_image_of_mem _ hbC
    exact disjoint_left.mp (hAb e).2 (mem_image_of_mem _ hb1) (hsub hbf)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := isPLCellOn_sdiff_iUnion_interior_of_caps
    (B := fun w => G w '' Cp w) (C := fun e => Pg e 0)
    (Dv := fun w => G w '' Cp w \ ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
      interior (G (ends e).1 '' Cp (ends e).1))
    hB hfin (fun e => (hends e).1) (fun e => (hPg e 0 (hone' e)).1) hBC hin hout hover
    (fun _ => rfl)
  refine ⟨fun w => G w '' Cp w \ ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
      interior (G (ends e).1 '' Cp (ends e).1),
    fun w => frontier (G w '' Cp w \ ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
      interior (G (ends e).1 '' Cp (ends e).1)),
    fun e => frontier (G (ends e).1 '' Cp (ends e).1) ∩ G (ends e).2 '' Cp (ends e).2,
    fun e => Pg e 0, fun _ => rfl, h1, h2, h3, h4, fun w => ?_, ?_⟩
  · intro y hy
    refine h5 w ⟨hcore w (image_mono (hKc w).2.1 hy), fun hyU => ?_⟩
    obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hyU
    have hne' : w ≠ (ends e).1 := fun h' => (hends e).1 (h'.symm.trans he.symm)
    exact disjoint_left.mp (hbody w (ends e).1 hne') hy hye
  · rw [mem_nhdsSet_iff_forall]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, hxw⟩ := mem_iUnion.mp (hΓ hx)
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds (hcore w (mem_image_of_mem h hxw)))
      (interior_subset.trans (h6 w))

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
