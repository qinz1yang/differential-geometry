import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingIsotopy
import DifferentialGeometry.Topology.Manifold.DiffeomorphFamily

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

private theorem mem_of_mem_of_fixes_compl {ι : Type*} {U : ι → Set M}
    {i : ι} {D : Diffeomorph I I M M ∞} {y : M}
    (hfix : ∀ z ∉ U i, D z = z ∧ D.symm z = z) (hy : y ∈ U i) : D y ∈ U i := by
  by_contra hc
  have h2 : D.symm (D y) = D y := (hfix (D y) hc).2
  have h3 : D y = y := h2 ▸ Diffeomorph.symm_apply_apply D y
  exact hc (h3.symm ▸ hy)

theorem diffeomorphList_diagonal_apply_eq_of_forall_notMem {ι : Type*}
    (d : ι → ℝ → Diffeomorph I I M M ∞) (U : ι → Set M)
    (hfix : ∀ i t x, x ∉ U i → d i t x = x ∧ (d i t).symm x = x)
    (l : List ι) (t : ι → ℝ) {y : M} (hy : ∀ i ∈ l, y ∉ U i) :
    diffeomorphList d l t y = y := by
  revert hy
  induction l with
  | nil => intro hy; rfl
  | cons a rest ih =>
    intro hy
    change diffeomorphList d rest t ((d a (t a)) y) = y
    rw [(hfix a (t a) y (hy a (List.mem_cons.mpr (Or.inl rfl)))).1]
    exact ih (fun i hi ↦ hy i (List.mem_cons.mpr (Or.inr hi)))

theorem diffeomorphList_diagonal_one_apply_eq_of_disjoint_support {ι : Type*}
    (d : ι → ℝ → Diffeomorph I I M M ∞) (U : ι → Set M)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hfix : ∀ i t x, x ∉ U i → d i t x = x ∧ (d i t).symm x = x)
    (l : List ι) (hl : l.Nodup) {i : ι} (hi : i ∈ l) {y : M}
    (hy : ∀ j ∈ l, j ≠ i → y ∉ U j) :
    diffeomorphList d l (fun _ ↦ (1 : ℝ)) y = d i 1 y := by
  revert hl hi hy
  induction l with
  | nil => intro hl hi hy; exact absurd hi (by simp)
  | cons a rest ih =>
    intro hl hi hy
    have hn := List.nodup_cons.mp hl
    change diffeomorphList d rest (fun _ ↦ (1 : ℝ)) ((d a 1) y) = d i 1 y
    by_cases hai : a = i
    · rw [← hai] at hy ⊢
      refine diffeomorphList_diagonal_apply_eq_of_forall_notMem d U hfix rest
        (fun _ ↦ (1 : ℝ)) ?_
      intro j hj
      have hja : j ≠ a := fun h ↦ hn.1 (h ▸ hj)
      by_cases hya : y ∈ U a
      · exact Set.disjoint_left.mp (hdisj a j (Ne.symm hja))
          (mem_of_mem_of_fixes_compl (hfix a 1) hya)
      · rw [(hfix a 1 y hya).1]
        exact hy j (List.mem_cons.mpr (Or.inr hj)) hja
    · rw [(hfix a 1 y (hy a (List.mem_cons.mpr (Or.inl rfl)) hai)).1]
      have hinew : i ∈ rest := by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm hai
        · exact h
      exact ih hn.2 hinew (fun j hj hji ↦ hy j (List.mem_cons.mpr (Or.inr hj)) hji)

variable {ι : Type*} [Fintype ι]

theorem diffeomorphList_univ_diagonal_zero (d : ι → ℝ → Diffeomorph I I M M ∞)
    (hzero : ∀ i, d i 0 = Diffeomorph.refl I M ∞) :
    diffeomorphList d (Finset.univ : Finset ι).toList (fun _ ↦ (0 : ℝ)) =
      Diffeomorph.refl I M ∞ :=
  diffeomorphList_zero d hzero _

theorem contMDiff_diffeomorphList_univ_diagonal (d : ι → ℝ → Diffeomorph I I M M ∞)
    (hd : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ d i p.1 p.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M ↦
        diffeomorphList d (Finset.univ : Finset ι).toList (fun _ ↦ q.1) q.2) := by
  have hdiag : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ι → ℝ) ∞
      (fun q : ℝ × M ↦ (fun _ : ι ↦ q.1 : ι → ℝ)) := by
    rw [contMDiff_pi_space]
    exact fun _ ↦ contMDiff_fst
  exact (contMDiff_diffeomorphList d hd _).comp (hdiag.prodMk contMDiff_snd)

theorem contMDiff_diffeomorphList_univ_diagonal_symm (d : ι → ℝ → Diffeomorph I I M M ∞)
    (hdi : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M ↦ (d i p.1).symm p.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M ↦
        (diffeomorphList d (Finset.univ : Finset ι).toList (fun _ ↦ q.1)).symm q.2) := by
  have hdiag : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ι → ℝ) ∞
      (fun q : ℝ × M ↦ (fun _ : ι ↦ q.1 : ι → ℝ)) := by
    rw [contMDiff_pi_space]
    exact fun _ ↦ contMDiff_fst
  exact (contMDiff_diffeomorphList_symm d hdi _).comp (hdiag.prodMk contMDiff_snd)

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology

universe u

private abbrev E₃ := EuclideanSpace ℝ (Fin 3)

variable {M : ClosedOrientedManifold.{u} 3} {I : Type u} [Fintype I]

theorem BallMarking.isotopic_of_supportFamily (B B' : BallMarking M I)
    (J : I → ℝ → Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞)
    (U : I → Set M.Carrier)
    (hJ : ∀ i, ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × M.Carrier ↦ J i q.1 q.2))
    (hJi : ∀ i, ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun q : ℝ × M.Carrier ↦ (J i q.1).symm q.2))
    (hJ0 : ∀ i, J i 0 = Diffeomorph.refl (𝓡 3) M.Carrier ∞)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hfix : ∀ i t x, x ∉ U i → J i t x = x ∧ (J i t).symm x = x)
    (hU : ∀ i j, i ≠ j → ∀ x ∈ Metric.closedBall (0 : E₃) 2, (B.ball i).chart x ∉ U j)
    (hJ1 : ∀ i, ∀ x ∈ Metric.closedBall (0 : E₃) 2,
      J i 1 ((B.ball i).chart x) = (B'.ball i).chart x) :
    B.Isotopic B' := by
  refine ⟨fun t ↦ Manifold.diffeomorphList J (Finset.univ : Finset I).toList (fun _ ↦ t),
    Manifold.contMDiff_diffeomorphList_univ_diagonal J hJ,
    Manifold.contMDiff_diffeomorphList_univ_diagonal_symm J hJi,
    Manifold.diffeomorphList_univ_diagonal_zero J hJ0, ?_⟩
  intro i x hx
  have hmem : i ∈ (Finset.univ : Finset I).toList := Finset.mem_toList.mpr (Finset.mem_univ i)
  have hy : ∀ j ∈ (Finset.univ : Finset I).toList, j ≠ i → (B.ball i).chart x ∉ U j :=
    fun j _ hji ↦ hU i j (Ne.symm hji) x hx
  rw [Manifold.diffeomorphList_diagonal_one_apply_eq_of_disjoint_support J U hdisj hfix _
    (Finset.nodup_toList _) hmem hy]
  exact hJ1 i x hx

theorem BallMarking.transport_of_supportDiffeomorphFamily (B B' : BallMarking M I)
    (F : I → Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞) (U : I → Set M.Carrier)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hfix : ∀ i x, x ∉ U i → F i x = x ∧ (F i).symm x = x)
    (hU : ∀ i j, i ≠ j → ∀ x ∈ Metric.closedBall (0 : E₃) 2, (B.ball i).chart x ∉ U j)
    (hF1 : ∀ i, ∀ x ∈ Metric.closedBall (0 : E₃) 2,
      F i ((B.ball i).chart x) = (B'.ball i).chart x) :
    B.Transport B' := by
  refine ⟨Manifold.diffeomorphList (fun i _ ↦ F i) (Finset.univ : Finset I).toList
    (fun _ ↦ (1 : ℝ)), ?_⟩
  intro i x hx
  have hmem : i ∈ (Finset.univ : Finset I).toList := Finset.mem_toList.mpr (Finset.mem_univ i)
  have hy : ∀ j ∈ (Finset.univ : Finset I).toList, j ≠ i → (B.ball i).chart x ∉ U j :=
    fun j _ hji ↦ hU i j (Ne.symm hji) x hx
  rw [Manifold.diffeomorphList_diagonal_one_apply_eq_of_disjoint_support (fun i _ ↦ F i) U hdisj
    (fun i t x hx ↦ hfix i x hx) _ (Finset.nodup_toList _) hmem hy]
  exact hF1 i x hx

theorem BallMarking.transport_of_supportDiffeomorphFamily_refl (B : BallMarking M I) :
    B.Transport B :=
  B.transport_of_supportDiffeomorphFamily B (fun _ ↦ Diffeomorph.refl (𝓡 3) M.Carrier ∞)
    (fun _ ↦ ∅) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ ⟨rfl, rfl⟩)
    (fun _ _ _ _ _ ↦ by simp) (fun _ _ _ ↦ rfl)

theorem connectedBallMarkingIsotopy_of_supportFamily
    (h : ∀ (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier] (I : Type u) [Fintype I]
      (B B' : BallMarking M I),
      ∃ (J : I → ℝ → Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞)
        (U : I → Set M.Carrier),
        (∀ i, ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun q : ℝ × M.Carrier ↦ J i q.1 q.2)) ∧
        (∀ i, ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
          (fun q : ℝ × M.Carrier ↦ (J i q.1).symm q.2)) ∧
        (∀ i, J i 0 = Diffeomorph.refl (𝓡 3) M.Carrier ∞) ∧
        (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
        (∀ i t x, x ∉ U i → J i t x = x ∧ (J i t).symm x = x) ∧
        (∀ i j, i ≠ j → ∀ x ∈ Metric.closedBall (0 : E₃) 2,
          (B.ball i).chart x ∉ U j) ∧
        (∀ i, ∀ x ∈ Metric.closedBall (0 : E₃) 2,
          J i 1 ((B.ball i).chart x) = (B'.ball i).chart x)) :
    connectedBallMarkingIsotopy.{u} := by
  intro M _ I _ B B'
  obtain ⟨J, U, hJ, hJi, hJ0, hdisj, hfix, hU, hJ1⟩ := h M I B B'
  exact B.isotopic_of_supportFamily B' J U hJ hJi hJ0 hdisj hfix hU hJ1

theorem BallMarking.isotopic_of_supportFamily_refl (B : BallMarking M I) : B.Isotopic B :=
  B.isotopic_of_supportFamily B (fun _ _ ↦ Diffeomorph.refl (𝓡 3) M.Carrier ∞)
    (fun _ ↦ ∅)
    (fun _ ↦ contMDiff_snd) (fun _ ↦ contMDiff_snd) (fun _ ↦ rfl)
    (fun _ _ _ ↦ by simp) (fun _ _ _ _ ↦ ⟨rfl, rfl⟩) (fun _ _ _ _ _ ↦ by simp)
    (fun _ _ _ ↦ rfl)

end DifferentialGeometry.Topology
