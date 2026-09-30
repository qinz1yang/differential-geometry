import DifferentialGeometry.Topology.Engulfing.ProtectedPolyhedron
import DifferentialGeometry.Topology.Manifold.GeneralPosition.PuncturedCellConnectivity

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {M : Type*} [MetricSpace M] {n p : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem exists_enclosing_core_with_connectivity (hpn : p + 3 ≤ n)
    (eM : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    {j : EuclideanSpace ℝ (Fin n) → M} (hj : IsOpenEmbedding j)
    {B : Set M} (hB : IsCompact B) (hBU : B ⊆ range j) :
    ∃ C : Set M, IsCompact C ∧ B ⊆ C ∧ C ⊆ range j ∧
      NewmanConnectivity (Cᶜ : Set M) (Subtype.val ⁻¹' range j) p := by
  let oldCharts : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := inferInstance
  let allCharts : ChartedSpace (EuclideanSpace ℝ (Fin n)) M :=
    { atlas := univ
      chartAt := oldCharts.chartAt
      mem_chart_source := oldCharts.mem_chart_source
      chart_mem_atlas := fun _ => mem_univ _ }
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) M := allCharts
  have hpre : IsCompact (j ⁻¹' B) := hj.isEmbedding.isInducing.isCompact_preimage' hB hBU
  obtain ⟨R, hR, hnorm⟩ := hpre.isBounded.exists_pos_norm_le
  let r : ℝ := 2 * R
  have hr : 0 < r := by dsimp [r]; positivity
  let e : Disk n → M := fun x => j (r • x.1)
  have he : isChartDisk e := by
    refine ⟨(hj.toOpenPartialHomeomorph j).symm, 0, r, mem_univ _, hr, ?_, ?_⟩
    · change closedBall 0 r ⊆ (hj.toOpenPartialHomeomorph j).source
      rw [IsOpenEmbedding.toOpenPartialHomeomorph_source]
      exact subset_univ _
    · intro x
      change j (r • x.1) = (hj.toOpenPartialHomeomorph j) (0 + r • x.1)
      simp only [zero_add, IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  have heU : range e ⊆ range j := by
    rintro y ⟨x, rfl⟩
    exact ⟨r • x.1, rfl⟩
  let C := e '' halfDisk n
  have hBC : B ⊆ C := by
    intro y hy
    obtain ⟨x, rfl⟩ := hBU hy
    have hxnorm := hnorm x hy
    have hh : ‖r⁻¹ • x‖ ≤ (1 / 2 : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      apply (inv_mul_le_iff₀ hr).mpr
      dsimp [r]
      linarith
    have hxD : r⁻¹ • x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      mem_closedBall_zero_iff.mpr (hh.trans (by norm_num))
    refine ⟨⟨r⁻¹ • x, hxD⟩, hh, ?_⟩
    change j (r • r⁻¹ • x) = j x
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hCU : C ⊆ range j := (image_subset_range e _).trans heU
  have hCcompact : IsCompact C := he.isCompact_image_halfDisk
  have hnonempty : (Subtype.val ⁻¹' range j : Set (Cᶜ : Set M)).Nonempty := by
    let i : Fin n := ⟨0, by omega⟩
    let v : Disk n := ⟨EuclideanSpace.single i (1 : ℝ), by simp⟩
    have hvnorm : ‖(v : EuclideanSpace ℝ (Fin n))‖ = 1 := by simp [v]
    have hvC : e v ∉ C := by
      intro hv
      obtain ⟨w, hw, hew⟩ := hv
      have hwv : w = v := he.injective hew
      subst w
      change ‖(v : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2 at hw
      rw [hvnorm] at hw
      norm_num at hw
    exact ⟨⟨e v, hvC⟩, heU (mem_range_self v)⟩
  let : ContractibleSpace (range j) := hj.isEmbedding.toHomeomorph.symm.contractibleSpace
  let a : (Subtype.val ⁻¹' range j : Set (Cᶜ : Set M)) ≃ₜ (range j \ C : Set M) :=
    { toEquiv :=
        { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
          invFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨C, hCcompact, hBC, hCU, hnonempty, ?_, ?_⟩
  · intro k hk f
    exact he.nullhomotopic_map_compl_halfDisk_of_homotopyEquiv_sphere (by omega) eM f
  · intro k hk f
    let af : C((Subtype.val ⁻¹' range j : Set (Cᶜ : Set M)), (range j \ C : Set M)) :=
      ⟨a, a.continuous⟩
    let ai : C((range j \ C : Set M), (Subtype.val ⁻¹' range j : Set (Cᶜ : Set M))) :=
      ⟨a.symm, a.symm.continuous⟩
    have hnull := (he.nullhomotopic_sdiff_halfDisk_of_contractible (by omega) heU
      (af.comp f)).comp_right ai
    have heq : ai.comp (af.comp f) = f := by
      ext x
      rfl
    rwa [heq] at hnull

theorem exists_cell_engulfing_retaining_compact (hpn : p + 3 ≤ n)
    (eM : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (hnewman : ∀ C : Set M, relativeNewmanAt (Cᶜ : Set M) n p (p + 1))
    {u j : EuclideanSpace ℝ (Fin n) → M} (hu : IsOpenEmbedding u) (hj : IsOpenEmbedding j)
    {B : Set M} (hB : IsCompact B) (hBU : B ⊆ range u)
    (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hK : K.faces.Finite)
    (hdim : ∀ s ∈ K.faces, s.card ≤ p + 1) :
    ∃ v : EuclideanSpace ℝ (Fin n) → M,
      IsOpenEmbedding v ∧ B ⊆ range v ∧ j '' K.space ⊆ range v := by
  obtain ⟨C, hC, hBC, hCU, hconn⟩ := exists_enclosing_core_with_connectivity hpn eM hu hB hBU
  obtain ⟨H, hfix, hcover, _⟩ := exists_protected_chart_polyhedron_engulfing
    hC.isClosed hu.isOpen_range hCU hpn hconn (hnewman C) K hK hdim hj
  refine ⟨H ∘ u, H.isOpenEmbedding.comp hu, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy⟩ := hBU hx
    exact ⟨y, by change H (u y) = x; rw [hy, hfix x (hBC hx)]⟩
  · simpa only [range_comp] using hcover

end DifferentialGeometry.Topology.Engulfing
