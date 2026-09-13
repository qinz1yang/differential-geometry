import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import DifferentialGeometry.Topology.ClosedBall.Extension

open Set Filter
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {X E M : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞} [IsManifold I n M]

omit [IsManifold I n M] in
private theorem correction
    (f U : X → M) (hf : Continuous f) (K C A S : Set X)
    (hC : IsClosed C) (hCK : C ⊆ K) (hCA : C ⊆ A)
    (hA : IsOpen A) (hS : IsOpen S)
    (hfS : ContMDiffOn 𝓘(ℝ, X) I n f S)
    (hU : ContMDiffOn 𝓘(ℝ, X) I n U A)
    (heq : EqOn U f (K ∩ A))
    (e : OpenPartialHomeomorph M E)
    (he : ContMDiffOn I 𝓘(ℝ, E) n e e.source)
    (heinv : ContMDiffOn 𝓘(ℝ, E) I n e.symm e.target)
    (B : Set E) (hB : IsOpen B) (hBc : Convex ℝ B) (hBt : B ⊆ e.target)
    (hUe : MapsTo U A (e.source ∩ e ⁻¹' B)) :
    ∃ g : X → M, Continuous g ∧ EqOn g f K ∧
      ∃ T : Set X, IsOpen T ∧ C ⊆ T ∧
        ContMDiffOn 𝓘(ℝ, X) I n g (S ∪ T) := by
  classical
  let O := e.source ∩ e ⁻¹' B
  have hO : IsOpen O := e.continuousOn.isOpen_inter_preimage e.open_source hB
  let W := A ∩ f ⁻¹' O
  have hW : IsOpen W := hA.inter (hO.preimage hf)
  have hCW : C ⊆ W := by
    intro x hx
    refine ⟨hCA hx, ?_⟩
    change f x ∈ O
    rw [← heq ⟨hCK hx, hCA hx⟩]
    exact hUe (hCA hx)
  obtain ⟨β, hβ0, hβ1, hβ⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, X) hW.isClosed_compl hC (disjoint_compl_left_iff_subset.mpr hCW)
    (n := n)
  let v : X → E := fun x => (1 - β x) • e (f x) + β x • e (U x)
  have hvB {x : X} (hx : x ∈ W) : v x ∈ B :=
    hBc hx.2.2 (hUe hx.1).2 (sub_nonneg.mpr (hβ x).2) (hβ x).1 (sub_add_cancel 1 _)
  let g := W.piecewise (e.symm ∘ v) f
  have hgW : EqOn g (e.symm ∘ v) W := piecewise_eqOn _ _ _
  have hg0 {x : X} (hx : β x = 0) : g x = f x := by
    by_cases hxW : x ∈ W
    · rw [hgW hxW]
      simp only [Function.comp_apply, v, hx, sub_zero, one_smul, zero_smul, add_zero]
      exact e.left_inv hxW.2.1
    · exact piecewise_eq_of_notMem _ _ _ hxW
  have hg1 {x : X} (hxW : x ∈ W) (hx : β x = 1) : g x = U x := by
    rw [hgW hxW]
    simp only [Function.comp_apply, v, hx, sub_self, zero_smul, one_smul, zero_add]
    exact e.left_inv (hUe hxW.1).1
  have hgoutside {x : X} (hx : x ∉ W) : g =ᶠ[𝓝 x] f := by
    filter_upwards [hβ0.filter_mono (nhds_le_nhdsSet hx)] with y hy
    exact hg0 hy
  have hcontW : ContinuousOn g W := by
    have hf' : ContinuousOn (e ∘ f) W :=
      e.continuousOn.comp hf.continuousOn (fun x hx => hx.2.1)
    have hU' : ContinuousOn (e ∘ U) W :=
      e.continuousOn.comp (hU.continuousOn.mono inter_subset_left)
      (fun x hx => (hUe hx.1).1)
    have hv : ContinuousOn v W :=
      (continuous_const.continuousOn.sub β.contMDiff.continuous.continuousOn).smul hf' |>.add
        (β.contMDiff.continuous.continuousOn.smul hU')
    exact (e.symm.continuousOn.comp hv (fun x hx => hBt (hvB hx))).congr hgW
  have hcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ W
    · exact (hcontW x hx).continuousAt (hW.mem_nhds hx)
    · exact hf.continuousAt.congr (hgoutside hx).symm
  have hEq : EqOn g f K := by
    intro x hx
    by_cases hxW : x ∈ W
    · rw [hgW hxW]
      simp only [Function.comp_apply, v, heq ⟨hx, hxW.1⟩, ← add_smul,
        sub_add_cancel, one_smul]
      exact e.left_inv hxW.2.1
    · exact piecewise_eq_of_notMem _ _ _ hxW
  let T := W ∩ interior {x | β x = 1}
  have hT : IsOpen T := hW.inter isOpen_interior
  have hCT : C ⊆ T := by
    intro x hx
    refine ⟨hCW hx, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact hβ1.filter_mono (nhds_le_nhdsSet hx)
  refine ⟨g, hcont, hEq, T, hT, hCT, ?_⟩
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rcases hx with hxS | hxT
  · by_cases hxW : x ∈ W
    · have hf' := (he.contMDiffAt (e.open_source.mem_nhds hxW.2.1)).comp x
        (hfS.contMDiffAt (hS.mem_nhds hxS))
      have hU' := (he.contMDiffAt (e.open_source.mem_nhds (hUe hxW.1).1)).comp x
        (hU.contMDiffAt (hA.mem_nhds hxW.1))
      have hv : ContMDiffAt 𝓘(ℝ, X) 𝓘(ℝ, E) n v x :=
        (contMDiffAt_const.sub β.contMDiff.contMDiffAt).smul hf' |>.add
          (β.contMDiff.contMDiffAt.smul hU')
      have hcomp := (heinv.contMDiffAt (e.open_target.mem_nhds (hBt (hvB hxW)))).comp x hv
      exact hcomp.congr_of_eventuallyEq (hgW.eventuallyEq_of_mem (hW.mem_nhds hxW))
    · exact (hfS.contMDiffAt (hS.mem_nhds hxS)).congr_of_eventuallyEq (hgoutside hxW)
  · exact (hU.contMDiffAt (hA.mem_nhds hxT.1.1)).congr_of_eventuallyEq
      (by
        filter_upwards [hT.mem_nhds hxT] with y hy
        exact hg1 hy.1 (interior_subset (s := {x : X | β x = 1}) hy.2))

omit [FiniteDimensional ℝ X] in
private theorem local_chart_data [I.Boundaryless]
    (f U : X → M) (K V : Set X) (x : X) (hxV : x ∈ V)
    (hV : IsOpen V) (hU : ContMDiffOn 𝓘(ℝ, X) I n U V)
    (heq : EqOn U f (K ∩ V)) :
    ∃ P : Set X, P ∈ 𝓝 x ∧ IsClosed P ∧
      ∃ A : Set X, IsOpen A ∧ P ⊆ A ∧
        ContMDiffOn 𝓘(ℝ, X) I n U A ∧ EqOn U f (K ∩ A) ∧
        ∃ e : OpenPartialHomeomorph M E,
          ContMDiffOn I 𝓘(ℝ, E) n e e.source ∧
          ContMDiffOn 𝓘(ℝ, E) I n e.symm e.target ∧
          ∃ B : Set E, IsOpen B ∧ Convex ℝ B ∧ B ⊆ e.target ∧
            MapsTo U A (e.source ∩ e ⁻¹' B) := by
  let e : OpenPartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I (U x)
      continuousOn_toFun := continuousOn_extChartAt _
      continuousOn_invFun := continuousOn_extChartAt_symm _
      open_source := isOpen_extChartAt_source _
      open_target := isOpen_extChartAt_target _ }
  have hxe : U x ∈ e.source := mem_extChartAt_source _
  obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.mp e.open_target (e (U x)) (e.map_source hxe)
  let B := Metric.ball (e (U x)) r
  let O := e.source ∩ e ⁻¹' B
  have hO : IsOpen O := e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  let A := V ∩ U ⁻¹' O
  have hA : IsOpen A := hU.continuousOn.isOpen_inter_preimage hV hO
  have hxA : x ∈ A := ⟨hxV, hxe, Metric.mem_ball_self hr⟩
  obtain ⟨P, hPn, hPc, hPA⟩ := exists_mem_nhds_isClosed_subset (hA.mem_nhds hxA)
  refine ⟨P, hPn, hPc, A, hA, hPA, hU.mono inter_subset_left,
    heq.mono (inter_subset_inter_right _ inter_subset_left), e, ?_, ?_,
    B, Metric.isOpen_ball, convex_ball _ _, hrt, fun y hy => hy.2⟩
  · change ContMDiffOn I 𝓘(ℝ, E) n (extChartAt I (U x)) (extChartAt I (U x)).source
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt (I := I) (n := n) (x := U x)
  · exact contMDiffOn_extChartAt_symm (I := I) (U x)

theorem exists_contMDiffOn_eqOn_of_locally_extendable [I.Boundaryless]
    {f : X → M} (hf : Continuous f) {K : Set X} (hK : IsCompact K)
    (hloc : ∀ x ∈ K, ∃ U : X → M, ∃ V : Set X,
      IsOpen V ∧ x ∈ V ∧ ContMDiffOn 𝓘(ℝ, X) I n U V ∧ EqOn U f (K ∩ V)) :
    ∃ g : X → M, Continuous g ∧ EqOn g f K ∧
      ∃ N : Set X, IsOpen N ∧ K ⊆ N ∧ ContMDiffOn 𝓘(ℝ, X) I n g N := by
  classical
  have hd : ∀ x : K, ∃ U : X → M, ∃ P : Set X,
      P ∈ 𝓝 (x : X) ∧ IsClosed P ∧
      ∃ A : Set X, IsOpen A ∧ P ⊆ A ∧
        ContMDiffOn 𝓘(ℝ, X) I n U A ∧ EqOn U f (K ∩ A) ∧
        ∃ e : OpenPartialHomeomorph M E,
          ContMDiffOn I 𝓘(ℝ, E) n e e.source ∧
          ContMDiffOn 𝓘(ℝ, E) I n e.symm e.target ∧
          ∃ B : Set E, IsOpen B ∧ Convex ℝ B ∧ B ⊆ e.target ∧
            MapsTo U A (e.source ∩ e ⁻¹' B) := by
    intro x
    obtain ⟨U, V, hV, hxV, hU, heq⟩ := hloc x x.property
    exact ⟨U, local_chart_data f U K V x hxV hV hU heq⟩
  choose U P hPn hPc A hAo hPA hUs hEq e hes hei B hBo hBc hBt hUe using hd
  have hind : ∀ t : Finset K, ∃ g : X → M, Continuous g ∧ EqOn g f K ∧
      ∃ N : Set X, IsOpen N ∧ (∀ x ∈ t, K ∩ P x ⊆ N) ∧
        ContMDiffOn 𝓘(ℝ, X) I n g N := by
    intro t
    induction t using Finset.induction with
    | empty =>
      exact ⟨f, hf, (fun _ _ => rfl), ∅, isOpen_empty, by simp, contMDiffOn_empty⟩
    | @insert x t _ ih =>
      obtain ⟨g, hg, hgf, N, hN, hcov, hgN⟩ := ih
      have hUg : EqOn (U x) g (K ∩ A x) := by
        intro y hy
        exact (hEq x hy).trans (hgf hy.1).symm
      obtain ⟨G, hG, hGg, T, hT, hCT, hGNT⟩ := correction g (U x) hg K
        (K ∩ P x) (A x) N (hK.isClosed.inter (hPc x)) inter_subset_left
        (fun y hy => hPA x hy.2) (hAo x) hN hgN (hUs x) hUg
        (e x) (hes x) (hei x) (B x) (hBo x) (hBc x) (hBt x) (hUe x)
      refine ⟨G, hG, hGg.trans hgf, N ∪ T, hN.union hT, ?_, hGNT⟩
      intro y hy z hz
      rcases Finset.mem_insert.mp hy with rfl | hyt
      · exact Or.inr (hCT hz)
      · exact Or.inl (hcov y hyt hz)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => interior (P x))
    (fun _ => isOpen_interior) (fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hPn ⟨x, hx⟩)⟩)
  obtain ⟨g, hg, heq, N, hN, hcov, hgs⟩ := hind t
  refine ⟨g, hg, heq, N, hN, ?_, hgs⟩
  intro x hx
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (ht hx)
  exact hcov y hyt ⟨hx, interior_subset hy⟩

theorem exists_contMDiffOn_extension_closedBall [I.Boundaryless]
    (a : X) {r : ℝ} (hr : 0 ≤ r) (u : Metric.closedBall a r → M)
    (hloc : ∀ x : Metric.closedBall a r, ∃ U : X → M, ∃ V : Set X,
      IsOpen V ∧ (x : X) ∈ V ∧ ContMDiffOn 𝓘(ℝ, X) I n U V ∧
        ∀ y : Metric.closedBall a r, (y : X) ∈ V → U y = u y) :
    ∃ g : X → M, Continuous g ∧ (∀ y : Metric.closedBall a r, g y = u y) ∧
      ∃ N : Set X, IsOpen N ∧ Metric.closedBall a r ⊆ N ∧
        ContMDiffOn 𝓘(ℝ, X) I n g N := by
  have hu : Continuous u := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨U, V, hV, hxV, hU, heq⟩ := hloc x
    have hUc : ContinuousAt (fun y : Metric.closedBall a r => U y) x :=
      (hU.continuousOn.continuousAt (hV.mem_nhds hxV)).comp
        continuous_subtype_val.continuousAt
    apply hUc.congr
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (hV.mem_nhds hxV)] with y hy
    exact heq y hy
  let f := ClosedBall.extension a hr ⟨u, hu⟩
  have hf : ∀ y : Metric.closedBall a r, f y = u y :=
    ClosedBall.extension_coe a hr ⟨u, hu⟩
  obtain ⟨g, hg, hgf, N, hN, hKN, hgs⟩ :=
    exists_contMDiffOn_eqOn_of_locally_extendable (I := I) f.continuous
      (isCompact_closedBall a r) (by
        intro x hx
        obtain ⟨U, V, hV, hxV, hU, heq⟩ := hloc ⟨x, hx⟩
        refine ⟨U, V, hV, hxV, hU, ?_⟩
        intro y hy
        exact (heq ⟨y, hy.1⟩ hy.2).trans (hf ⟨y, hy.1⟩).symm)
  exact ⟨g, hg, fun y => (hgf y.property).trans (hf y), N, hN, hKN, hgs⟩

end DifferentialGeometry.Topology
