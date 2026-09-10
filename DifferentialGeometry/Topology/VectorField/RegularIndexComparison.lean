import DifferentialGeometry.Topology.VectorField.RegularChartIndexSum
import DifferentialGeometry.Topology.Manifold.FiniteInteriorCharts

set_option autoImplicit false
noncomputable section
open Set Metric Filter Bundle
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [CompactSpace M]
  (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H) [IsManifold I ∞ M]

theorem interiorIndexSum_eq_of_regular_boundary_germ
    (V W : ∀ x : M, TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I M)))
    (hVreg : ∀ x, ∀ hz : V x = 0,
      (linearizationAtZero ((hV x).mdifferentiableAt (by simp)) hz).det ≠ 0)
    (hWreg : ∀ x, ∀ hz : W x = 0,
      (linearizationAtZero ((hW x).mdifferentiableAt (by simp)) hz).det ≠ 0)
    (hVfinite : {x | V x = 0}.Finite)
    (hVisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
    (hVint : ∀ x, V x = 0 → I.IsInteriorPoint x)
    (hWfinite : {x | W x = 0}.Finite)
    (hWisolated : ∀ x, W x = 0 → HasContinuousIsolatedZero I W x)
    (hWint : ∀ x, W x = 0 → I.IsInteriorPoint x)
    (hboundary : ∀ x, ¬I.IsInteriorPoint x → V =ᶠ[𝓝 x] W) :
    interiorIndexSum I V hVfinite hVisolated hVint =
      interiorIndexSum I W hWfinite hWisolated hWint := by
  classical
  let O := {x : M | V =ᶠ[𝓝 x] W}
  have hO : IsOpen O := isOpen_setOfPred_eventually_nhds
  have hK : IsCompact Oᶜ := hO.isClosed_compl.isCompact
  have hKI : Oᶜ ⊆ I.interior M := by
    intro x hx
    by_contra hn
    exact hx (hboundary x hn)
  obtain ⟨U, hU, hKU, hUI, hUc⟩ := exists_open_between_and_isCompact_closure hK
    (I.isOpen_interior (n := ∞) (by simp)) hKI
  let S₀ := Uᶜ
  have hS₀ : IsCompact S₀ := hU.isClosed_compl.isCompact
  have hSgerm : ∀ x ∈ S₀, V =ᶠ[𝓝 x] W := by
    intro x hx
    by_contra hn
    exact hx (hKU hn)
  let c (p : closure U) := Poincare.Manifold.interiorChart I ∞ p.val
  have hcs (p : closure U) : p.val ∈ (c p).source :=
    (Poincare.Manifold.mem_interiorChart_source_iff I ∞ p.val).mpr (hUI p.property)
  choose R hR hRt hsub using
    fun p : closure U => Poincare.Manifold.exists_interiorChart_closedBall_subset I
      (hUI p.property) (U := univ) univ_mem
  let a (p : closure U) := c p p.val
  let C (p : closure U) := (c p).symm '' closedBall (a p) (R p / 4)
  have hCr (p : closure U) : 0 < R p / 4 ∧ R p / 4 < R p / 2 ∧ R p / 2 < R p := by
    have hh := hR p
    constructor
    · positivity
    · constructor <;> linarith
  have hCt (p : closure U) : closedBall (a p) (R p / 4) ⊆ (c p).target :=
    (closedBall_subset_closedBall ((hCr p).2.1.le.trans (hCr p).2.2.le)).trans (hRt p)
  have hCcompact (p : closure U) : IsCompact (C p) :=
    (isCompact_closedBall (a p) (R p / 4)).image_of_continuousOn
      ((c p).symm.contMDiffOn.continuousOn.mono (hCt p))
  have hCnhds (p : closure U) : C p ∈ 𝓝 p.val := by
    have ht := (c p).toOpenPartialHomeomorph.continuousAt (hcs p)
    apply Filter.mem_of_superset (inter_mem ((c p).open_source.mem_nhds (hcs p))
      (ht.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self (hCr p).1))))
    intro y hy
    exact ⟨c p y, ball_subset_closedBall hy.2, (c p).left_inv hy.1⟩
  obtain ⟨t, hcover⟩ := hUc.elim_nhds_subcover' (fun x hx => C ⟨x, hx⟩)
    (fun x hx => hCnhds ⟨x, hx⟩)
  have hchain (t : Finset (closure U)) :
      ∃ (G : ∀ x : M, TangentSpace I x)
        (hG : ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)))
        (hGfinite : {x | G x = 0}.Finite)
        (hGisolated : ∀ x, G x = 0 → HasContinuousIsolatedZero I G x)
        (hGint : ∀ x, G x = 0 → I.IsInteriorPoint x),
        (∀ x, ∀ hz : G x = 0,
          (linearizationAtZero ((hG x).mdifferentiableAt (by simp)) hz).det ≠ 0) ∧
        (∀ x ∈ S₀ ∪ ⋃ p ∈ t, C p, G =ᶠ[𝓝 x] W) ∧
        interiorIndexSum I G hGfinite hGisolated hGint =
          interiorIndexSum I V hVfinite hVisolated hVint := by
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨V, hV, hVfinite, hVisolated, hVint, hVreg, ?_, rfl⟩
      simpa using hSgerm
    | @insert p t _ ih =>
      obtain ⟨G, hG, hGfinite, hGisolated, hGint, hGreg, hGgerm, hGindex⟩ := ih
      have hS : IsCompact (S₀ ∪ ⋃ q ∈ t, C q) :=
        hS₀.union (t.isCompact_biUnion (fun q _ => hCcompact q))
      obtain ⟨F, hF, hFfinite, hFisolated, hFint, hinner, _, hprotected, hFreg, hFindex⟩ :=
        exists_regular_chart_splice_interiorIndexSum_eq I (c p) G W hG hW hGreg hWreg
          hGfinite hGisolated hGint (a p) (half_pos (hR p)) (hCr p).2.2 (hRt p) hS hGgerm
      have hcore : ∀ x ∈ C p, F =ᶠ[𝓝 x] W := by
        rintro x ⟨y, hy, rfl⟩
        have hyt := hCt p hy
        have hxs := (c p).map_target hyt
        have hball : c p ((c p).symm y) ∈ ball (a p) (R p / 2) := by
          erw [(c p).right_inv hyt]
          exact lt_of_le_of_lt hy (hCr p).2.1
        have ht := (c p).toOpenPartialHomeomorph.continuousAt hxs
        filter_upwards [(c p).open_source.mem_nhds hxs,
          ht.preimage_mem_nhds (isOpen_ball.mem_nhds hball)] with z hz hzb
        exact hinner z ⟨c p z, ball_subset_closedBall hzb, (c p).left_inv hz⟩
      refine ⟨F, hF, hFfinite, hFisolated, hFint, hFreg, ?_, hFindex.trans hGindex⟩
      intro x hx
      rcases hx with hx | hx
      · exact hprotected x (Or.inl hx)
      · obtain ⟨q, hqt, hxq⟩ := mem_iUnion₂.mp hx
        rcases Finset.mem_insert.mp hqt with hqp | hqt
        · subst q
          exact hcore x hxq
        · exact hprotected x (Or.inr (mem_iUnion₂.mpr ⟨q, hqt, hxq⟩))
  obtain ⟨G, hG, hGfinite, hGisolated, hGint, _, hGgerm, hGindex⟩ := hchain t
  have hGW : G = W := by
    funext x
    apply (hGgerm x ?_).self_of_nhds
    by_cases hx : x ∈ U
    · exact Or.inr (hcover (subset_closure hx))
    · exact Or.inl hx
  subst G
  exact hGindex.symm

end Poincare.VectorField
