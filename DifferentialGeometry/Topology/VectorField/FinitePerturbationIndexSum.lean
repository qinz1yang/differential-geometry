import DifferentialGeometry.Topology.VectorField.FinitePerturbation
import DifferentialGeometry.Topology.VectorField.ChartIndexHomotopy

set_option autoImplicit false
noncomputable section
open Set Metric Filter Bundle
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.VectorField
variable {d : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M]
  (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (d + 1))) H) [IsManifold I ∞ M]
  (V : ∀ x : M, TangentSpace I x)
  (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))

include hV in
theorem exists_regular_perturbation_interiorIndexSum_eq
    (hfinite : {x | V x = 0}.Finite)
    (hinterior : ∀ x, V x = 0 → I.IsInteriorPoint x) :
    ∃ (hisolated : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
      (G : ∀ x : M, TangentSpace I x)
      (hG : ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)))
      (hGfinite : {x | G x = 0}.Finite)
      (hGisolated : ∀ x, G x = 0 → HasContinuousIsolatedZero I G x)
      (hGinterior : ∀ x, G x = 0 → I.IsInteriorPoint x),
      IsCompact (tsupport (fun x => G x - V x)) ∧
      tsupport (fun x => G x - V x) ⊆ {x | I.IsInteriorPoint x} ∧
      (∀ x, ¬I.IsInteriorPoint x →
        (fun y => (⟨y, G y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
          (fun y => (⟨y, V y⟩ : TangentBundle I M))) ∧
      (∀ x, ∀ hz : G x = 0,
        LinearMap.det (linearizationAtZero ((hG x).mdifferentiableAt (by simp)) hz).toLinearMap ≠ 0) ∧
      interiorIndexSum I G hGfinite hGisolated hGinterior =
        interiorIndexSum I V hfinite hisolated hinterior := by
  classical
  let : Fintype {x | V x = 0} := hfinite.fintype
  have hisolated (x : M) (hx : V x = 0) : HasContinuousIsolatedZero I V x := by
    refine ⟨hx, ⟨univ, univ_mem, hV.continuous.continuousOn⟩, ?_⟩
    have hclosed := (show ({y | V y = 0} \ {x}).Finite from hfinite.sdiff).isClosed
    have hnx : x ∈ ({y | V y = 0} \ {x})ᶜ := by simp
    filter_upwards [hclosed.isOpen_compl.mem_nhds hnx] with y hy
    intro hzero
    by_contra hne
    exact hy ⟨hzero, hne⟩
  obtain ⟨c, r, R, _, hr, hRt, hdis, hp⟩ :=
    exists_pairwise_disjoint_zero_charts I V hfinite hinterior
  let a (p : {x | V x = 0}) := c p p.val
  let K (p : {x | V x = 0}) := (c p).symm '' closedBall (a p) (R p)
  have hcover (x : M) (hx : V x = 0) : x ∈ ⋃ p, K p := by
    obtain ⟨y, hy, he⟩ := (hp ⟨x, hx⟩).2.1
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, y,
      ball_subset_closedBall (ball_subset_ball (hr ⟨x, hx⟩).2.le hy), he⟩
  have hUnion : (⋃ p, K p) ⊆ {x | I.IsInteriorPoint x} := by
    intro x hx
    obtain ⟨p, y, hy, rfl⟩ := mem_iUnion.mp hx
    exact DifferentialGeometry.Manifold.isInteriorPoint_of_model_partialDiffeomorph I ∞ (c p).symm
      (by simp) (hRt p hy)
  obtain ⟨ρ, v, G, hG, _, _, hcompact, hsupport, hgerm, _, hboundary, hGfinite, hregular⟩ :=
    exists_regular_perturbation_in_disjoint_charts I V hV c a r R hr hRt hdis hcover
      (fun p y hy hyr => (hp p).2.2.2.2.1 y hy hyr |>.1) (fun _ => 1) (fun _ => zero_lt_one)
  have hGisolated (x : M) (hx : G x = 0) : HasContinuousIsolatedZero I G x := (hregular x hx).1
  have hGinterior (x : M) (hx : G x = 0) : I.IsInteriorPoint x := (hregular x hx).2.1
  have hGcover (x : M) (hz : G x = 0) : x ∈ ⋃ p, K p := by
    by_contra hx
    have he : G x = V x := TotalSpace.mk_injective x ((hgerm x hx).self_of_nhds)
    exact hx (hcover x (he.symm.trans hz))
  have hlocal (p : {x | V x = 0}) :
      interiorIndexSumOn I G hGfinite hGisolated hGinterior (K p) =
        interiorIndexSumOn I V hfinite hisolated hinterior (K p) := by
    let e : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (d + 1))) I
        (EuclideanSpace ℝ (Fin (d + 1))) M 1 := {
      (c p).symm with
      contMDiffOn_toFun := (c p).symm.contMDiffOn_toFun.of_le (by simp)
      contMDiffOn_invFun := (c p).symm.contMDiffOn_invFun.of_le (by simp) }
    exact (interiorIndexSumOn_eq_of_parametrization_boundary_eq I e (hRt p)
      V hV.continuous.continuousOn ((hr p).1.trans (hr p).2) hfinite hisolated hinterior
      G hG.continuous.continuousOn hGfinite hGisolated hGinterior
      (fun y hy => (hp p).2.2.2.2.2 y hy |>.1) (fun y hy => (hboundary p y hy).symm)).symm
  have hpartition (W : ∀ x : M, TangentSpace I x) (hf : {x | W x = 0}.Finite)
      (hi : ∀ x, W x = 0 → HasContinuousIsolatedZero I W x)
      (hint : ∀ x, W x = 0 → I.IsInteriorPoint x)
      (hc : ∀ x, W x = 0 → x ∈ ⋃ p, K p) :
      interiorIndexSum I W hf hi hint = ∑ p, interiorIndexSumOn I W hf hi hint (K p) := by
    have hregion : interiorIndexSumOn I W hf hi hint (⋃ p, K p) =
        interiorIndexSum I W hf hi hint := by
      unfold interiorIndexSumOn interiorIndexSum
      apply Finset.sum_filter_of_ne
      intro p _ _
      exact hc p (hf.mem_toFinset.mp p.property)
    rw [← hregion]
    simpa only [Finset.mem_univ, iUnion_true] using
      interiorIndexSumOn_biUnion I W hf hi hint Finset.univ K
        (fun p _ q _ hpq => hdis hpq)
  refine ⟨hisolated, G, hG, hGfinite, hGisolated, hGinterior, hcompact,
    hsupport.trans hUnion, fun x hx => hgerm x (fun h => hx (hUnion h)),
    fun x hz => (hregular x hz).2.2, ?_⟩
  rw [hpartition G hGfinite hGisolated hGinterior hGcover,
    hpartition V hfinite hisolated hinterior hcover]
  exact Finset.sum_congr rfl (fun p _ => hlocal p)

end DifferentialGeometry.VectorField
