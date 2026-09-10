import DifferentialGeometry.Bundle.FinitePatch
import DifferentialGeometry.Topology.VectorField.ChartPerturbation
import DifferentialGeometry.Topology.VectorField.FiniteZeroCharts

set_option autoImplicit false
noncomputable section
open Set Metric Filter Bundle
open scoped Manifold ContDiff Topology
namespace Poincare.VectorField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
  (V : ∀ x : M, TangentSpace I x)
  (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))

include hV in
theorem exists_regular_perturbation_in_disjoint_charts {ι : Type*} [Fintype ι]
    (c : ι → PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) (a : ι → E) (r R : ι → ℝ)
    (hr : ∀ p, 0 < r p ∧ r p < R p)
    (hRt : ∀ p, closedBall (a p) (R p) ⊆ (c p).target)
    (hdis : Pairwise (fun p q => Disjoint
      ((c p).symm '' closedBall (a p) (R p)) ((c q).symm '' closedBall (a q) (R q))))
    (hcover : ∀ x, V x = 0 → x ∈ ⋃ p, (c p).symm '' closedBall (a p) (R p))
    (hannulus : ∀ p y, y ∈ closedBall (a p) (R p) → r p ≤ dist y (a p) →
      V ((c p).symm y) ≠ 0)
    (ε : ι → ℝ) (hε : ∀ p, 0 < ε p) :
    ∃ (ρ : ι → E → ℝ) (v : ι → E) (G : ∀ x : M, TangentSpace I x)
      (hG : ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M))),
      G = Poincare.VectorBundle.finitePatch V (fun p => patchInCoordinates (c p) V
        (Poincare.Calculus.bumpPerturbation
          (_root_.VectorField.mpullback 𝓘(ℝ, E) I (c p).symm V) (ρ p) (v p))) ∧
      (∀ p, ContDiff ℝ ∞ (ρ p) ∧ HasCompactSupport (ρ p) ∧
        Function.support (ρ p) = ball (a p) (R p) ∧
        EqOn (ρ p) 1 (closedBall (a p) (r p)) ∧ (∀ y, ρ p y ∈ Icc (0 : ℝ) 1) ∧ ‖v p‖ < ε p) ∧
      IsCompact (tsupport (fun x => G x - V x)) ∧
      tsupport (fun x => G x - V x) ⊆ ⋃ p, (c p).symm '' closedBall (a p) (R p) ∧
      (∀ x ∉ ⋃ p, (c p).symm '' closedBall (a p) (R p),
        (fun y => (⟨y, G y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
          (fun y => (⟨y, V y⟩ : TangentBundle I M))) ∧
      (∀ p x, x ∈ (c p).symm '' closedBall (a p) (R p) →
        (fun y => (⟨y, G y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
          (fun y => (⟨y, patchInCoordinates (c p) V (Poincare.Calculus.bumpPerturbation
            (_root_.VectorField.mpullback 𝓘(ℝ, E) I (c p).symm V) (ρ p) (v p)) y⟩ :
              TangentBundle I M))) ∧
      (∀ p y, y ∈ sphere (a p) (R p) → G ((c p).symm y) = V ((c p).symm y)) ∧
      {x | G x = 0}.Finite ∧
      (∀ x, ∀ hz : G x = 0, HasContinuousIsolatedZero I G x ∧ I.IsInteriorPoint x ∧
        LinearMap.det (linearizationAtZero ((hG x).mdifferentiableAt (by simp)) hz).toLinearMap ≠ 0) := by
  classical
  choose ρ v Q hQ hρ hρcompact hρsupport hρone hρrange hQdef hv hsupport hcompact
    htsupport hgerm hcoordinate hsmall hboundary hfiniteQ hregularQ using
      fun p => exists_small_regular_chart_perturbation (c p) V hV (a p)
        (hr p).1 (hr p).2 (hRt p) (hannulus p) (hε p)
  let K : ι → Set M := fun p => (c p).symm '' closedBall (a p) (R p)
  have hK (p : ι) : IsCompact (K p) :=
    (isCompact_closedBall (a p) (R p)).image_of_continuousOn
      ((c p).symm.toOpenPartialHomeomorph.continuousOn.mono (hRt p))
  have hC : IsCompact (⋃ p, K p) := isCompact_iUnion hK
  let G := Poincare.VectorBundle.finitePatch V Q
  have hG : ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M)) :=
    Poincare.VectorBundle.contMDiff_finitePatch V Q I hV hQ
  have hQout (p : ι) (x : M) (hx : x ∉ K p) : ∀ᶠ y in 𝓝 x, Q p y = V y := by
    filter_upwards [hgerm p x hx] with y hy
    exact TotalSpace.mk_injective y hy
  have hGout (x : M) (hx : x ∉ ⋃ p, K p) : ∀ᶠ y in 𝓝 x, G y = V y :=
    Poincare.VectorBundle.finitePatch_eventuallyEq_self V Q
      (fun p => hQout p x (fun hp => hx (mem_iUnion.mpr ⟨p, hp⟩)))
  have hGQ (p : ι) (x : M) (hx : x ∈ K p) : ∀ᶠ y in 𝓝 x, G y = Q p y :=
    Poincare.VectorBundle.finitePatch_eventuallyEq_patch V Q p (fun q hqp =>
      hQout q x (fun hq => Set.disjoint_left.mp (hdis hqp.symm) hx hq))
  have hGQgraph (p : ι) (x : M) (hx : x ∈ K p) :
      (fun y => (⟨y, G y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
        (fun y => (⟨y, Q p y⟩ : TangentBundle I M)) := by
    filter_upwards [hGQ p x hx] with y hy
    exact congrArg (fun w : TangentSpace I y => (⟨y, w⟩ : TangentBundle I M)) hy
  have hGcover (x : M) (hz : G x = 0) : x ∈ ⋃ p, K p := by
    by_contra hx
    exact hx (hcover x ((hGout x hx).self_of_nhds.symm.trans hz))
  have hfinite : {x | G x = 0}.Finite := by
    apply (Set.finite_iUnion (fun p => hfiniteQ p)).subset
    intro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hGcover x hx)
    exact mem_iUnion.mpr ⟨p, hp, (hGQ p x hp).self_of_nhds.symm.trans hx⟩
  have hts : tsupport (fun x => G x - V x) ⊆ ⋃ p, K p := by
    apply closure_minimal _ hC.isClosed
    intro x hx
    by_contra hxC
    exact hx (sub_eq_zero.mpr ((hGout x hxC).self_of_nhds))
  refine ⟨ρ, v, G, hG, ?_, fun p => ⟨hρ p, hρcompact p, hρsupport p,
    hρone p, hρrange p, hv p⟩, hC.of_isClosed_subset isClosed_closure hts, hts,
    ?_, ?_, ?_, hfinite, ?_⟩
  · change Poincare.VectorBundle.finitePatch V Q = _
    congr 1
    funext p
    exact hQdef p
  · intro x hx
    filter_upwards [hGout x hx] with y hy
    exact congrArg (fun w : TangentSpace I y => (⟨y, w⟩ : TangentBundle I M)) hy
  · intro p x hx
    simpa only [hQdef p] using hGQgraph p x hx
  · intro p y hy
    have hx : (c p).symm y ∈ K p := ⟨y, sphere_subset_closedBall hy, rfl⟩
    rw [(hGQ p _ hx).self_of_nhds]
    have hh := hboundary p y hy
    change (mfderiv 𝓘(ℝ, E) I (c p).symm y).inverse (Q p ((c p).symm y)) =
      (mfderiv 𝓘(ℝ, E) I (c p).symm y).inverse (V ((c p).symm y)) at hh
    exact (isInvertible_mfderiv_partialDiffeomorph (c p).symm (by simp)
      (hRt p (sphere_subset_closedBall hy))).inverse.injective hh
  · intro x hz
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hGcover x hz)
    have hzp : Q p x = 0 := (hGQ p x hp).self_of_nhds.symm.trans hz
    obtain ⟨_, hiso, hdet⟩ := hregularQ p x hp hzp
    refine ⟨hiso.congr ((hGQ p x hp).mono (fun _ hy => hy.symm)), ?_, ?_⟩
    · obtain ⟨y, hy, rfl⟩ := hp
      exact Poincare.Manifold.isInteriorPoint_of_model_partialDiffeomorph I ∞ (c p).symm
        (by simp) (hRt p hy)
    · rw [linearizationAtZero_congr_of_eventuallyEq
        ((hG x).mdifferentiableAt (by simp)) ((hQ p x).mdifferentiableAt (by simp))
        hz hzp (hGQgraph p x hp)]
      exact hdet

include hV in
theorem exists_compactly_supported_regular_perturbation
    (hfinite : {x | V x = 0}.Finite)
    (hinterior : ∀ x, V x = 0 → I.IsInteriorPoint x) :
    ∃ (G : ∀ x : M, TangentSpace I x)
      (hG : ContMDiff I I.tangent ∞ (fun x => (⟨x, G x⟩ : TangentBundle I M))),
      IsCompact (tsupport (fun x => G x - V x)) ∧
      tsupport (fun x => G x - V x) ⊆ {x | I.IsInteriorPoint x} ∧
      (∀ x, ¬I.IsInteriorPoint x →
        (fun y => (⟨y, G y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
          (fun y => (⟨y, V y⟩ : TangentBundle I M))) ∧
      {x | G x = 0}.Finite ∧
      (∀ x, ∀ hz : G x = 0, HasContinuousIsolatedZero I G x ∧ I.IsInteriorPoint x ∧
        LinearMap.det (linearizationAtZero ((hG x).mdifferentiableAt (by simp)) hz).toLinearMap ≠ 0) := by
  let : Fintype {x | V x = 0} := hfinite.fintype
  obtain ⟨c, r, R, _, hr, hRt, hdis, hp⟩ :=
    exists_pairwise_disjoint_zero_charts I V hfinite hinterior
  have hcover (x : M) (hx : V x = 0) :
      x ∈ ⋃ p : {x | V x = 0}, (c p).symm '' closedBall (c p p.val) (R p) := by
    apply mem_iUnion.mpr
    refine ⟨⟨x, hx⟩, ?_⟩
    obtain ⟨y, hy, he⟩ := (hp ⟨x, hx⟩).2.1
    exact ⟨y, ball_subset_closedBall (ball_subset_ball (hr ⟨x, hx⟩).2.le hy), he⟩
  have hUnion : (⋃ p, (c p).symm '' closedBall (c p p.val) (R p)) ⊆
      {x | I.IsInteriorPoint x} := by
    intro x hx
    obtain ⟨p, y, hy, rfl⟩ := mem_iUnion.mp hx
    exact Poincare.Manifold.isInteriorPoint_of_model_partialDiffeomorph I ∞ (c p).symm
      (by simp) (hRt p hy)
  obtain ⟨ρ, v, G, hG, _, _, hcompact, hsupport, hgerm, _, _, hGfinite, hregular⟩ :=
    exists_regular_perturbation_in_disjoint_charts I V hV c (fun p => c p p.val) r R
      hr hRt hdis hcover (fun p y hy hyr => (hp p).2.2.2.2.1 y hy hyr |>.1)
      (fun _ => 1) (fun _ => zero_lt_one)
  exact ⟨G, hG, hcompact, hsupport.trans hUnion,
    fun x hx => hgerm x (fun h => hx (hUnion h)), hGfinite, hregular⟩

end Poincare.VectorField
