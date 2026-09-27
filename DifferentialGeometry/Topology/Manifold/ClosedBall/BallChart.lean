import DifferentialGeometry.Topology.Manifold.ClosedBall.Coordinates
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Quotient

set_option autoImplicit false
noncomputable section

open Set Manifold Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {m : ℕ}
local notation "EuN" => EuclideanSpace ℝ (Fin (m + 1))
private local instance closedCellCharts : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  Handle.closedCellChartedSpaceSucc m
private local instance closedCellSmooth : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m

private def closedCellInsertion (x : EuN) : ClosedCell (m + 1) :=
  if hx : ‖x‖ ≤ 1 then ⟨x, hx⟩ else ⟨0, by simp⟩

private theorem closedCellInsertion_val {x : EuN} (hx : ‖x‖ < 1) :
    (closedCellInsertion x).val = x := by
  rw [closedCellInsertion, dif_pos hx.le]

private theorem closedCellInsertion_eventually {x : EuN} (hx : ‖x‖ < 1) :
    (Subtype.val : ClosedCell (m + 1) → EuN) ∘ closedCellInsertion =ᶠ[𝓝 x] id := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
  exact closedCellInsertion_val hy

private theorem closedCellInsertion_contMDiffAt {x : EuN} (hx : ‖x‖ < 1) :
    ContMDiffAt (𝓡 (m + 1)) (𝓡∂ (m + 1)) ∞ closedCellInsertion x := by
  have hi := closedCellInsertion_eventually hx
  apply (ContMDiffAt.iff_comp_isImmersionAt
    ((isSmoothEmbedding_closedCell_inclusion m).isImmersion.isImmersionAt
      (closedCellInsertion x))).mpr
  refine ⟨?_, hi.contMDiffAt_iff.mpr contMDiffAt_id⟩
  exact _root_.Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (continuousAt_id.congr hi.symm)

private theorem closedCellInsertion_injective_mfderiv {x : EuN} (hx : ‖x‖ < 1) :
    Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡∂ (m + 1)) closedCellInsertion x) := by
  have hc := mfderiv_comp x
    ((isSmoothEmbedding_closedCell_inclusion m).contMDiff.mdifferentiableAt (by simp))
    ((closedCellInsertion_contMDiffAt hx).mdifferentiableAt (by simp))
  rw [(closedCellInsertion_eventually hx).mfderiv_eq, mfderiv_id] at hc
  intro v w hvw
  have h := congrArg (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
    (Subtype.val : ClosedCell (m + 1) → EuN) (closedCellInsertion x)) hvw
  have heq (u : TangentSpace (𝓡 (m + 1)) x) :=
    congrArg (fun L : EuN →L[ℝ] EuN => L u) hc
  exact (heq v).trans (h.trans (heq w).symm)

section Embedding

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N]
  [IsManifold (𝓡 (m + 1)) ∞ N]

theorem exists_partialDiffeomorph_of_closedCell_embedding
    (f : ClosedCell (m + 1) → N)
    (hf : IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ f) :
    ∃ φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) EuN N ∞,
      φ.source = Metric.ball 0 1 ∧
      φ.target = f '' {x : ClosedCell (m + 1) | ‖x.val‖ < 1} ∧
      ∀ (x : EuN) (hx : ‖x‖ < 1), φ x = f ⟨x, hx.le⟩ := by
  let g : EuN → N := f ∘ closedCellInsertion
  have hs : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ g (Metric.ball 0 1) := by
    intro x hx
    have hx' : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
    exact (hf.contMDiff.contMDiffAt.comp x (closedCellInsertion_contMDiffAt hx')).contMDiffWithinAt
  have hlocal : IsLocalDiffeomorphOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ g
      (Metric.ball 0 1) := by
    intro x
    have hx : ‖x.val‖ < 1 := mem_ball_zero_iff.mp x.property
    have hder : Function.Injective (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) g x.val) := by
      rw [show g = f ∘ closedCellInsertion from rfl,
        mfderiv_comp x.val (hf.contMDiff.mdifferentiableAt (by simp))
          ((closedCellInsertion_contMDiffAt hx).mdifferentiableAt (by simp))]
      exact ((hf.isImmersion.isImmersionAt _).injective_mfderiv (by simp)).comp
        (closedCellInsertion_injective_mfderiv hx)
    let D : EuN →L[ℝ] EuN := mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) g x.val
    have hD : Function.Injective D := hder
    let A : EuN ≃L[ℝ] EuN :=
      (D.toLinearMap.linearEquivOfInjective hD rfl).toContinuousLinearEquiv
    exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv g hs Metric.isOpen_ball
      x.val x.property A
      ((hs.contMDiffAt (Metric.isOpen_ball.mem_nhds x.property)).mdifferentiableAt
        (by simp)).hasMFDerivAt
  have hinj : Set.InjOn g (Metric.ball 0 1) := by
    intro x hx y hy h
    have hx' : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have hy' : ‖y‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hy
    have h' := congrArg Subtype.val (hf.isEmbedding.injective h)
    simpa only [closedCellInsertion_val hx', closedCellInsertion_val hy'] using h'
  obtain ⟨φ, hsource, htarget, hφ⟩ := exists_partialDiffeomorph_of_injOn
    Metric.isOpen_ball hlocal hinj
  refine ⟨φ, hsource, ?_, ?_⟩
  · rw [htarget]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
      exact ⟨closedCellInsertion x, by
        change ‖(closedCellInsertion x).val‖ < 1
        rwa [closedCellInsertion_val hx'], rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.val, by simpa [Metric.mem_ball, dist_zero_right] using hx, ?_⟩
      change f (closedCellInsertion x.val) = f x
      congr 1
      exact Subtype.ext (closedCellInsertion_val hx)
  · intro x hx
    rw [hφ]
    change f (closedCellInsertion x) = f ⟨x, hx.le⟩
    congr 1
    exact Subtype.ext (closedCellInsertion_val hx)

theorem exists_partialDiffeomorph_smul_of_closedCell_embedding
    (f : ClosedCell (m + 1) → N)
    (hf : IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ f)
    (r : ℝ) (hr : 0 < r) :
    ∃ φ : PartialDiffeomorph (𝓡 (m + 1)) (𝓡 (m + 1)) EuN N ∞,
      φ.source = Metric.ball 0 r⁻¹ ∧
      φ.target = f '' {x : ClosedCell (m + 1) | ‖x.val‖ < 1} ∧
      ∀ (x : EuN) (hx : ‖r • x‖ < 1), φ x = f ⟨r • x, hx.le⟩ := by
  obtain ⟨φ, hsource, htarget, hφ⟩ := exists_partialDiffeomorph_of_closedCell_embedding f hf
  let A : EuN ≃L[ℝ] EuN :=
    (LinearEquiv.smulOfNeZero ℝ EuN r hr.ne').toContinuousLinearEquiv
  let ψ := A.toDiffeomorph.toPartialDiffeomorph.trans φ
  refine ⟨ψ, ?_, ?_, ?_⟩
  · change Set.univ ∩ A ⁻¹' φ.source = Metric.ball 0 r⁻¹
    rw [hsource, Set.univ_inter]
    ext x
    change (r • x ∈ Metric.ball (0 : EuN) 1) ↔ x ∈ Metric.ball 0 r⁻¹
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [← one_div, lt_div_iff₀ hr, mul_comm]
  · change φ.target ∩ φ.symm ⁻¹' Set.univ = _
    rw [Set.preimage_univ, Set.inter_univ, htarget]
  · intro x hx
    exact hφ (r • x) hx

theorem exists_ballChart_of_closedCell_embedding
    (f : ClosedCell (m + 1) → N)
    (hf : IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ f)
    (r : ℝ) (hr : 0 < r) (hr' : r < 1 / 2) :
    ∃ c : BallChart (m + 1) (𝓡 (m + 1)) N,
      c.chart.source = Metric.ball 0 r⁻¹ ∧
      c.chart.target = f '' {x : ClosedCell (m + 1) | ‖x.val‖ < 1} ∧
      ∀ (x : EuN) (hx : ‖r • x‖ < 1), c.chart x = f ⟨r • x, hx.le⟩ := by
  obtain ⟨φ, hs, ht, hφ⟩ := exists_partialDiffeomorph_smul_of_closedCell_embedding f hf r hr
  have hR : (2 : ℝ) < r⁻¹ := by
    rw [← one_div, lt_div_iff₀ hr]
    linarith
  let c : BallChart (m + 1) (𝓡 (m + 1)) N :=
    ⟨φ, by
      rw [hs]
      exact Metric.closedBall_subset_ball hR⟩
  exact ⟨c, hs, ht, hφ⟩

theorem exists_ballChart_quarter_of_closedCell_embedding
    (f : ClosedCell (m + 1) → N)
    (hf : IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ f) :
    ∃ c : BallChart (m + 1) (𝓡 (m + 1)) N,
      c.chart.source = Metric.ball 0 4 ∧
      c.chart.target = f '' {x : ClosedCell (m + 1) | ‖x.val‖ < 1} ∧
      ∀ (x : EuN) (hx : ‖(1 / 4 : ℝ) • x‖ < 1),
        c.chart x = f ⟨(1 / 4 : ℝ) • x, hx.le⟩ := by
  simpa only [one_div, inv_inv] using
    exists_ballChart_of_closedCell_embedding f hf (1 / 4) (by norm_num) (by norm_num)

end Embedding

private theorem mfderiv_closedCellInsertion {x : EuN} (hx : ‖x‖ < 1) :
    mfderiv (𝓡 (m + 1)) (𝓡∂ (m + 1)) closedCellInsertion x =
      ContinuousLinearMap.id ℝ EuN := by
  have hc := mfderiv_comp x
    ((isSmoothEmbedding_closedCell_inclusion m).contMDiff.mdifferentiableAt (by simp))
    ((closedCellInsertion_contMDiffAt hx).mdifferentiableAt (by simp))
  have hxi : ‖(closedCellInsertion x).val‖ < 1 := by
    rwa [closedCellInsertion_val hx]
  rw [(closedCellInsertion_eventually hx).mfderiv_eq, mfderiv_id,
    mfderiv_closedCell_inclusion_of_norm_lt_one hxi] at hc
  ext v
  exact (congrArg (fun L : EuN →L[ℝ] EuN => L v) hc).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

theorem mfderiv_eq_of_eq_closedCell_smul
    {f : ClosedCell (m + 1) → N} {F : EuN → N} {r : ℝ} {x : EuN}
    (hx : ‖r • x‖ < 1)
    (hf : MDifferentiableAt (𝓡∂ (m + 1)) I f ⟨r • x, hx.le⟩)
    (hF : ∀ (y : EuN) (hy : ‖r • y‖ < 1), F y = f ⟨r • y, hy.le⟩)
    (v : EuN) :
    mfderiv (𝓡 (m + 1)) I F x v =
      mfderiv (𝓡∂ (m + 1)) I f ⟨r • x, hx.le⟩ (r • v) := by
  have hins : closedCellInsertion (r • x) = (⟨r • x, hx.le⟩ : ClosedCell (m + 1)) :=
    Subtype.ext (closedCellInsertion_val hx)
  have hf' : MDifferentiableAt (𝓡∂ (m + 1)) I f (closedCellInsertion (r • x)) := by
    rw [hins]
    exact hf
  have hs : MDifferentiableAt (𝓡 (m + 1)) (𝓡 (m + 1)) (fun y : EuN => r • y) x :=
    mdifferentiableAt_iff_differentiableAt.mpr ((hasFDerivAt_id x).const_smul r).differentiableAt
  have hk := (closedCellInsertion_contMDiffAt hx).mdifferentiableAt (by simp)
  have heq : F =ᶠ[𝓝 x] (fun y => f (closedCellInsertion (r • y))) := by
    have hscale : Continuous (fun y : EuN => r • y) := continuous_id.const_smul r
    have hopen : IsOpen {y : EuN | ‖r • y‖ < 1} :=
      isOpen_lt hscale.norm continuous_const
    filter_upwards [hopen.mem_nhds hx] with y hy
    change ‖r • y‖ < 1 at hy
    simpa only [closedCellInsertion, dif_pos hy.le] using hF y hy
  have hscale : mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) (fun y : EuN => r • y) x v = r • v := by
    have hd : (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1))
        (fun y : EuN => r • y) x : EuN →L[ℝ] EuN) = r • ContinuousLinearMap.id ℝ EuN := by
      rw [mfderiv_eq_fderiv]
      exact ((hasFDerivAt_id x).const_smul r).fderiv
    exact congrArg (fun L : EuN →L[ℝ] EuN => L v) hd
  have hk_apply (w : EuN) :
      mfderiv (𝓡 (m + 1)) (𝓡∂ (m + 1)) closedCellInsertion (r • x) w = w :=
    congrArg (fun L : EuN →L[ℝ] EuN => L w) (mfderiv_closedCellInsertion hx)
  have hinner : mfderiv (𝓡 (m + 1)) (𝓡∂ (m + 1))
      (closedCellInsertion ∘ fun y : EuN => r • y) x v = r • v := by
    have h := mfderiv_comp_apply x hk hs v
    exact h.trans ((hk_apply _).trans hscale)
  have hmain := mfderiv_comp_apply x hf' (hk.comp x hs) v
  rw [hinner] at hmain
  have hpoint := congrArg
    (fun y : ClosedCell (m + 1) => (mfderiv (𝓡∂ (m + 1)) I f y : EuN →L[ℝ] E) (r • v)) hins
  have heqm : (mfderiv (𝓡 (m + 1)) I F x : EuN →L[ℝ] E) =
      mfderiv (𝓡 (m + 1)) I (f ∘ (closedCellInsertion ∘ fun y : EuN => r • y)) x :=
    heq.mfderiv_eq
  exact (congrArg (fun L : EuN →L[ℝ] E => L v) heqm).trans (hmain.trans hpoint)

end DifferentialGeometry.Topology.Manifold
