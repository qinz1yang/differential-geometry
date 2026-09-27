import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDoubleCharts
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.MetricTruncation

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

private def patchOpen (north : S3) (R : ℝ) : TopologicalSpace.Opens S3 :=
  ⟨(compactDoubleCapPartialDiffeomorph north R).target,
    (compactDoubleCapPartialDiffeomorph north R).open_target⟩

private theorem patchOpen_subset (north : S3) (R : ℝ) :
    patchOpen north R ≤ stereographicImage north := by
  rintro p ⟨x, _, rfl⟩
  exact (compactDoubleCapChart north R x).property

private def exteriorOpen (north : S3) (R : ℝ) : TopologicalSpace.Opens S3 :=
  ⟨(compactDoubleCapMap north R '' Metric.closedBall 0 (R - 1))ᶜ,
    ((isCompact_closedBall (0 : E3) (R - 1)).image
      (contMDiff_compactDoubleCapMap north R).continuous).isClosed.isOpen_compl⟩

private theorem patch_cover (north : S3) (R : ℝ) (p : S3) :
    p ∈ patchOpen north R ∨ p ∈ exteriorOpen north R := by
  classical
  by_cases hp : p ∈ compactDoubleCapMap north R '' Metric.closedBall 0 (R - 1)
  · obtain ⟨x, hx, rfl⟩ := hp
    exact Or.inl ⟨x, (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt
      (by linarith))), rfl⟩
  · exact Or.inr hp

private def patchChartMetric (north : S3) (R : ℝ)
    (g : SmoothRiemannianMetric (𝓡 3) E3) :
    SmoothRiemannianMetric (𝓡 3) (patchOpen north R) :=
  (Diffeomorph.pullbackMetricCross g (compactDoubleCapChart north R).symm).restrictOpenOfSubset
    (patchOpen_subset north R)

private theorem capChart_mfderiv (north : S3) (R : ℝ) (x : E3) :
    mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapChart north R) x =
      mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x := by
  have he : (Subtype.val : stereographicImage north → S3) ∘ compactDoubleCapChart north R =
      compactDoubleCapMap north R := rfl
  rw [← he, mfderiv_comp x (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((compactDoubleCapChart north R).contMDiff.mdifferentiableAt (by simp)), mfderiv_subtype_val]
  rfl

private theorem patchChartMetric_pullback (north : S3) (R : ℝ)
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (hx : compactDoubleCapMap north R x ∈ patchOpen north R) (v w : E3) :
    (patchChartMetric north R g).inner ⟨compactDoubleCapMap north R x, hx⟩
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) = g.inner x v w := by
  let D := compactDoubleCapChart north R
  have he : (D.symm : stereographicImage north → E3) ∘ D = id := funext D.symm_apply_apply
  have hd := mfderiv_comp x (D.symm.contMDiff.mdifferentiable (by simp) (D x))
    (D.contMDiff.mdifferentiable (by simp) x)
  rw [he, mfderiv_id] at hd
  have hv := congrArg (fun A => A v) hd.symm
  have hw := congrArg (fun A => A w) hd.symm
  change g.inner (D.symm (D x))
    (mfderiv (𝓡 3) (𝓡 3) D.symm (D x) (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v))
    (mfderiv (𝓡 3) (𝓡 3) D.symm (D x) (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w)) = _
  rw [← capChart_mfderiv]
  dsimp only [TangentSpace] at hv hw ⊢
  erw [hv, hw, D.symm_apply_apply]
  rfl

private theorem patch_overlap (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (g : SmoothRiemannianMetric (𝓡 3) E3)
    (hend : ∀ x : E3, R - 1 ≤ ‖x‖ → ∀ v w : E3, g.inner x v w = metric.inner x v w)
    (p : S3) (hp : p ∈ patchOpen north R) (hq : p ∈ exteriorOpen north R)
    (v w : TangentSpace (𝓡 3) p) :
    (patchChartMetric north R g).inner ⟨p, hp⟩ v w =
      ((compactDoubleMetric north R hR).restrictOpen (exteriorOpen north R)).inner ⟨p, hq⟩ v w := by
  obtain ⟨x, hx, rfl⟩ := hp
  have hn : R - 1 ≤ ‖x‖ := by
    by_contra! hn
    exact hq ⟨x, by simpa using hn.le, rfl⟩
  obtain ⟨a, ha⟩ := ((compactDoubleCapChart north R).mfderivToContinuousLinearEquiv (by simp) x).surjective v
  obtain ⟨b, hb⟩ := ((compactDoubleCapChart north R).mfderivToContinuousLinearEquiv (by simp) x).surjective w
  change mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapChart north R) x a = v at ha
  change mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapChart north R) x b = w at hb
  rw [capChart_mfderiv] at ha hb
  dsimp only [TangentSpace] at ha hb ⊢
  erw [← ha, ← hb]
  exact (patchChartMetric_pullback north R g x ⟨x, hx, rfl⟩ a b).trans
    ((hend x hn a b).trans (compactDoubleMetric_cap_pullback north R hR x hx a b).symm)

private def patchUnionChart (north : S3) (R : ℝ) :
    S3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ ↥(patchOpen north R ⊔ exteriorOpen north R) where
  toFun := fun p => ⟨p, patch_cover north R p⟩
  invFun := Subtype.val
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (patchOpen north R ⊔ exteriorOpen north R) _).mp
    exact contMDiff_id
  contMDiff_invFun := contMDiff_subtype_val

private theorem patchUnionChart_mfderiv (north : S3) (R : ℝ) (p : S3) :
    mfderiv (𝓡 3) (𝓡 3) (patchUnionChart north R) p = ContinuousLinearMap.id ℝ E3 := by
  have he : (Subtype.val : ↥(patchOpen north R ⊔ exteriorOpen north R) → S3) ∘
      patchUnionChart north R = id := rfl
  have hh := mfderiv_congr (I := 𝓡 3) (I' := 𝓡 3) (x := p) he
  rw [mfderiv_comp p (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((patchUnionChart north R).contMDiff.mdifferentiableAt (by simp)), mfderiv_subtype_val,
    mfderiv_id] at hh
  exact hh

def compactDoublePatchedMetric (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (g : SmoothRiemannianMetric (𝓡 3) E3)
    (hend : ∀ x : E3, R - 1 ≤ ‖x‖ → ∀ v w : E3, g.inner x v w = metric.inner x v w) :
    SmoothRiemannianMetric (𝓡 3) S3 :=
  Diffeomorph.pullbackMetricCross
    (DifferentialGeometry.Geometry.Metric.glueMetric (patchOpen north R) (exteriorOpen north R)
      (patchChartMetric north R g) ((compactDoubleMetric north R hR).restrictOpen (exteriorOpen north R))
      (patch_overlap north R hR g hend)) (patchUnionChart north R)

theorem compactDoublePatchedMetric_cap_pullback (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (g : SmoothRiemannianMetric (𝓡 3) E3)
    (hend : ∀ x : E3, R - 1 ≤ ‖x‖ → ∀ v w : E3, g.inner x v w = metric.inner x v w)
    (x : E3) (hx : x ∈ Metric.ball 0 (R + 1)) (v w : E3) :
    (compactDoublePatchedMetric north R hR g hend).inner (compactDoubleCapMap north R x)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) = g.inner x v w := by
  unfold compactDoublePatchedMetric
  rw [Diffeomorph.pullbackMetricCross_inner, patchUnionChart_mfderiv]
  exact (DifferentialGeometry.Geometry.Metric.glueMetric_inner_left (patchOpen north R) (exteriorOpen north R)
    (patchChartMetric north R g) ((compactDoubleMetric north R hR).restrictOpen (exteriorOpen north R))
    (patch_overlap north R hR g hend) ⟨compactDoubleCapMap north R x, ⟨x, hx, rfl⟩⟩ _ _).trans
      (patchChartMetric_pullback north R g x ⟨x, hx, rfl⟩ v w)

theorem compactDoublePatchedMetric_inner_exterior (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (g : SmoothRiemannianMetric (𝓡 3) E3)
    (hend : ∀ x : E3, R - 1 ≤ ‖x‖ → ∀ v w : E3, g.inner x v w = metric.inner x v w)
    (p : S3) (hp : p ∉ compactDoubleCapMap north R '' Metric.closedBall 0 (R - 1))
    (v w : TangentSpace (𝓡 3) p) :
    (compactDoublePatchedMetric north R hR g hend).inner p v w =
      (compactDoubleMetric north R hR).inner p v w := by
  unfold compactDoublePatchedMetric
  rw [Diffeomorph.pullbackMetricCross_inner, patchUnionChart_mfderiv]
  exact DifferentialGeometry.Geometry.Metric.glueMetric_inner_right (patchOpen north R) (exteriorOpen north R)
    (patchChartMetric north R g) ((compactDoubleMetric north R hR).restrictOpen (exteriorOpen north R))
    (patch_overlap north R hR g hend) ⟨p, hp⟩ v w

def compactDoubleTruncationMetric (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (g : SmoothRiemannianMetric (𝓡 3) E3) :
    SmoothRiemannianMetric (𝓡 3) S3 :=
  compactDoublePatchedMetric north R hR
    (metricTruncation g R (by linarith [le_max_right transitionEnd 2]))
    (fun _ hx v w => metricTruncation_inner_end g R _ hx v w)

theorem compactDoubleTruncationMetric_cap_pullback (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (g : SmoothRiemannianMetric (𝓡 3) E3)
    (x : E3) (hx : x ∈ Metric.ball 0 (R + 1)) (v w : E3) :
    (compactDoubleTruncationMetric north R hR g).inner (compactDoubleCapMap north R x)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) =
      (metricTruncation g R (by linarith [le_max_right transitionEnd 2])).inner x v w :=
  compactDoublePatchedMetric_cap_pullback north R hR _ _ x hx v w

theorem compactDoubleTruncationMetric_cap_pullback_core (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (g : SmoothRiemannianMetric (𝓡 3) E3)
    (x : E3) (hx : ‖x‖ ≤ R - 2) (v w : E3) :
    (compactDoubleTruncationMetric north R hR g).inner (compactDoubleCapMap north R x)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x v)
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north R) x w) = g.inner x v w := by
  exact (compactDoubleTruncationMetric_cap_pullback north R hR g x
    (by simpa using hx.trans_lt (by linarith : R - 2 < R + 1)) v w).trans
      (metricTruncation_inner_core g R _ hx v w)

theorem compactDoubleTruncationMetric_inner_exterior (north : S3) (R : ℝ)
    (hR : max transitionEnd 2 + 2 ≤ R) (g : SmoothRiemannianMetric (𝓡 3) E3)
    (p : S3) (hp : p ∉ compactDoubleCapMap north R '' Metric.closedBall 0 (R - 1))
    (v w : TangentSpace (𝓡 3) p) :
    (compactDoubleTruncationMetric north R hR g).inner p v w =
      (compactDoubleMetric north R hR).inner p v w :=
  compactDoublePatchedMetric_inner_exterior north R hR _ _ p hp v w

end DifferentialGeometry.PDE.RicciFlow.StandardCap
