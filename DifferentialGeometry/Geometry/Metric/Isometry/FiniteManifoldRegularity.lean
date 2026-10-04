import DifferentialGeometry.Geometry.Metric.Isometry.FiniteRegularity
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrameExamples

/-!
# Finite manifold regularity of the same metric diffeomorphism

Actual native chart coefficients satisfy the metric bootstrap equation. Identifying the two
model spaces by the original differential upgrades both directions of the same equivalence.
-/

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.MetricIsometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {r : ℕ∞}
  [IsManifold I ((r : ℕ∞ω) + 2) M] [IsManifold J ((r : ℕ∞ω) + 2) N]
  [IsManifold I 1 M] [IsManifold J 1 N]

private def coordinateMetric
    (h : ContMDiffRiemannianMetric J ((r : ℕ∞ω) + 1) F (TangentSpace J : N → Type _))
    (a : E → N) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let B : F →L[ℝ] F →L[ℝ] ℝ := h.inner (a y)
  let D : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) J a y
  B.bilinearComp D D

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [J.Boundaryless]
  [IsManifold J ((r : ℕ∞ω) + 2) N] in
private theorem coordinateMetric_regular
    (h : ContMDiffRiemannianMetric J ((r : ℕ∞ω) + 1) F (TangentSpace J : N → Type _))
    (a : PartialDiffeomorph 𝓘(ℝ, E) J E N ((r : ℕ∞ω) + 2)) :
    ContDiffOn ℝ ((r : ℕ∞ω) + 1) (coordinateMetric h a) a.source :=
  h.contDiffOn_pullback_inner le_rfl (by norm_num [add_assoc]) a.open_source a.contMDiffOn_toFun

omit [FiniteDimensional ℝ F] [J.Boundaryless]
  [IsManifold J ((r : ℕ∞ω) + 2) N] in
private theorem coordinateMetric_coercive
    (h : ContMDiffRiemannianMetric J ((r : ℕ∞ω) + 1) F (TangentSpace J : N → Type _))
    (a : PartialDiffeomorph 𝓘(ℝ, E) J E N ((r : ℕ∞ω) + 2))
    {y : E} (hy : y ∈ a.source) : IsCoercive (coordinateMetric h a y) := by
  have hn : ((r : ℕ∞ω) + 2) ≠ 0 := by simp
  let hi : E ≃L[ℝ] F :=
    (a.isLocalDiffeomorphAt _ _ _ hy).mfderivToContinuousLinearEquiv hn
  apply ContinuousLinearMap.isCoercive_of_posDef
  intro v hv
  dsimp only [coordinateMetric]
  erw [ContinuousLinearMap.bilinearComp_apply]
  apply h.pos
  intro hz
  have hinj : Function.Injective (mfderiv 𝓘(ℝ, E) J a y : E →L[ℝ] F) := by
    change Function.Injective (fun v : E => hi v)
    exact hi.injective
  exact hv (hinj (hz.trans (map_zero _).symm))

omit [FiniteDimensional ℝ F] in
private theorem metric_map_regular
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J ((r : ℕ∞ω) + 1) F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N r) (hr : 2 ≤ r)
    (hpull : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w =
      h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w)) :
    ContMDiff I J ((r : ℕ∞ω) + 2) f := by
  have hr0 : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le (by norm_num) hr)
  have hrr : (r : ℕ∞ω) ≤ (r : ℕ∞ω) + 2 := le_add_of_nonneg_right zero_le
  let : IsManifold I (r : ℕ∞ω) M := IsManifold.of_le hrr
  let : IsManifold J (r : ℕ∞ω) N := IsManifold.of_le hrr
  let : DifferentialGeometry.ContinuousDualEquiv E :=
    IsCoercive.continuousDualEquivOfFiniteDimensional
  intro x
  let L : E ≃L[ℝ] F := f.mfderivToContinuousLinearEquiv hr0 x
  let a := DifferentialGeometry.PartialDiffeomorph.extChartAt I ((r : ℕ∞ω) + 2) x
  let l : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ((r : ℕ∞ω) + 2) :=
    { toEquiv := L.toLinearEquiv.toEquiv
      contMDiff_toFun := L.contDiff.contMDiff
      contMDiff_invFun := L.symm.contDiff.contMDiff }
  let b := (DifferentialGeometry.PartialDiffeomorph.extChartAt J
    ((r : ℕ∞ω) + 2) (f x)).trans l.symm.toPartialDiffeomorph
  let ar := DifferentialGeometry.PartialDiffeomorph.ofLE a hrr
  let br := DifferentialGeometry.PartialDiffeomorph.ofLE b hrr
  let P := (ar.symm.trans f.toPartialDiffeomorph).trans br
  have hax : x ∈ a.source := mem_extChartAt_source x
  have hbx : f x ∈ b.source := ⟨mem_extChartAt_source (f x), mem_univ _⟩
  have hPx : a x ∈ P.source := by
    refine ⟨⟨a.map_source hax, mem_univ _⟩, ?_⟩
    change f (a.symm (a x)) ∈ b.source
    exact (congrArg (fun z => f z ∈ b.source) (a.left_inv hax)).mpr hbx
  have hPmap : MapsTo P P.source b.target := fun y hy => hy.2 |> b.map_source
  have hPsrc : P.source ⊆ a.target := fun y hy => hy.1.1
  have hbP (y : E) (hy : y ∈ P.source) : P y ∈ b.target := hPmap hy
  have hPeq (y : E) (hy : y ∈ P.source) : b.symm (P y) = f (a.symm y) :=
    b.left_inv hy.2
  have hmetric (y : E) (hy : y ∈ P.source) (v w : E) :
      coordinateMetric g a.symm y v w =
        coordinateMetric h b.symm (P y) (fderiv ℝ P y v) (fderiv ℝ P y w) := by
    have haD := a.symm.mdifferentiableAt (by simp) (hPsrc hy)
    have hfD := f.contMDiff.mdifferentiableAt (x := a.symm y) hr0
    have hbD := b.symm.mdifferentiableAt (by simp) (hbP y hy)
    have hPD := P.mdifferentiableAt hr0 hy
    have heq : b.symm ∘ P =ᶠ[𝓝 y] f ∘ a.symm := by
      filter_upwards [P.open_source.mem_nhds hy] with z hz
      exact hPeq z hz
    have hd := (mfderiv_comp y hbD hPD).symm.trans
      (heq.mfderiv_eq.trans (mfderiv_comp y hfD haD))
    rw [mfderiv_eq_fderiv] at hd
    have hdv : (mfderiv 𝓘(ℝ, E) J b.symm (P y) : E →L[ℝ] F) (fderiv ℝ P y v) =
        (mfderiv I J f (a.symm y) : E →L[ℝ] F)
          ((mfderiv 𝓘(ℝ, E) I a.symm y : E →L[ℝ] E) v) :=
      congrArg (fun D : E →L[ℝ] F => D v) hd
    have hdw : (mfderiv 𝓘(ℝ, E) J b.symm (P y) : E →L[ℝ] F) (fderiv ℝ P y w) =
        (mfderiv I J f (a.symm y) : E →L[ℝ] F)
          ((mfderiv 𝓘(ℝ, E) I a.symm y : E →L[ℝ] E) w) :=
      congrArg (fun D : E →L[ℝ] F => D w) hd
    change g.inner (a.symm y) (mfderiv 𝓘(ℝ, E) I a.symm y v)
      (mfderiv 𝓘(ℝ, E) I a.symm y w) =
      h.inner (b.symm (P y)) (mfderiv 𝓘(ℝ, E) J b.symm (P y) (fderiv ℝ P y v))
        (mfderiv 𝓘(ℝ, E) J b.symm (P y) (fderiv ℝ P y w))
    rw [hPeq y hy, hpull]
    erw [hdv, hdw]
  have hPDiff : ContDiffOn ℝ ((r : ℕ∞ω) + 2) P P.source := by
    apply contDiffOn_of_metric_pullback P.open_source b.open_target
      ((coordinateMetric_regular g a.symm).mono hPsrc)
      (coordinateMetric_regular h b.symm)
    · intro y hy v w
      exact h.symm (b.symm y) _ _
    · intro y hy
      exact coordinateMetric_coercive h b.symm hy
    · exact P.contMDiffOn_toFun.contDiffOn.of_le (WithTop.coe_le_coe.mpr hr)
    · exact hPmap
    · intro y hy
      have hi := (P.isLocalDiffeomorphAt _ _ _ hy).isInvertible_mfderiv hr0
      rwa [mfderiv_eq_fderiv] at hi
    · exact hmetric
  have hPAt : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ((r : ℕ∞ω) + 2) P (a x) :=
    (hPDiff.contDiffAt (P.open_source.mem_nhds hPx)).contMDiffAt
  have hba : ContMDiffAt I J ((r : ℕ∞ω) + 2) (b.symm ∘ P ∘ a) x :=
    (b.symm.contMDiffOn_toFun.contMDiffAt (b.open_target.mem_nhds (hbP _ hPx))).comp x
      (hPAt.comp x (a.contMDiffOn_toFun.contMDiffAt (a.open_source.mem_nhds hax)))
  apply hba.congr_of_eventuallyEq
  have hc := a.contMDiffOn_toFun.continuousOn.continuousAt (a.open_source.mem_nhds hax)
  filter_upwards [a.open_source.mem_nhds hax, hc.preimage_mem_nhds
    (P.open_source.mem_nhds hPx)] with z hz hPz
  exact ((hPeq (a z) hPz).trans (congrArg f (a.left_inv hz))).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [I.Boundaryless] [J.Boundaryless]
  [IsManifold I ((r : ℕ∞ω) + 2) M] [IsManifold J ((r : ℕ∞ω) + 2) N] in
private theorem metric_inverse_preserves
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J ((r : ℕ∞ω) + 1) F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N r) (hr : 2 ≤ r)
    (hpull : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w =
      h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (y : N) (v w : TangentSpace J y) :
    h.inner y v w = g.inner (f.symm y) (mfderiv J I f.symm y v)
      (mfderiv J I f.symm y w) := by
  have hr0 : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast ne_of_gt (lt_of_lt_of_le (by norm_num) hr)
  have heq : f ∘ f.symm = (id : N → N) := funext f.apply_symm_apply
  have hd := mfderiv_comp y (f.contMDiff.mdifferentiableAt (x := f.symm y) hr0)
    (f.symm.contMDiff.mdifferentiableAt (x := y) hr0)
  rw [heq, mfderiv_id] at hd
  change (ContinuousLinearMap.id ℝ F) =
    (mfderiv I J f (f.symm y) : E →L[ℝ] F).comp
      (mfderiv J I f.symm y : F →L[ℝ] E) at hd
  have hv : (mfderiv I J f (f.symm y) : E →L[ℝ] F)
      ((mfderiv J I f.symm y : F →L[ℝ] E) v) = v :=
    congrArg (fun A : F →L[ℝ] F => A v) hd.symm
  have hw : (mfderiv I J f (f.symm y) : E →L[ℝ] F)
      ((mfderiv J I f.symm y : F →L[ℝ] E) w) = w :=
    congrArg (fun A : F →L[ℝ] F => A w) hd.symm
  have hp := hpull (f.symm y) (mfderiv J I f.symm y v) (mfderiv J I f.symm y w)
  change (g.inner (f.symm y) : E →L[ℝ] E →L[ℝ] ℝ)
    ((mfderiv J I f.symm y : F →L[ℝ] E) v) ((mfderiv J I f.symm y : F →L[ℝ] E) w) =
    (h.inner (f (f.symm y)) : F →L[ℝ] F →L[ℝ] ℝ)
      ((mfderiv I J f (f.symm y) : E →L[ℝ] F) ((mfderiv J I f.symm y : F →L[ℝ] E) v))
      ((mfderiv I J f (f.symm y) : E →L[ℝ] F) ((mfderiv J I f.symm y : F →L[ℝ] E) w)) at hp
  rw [f.apply_symm_apply] at hp
  erw [hv, hw] at hp
  exact hp.symm

def upgradeMetricDiffeomorph
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J ((r : ℕ∞ω) + 1) F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N r) (hr : 2 ≤ r)
    (hpull : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w =
      h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w)) :
    Diffeomorph I J M N ((r : ℕ∞ω) + 2) where
  toEquiv := f.toEquiv
  contMDiff_toFun := metric_map_regular g h f hr hpull
  contMDiff_invFun := metric_map_regular h g f.symm hr
    (metric_inverse_preserves g h f hr hpull)

theorem upgradeMetricDiffeomorph_toEquiv
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J ((r : ℕ∞ω) + 1) F (TangentSpace J : N → Type _))
    (f : Diffeomorph I J M N r) (hr : 2 ≤ r)
    (hpull : ∀ (x : M) (v w : TangentSpace I x), g.inner x v w =
      h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w)) :
    (upgradeMetricDiffeomorph g h f hr hpull).toEquiv = f.toEquiv := rfl

open DifferentialGeometry.Geometry.ExactSplitting in
def realMetricIdentityUpgrade : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ 4 :=
  upgradeMetricDiffeomorph (r := 2) realFrameMetric realFrameMetric
    (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ 2) le_rfl (by
      intro x v w
      change realFrameMetric.inner x v w =
        realFrameMetric.inner x (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x v)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id x w)
      rw [mfderiv_id]
      rfl)

theorem realMetricIdentityUpgrade_apply (x : ℝ) : realMetricIdentityUpgrade x = x := rfl

end DifferentialGeometry.Geometry.MetricIsometry
