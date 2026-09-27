import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientCanonicalNeighborhood

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle

universe u

theorem modelDepth_pos {eps : ℝ} (heps : 0 < eps) : 0 < modelDepth eps :=
  inv_pos.mpr heps

theorem derivWithin_Icc_eq_derivWithin_Iic {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {d : ℝ} (hd : 0 < d) (f : ℝ → G) {s : ℝ}
    (hs : s ∈ Set.Icc (-d) 0)
    (hleft : s = -d → DifferentiableWithinAt ℝ f (Set.Iic 0) s) :
    derivWithin f (Set.Icc (-d) 0) s = derivWithin f (Set.Iic 0) s := by
  rcases eq_or_ne s (-d) with rfl | hne
  · exact derivWithin_subset (fun x hx => hx.2)
      ((uniqueDiffOn_Icc (show (-d : ℝ) < 0 by linarith)).uniqueDiffWithinAt
        ⟨le_rfl, by linarith⟩)
      (hleft rfl)
  · have hlt : -d < s := lt_of_le_of_ne hs.1 (Ne.symm hne)
    refine derivWithin_congr_set ?_
    filter_upwards [eventually_gt_nhds hlt] with x hx
    exact propext ⟨fun h => h.2, fun h => ⟨le_of_lt hx, h⟩⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N] [IsManifold I3 1 N] [T2Space N] [SigmaCompactSpace N]

structure MetricComparisonOn.SourcePastExtension {eps : ℝ}
    {h : ℝ → SmoothRiemannianMetric I3 N} {ghat : ℝ → SmoothRiemannianMetric I3 M}
    {F : PartialDiffeomorph I3 I3 N M ∞}
    {U : Set N} {times : Set ℝ} {order : ℕ}
    (C : MetricComparisonOn h ghat (F : N → M) U times order eps) : Prop where
  pullback_eq_source : ∀ s, ∀ y ∈ F.source, ∀ v : Fin 2 → TangentSpace I3 y,
    C.pullback s y v = (ghat s).inner (F y)
      (mfderiv I3 I3 (F : N → M) y (v 0)) (mfderiv I3 I3 (F : N → M) y (v 1))
  jet_succ_past : ∀ b s, s ≤ 0 → ∀ y : N, ∀ v : Fin 2 → TangentSpace I3 y,
    C.jet (b + 1) s y v = derivWithin (fun a => C.jet b a y v) (Set.Iic 0) s
  jet_succ_future : ∀ b s, 0 < s → ∀ y : N, ∀ v : Fin 2 → TangentSpace I3 y,
    C.jet (b + 1) s y v = derivWithin (fun a => C.jet b a y v) (Set.Iic 0) s

def ModelComparison.pastDifferentiableOnWindow {eps : ℝ}
    {h : ℝ → SmoothRiemannianMetric I3 N} {ghat : ℝ → SmoothRiemannianMetric I3 M}
    {p : N} {x : M} {F : PartialDiffeomorph I3 I3 N M ∞}
    (C : ModelComparison (I := I3) eps h ghat p x F) : Prop :=
  ∀ (b : ℕ) (y : N),
    y ∈ riemannianClosedBallOf (I := I3) (h 0) p (modelRadius eps) →
      ∀ v : Fin 2 → TangentSpace I3 y,
      DifferentiableWithinAt ℝ (fun a => C.jet b a y v) (Set.Iic 0) (-(modelDepth eps))

def ModelComparison.toMetricComparisonOn {eps : ℝ}
    {h : ℝ → SmoothRiemannianMetric I3 N} {ghat : ℝ → SmoothRiemannianMetric I3 M}
    {p : N} {x : M} {F : PartialDiffeomorph I3 I3 N M ∞}
    (C : ModelComparison (I := I3) eps h ghat p x F) (heps : 0 < eps)
    (hext : ModelComparison.pastDifferentiableOnWindow C) :
    MetricComparisonOn h ghat (F : N → M)
      (riemannianClosedBallOf (I := I3) (h 0) p (modelRadius eps))
      (Set.Icc (-(modelDepth eps)) 0) (modelOrder eps) eps where
  pullback := C.pullback
  pullback_eq := fun s y hy v =>
    C.pullback_apply s y
      (C.buffered_ball_subset
        (riemannianClosedBallOf_mono (I := I3) (h 0) p (by linarith) hy)) v
  jet := C.jet
  jet_zero := C.jet_zero
  jet_succ := fun b s hs y hy v =>
    (C.jet_succ b s y v).trans
      (derivWithin_Icc_eq_derivWithin_Iic (modelDepth_pos heps)
        (fun a => C.jet b a y v) hs (fun hsd => hsd.symm ▸ hext b y hy v)).symm
  equivalence := C.metric_equivalence
  close := C.cm_close

def MetricComparisonOn.toModelComparison {eps : ℝ}
    {h : ℝ → SmoothRiemannianMetric I3 N} {ghat : ℝ → SmoothRiemannianMetric I3 M}
    {p : N} {x : M} {F : PartialDiffeomorph I3 I3 N M ∞}
    (C : MetricComparisonOn h ghat (F : N → M)
      (riemannianClosedBallOf (I := I3) (h 0) p (modelRadius eps))
      (Set.Icc (-(modelDepth eps)) 0) (modelOrder eps) eps)
    (hext : C.SourcePastExtension)
    (hball : riemannianClosedBallOf (I := I3) (h 0) p (modelRadius eps + 1) ⊆ F.source)
    (hbase : F p = x)
    (hcap : riemannianBallOf (I := I3) (ghat 0) x (modelRadius eps - 1) ⊆ F '' F.source) :
    ModelComparison (I := I3) eps h ghat p x F :=
  { buffered_ball_subset := hball
    base_map := hbase
    pullback := C.pullback
    pullback_apply := hext.pullback_eq_source
    jet := C.jet
    jet_zero := C.jet_zero
    jet_succ := fun b s y v => by
      by_cases hs : s ≤ 0
      · exact hext.jet_succ_past b s hs y v
      · exact hext.jet_succ_future b s (not_le.mp hs) y v
    metric_equivalence := C.equivalence
    cm_close := C.close
    source_capture := hcap }

omit [T2Space M] [SigmaCompactSpace M] in
theorem MetricComparisonOn.toModelComparison_pullback {eps : ℝ}
    {h : ℝ → SmoothRiemannianMetric I3 N} {ghat : ℝ → SmoothRiemannianMetric I3 M}
    {p : N} {x : M} {F : PartialDiffeomorph I3 I3 N M ∞}
    (C : MetricComparisonOn h ghat (F : N → M)
      (riemannianClosedBallOf (I := I3) (h 0) p (modelRadius eps))
      (Set.Icc (-(modelDepth eps)) 0) (modelOrder eps) eps)
    (hext : C.SourcePastExtension)
    (hball : riemannianClosedBallOf (I := I3) (h 0) p (modelRadius eps + 1) ⊆ F.source)
    (hbase : F p = x)
    (hcap : riemannianBallOf (I := I3) (ghat 0) x (modelRadius eps - 1) ⊆ F '' F.source) :
    (C.toModelComparison hext hball hbase hcap).pullback = C.pullback :=
  rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem MetricComparisonOn.toModelComparison_jet {eps : ℝ}
    {h : ℝ → SmoothRiemannianMetric I3 N} {ghat : ℝ → SmoothRiemannianMetric I3 M}
    {p : N} {x : M} {F : PartialDiffeomorph I3 I3 N M ∞}
    (C : MetricComparisonOn h ghat (F : N → M)
      (riemannianClosedBallOf (I := I3) (h 0) p (modelRadius eps))
      (Set.Icc (-(modelDepth eps)) 0) (modelOrder eps) eps)
    (hext : C.SourcePastExtension)
    (hball : riemannianClosedBallOf (I := I3) (h 0) p (modelRadius eps + 1) ⊆ F.source)
    (hbase : F p = x)
    (hcap : riemannianBallOf (I := I3) (ghat 0) x (modelRadius eps - 1) ⊆ F '' F.source) :
    (C.toModelComparison hext hball hbase hcap).jet = C.jet :=
  rfl

def modelComparison_refl (g : ℝ → SmoothRiemannianMetric I3 M) (p : M) {eps : ℝ}
    (heps : 0 < eps) [IsManifold I3 1 M] :
    ModelComparison (I := I3) eps g g p p (PartialDiffeomorph.refl (I := I3) M) := by
  have hfun : (↑(PartialDiffeomorph.refl (I := I3) M) : M → M) = id := by funext w; rfl
  let C : MetricComparisonOn g g (↑(PartialDiffeomorph.refl (I := I3) M) : M → M)
      (riemannianClosedBallOf (I := I3) (g 0) p (modelRadius eps))
      (Set.Icc (-(modelDepth eps)) 0) (modelOrder eps) eps :=
    { pullback := fun s => metricTensorField (I := I3) (g s)
      pullback_eq := by
        intro s y hy v
        rw [metricTensorField_apply, hfun, mfderiv_id]
        rfl
      jet := fun _ _ => 0
      jet_zero := by intro s y v; simp [metricTensorField_apply, sub_self]
      jet_succ := by intro b s hs y hy v; simp
      equivalence := by
        intro s hs y hy v
        have hnn := inner_self_nonneg (g s) y v
        simp only [metricTensorField_apply]
        constructor <;> nlinarith
      close := by
        intro a b hab s hs y hy
        exact tensor02CovDerivNormWith_zero_le heps.le (g s) a y }
  exact MetricComparisonOn.toModelComparison (C := C)
    (hext := { pullback_eq_source := by
                 intro s y hy v
                 rw [metricTensorField_apply, hfun, mfderiv_id]
                 rfl
               jet_succ_past := by intro b s hs y v; simp [C]
               jet_succ_future := by intro b s hs y v; simp [C] })
    (fun y _ => Set.mem_univ y) rfl (fun y _ => ⟨y, Set.mem_univ y, rfl⟩)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
