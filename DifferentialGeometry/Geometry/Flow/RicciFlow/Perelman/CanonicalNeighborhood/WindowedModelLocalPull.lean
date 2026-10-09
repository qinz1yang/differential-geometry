import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessComparisonConstruction
import DifferentialGeometry.Geometry.Metric.Construction.TensorOpenExtension
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Manifold.ULift
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPullback
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Bundle.Orientation.Map

set_option autoImplicit false

noncomputable section

open Set Bundle Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]

private def pullbackOrientationAt (o : TangentOrientationSection M) {f : N → M}
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) (y : N) :
    Orientation ℝ (TangentSpace ThreeModel y) (Fin 3) :=
  Orientation.map (Fin 3) (hf.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv.symm
    (o.orientation (f y))

private theorem mem_trivializationAt_baseSet_self (z : M) :
    z ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) z).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet]
  exact mem_chart_source ThreeSpace z

private theorem isCompatibleOrientation_pullbackOrientationAt (o : TangentOrientationSection M)
    {f : N → M} (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) :
    DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := ThreeSpace)
      (TangentSpace ThreeModel) (pullbackOrientationAt o hf) := by
  intro x
  let t := trivializationAt ThreeSpace (TangentSpace ThreeModel) x
  let T := trivializationAt ThreeSpace (TangentSpace ThreeModel) (f x)
  have hxt : x ∈ t.baseSet := mem_trivializationAt_baseSet_self x
  obtain ⟨UM, hUMo, hfxU, hUMT, hconst⟩ :=
    o.locally_constant (f x) (f x) (mem_trivializationAt_baseSet_self (f x))
  set c := Orientation.map (Fin 3)
    (tangentChartEquiv M (f x) (f x) (mem_trivializationAt_baseSet_self (f x)))
    (o.orientation (f x))
  let A : N → ThreeSpace →L[ℝ] ThreeSpace :=
    inTangentCoordinates ThreeModel ThreeModel id f (mfderiv ThreeModel ThreeModel f) x
  have hA : ContinuousAt A x :=
    ((hf x).contMDiffAt.mfderiv_const (m := 0) (by simp)).continuousAt
  have hdet : ContinuousAt (fun y => (A y).det) x :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hA
  let e := fun y => (hf.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ ThreeSpace := by simp
  have hkey : ∀ y (hy : y ∈ t.baseSet) (hfy : f y ∈ UM),
      ∃ B : ThreeSpace ≃ₗ[ℝ] ThreeSpace, (B : ThreeSpace →ₗ[ℝ] ThreeSpace) = (A y).toLinearMap ∧
        Orientation.map (Fin 3) B (Orientation.map (Fin 3) (t.linearEquivAt ℝ y hy)
          (pullbackOrientationAt o hf y)) = c := by
    intro y hy hfy
    let L := t.linearEquivAt ℝ y hy
    let Mf := T.linearEquivAt ℝ (f y) (hUMT hfy)
    refine ⟨L.symm.trans ((e y).trans Mf), ?_, ?_⟩
    · apply LinearMap.ext
      intro v
      change Mf (e y (L.symm v)) = T.continuousLinearMapAt ℝ (f y)
        (mfderiv ThreeModel ThreeModel f y (t.symmL ℝ y v))
      rw [Trivialization.symmL_apply _ hy,
        Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) (e := T) (hUMT hfy)]
      rfl
    · unfold pullbackOrientationAt
      rw [DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        DifferentialGeometry.VectorBundle.map_orientation_trans_between]
      have hMf : (((e y).symm.trans L).trans (L.symm.trans ((e y).trans Mf))) = Mf := by
        apply LinearEquiv.ext
        intro v
        simp
      change Orientation.map (Fin 3) (((e y).symm.trans L).trans (L.symm.trans ((e y).trans Mf)))
        (o.orientation (f y)) = c
      rw [hMf]
      exact hconst (f y) hfy
  have hbaseN : t.baseSet ∩ f ⁻¹' UM ∈ 𝓝 x :=
    inter_mem (t.open_baseSet.mem_nhds hxt)
      (((hf x).contMDiffAt.continuousAt).preimage_mem_nhds (hUMo.mem_nhds hfxU))
  obtain ⟨Bx, hBx, _⟩ := hkey x hxt hfxU
  have hdx : (A x).det ≠ 0 := by
    change LinearMap.det (A x).toLinearMap ≠ 0
    rw [← hBx]
    exact Bx.isUnit_det'.ne_zero
  rcases lt_or_gt_of_ne hdx with hneg | hpos
  · refine ⟨t, inferInstance, t.baseSet ∩ f ⁻¹' UM ∩ {y | (A y).det < 0},
      inter_mem hbaseN (hdet.eventually (isOpen_Iio.mem_nhds hneg)),
      fun y hy => hy.1.1, -c, fun y hy => ?_⟩
    obtain ⟨B, hB, hBc⟩ := hkey y hy.1.1 hy.1.2
    have hBdet : LinearMap.det (B : ThreeSpace →ₗ[ℝ] ThreeSpace) < 0 := by rw [hB]; exact hy.2
    rw [(Orientation.map_eq_neg_iff_det_neg _ B hcard).2 hBdet] at hBc
    change Orientation.map (Fin 3) (t.linearEquivAt ℝ y hy.1.1) (pullbackOrientationAt o hf y) = -c
    rw [← hBc]
    exact (neg_neg (G := Orientation ℝ ThreeSpace (Fin 3)) _).symm
  · refine ⟨t, inferInstance, t.baseSet ∩ f ⁻¹' UM ∩ {y | 0 < (A y).det},
      inter_mem hbaseN (hdet.eventually (isOpen_Ioi.mem_nhds hpos)),
      fun y hy => hy.1.1, c, fun y hy => ?_⟩
    obtain ⟨B, hB, hBc⟩ := hkey y hy.1.1 hy.1.2
    have hBdet : 0 < LinearMap.det (B : ThreeSpace →ₗ[ℝ] ThreeSpace) := by rw [hB]; exact hy.2
    rw [(Orientation.map_eq_iff_det_pos _ B hcard).2 hBdet] at hBc
    exact hBc

def TangentOrientationSection.pullback (o : TangentOrientationSection M) {f : N → M}
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) : TangentOrientationSection N where
  orientation := pullbackOrientationAt o hf
  locally_constant := by
    obtain ⟨O, hO⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_compatibleOrientation
      ThreeModel (by simp) _ (isCompatibleOrientation_pullbackOrientationAt o hf)
    rw [← hO]
    exact O.locally_constant

theorem TangentOrientationSection.preservesTangentOrientationAt_pullback
    (o : TangentOrientationSection M) {f : N → M}
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) (y : N) :
    ∃ hb : Function.Bijective (mfderiv ThreeModel ThreeModel f y),
      PreservesTangentOrientationAt (o.pullback hf) o f y hb := by
  let e := hf.mfderivToContinuousLinearEquiv (by simp) y
  refine ⟨e.bijective, ?_⟩
  have he : LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel f y).toLinearMap e.bijective =
      e.toLinearEquiv := LinearEquiv.ext fun _ => rfl
  unfold PreservesTangentOrientationAt
  rw [he]
  change Orientation.map (Fin 3) e.toLinearEquiv
    (Orientation.map (Fin 3) e.toLinearEquiv.symm (o.orientation (f y))) = o.orientation (f y)
  rw [DifferentialGeometry.VectorBundle.map_orientation_trans_between, LinearEquiv.symm_trans_self,
    Orientation.map_refl]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Metric (riemannianBallOf_subset_interior_riemannianClosedBallOf)

section Comparison

variable {P : Type*} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {L : Type*} [TopologicalSpace L] [ChartedSpace ThreeSpace L] [IsManifold I3 ∞ L]
  [T2Space L] [SigmaCompactSpace L]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace ThreeSpace Q] [IsManifold I3 ∞ Q]
  {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

omit [SigmaCompactSpace L] in
private theorem exists_tensor0SField_eq_partialPullback (G : PartialDiffeomorph I3 I3 L M ∞)
    {K : Set L} (hK : IsCompact K) (hKG : K ⊆ G.source)
    (A : Tensor0SField (I := I3) (M := M) (n := ∞) 2) :
    ∃ B : Tensor0SField (I := I3) (M := L) (n := ∞) 2, ∀ y ∈ K,
      ∀ v : Fin 2 → TangentSpace I3 y,
        B y v = A (G y) (fun j => mfderiv I3 I3 G y (v j)) := by
  let U : TopologicalSpace.Opens L := ⟨G.source, G.open_source⟩
  let V : TopologicalSpace.Opens M :=
    ⟨G '' (U : Set L), DifferentialGeometry.image_opens_isOpen G (U := U) subset_rfl⟩
  let psi := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo G (U := U) subset_rfl
  let C := pullbackTensor02FieldCross psi (restrictOpen0S (I := I3) 2 (V := V) A)
  obtain ⟨B, hB⟩ := DifferentialGeometry.exists_tensor0SField_eqOn_openSubtype 2 U hK hKG C
  refine ⟨B, fun y hy v => ?_⟩
  refine (hB ⟨y, hKG hy⟩ hy v).trans ?_
  refine (pullbackTensor02FieldCross_apply psi _ ⟨y, hKG hy⟩ v).trans ?_
  change A (G y) (fun j => mfderiv I3 I3 psi ⟨y, hKG hy⟩ (v j)) = _
  congr 1
  funext j
  exact DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo G subset_rfl _ (v j)

private def MetricComparisonOn.transportLocalIsometry {h : ℝ → SmoothRiemannianMetric I3 P}
    {g : ℝ → SmoothRiemannianMetric I3 Q} {F : P → Q} {U : Set P} {times : Set ℝ} {order : ℕ}
    {eps : ℝ} (C : MetricComparisonOn h g F U times order eps) (Ψ : L ≃ₘ⟮I3, I3⟯ P)
    (g' : ℝ → SmoothRiemannianMetric I3 M) (G : PartialDiffeomorph I3 I3 L M ∞)
    (hK : IsCompact (Ψ ⁻¹' U)) (hKG : Ψ ⁻¹' U ⊆ G.source)
    (hG : ∀ s ∈ times, ∀ y ∈ Ψ ⁻¹' U, ∀ v w : TangentSpace I3 y,
      (g s).inner (F (Ψ y)) (mfderiv I3 I3 F (Ψ y) (mfderiv I3 I3 Ψ y v))
          (mfderiv I3 I3 F (Ψ y) (mfderiv I3 I3 Ψ y w)) =
        (g' s).inner (G y) (mfderiv I3 I3 G y v) (mfderiv I3 I3 G y w)) :
    MetricComparisonOn (fun s => DifferentialGeometry.Diffeomorph.pullbackMetricCross (h s) Ψ)
      g' G (Ψ ⁻¹' U) times order eps := by
  classical
  have hB := fun s => exists_tensor0SField_eq_partialPullback G hK hKG
    (metricTensorField (I := I3) (g' s))
  choose B hB using hB
  refine
    { pullback := fun s => if s ∈ times then pullbackTensor02FieldCross Ψ (C.pullback s) else B s
      pullback_eq := ?_
      jet := fun b s => if b = 0 ∧ s ∉ times then
          B s - metricTensorField (I := I3)
            (DifferentialGeometry.Diffeomorph.pullbackMetricCross (h s) Ψ)
        else pullbackTensor02FieldCross Ψ (C.jet b s)
      jet_zero := ?_
      jet_succ := ?_
      equivalence := ?_
      close := ?_ }
  · intro s y hy v
    by_cases hs : s ∈ times
    · simp only [ite_eq_left hs]
      rw [pullbackTensor02FieldCross_apply, C.pullback_eq s (Ψ y) hy]
      exact hG s hs y hy (v 0) (v 1)
    · simp only [ite_eq_right hs]
      rw [hB s y hy v, metricTensorField_apply]
  · intro s y v
    by_cases hs : s ∈ times
    · simp only [hs, not_true_eq_false, and_false, ite_false, ite_true]
      rw [pullbackTensor02FieldCross_apply, pullbackTensor02FieldCross_apply, C.jet_zero,
        DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner]
    · simp only [hs, not_false_eq_true, and_self, ite_true, ite_false]
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
        metricTensorField_apply]
  · intro b s hs y hy v
    simp only [Nat.add_one_ne_zero, false_and, ite_false]
    rw [pullbackTensor02FieldCross_apply, C.jet_succ b s hs (Ψ y) hy]
    apply derivWithin_congr
    · intro a ha
      simp only [ha, not_true_eq_false, and_false, ite_false, pullbackTensor02FieldCross_apply]
    · simp only [hs, not_true_eq_false, and_false, ite_false, pullbackTensor02FieldCross_apply]
  · intro s hs y hy v
    simp only [ite_eq_left hs]
    rw [pullbackTensor02FieldCross_apply,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner]
    exact C.equivalence s hs (Ψ y) hy (mfderiv I3 I3 Ψ y v)
  · intro a b hab s hs y hy
    simp only [hs, not_true_eq_false, and_false, ite_false]
    rw [tensor02CovDerivNormWith_pullbackTensor02FieldCross]
    exact C.close a b hab s hs (Ψ y) hy

omit [SigmaCompactSpace L] [T2Space P] [SigmaCompactSpace P] in
private theorem riemannianClosedBallOf_pullbackMetricCross_symm
    (g : SmoothRiemannianMetric I3 P) (Ψ : L ≃ₘ⟮I3, I3⟯ P) (p : P) (r : ℝ) :
    riemannianClosedBallOf (DifferentialGeometry.Diffeomorph.pullbackMetricCross g Ψ)
        (Ψ.symm p) r = Ψ ⁻¹' riemannianClosedBallOf g p r := by
  ext y
  change riemannianEDistOf (DifferentialGeometry.Diffeomorph.pullbackMetricCross g Ψ)
      (Ψ.symm p) y ≤ _ ↔ riemannianEDistOf g p (Ψ y) ≤ _
  rw [DifferentialGeometry.riemannianEDistOf_pullbackMetricCross, Diffeomorph.apply_symm_apply]

private theorem preservesTangentOrientationAt_comp {A B C : Type*} [TopologicalSpace A]
    [ChartedSpace ThreeSpace A] [IsManifold I3 ∞ A] [TopologicalSpace B] [ChartedSpace ThreeSpace B]
    [IsManifold I3 ∞ B] [TopologicalSpace C] [ChartedSpace ThreeSpace C] [IsManifold I3 ∞ C]
    {oA : TangentOrientationSection A} {oB : TangentOrientationSection B}
    {oC : TangentOrientationSection C} {f : A → B} {g : B → C} {y : A}
    (hf : MDifferentiableAt I3 I3 f y) (hg : MDifferentiableAt I3 I3 g (f y))
    (hbf : Function.Bijective (mfderiv I3 I3 f y))
    (hbg : Function.Bijective (mfderiv I3 I3 g (f y)))
    (hpf : PreservesTangentOrientationAt oA oB f y hbf)
    (hpg : PreservesTangentOrientationAt oB oC g (f y) hbg) :
    ∃ hb : Function.Bijective (mfderiv I3 I3 (g ∘ f) y),
      PreservesTangentOrientationAt oA oC (g ∘ f) y hb := by
  have hcomp : mfderiv I3 I3 (g ∘ f) y = (mfderiv I3 I3 g (f y)).comp (mfderiv I3 I3 f y) :=
    mfderiv_comp y hg hf
  have hb : Function.Bijective (mfderiv I3 I3 (g ∘ f) y) := by
    rw [hcomp]
    exact hbg.comp hbf
  refine ⟨hb, ?_⟩
  unfold PreservesTangentOrientationAt at hpf hpg ⊢
  have he : LinearEquiv.ofBijective (mfderiv I3 I3 (g ∘ f) y).toLinearMap hb =
      (LinearEquiv.ofBijective (mfderiv I3 I3 f y).toLinearMap hbf).trans
        (LinearEquiv.ofBijective (mfderiv I3 I3 g (f y)).toLinearMap hbg) := by
    apply LinearEquiv.ext
    intro v
    simp only [LinearEquiv.ofBijective_apply, LinearEquiv.trans_apply,
      ContinuousLinearMap.coe_coe, hcomp, ContinuousLinearMap.comp_apply]
  rw [he, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between, hpf, hpg]
  rfl

end Comparison

universe u v

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  DifferentialGeometry.Topology.uliftChartedSpace DifferentialGeometry.Topology.isManifold_ulift

variable {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] {M : Type (max u v)} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {DN DM : RealTimeInterval} {S : SolutionOn (I := I3) (M := N) DN}
  {S' : SolutionOn (I := I3) (M := M) DM} {eps kappa : ℝ} {x : N} {t : ℝ}

def WindowedModelWitness.ofLocalPull (W : WindowedModelWitness eps kappa S x t)
    (Φ : PartialDiffeomorph I3 I3 N M ∞) (hΦ : Φ.source = univ) (ht : t ∈ DM.carrier)
    (hwin : Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ DM.carrier)
    (hmetric : ∀ τ ∈ Icc (t - (eps * S.scalar t x)⁻¹) t, ∀ y (v w : TangentSpace I3 y),
      (S.base.metric τ).inner y v w =
        (S'.base.metric τ).inner (Φ y) (mfderiv I3 I3 Φ y v) (mfderiv I3 I3 Φ y w)) :
    WindowedModelWitness eps kappa S' (Φ x) t := by
  let _ : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let P := W.model
  let Ψ : ULift.{u} P.M ≃ₘ⟮I3, I3⟯ P.M :=
    (DifferentialGeometry.Topology.uliftDiffeomorph I3 P.M).symm
  let P' := P.pullback Ψ
  let G : PartialDiffeomorph I3 I3 (ULift.{u} P.M) M ∞ :=
    Ψ.toPartialDiffeomorph.trans (W.embedding.trans Φ)
  have hΦl : IsLocalDiffeomorph I3 I3 ∞ Φ := fun y =>
    Φ.isLocalDiffeomorphAt I3 I3 ∞ (by rw [hΦ]; exact mem_univ y)
  have hR : 0 ≤ (eps * S.scalar t x)⁻¹ := inv_nonneg.mpr (mul_pos W.eps_pos W.scalar_pos).le
  have htwin : t ∈ Icc (t - (eps * S.scalar t x)⁻¹) t := ⟨by linarith, le_rfl⟩
  have hsc : S'.scalar t (Φ x) = S.scalar t x := by
    have hmet : S.base.metric t = localPullMetric (S'.base.metric t) Φ hΦl :=
      SmoothRiemannianMetric.ext_inner fun y v w =>
        (hmetric t htwin y v w).trans (localPullMetric_inner _ _ _ y v w).symm
    change metricScalarAt (S'.base.metric t) (Φ x) = metricScalarAt (S.base.metric t) x
    rw [hmet, metricScalarAt_localPull]
  have hQ : 0 < S'.scalar t (Φ x) := hsc ▸ W.scalar_pos
  have hpara : ∀ s ∈ Icc (-modelDepth eps) 0,
      parabolicTime t (S.scalar t x) s ∈ Icc (t - (eps * S.scalar t x)⁻¹) t := by
    intro s hs
    have hQx := W.scalar_pos
    have h1 : -modelDepth eps / S.scalar t x ≤ s / S.scalar t x :=
      div_le_div_of_nonneg_right hs.1 hQx.le
    have h2 : s / S.scalar t x ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hQx.le
    have h3 : -modelDepth eps / S.scalar t x = -(eps * S.scalar t x)⁻¹ := by
      rw [modelDepth, mul_inv, neg_div, div_eq_mul_inv]
    refine ⟨?_, ?_⟩ <;> dsimp only [parabolicTime] <;> linarith
  have hballs : ∀ r, riemannianClosedBallOf (P'.S.base.metric 0) P'.basepoint r =
      Ψ ⁻¹' riemannianClosedBallOf (P.S.base.metric 0) P.basepoint r := fun r =>
    riemannianClosedBallOf_pullbackMetricCross_symm (P.S.base.metric 0) Ψ P.basepoint r
  have hGsrc : ∀ y, y ∈ G.source ↔ Ψ y ∈ W.embedding.source := by
    intro y
    change (y ∈ univ ∧ Ψ y ∈ W.embedding.source ∧ W.embedding (Ψ y) ∈ Φ.source) ↔ _
    rw [hΦ]
    simp only [mem_univ, and_true, true_and]
  have hsmall : riemannianClosedBallOf (P.S.base.metric 0) P.basepoint (modelRadius eps) ⊆
      W.embedding.source :=
    (riemannianClosedBallOf_mono _ _ (by linarith)).trans W.buffered_ball
  have hanc : IsAncientKappaSolution kappa P' :=
    P.pullback_isAncientKappaSolution Ψ W.model_ancient
  have hcpt : IsCompact (riemannianClosedBallOf (P'.S.base.metric 0) P'.basepoint
      (modelRadius eps)) :=
    DifferentialGeometry.RiemannianMetricComplete.closedEBall_isCompact
      (⟨hanc.complete 0 (by simp)⟩ : RiemannianMetricComplete (P'.S.base.metric 0)) _ _
  have hGsub : riemannianClosedBallOf (P'.S.base.metric 0) P'.basepoint (modelRadius eps) ⊆
      G.source := by
    intro y hy
    rw [hballs] at hy
    exact (hGsrc y).2 (hsmall hy)
  let g' := rescaledMetric S' t (S'.scalar t (Φ x)) hQ
  have hcomp : MetricComparisonOn (fun s => P'.S.base.metric s) g' G
      (riemannianClosedBallOf (P'.S.base.metric 0) P'.basepoint (modelRadius eps))
      (Icc (-modelDepth eps) 0) (modelOrder eps) eps := by
    have hK := hcpt
    have hKG := hGsub
    rw [hballs] at hK hKG ⊢
    refine W.comparison.transportLocalIsometry Ψ g' G hK hKG ?_
    intro s hs y hy v w
    have hFd : MDifferentiableAt I3 I3 W.embedding (Ψ y) :=
      W.embedding.mdifferentiableAt (by decide) (hsmall hy)
    have hΨd : MDifferentiableAt I3 I3 Ψ y := (Ψ.contMDiff y).mdifferentiableAt (by decide)
    have hΦd : MDifferentiableAt I3 I3 Φ (W.embedding (Ψ y)) :=
      Φ.mdifferentiableAt (by decide) (by rw [hΦ]; exact mem_univ _)
    have hGd : mfderiv I3 I3 G y =
        (mfderiv I3 I3 Φ (W.embedding (Ψ y))).comp
          ((mfderiv I3 I3 W.embedding (Ψ y)).comp (mfderiv I3 I3 Ψ y)) := by
      rw [show (G : ULift.{u} P.M → M) = Φ ∘ (W.embedding ∘ Ψ) from rfl,
        mfderiv_comp y hΦd (hFd.comp y hΨd), mfderiv_comp y hFd hΨd]
      rfl
    rw [hGd]
    simp only [g', rescaledMetric, scaleMetric_inner, hsc]
    rw [hmetric _ (hpara s hs)]
    rfl
  have hbase : G P'.basepoint = Φ x := by
    change Φ (W.embedding (Ψ (Ψ.symm P.basepoint))) = Φ x
    rw [Diffeomorph.apply_symm_apply, W.base_map]
  exact
    { eps_pos := W.eps_pos
      eps_lt_one := W.eps_lt_one
      time_mem := ht
      scalar_pos := hQ
      window_mem := by rw [hsc]; exact hwin
      model := P'
      model_ancient := hanc
      model_scalar_base := by
        change (P.S.pullback Ψ).scalar 0 (Ψ.symm P.basepoint) = 1
        rw [SolutionOn.pullback_scalar, Diffeomorph.apply_symm_apply]
        exact W.model_scalar_base
      embedding := G
      buffered_ball := by
        intro y hy
        rw [hballs] at hy
        exact (hGsrc y).2 (W.buffered_ball hy)
      base_map := hbase
      comparison := hcomp
      source_capture := by
        obtain ⟨eta, heta, hcapture⟩ := MetricComparisonOn.exists_source_capture_reserve
          (fun s => P'.S.base.metric s) g' G P'.basepoint
          (⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩ :
            (0 : ℝ) ∈ Icc (-modelDepth eps) 0)
          W.eps_pos W.eps_lt_one hcomp hcpt hGsub
        intro z hz
        have hz' : z ∈ riemannianClosedBallOf (g' 0) (G P'.basepoint)
            (modelRadius eps - 1 + eta) := by
          rw [hbase]
          exact riemannianClosedBallOf_mono _ _ (by linarith) (interior_subset
            (riemannianBallOf_subset_interior_riemannianClosedBallOf _ _ _ hz))
        obtain ⟨w, hw, rfl⟩ := hcapture hz'
        exact ⟨w, hGsub hw, rfl⟩ }

theorem WindowedModelWitness.ofLocalPull_model (W : WindowedModelWitness eps kappa S x t)
    (Φ : PartialDiffeomorph I3 I3 N M ∞) (hΦ : Φ.source = univ) (ht : t ∈ DM.carrier)
    (hwin : Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ DM.carrier)
    (hmetric : ∀ τ ∈ Icc (t - (eps * S.scalar t x)⁻¹) t, ∀ y (v w : TangentSpace I3 y),
      (S.base.metric τ).inner y v w =
        (S'.base.metric τ).inner (Φ y) (mfderiv I3 I3 Φ y v) (mfderiv I3 I3 Φ y w)) :
    (W.ofLocalPull Φ hΦ ht hwin hmetric).model =
      W.model.pullback (DifferentialGeometry.Topology.uliftDiffeomorph.{v, u} I3 W.model.M).symm :=
  rfl

theorem WindowedModelWitness.ofLocalPull_embedding (W : WindowedModelWitness eps kappa S x t)
    (Φ : PartialDiffeomorph I3 I3 N M ∞) (hΦ : Φ.source = univ) (ht : t ∈ DM.carrier)
    (hwin : Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ DM.carrier)
    (hmetric : ∀ τ ∈ Icc (t - (eps * S.scalar t x)⁻¹) t, ∀ y (v w : TangentSpace I3 y),
      (S.base.metric τ).inner y v w =
        (S'.base.metric τ).inner (Φ y) (mfderiv I3 I3 Φ y v) (mfderiv I3 I3 Φ y w)) :
    (W.ofLocalPull Φ hΦ ht hwin hmetric).embedding =
      ((DifferentialGeometry.Topology.uliftDiffeomorph.{v, u} I3
        W.model.M).symm.toPartialDiffeomorph).trans (W.embedding.trans Φ) :=
  rfl

theorem OrientedWitness.ofLocalPull {oN : TangentOrientationSection N}
    {o : TangentOrientationSection M} (h : OrientedWitness S oN eps kappa x t)
    (Φ : PartialDiffeomorph I3 I3 N M ∞) (hΦ : Φ.source = univ)
    (hor : ∀ y, ∃ hb : Function.Bijective (mfderiv I3 I3 Φ y),
      PreservesTangentOrientationAt oN o Φ y hb)
    (ht : t ∈ DM.carrier) (hwin : Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ DM.carrier)
    (hmetric : ∀ τ ∈ Icc (t - (eps * S.scalar t x)⁻¹) t, ∀ y (v w : TangentSpace I3 y),
      (S.base.metric τ).inner y v w =
        (S'.base.metric τ).inner (Φ y) (mfderiv I3 I3 Φ y v) (mfderiv I3 I3 Φ y w)) :
    OrientedWitness S' o eps kappa (Φ x) t := by
  obtain ⟨W, oP, hoP⟩ := h
  let Ψ : ULift.{u} W.model.M ≃ₘ⟮I3, I3⟯ W.model.M :=
    (DifferentialGeometry.Topology.uliftDiffeomorph I3 W.model.M).symm
  refine ⟨W.ofLocalPull Φ hΦ ht hwin hmetric, oP.pullback Ψ.isLocalDiffeomorph, ?_⟩
  intro y hy
  have hy' : Ψ y ∈ W.embedding.source := by
    change y ∈ univ ∧ Ψ y ∈ W.embedding.source ∧ W.embedding (Ψ y) ∈ Φ.source at hy
    exact hy.2.1
  obtain ⟨hb₁, hp₁⟩ := oP.preservesTangentOrientationAt_pullback Ψ.isLocalDiffeomorph y
  obtain ⟨hb₂, hp₂⟩ := hoP (Ψ y) hy'
  obtain ⟨hb₃, hp₃⟩ := hor (W.embedding (Ψ y))
  have hΨd : MDifferentiableAt I3 I3 Ψ y := (Ψ.contMDiff y).mdifferentiableAt (by decide)
  have hFd : MDifferentiableAt I3 I3 W.embedding (Ψ y) :=
    W.embedding.mdifferentiableAt (by decide) hy'
  have hΦd : MDifferentiableAt I3 I3 Φ (W.embedding (Ψ y)) :=
    Φ.mdifferentiableAt (by decide) (by rw [hΦ]; exact mem_univ _)
  obtain ⟨hb₄, hp₄⟩ := preservesTangentOrientationAt_comp (A := ULift.{u} W.model.M) hΨd hFd
    hb₁ hb₂ hp₁ hp₂
  have hFΨd : MDifferentiableAt I3 I3 (W.embedding ∘ Ψ) y := hFd.comp y hΨd
  obtain ⟨hb₅, hp₅⟩ := preservesTangentOrientationAt_comp (A := ULift.{u} W.model.M)
    hFΨd hΦd hb₄ hb₃ hp₄ hp₃
  exact ⟨hb₅, hp₅⟩

theorem OrientedWitness.ofLocalPull_of_pullback {o : TangentOrientationSection M}
    (Φ : PartialDiffeomorph I3 I3 N M ∞) (hΦ : Φ.source = univ)
    (hΦl : IsLocalDiffeomorph I3 I3 ∞ Φ) (h : OrientedWitness S (o.pullback hΦl) eps kappa x t)
    (ht : t ∈ DM.carrier) (hwin : Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ DM.carrier)
    (hmetric : ∀ τ ∈ Icc (t - (eps * S.scalar t x)⁻¹) t,
      S.base.metric τ = localPullMetric (S'.base.metric τ) Φ hΦl) :
    OrientedWitness S' o eps kappa (Φ x) t :=
  h.ofLocalPull Φ hΦ (o.preservesTangentOrientationAt_pullback hΦl) ht hwin
    fun τ hτ y v w => by rw [hmetric τ hτ, localPullMetric_inner]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
