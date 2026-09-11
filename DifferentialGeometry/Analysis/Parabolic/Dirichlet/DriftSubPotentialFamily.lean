import DifferentialGeometry.Analysis.DenseExtension
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSeparability
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.CompactIntegral
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.DriftSubPotential
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff InnerProductSpace Manifold RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs
open DifferentialGeometry.Analysis.Sobolev.Intrinsic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private local instance driftSubPotentialFormFamilySeminormed
    {q : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) →L[ℝ]
        H1ComplDirichlet q →L[ℝ] ℝ) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q))
    (H1ComplDirichlet q →L[ℝ] ℝ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

private local instance driftSubPotentialAdjointFamilySeminormed
    {q : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup
      (H1ComplDirichlet q →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :=
  @ContinuousLinearMap.toSeminormedAddCommGroup ℝ ℝ
    (H1ComplDirichlet q)
    (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

noncomputable def dirichletDriftSubPotentialFormOnIcc
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) (T : ℝ) :
    ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q) →L[ℝ]
      H1ComplDirichlet q →L[ℝ] ℝ :=
  fun t => if t ∈ Icc (0 : ℝ) T then
    dirichletDriftSubPotentialForm q (Y t) (a t)
  else 0

noncomputable def dirichletDriftSubPotentialOnIcc
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) (T : ℝ) :
    ℝ → DirichletHs q 0 →L[ℝ] DirichletHs q (-1) :=
  fun t => dirichletL2BilinearFormToHs q
    (dirichletDriftSubPotentialFormOnIcc q Y a T t)

theorem dirichletDriftSubPotentialFormOnIcc_eq
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) {T t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    dirichletDriftSubPotentialFormOnIcc q Y a T t =
      dirichletDriftSubPotentialForm q (Y t) (a t) := by
  rw [dirichletDriftSubPotentialFormOnIcc, if_pos ht]

theorem dirichletDriftSubPotentialOnIcc_eq
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) {T t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    dirichletDriftSubPotentialOnIcc q Y a T t =
      dirichletDriftSubPotential q (Y t) (a t) := by
  unfold dirichletDriftSubPotentialOnIcc dirichletDriftSubPotential
  rw [dirichletDriftSubPotentialFormOnIcc_eq q Y a ht]

theorem norm_dirichletDriftSubPotentialFormOnIcc_le_of_bound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) {T B C : ℝ}
    (hB : 0 ≤ B)
    (hY : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      q.inner x (Y t x) (Y t x) ≤ B)
    (hC : 0 ≤ C)
    (hcoeff : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      |divergence (I := I_half n)
          (leviCivitaConnectionOfMetric (I := I_half n) q) (Y t) x + a t x| ≤ C)
    (t : ℝ) :
    ‖dirichletDriftSubPotentialFormOnIcc q Y a T t‖ ≤
      Real.sqrt B + C * ‖H1ComplDirichletToLp q‖ := by
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · rw [dirichletDriftSubPotentialFormOnIcc_eq q Y a ht]
    exact norm_dirichletDriftSubPotentialForm_le_of_bound q (Y t) (a t)
      hB (hY t ht) hC (hcoeff t ht)
  · rw [dirichletDriftSubPotentialFormOnIcc, if_neg ht, norm_zero]
    exact add_nonneg (Real.sqrt_nonneg B) (mul_nonneg hC (norm_nonneg _))

theorem norm_dirichletDriftSubPotentialOnIcc_le_of_bound
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) {T B C : ℝ}
    (hB : 0 ≤ B)
    (hY : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      q.inner x (Y t x) (Y t x) ≤ B)
    (hC : 0 ≤ C)
    (hcoeff : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      |divergence (I := I_half n)
          (leviCivitaConnectionOfMetric (I := I_half n) q) (Y t) x + a t x| ≤ C)
    (t : ℝ) :
    ‖dirichletDriftSubPotentialOnIcc q Y a T t‖ ≤
      Real.sqrt B + C * ‖H1ComplDirichletToLp q‖ := by
  exact (dirichletL2BilinearFormToHs_norm_le q
    (dirichletDriftSubPotentialFormOnIcc q Y a T t)).trans
      (norm_dirichletDriftSubPotentialFormOnIcc_le_of_bound
        q Y a hB hY hC hcoeff t)

omit [T2Space M] [CompactSpace M] in
private theorem tangentSectionAction_family_continuousOn
    {K : Set ℝ}
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hY : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.1 p.2) :
          TangentBundle (I_half n) M))
      (K ×ˢ (Set.univ : Set M)))
    {f : M → ℝ} (hf : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ f) :
    ContinuousOn
      (fun p : ℝ × M => tangentSectionAction (I := I_half n) (Y p.1) f p.2)
      (K ×ˢ (Set.univ : Set M)) := by
  have htan : Continuous
      (tangentMap (I_half n) 𝓘(ℝ, ℝ) f) :=
    hf.continuous_tangentMap (by simp)
  have hcomp : ContinuousOn
      (fun p : ℝ × M =>
        tangentMap (I_half n) 𝓘(ℝ, ℝ) f
          (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.1 p.2)))
      (K ×ˢ (Set.univ : Set M)) :=
    htan.continuousOn.comp hY (fun _ _ => Set.mem_univ _)
  have hsnd : Continuous
      (fun p : TangentBundle 𝓘(ℝ, ℝ) ℝ => p.2) :=
    (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ) (n := 0)).continuous
  exact (hsnd.continuousOn.comp hcomp (fun _ _ => Set.mem_univ _)).congr
    (fun _ _ => rfl)

private theorem continuousOn_dirichletDriftSubPotentialForm_smooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) {T : ℝ}
    (hY : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (ha : ContinuousOn (fun p : ℝ × M => a p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (u v : SmoothScalarDirichlet q) :
    ContinuousOn (fun t => dirichletDriftSubPotentialForm q (Y t) (a t)
      (smoothToLpDirichlet q u) (smoothToH1ComplDirichlet q v))
      (Icc (0 : ℝ) T) := by
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) q
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I_half n) (M := M) q
  have haction := tangentSectionAction_family_continuousOn Y hY u.smooth
  have hv : ContinuousOn (fun p : ℝ × M => v.toFun p.2)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) :=
    v.smooth.continuous.continuousOn.comp continuousOn_snd
      (fun _ _ => Set.mem_univ _)
  have hu : ContinuousOn (fun p : ℝ × M => u.toFun p.2)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) :=
    u.smooth.continuous.continuousOn.comp continuousOn_snd
      (fun _ _ => Set.mem_univ _)
  have hdrift : ContinuousOn
      (fun t : ℝ => ∫ x,
        tangentSectionAction (I := I_half n) (Y t) u.toFun x * v.toFun x ∂μ)
      (Icc (0 : ℝ) T) :=
    integral_contOn_compact μ _ isCompact_Icc (haction.mul hv)
  have hpotential : ContinuousOn
      (fun t : ℝ => ∫ x, a t x * u.toFun x * v.toFun x ∂μ)
      (Icc (0 : ℝ) T) :=
    integral_contOn_compact μ _ isCompact_Icc ((ha.mul hu).mul hv)
  refine (hdrift.sub hpotential).congr ?_
  intro t _
  exact dirichletDriftSubPotentialForm_apply_smooth q (Y t) (a t) u v

theorem dirichletDriftSubPotentialFormOnIcc_aestronglyMeasurable
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) {T : ℝ}
    (hY : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (ha : ContinuousOn (fun p : ℝ × M => a p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (u : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q))
    (v : H1ComplDirichlet q) :
    AEStronglyMeasurable
      (fun t => dirichletDriftSubPotentialFormOnIcc q Y a T t u v)
      (timeMeasure T) := by
  apply AEStronglyMeasurable.clm_apply₂_of_denseRange
    (denseRange_smoothToLpDirichlet q)
    (denseRange_smoothToH1ComplDirichlet q)
  intro u₀ v₀
  unfold timeMeasure
  have hraw := continuousOn_dirichletDriftSubPotentialForm_smooth
    q Y a hY ha u₀ v₀
  refine (hraw.aestronglyMeasurable measurableSet_Icc).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [dirichletDriftSubPotentialFormOnIcc_eq q Y a ht]

theorem dirichletDriftSubPotentialOnIcc_apply_aestronglyMeasurable
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) {T : ℝ}
    (hY : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (ha : ContinuousOn (fun p : ℝ × M => a p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (u : DirichletHs q 0) :
    AEStronglyMeasurable
      (fun t => dirichletDriftSubPotentialOnIcc q Y a T t u)
      (timeMeasure T) := by
  let B := dirichletDriftSubPotentialFormOnIcc q Y a T
  let F : ℝ → H1ComplDirichlet q →L[ℝ] ℝ :=
    fun t => B t (dirichletHsZeroEquivL2 q u)
  have hFapply (v : H1ComplDirichlet q) :
      AEStronglyMeasurable (fun t => F t v) (timeMeasure T) := by
    exact dirichletDriftSubPotentialFormOnIcc_aestronglyMeasurable
      q Y a hY ha (dirichletHsZeroEquivL2 q u) v
  have hrep := dualRepresentative_aestronglyMeasurable_of_apply_aestronglyMeasurable
    F hFapply
  have hF : AEStronglyMeasurable F (timeMeasure T) := by
    have hdual :=
      (InnerProductSpace.toDual ℝ (H1ComplDirichlet q)).continuous.comp_aestronglyMeasurable hrep
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hdual
  have hout :=
    (dirichletHsNegOneEquivH1Dual q).symm.continuous.comp_aestronglyMeasurable hF
  change AEStronglyMeasurable
    (fun t => (dirichletHsNegOneEquivH1Dual q).symm
      (B t (dirichletHsZeroEquivL2 q u))) (timeMeasure T)
  exact hout

theorem dirichletHsNegOneEquivH1Dual_driftSubPotentialOnIcc_apply_smooth
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) {T t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (u v : SmoothScalarDirichlet q) :
    dirichletHsNegOneEquivH1Dual q
        (dirichletDriftSubPotentialOnIcc q Y a T t
          ((dirichletHsZeroEquivL2 q).symm (smoothToLpDirichlet q u)))
        (smoothToH1ComplDirichlet q v) =
      (∫ x, tangentSectionAction (I := I_half n) (Y t) u.toFun x * v.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q)) -
        ∫ x, a t x * u.toFun x * v.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) q) := by
  rw [dirichletDriftSubPotentialOnIcc_eq q Y a ht]
  exact dirichletHsNegOneEquivH1Dual_driftSubPotential_apply_smooth
    q (Y t) (a t) u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space M] in
private theorem exists_driftSubPotential_coefficient_bounds
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) {K : Set ℝ} (hK : IsCompact K)
    (hY : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.1 p.2) :
          TangentBundle (I_half n) M)) (K ×ˢ (Set.univ : Set M)))
    (hdiv : ContinuousOn
      (fun p : ℝ × M => divergence (I := I_half n)
        (leviCivitaConnectionOfMetric (I := I_half n) q) (Y p.1) p.2)
      (K ×ˢ (Set.univ : Set M)))
    (ha : ContinuousOn (fun p : ℝ × M => a p.1 p.2)
      (K ×ˢ (Set.univ : Set M))) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      (∀ t ∈ K, ∀ x : M, q.inner x (Y t x) (Y t x) ≤ B) ∧
      (∀ t ∈ K, ∀ x : M,
        |divergence (I := I_half n)
          (leviCivitaConnectionOfMetric (I := I_half n) q) (Y t) x + a t x| ≤ C) := by
  let cg := q.toContinuousRiemannianMetric
  let rb : Bundle.RiemannianBundle (TangentSpace (I_half n) : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have hsq : ContinuousOn
      (fun p : ℝ × M => q.inner p.2 (Y p.1 p.2) (Y p.1 p.2))
      (K ×ˢ (Set.univ : Set M)) := by
    exact (hY.inner_bundle (F := EuclideanSpace ℝ (Fin n))
      (E := TangentSpace (I_half n)) (b := fun p : ℝ × M => p.2) hY).congr (fun _ _ => rfl)
  obtain ⟨B, hB⟩ := (hK.prod isCompact_univ).bddAbove_image hsq
  obtain ⟨C, hC⟩ := (hK.prod isCompact_univ).bddAbove_image ((hdiv.add ha).abs)
  refine ⟨max B 0, max C 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro t ht x
    exact (hB ⟨(t, x), ⟨ht, Set.mem_univ x⟩, rfl⟩).trans (le_max_left _ _)
  · intro t ht x
    exact (hC ⟨(t, x), ⟨ht, Set.mem_univ x⟩, rfl⟩).trans (le_max_left _ _)

theorem exists_uniform_norm_dirichletDriftSubPotentialOnIcc
    (q : SmoothRiemannianMetric (I_half n) M)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯) {T : ℝ}
    (hY : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hdiv : ContinuousOn
      (fun p : ℝ × M => divergence (I := I_half n)
        (leviCivitaConnectionOfMetric (I := I_half n) q) (Y p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (ha : ContinuousOn (fun p : ℝ × M => a p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, ‖dirichletDriftSubPotentialOnIcc q Y a T t‖ ≤ C := by
  obtain ⟨B, C, hB, hC, hYbound, hcoeff⟩ :=
    exists_driftSubPotential_coefficient_bounds q Y a isCompact_Icc hY hdiv ha
  refine ⟨Real.sqrt B + C * ‖H1ComplDirichletToLp q‖,
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hC (norm_nonneg _)), ?_⟩
  exact norm_dirichletDriftSubPotentialOnIcc_le_of_bound q Y a hB hYbound hC hcoeff

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
