import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.SourceReferenceMetricBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.SourceIndexCoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReferenceSupportBounds
import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Germ
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import DifferentialGeometry.Analysis.SpecialFunctions.SqrtTailBounds

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (times : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < times i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem times q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem times q hsigma

omit [I.Boundaryless] in
private theorem source_index_bounds_of_metric_eq
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {D₁ D₂ : RealTimeInterval}
    (S₁ : SolutionOn (I := I) (M := M) D₁)
    (S₂ : SolutionOn (I := I) (M := M) D₂) (s t : ℝ)
    (heq : S₁.base.metric s = S₂.base.metric t) (x : M) {K C N : ℝ}
    (h :
      Real.sqrt (Tensor0SBundle.normSq0S (S₁.base.metric s) x 4
        (S₁.base.rm04 s x)) ≤ K ∧
      Real.sqrt (Tensor0SBundle.normSq0S (S₁.base.metric s) x 2
        (DifferentialGeometry.Geometry.Operator.hessianSec (I := I) (S₁.base.connection s)
          (metricCov_smooth (I := I) (S₁.base.metric s))
          (S₁.scalar s) (scalarSmoothOfSolution S₁ s) x)) ≤ C ∧
      Real.sqrt (Tensor0SBundle.normSq0S (S₁.base.metric s) x 3
        (Tensor0SBundle.totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S₁.base.connection s)
          (S₁.ricci s) x)) ≤ N) :
    Real.sqrt (Tensor0SBundle.normSq0S (S₂.base.metric t) x 4
      (S₂.base.rm04 t x)) ≤ K ∧
    Real.sqrt (Tensor0SBundle.normSq0S (S₂.base.metric t) x 2
      (DifferentialGeometry.Geometry.Operator.hessianSec (I := I) (S₂.base.connection t)
        (metricCov_smooth (I := I) (S₂.base.metric t))
        (S₂.scalar t) (scalarSmoothOfSolution S₂ t) x)) ≤ C ∧
    Real.sqrt (Tensor0SBundle.normSq0S (S₂.base.metric t) x 3
      (Tensor0SBundle.totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S₂.base.connection t)
        (S₂.ricci t) x)) ≤ N := by
  dsimp only [SolutionFamily.rm04, SolutionFamily.connection, SolutionOn.scalar,
    SolutionFamily.scalar, SolutionOn.ricci, SolutionFamily.ricci] at h ⊢
  have hscalar : S₁.base.scalar s = S₂.base.scalar t := by
    funext y
    exact congrArg (fun g : SmoothRiemannianMetric I M => metricScalarAt g y) heq
  rw [heq] at h
  simpa only [hscalar] using h

namespace FlowMetricConvergenceData

theorem exists_eventually_poleEndpoint_redLength_upper_support_on_time_interval_of_geodesic_capture
    (Φ : PointedCGHMaps (I := I) Y P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    {δ T : ℝ} (hδ : 1 < δ)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt (1 - T) (-(δ - 1) / 2))
    (hG : MetricFamilySmoothOn (Y).D co.gInf)
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J K : Set P.M} (hK : IsCompact K) (hJK : J ⊆ K)
    {B W : ℝ}
    (hcost : ∀ᶠ k in atTop, ∀ tau ∈ Icc δ T, ∀ y ∈ J,
      @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p
        (Φ.map (co.φ k) y) tau ≤ W)
    (hcapture : ∀ᶠ k in atTop, ∀ tau ∈ Icc δ T, ∀ y ∈ J, ∀ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
      @IsLRegularizedGeodesicOn E _ _ _ H _ I _ F.M F.topology F.charted F.smooth F.t2 _
        ((U).term (phi (co.φ k))).S 0 alpha (Ioc 0 (Real.sqrt tau)) →
      alpha 0 = p → alpha (Real.sqrt tau) = Φ.map (co.φ k) y →
      @lRegularizedAction E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 alpha 0 (Real.sqrt tau) =
        @lCost E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p (Φ.map (co.φ k) y) tau →
      alpha '' Icc (max (Real.sqrt ((1 + δ) / 2)) (Real.sqrt tau / 2))
        (Real.sqrt tau) ⊆ Φ.map (co.φ k) '' K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ n : ℕ, ∀ k ≥ n, ∀ tau ∈ Icc δ T, ∀ beta : ℝ → P.M,
      IsGeodesicAt R beta 0 → beta 0 ∈ J →
      Real.sqrt (R.inner (beta 0)
        (lVelocity (I := I) beta 0) (lVelocity (I := I) beta 0)) ≤ B →
      ∃ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ ∧
        ψ 0 = @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p
          (Φ.map (co.φ k) (beta 0)) tau ∧
        (fun r ↦ @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p
          (Φ.map (co.φ k) (beta r)) tau) ≤ᶠ[𝓝 (0 : ℝ)] ψ ∧
        deriv (deriv ψ) 0 ≤ D := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hwindowRegular : Icc (1 - T) (-(δ - 1) / 2) ⊆ ancientTimeInterval.regular := by
    intro t ht
    change t < 0
    linarith [ht.2]
  obtain ⟨Λ, A, hΛ, hA, n₁, href⟩ :=
    FlowMetricConvergenceData.exists_eventually_source_reference_metric_bounds
      Φ R bf hsrc htgt co hG hwindowRegular hK
  obtain ⟨K₀, C, N, _hK₀, _hC, _hN, n₂, hcoeff⟩ :=
    FlowMetricConvergenceData.exists_eventually_source_index_norm_bounds_on_time_interval
      Φ R bf hsrc htgt co hG hwindowRegular hboundary hK
  obtain ⟨n₃, hcost⟩ := eventually_atTop.mp hcost
  obtain ⟨n₄, hcapture⟩ := eventually_atTop.mp hcapture
  obtain ⟨D, hD, hsupport⟩ :=
    exists_uniform_redLength_upper_support_second_derivative_bound_on_final_tails
      (δ := δ) (T := T) (a₀ := Real.sqrt ((1 + δ) / 2))
      (μ := Λ) (Λ := Λ) (A := A) (B := B) (K₀ := K₀)
      (C := C) (N := N) («U» := W) (zero_lt_one.trans hδ)
      (Real.sqrt_midpoint_one_lt hδ) (zero_le_one.trans hΛ)
      (zero_le_one.trans hΛ) hA.le
  refine ⟨D, hD, max (max n₁ n₂) (max n₃ n₄), ?_⟩
  intro k hk tau htau beta hbeta hbetaJ hspeed
  have hk₁ : n₁ ≤ k := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
  have hk₂ : n₂ ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
  have hk₃ : n₃ ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hk₄ : n₄ ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  obtain ⟨h, V, hKV, hVs, hisometry, hmetric, hconnection⟩ := href k hk₁
  have hbetaV : beta 0 ∈ V := hKV (hJK hbetaJ)
  have hlocal : IsLocalDiffeomorphOn I I ∞ (Φ.map (co.φ k)) V := by
    intro x
    exact (Φ.partialDiffeomorph (co.φ k)).isLocalDiffeomorphAt I I ∞ (hVs x.2)
  have hmapGeo := isGeodesicAt_map_of_local_isometry_on R h V.isOpen hlocal
    hisometry hbetaV hbeta
  have hvelocity : lVelocity (I := I) (fun r ↦ Φ.map (co.φ k) (beta r)) 0 =
      mfderiv I I (Φ.map (co.φ k)) (beta 0) (lVelocity (I := I) beta 0) := by
    exact mfderiv_comp_apply 0 ((hlocal ⟨beta 0, hbetaV⟩).mdifferentiableAt (by simp))
      ((DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt hbeta).mdifferentiableAt
        (by simp)) 1
  have hmapSpeed : Real.sqrt (h.inner (Φ.map (co.φ k) (beta 0))
      (lVelocity (I := I) (fun r ↦ Φ.map (co.φ k) (beta r)) 0)
      (lVelocity (I := I) (fun r ↦ Φ.map (co.φ k) (beta r)) 0)) ≤ B := by
    rw [hvelocity, ← hisometry (beta 0) hbetaV]
    exact hspeed
  have hclock (s : ℝ)
      (hs : s ∈ Icc (max (Real.sqrt ((1 + δ) / 2)) (Real.sqrt tau / 2))
        (Real.sqrt tau)) :
      1 - s ^ 2 ∈ Icc (1 - T) (-(δ - 1) / 2) :=
    Real.one_sub_sq_mem_Icc_of_mem_final_tail hδ htau hs
  have hshift (s : ℝ) :
      ((Y).term (phi (co.φ k))).S.base.metric (1 - s ^ 2) =
        ((U).term (phi (co.φ k))).S.base.metric (0 - s ^ 2) := by
    rw [poleEndpointRescaledFlowSeq_metric_eq_shift]
    congr 1
    ring
  have hcaptureMap : ∀ z ∈ Φ.map (co.φ k) '' J,
      ∀ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
      @IsLRegularizedGeodesicOn E _ _ _ H _ I _ F.M F.topology F.charted F.smooth F.t2 _
        ((U).term (phi (co.φ k))).S 0 alpha (Ioc 0 (Real.sqrt tau)) →
      alpha 0 = p → alpha (Real.sqrt tau) = z →
      @lRegularizedAction E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 alpha 0 (Real.sqrt tau) =
        @lCost E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p z tau →
      alpha '' Icc (max (Real.sqrt ((1 + δ) / 2)) (Real.sqrt tau / 2))
        (Real.sqrt tau) ⊆ Φ.map (co.φ k) '' K := by
    rintro z ⟨y, hy, rfl⟩ alpha halpha hgeo hstart hend hact
    exact hcapture k hk₄ tau htau y hy alpha halpha hgeo hstart hend hact
  have hcostMap : ∀ z ∈ Φ.map (co.φ k) '' J,
      @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p z tau ≤ W := by
    rintro z ⟨y, hy, rfl⟩
    exact hcost k hk₃ tau htau y hy
  have hreference : ∀ s ∈ Icc (max (Real.sqrt ((1 + δ) / 2)) (Real.sqrt tau / 2))
      (Real.sqrt tau), ∀ x ∈ Φ.map (co.φ k) '' K,
      ∀ z : TangentSpace I x,
      h.inner x z z ≤ Λ * (((U).term (phi (co.φ k))).S.base.metric (0 - s ^ 2)).inner x z z := by
    intro s hs x hx z
    have hlower := ((hmetric (1 - s ^ 2) (hclock s hs)).2 x hx z).1
    rw [hshift s] at hlower
    have hscaled := mul_le_mul_of_nonneg_left hlower (zero_le_one.trans hΛ)
    simp only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (zero_lt_one.trans_le hΛ)),
      one_mul] at hscaled
    exact hscaled
  have hupper : ∀ s ∈ Icc (max (Real.sqrt ((1 + δ) / 2)) (Real.sqrt tau / 2))
      (Real.sqrt tau), ∀ x ∈ Φ.map (co.φ k) '' K,
      ∀ z : TangentSpace I x,
      (((U).term (phi (co.φ k))).S.base.metric (0 - s ^ 2)).inner x z z ≤ Λ * h.inner x z z := by
    intro s hs x hx z
    have hh := ((hmetric (1 - s ^ 2) (hclock s hs)).2 x hx z).2
    rw [hshift s] at hh
    exact hh
  have hconnectionMap : ∀ s ∈ Icc (max (Real.sqrt ((1 + δ) / 2)) (Real.sqrt tau / 2))
      (Real.sqrt tau), ∀ x ∈ Φ.map (co.φ k) '' K,
      ∀ u w : TangentSpace I x,
      Real.sqrt (h.inner x
        (CovariantDerivative.difference
          (metricCov (((U).term (phi (co.φ k))).S.base.metric (0 - s ^ 2))) (metricCov h) x u w)
        (CovariantDerivative.difference
          (metricCov (((U).term (phi (co.φ k))).S.base.metric (0 - s ^ 2))) (metricCov h) x u w)) ≤
        A * Real.sqrt (h.inner x u u) * Real.sqrt (h.inner x w w) := by
    rintro s hs x ⟨y, hy, rfl⟩ u w
    have hh := hconnection (1 - s ^ 2) (hclock s hs) y hy u w
    rw [hshift s] at hh
    exact hh
  have hfinal := hsupport tau htau ((U).term (phi (co.φ k))) (hF (phi (co.φ k)))
    h p (Φ.map (co.φ k) '' J) (Φ.map (co.φ k) '' K)
    hcaptureMap hcostMap
    hreference
    hupper
    hconnectionMap
    (fun s hs x hx ↦ (source_index_bounds_of_metric_eq
      (((Y).term (phi (co.φ k))).S) (((U).term (phi (co.φ k))).S)
      (1 - s ^ 2) (0 - s ^ 2) (hshift s) x
      (hcoeff k hk₂ (1 - s ^ 2) (hclock s hs) x hx)).1)
    (fun s hs x hx ↦ (source_index_bounds_of_metric_eq
      (((Y).term (phi (co.φ k))).S) (((U).term (phi (co.φ k))).S)
      (1 - s ^ 2) (0 - s ^ 2) (hshift s) x
      (hcoeff k hk₂ (1 - s ^ 2) (hclock s hs) x hx)).2.1)
    (fun s hs x hx ↦ (source_index_bounds_of_metric_eq
      (((Y).term (phi (co.φ k))).S) (((U).term (phi (co.φ k))).S)
      (1 - s ^ 2) (0 - s ^ 2) (hshift s) x
      (hcoeff k hk₂ (1 - s ^ 2) (hclock s hs) x hx)).2.2)
    (fun r ↦ Φ.map (co.φ k) (beta r)) hmapGeo ⟨beta 0, hbetaJ, rfl⟩ hmapSpeed
  exact hfinal


end FlowMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
