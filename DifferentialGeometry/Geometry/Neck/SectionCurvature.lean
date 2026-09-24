import DifferentialGeometry.Geometry.Neck.SpatialChart
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Curvature.RestrictedRoundCylinderSectional
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EqualDimensionImmersion

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) := ⟨by simp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

theorem NormalizedNeck.metricRm04_chart_horizontal_pos
    (N : NormalizedNeck g δ k) (hδ : δ < 1 / 1000) (hk : 2 ≤ k)
    (x : neckBuffer δ) (hx : x ∈ neckClosedTest δ)
    (u v : TangentSpace (𝓡 2) x.val.1)
    (hu : (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.val.1 u u = 1)
    (hv : (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.val.1 v v = 1)
    (huv : (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner x.val.1 u v = 0) :
    0 < metricRm04StandardAt g (N.chart x)
      (mfderiv NeckCylinderModel ThreeModel N.chart x (u, 0))
      (mfderiv NeckCylinderModel ThreeModel N.chart x (v, 0))
      (mfderiv NeckCylinderModel ThreeModel N.chart x (v, 0))
      (mfderiv NeckCylinderModel ThreeModel N.chart x (u, 0)) := by
  have hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m N.normalizedMetric
      ((Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)).restrictOpen (neckBuffer δ))
      ((Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)).restrictOpen (neckBuffer δ)) x ≤ δ := by
    intro m hm
    rw [← roundCylinderMetric_eq_geometry]
    exact (derivNorm_le_sup (isCompact_neckClosedTest δ) (hm.trans hk) _ _ _ hx).trans N.closeness.le
  have hpos := metricRm04_restricted_roundCylinder_horizontal_pos_of_small_metric_derivatives
    (neckBuffer δ) N.normalizedMetric x hδ hsmall u v hu hv huv
  have hlocal : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ N.chart := fun y =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq
      (by simp [ThreeSpace, Module.finrank_prod]) (N.chart_smooth.isImmersion.isImmersionAt y)
  have heq : N.normalizedMetric = localPullMetric (scaleMetric N.scale N.scale_pos g) N.chart hlocal := by
    apply SmoothRiemannianMetric.ext_inner
    intro y V W
    rw [localPullMetric_inner, scaleMetric_inner, N.normalized_inner]
  rw [heq] at hpos
  erw [metricRm04StandardAt_localPullMetric, metricRmStandard_scale] at hpos
  exact (mul_pos_iff_of_pos_left N.scale_pos).mp hpos


private def neckCentralSection (hδ : 0 < δ) (y : Sphere 2) : neckBuffer δ :=
  ⟨(y, 0), by have := inv_pos.mpr hδ; constructor <;> linarith⟩

private theorem mfderiv_neckCentralSection (hδ : 0 < δ) (y : Sphere 2)
    (u : TangentSpace (𝓡 2) y) :
    mfderiv (𝓡 2) NeckCylinderModel (neckCentralSection hδ) y u = (u, 0) := by
  have hs : (Subtype.val : neckBuffer δ → NeckCylinder) ∘ neckCentralSection hδ =
      fun z : Sphere 2 => (z, (0 : ℝ)) := rfl
  have hder := DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓡 2) (J := NeckCylinderModel)
    (neckCentralSection hδ) y
  change mfderiv (𝓡 2) NeckCylinderModel (Subtype.val ∘ neckCentralSection hδ) y = _ at hder
  rw [hs, mfderiv_prod_left] at hder
  exact congrArg (fun L => L u) hder.symm

theorem NormalizedNeck.exists_metricRm04_centralSphere_pos
    (N : NormalizedNeck g δ k) (hδ : δ < 1 / 1000) (hk : 2 ≤ k)
    (y : Sphere 2) :
    let f : Sphere 2 → M := fun z => N.chart ⟨(z, 0), by
      have := inv_pos.mpr N.delta_pos; constructor <;> linarith⟩
    ∃ u v : TangentSpace (𝓡 2) y,
      0 < metricRm04StandardAt g (f y)
        (mfderiv (𝓡 2) ThreeModel f y u) (mfderiv (𝓡 2) ThreeModel f y v)
        (mfderiv (𝓡 2) ThreeModel f y v) (mfderiv (𝓡 2) ThreeModel f y u) := by
  dsimp only
  let F : Sphere 2 → neckBuffer δ := neckCentralSection N.delta_pos
  let x : neckBuffer δ := F y
  have hx : x ∈ neckClosedTest δ := by
    change -δ⁻¹ ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ δ⁻¹
    have hp := (inv_pos.mpr N.delta_pos).le
    exact ⟨neg_nonpos.mpr hp, hp⟩
  obtain ⟨basis, hB⟩ := Tensor0SBundle.exists_orthonormal_basis
    (Geometry.roundMetric (E := ThreeSpace) (n := 2)) y
  let i : Fin (Module.finrank ℝ (TangentSpace (𝓡 2) y)) := ⟨0, by change 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)); simp⟩
  let j : Fin (Module.finrank ℝ (TangentSpace (𝓡 2) y)) := ⟨1, by change 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)); simp⟩
  have hu : (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner y (basis i) (basis i) = 1 := by
    simpa using hB i i
  have hv : (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner y (basis j) (basis j) = 1 := by
    simpa using hB j j
  have huv : (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner y (basis i) (basis j) = 0 := by
    have hij : i ≠ j := by intro hij; have := congrArg Fin.val hij; norm_num [i, j] at this
    simpa only [hij, if_false] using hB i j
  have hpos := N.metricRm04_chart_horizontal_pos hδ hk x hx (basis i) (basis j) hu hv huv
  have hF : ContMDiff (𝓡 2) NeckCylinderModel ∞ F := by
    apply (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff (neckBuffer δ) F).mp
    exact contMDiff_id.prodMk contMDiff_const
  have hd (u : TangentSpace (𝓡 2) y) :
      mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y u =
        mfderiv NeckCylinderModel ThreeModel N.chart x (u, 0) := by
    rw [mfderiv_comp_apply y (N.chart_smooth.contMDiff.mdifferentiableAt (by simp))
      (hF.mdifferentiableAt (by simp)), mfderiv_neckCentralSection]
    rfl
  refine ⟨basis i, basis j, ?_⟩
  change 0 < metricRm04StandardAt g ((N.chart ∘ F) y)
    (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y (basis i))
    (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y (basis j))
    (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y (basis j))
    (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y (basis i))
  rw [hd, hd]
  exact hpos


theorem NormalizedNeck.metricRm04_chart_lower_bound_of_normalized
    (N : NormalizedNeck g δ k) (x : neckBuffer δ) (c : ℝ)
    (u v : TangentSpace NeckCylinderModel x)
    (hbound : c * (N.normalizedMetric.inner x u u * N.normalizedMetric.inner x v v -
        (N.normalizedMetric.inner x u v) ^ 2) ≤
      metricRm04StandardAt N.normalizedMetric x u v v u) :
    c * N.scale *
      (g.inner (N.chart x) (mfderiv NeckCylinderModel ThreeModel N.chart x u)
          (mfderiv NeckCylinderModel ThreeModel N.chart x u) *
        g.inner (N.chart x) (mfderiv NeckCylinderModel ThreeModel N.chart x v)
          (mfderiv NeckCylinderModel ThreeModel N.chart x v) -
        (g.inner (N.chart x) (mfderiv NeckCylinderModel ThreeModel N.chart x u)
          (mfderiv NeckCylinderModel ThreeModel N.chart x v)) ^ 2) ≤
      metricRm04StandardAt g (N.chart x)
        (mfderiv NeckCylinderModel ThreeModel N.chart x u)
        (mfderiv NeckCylinderModel ThreeModel N.chart x v)
        (mfderiv NeckCylinderModel ThreeModel N.chart x v)
        (mfderiv NeckCylinderModel ThreeModel N.chart x u) := by
  have hlocal : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ N.chart := fun y =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq
      (by simp [ThreeSpace, Module.finrank_prod]) (N.chart_smooth.isImmersion.isImmersionAt y)
  have heq : N.normalizedMetric =
      localPullMetric (scaleMetric N.scale N.scale_pos g) N.chart hlocal := by
    apply SmoothRiemannianMetric.ext_inner
    intro y V W
    rw [localPullMetric_inner, scaleMetric_inner, N.normalized_inner]
  have hRm : metricRm04StandardAt N.normalizedMetric x u v v u =
      N.scale * metricRm04StandardAt g (N.chart x)
        (mfderiv NeckCylinderModel ThreeModel N.chart x u)
        (mfderiv NeckCylinderModel ThreeModel N.chart x v)
        (mfderiv NeckCylinderModel ThreeModel N.chart x v)
        (mfderiv NeckCylinderModel ThreeModel N.chart x u) := by
    exact (congrArg (fun h => metricRm04StandardAt h x u v v u) heq).trans
      ((metricRm04StandardAt_localPullMetric
        (scaleMetric N.scale N.scale_pos g) N.chart hlocal x u v v u).trans
        (metricRmStandard_scale N.scale N.scale_pos g (N.chart x)
          (mfderiv NeckCylinderModel ThreeModel N.chart x u)
          (mfderiv NeckCylinderModel ThreeModel N.chart x v)
          (mfderiv NeckCylinderModel ThreeModel N.chart x v)
          (mfderiv NeckCylinderModel ThreeModel N.chart x u)))
  rw [hRm, N.normalized_inner, N.normalized_inner, N.normalized_inner] at hbound
  apply (mul_le_mul_iff_right₀ N.scale_pos).mp
  convert hbound using 1 <;> first | rfl | ring

theorem NormalizedNeck.metricRm04_centralSphere_lower_bound_of_normalized
    (N : NormalizedNeck g δ k) (c : ℝ) (y : Sphere 2)
    (u v : TangentSpace (𝓡 2) y)
    (hbound : ∀ (x : neckBuffer δ), x ∈ neckClosedTest δ →
      ∀ (a b : TangentSpace (𝓡 2) x.val.1),
      c * (N.normalizedMetric.inner x (a, 0) (a, 0) *
          N.normalizedMetric.inner x (b, 0) (b, 0) -
          (N.normalizedMetric.inner x (a, 0) (b, 0)) ^ 2) ≤
        metricRm04StandardAt N.normalizedMetric x (a, 0) (b, 0) (b, 0) (a, 0)) :
    let f : Sphere 2 → M := fun z => N.chart ⟨(z, 0), by
      have := inv_pos.mpr N.delta_pos; constructor <;> linarith⟩
    c * N.scale *
      (g.inner (f y) (mfderiv (𝓡 2) ThreeModel f y u)
          (mfderiv (𝓡 2) ThreeModel f y u) *
        g.inner (f y) (mfderiv (𝓡 2) ThreeModel f y v)
          (mfderiv (𝓡 2) ThreeModel f y v) -
        (g.inner (f y) (mfderiv (𝓡 2) ThreeModel f y u)
          (mfderiv (𝓡 2) ThreeModel f y v)) ^ 2) ≤
      metricRm04StandardAt g (f y)
        (mfderiv (𝓡 2) ThreeModel f y u) (mfderiv (𝓡 2) ThreeModel f y v)
        (mfderiv (𝓡 2) ThreeModel f y v) (mfderiv (𝓡 2) ThreeModel f y u) := by
  dsimp only
  let F : Sphere 2 → neckBuffer δ := neckCentralSection N.delta_pos
  let x : neckBuffer δ := F y
  have hx : x ∈ neckClosedTest δ := by
    change -δ⁻¹ ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ δ⁻¹
    have hp := (inv_pos.mpr N.delta_pos).le
    exact ⟨neg_nonpos.mpr hp, hp⟩
  have hF : ContMDiff (𝓡 2) NeckCylinderModel ∞ F := by
    apply (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff (neckBuffer δ) F).mp
    exact contMDiff_id.prodMk contMDiff_const
  have hd (a : TangentSpace (𝓡 2) y) :
      mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y a =
        mfderiv NeckCylinderModel ThreeModel N.chart x (a, 0) := by
    rw [mfderiv_comp_apply y (N.chart_smooth.contMDiff.mdifferentiableAt (by simp))
      (hF.mdifferentiableAt (by simp)), mfderiv_neckCentralSection]
    rfl
  change c * N.scale *
      (g.inner ((N.chart ∘ F) y) (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y u)
          (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y u) *
        g.inner ((N.chart ∘ F) y) (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y v)
          (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y v) -
        (g.inner ((N.chart ∘ F) y) (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y u)
          (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y v)) ^ 2) ≤
      metricRm04StandardAt g ((N.chart ∘ F) y)
        (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y u)
        (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y v)
        (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y v)
        (mfderiv (𝓡 2) ThreeModel (N.chart ∘ F) y u)
  rw [hd, hd]
  exact N.metricRm04_chart_lower_bound_of_normalized x c (u, 0) (v, 0) (hbound x hx u v)

theorem NormalizedNeck.metricRm04_centralSphere_lower_bound
    (N : NormalizedNeck g δ k) (hδ : δ ≤ 1 / 1000) (hk : 2 ≤ k)
    (y : Sphere 2) (u v : TangentSpace (𝓡 2) y) :
    let f : Sphere 2 → M := fun z => N.chart ⟨(z, 0), by
      have := inv_pos.mpr N.delta_pos; constructor <;> linarith⟩
    (N.scale / 16) *
      (g.inner (f y) (mfderiv (𝓡 2) ThreeModel f y u)
          (mfderiv (𝓡 2) ThreeModel f y u) *
        g.inner (f y) (mfderiv (𝓡 2) ThreeModel f y v)
          (mfderiv (𝓡 2) ThreeModel f y v) -
        (g.inner (f y) (mfderiv (𝓡 2) ThreeModel f y u)
          (mfderiv (𝓡 2) ThreeModel f y v)) ^ 2) ≤
      metricRm04StandardAt g (f y)
        (mfderiv (𝓡 2) ThreeModel f y u) (mfderiv (𝓡 2) ThreeModel f y v)
        (mfderiv (𝓡 2) ThreeModel f y v) (mfderiv (𝓡 2) ThreeModel f y u) := by
  have hbound : ∀ (x : neckBuffer δ), x ∈ neckClosedTest δ →
      ∀ (a b : TangentSpace (𝓡 2) x.val.1),
      (1 / 16 : ℝ) * (N.normalizedMetric.inner x (a, 0) (a, 0) *
          N.normalizedMetric.inner x (b, 0) (b, 0) -
          (N.normalizedMetric.inner x (a, 0) (b, 0)) ^ 2) ≤
        metricRm04StandardAt N.normalizedMetric x (a, 0) (b, 0) (b, 0) (a, 0) := by
    intro x hx a b
    apply metricRm04_restricted_roundCylinder_horizontal_lower_bound_of_small_metric_derivatives
      (neckBuffer δ) N.normalizedMetric x hδ _ a b
    intro m hm
    rw [← roundCylinderMetric_eq_geometry]
    exact (derivNorm_le_sup (isCompact_neckClosedTest δ) (hm.trans hk) _ _ _ hx).trans N.closeness.le
  have h := N.metricRm04_centralSphere_lower_bound_of_normalized (1 / 16) y u v hbound
  have heq : (1 / 16 : ℝ) * N.scale = N.scale / 16 := by ring
  simpa only [heq] using h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

private theorem metricRm04_cylindricalChart_eq
    (nk : SpatialNeck g eps p) (x : nk.cylindricalChart.domain)
    (u v w z : TangentSpace IC x) :
    metricRm04StandardAt
        (Diffeomorph.pullbackMetricCross
          (scaleMetric nk.cylindricalChart.scale nk.cylindricalChart.scale_pos
            (g.restrictOpen nk.cylindricalChart.target)) nk.cylindricalChart.chart) x u v w z =
      metricScalarAt g p * metricRm04StandardAt g (nk.map x.val)
        (mfderiv IC I3 nk.map x.val u) (mfderiv IC I3 nk.map x.val v)
        (mfderiv IC I3 nk.map x.val w) (mfderiv IC I3 nk.map x.val z) := by
  let C := nk.cylindricalChart
  have h₁ := metricRm04Standard_pullbackCross
    (scaleMetric C.scale C.scale_pos (g.restrictOpen C.target)) C.chart x u v w z
  have h₂ := metricRmStandard_scale C.scale C.scale_pos (g.restrictOpen C.target) (C.chart x)
    (mfderiv IC I3 C.chart x u) (mfderiv IC I3 C.chart x v)
    (mfderiv IC I3 C.chart x w) (mfderiv IC I3 C.chart x z)
  have h₃ := metricRm04StandardAt_restrictOpen g C.target (C.chart x)
    (mfderiv IC I3 C.chart x u) (mfderiv IC I3 C.chart x v)
    (mfderiv IC I3 C.chart x w) (mfderiv IC I3 C.chart x z)
  simp only [mfderiv_subtype_val_apply] at h₃
  have hd (a : TangentSpace IC x) :
      mfderiv IC I3 C.chart x a = mfderiv IC I3 nk.map x.val a :=
    PartialDiffeomorph.mfderiv_toOpensDiffeo nk.map nk.domain x a
  have h := h₁.trans (h₂.trans (congrArg (C.scale * ·) h₃))
  rw [hd, hd, hd, hd] at h
  exact h

private theorem metricRm04_map_horizontal_lower_bound
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 1000)
    (x : nk.cylindricalChart.domain) (u v : TangentSpace I2 x.val.1) :
    metricScalarAt g p / 16 *
      (g.inner (nk.map x.val) (mfderiv IC I3 nk.map x.val (u, 0))
          (mfderiv IC I3 nk.map x.val (u, 0)) *
        g.inner (nk.map x.val) (mfderiv IC I3 nk.map x.val (v, 0))
          (mfderiv IC I3 nk.map x.val (v, 0)) -
        (g.inner (nk.map x.val) (mfderiv IC I3 nk.map x.val (u, 0))
          (mfderiv IC I3 nk.map x.val (v, 0))) ^ 2) ≤
      metricRm04StandardAt g (nk.map x.val)
        (mfderiv IC I3 nk.map x.val (u, 0)) (mfderiv IC I3 nk.map x.val (v, 0))
        (mfderiv IC I3 nk.map x.val (v, 0)) (mfderiv IC I3 nk.map x.val (u, 0)) := by
  change EuclideanSpace ℝ (Fin 2) at u v
  let C := nk.cylindricalChart
  let G := Diffeomorph.pullbackMetricCross
    (scaleMetric C.scale C.scale_pos (g.restrictOpen C.target)) C.chart
  have hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m G
      ((Geometry.Metric.roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen C.domain)
      ((Geometry.Metric.roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen C.domain) x ≤ eps :=
    nk.cylindricalChart_metricCloseOn x (Set.mem_univ x)
  have hbound := metricRm04_restricted_roundCylinder_horizontal_lower_bound_of_small_metric_derivatives
    C.domain G x heps hsmall u v
  have hd (a : TangentSpace IC x) :
      mfderiv IC I3 C.chart x a = mfderiv IC I3 nk.map x.val a :=
    PartialDiffeomorph.mfderiv_toOpensDiffeo nk.map nk.domain x a
  have hinner (a b : TangentSpace IC x) :
      G.inner x a b = metricScalarAt g p * g.inner (nk.map x.val)
        (mfderiv IC I3 nk.map x.val a) (mfderiv IC I3 nk.map x.val b) := by
    rw [Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner,
      SmoothRiemannianMetric.restrictOpen_inner, hd, hd]
    rfl
  have hRm : metricRm04StandardAt G x (u, 0) (v, 0) (v, 0) (u, 0) =
      metricScalarAt g p * metricRm04StandardAt g (nk.map x.val)
        (mfderiv IC I3 nk.map x.val (u, 0)) (mfderiv IC I3 nk.map x.val (v, 0))
        (mfderiv IC I3 nk.map x.val (v, 0)) (mfderiv IC I3 nk.map x.val (u, 0)) := by
    exact metricRm04_cylindricalChart_eq nk x (u, 0) (v, 0) (v, 0) (u, 0)
  erw [hRm, hinner, hinner, hinner] at hbound
  apply (mul_le_mul_iff_right₀ nk.Q_pos).mp
  convert hbound using 1 <;> first | rfl | ring

theorem SpatialNeck.metricRm04_section_lower_bound
    (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 1000)
    {s : ℝ} (hs : s ∈ Set.Ioo (-eps⁻¹) eps⁻¹)
    (q : Sphere 2) (u v : TangentSpace I2 q) :
    let f : Sphere 2 → M := fun z => nk.map (z, s)
    metricScalarAt g p / 16 *
      (g.inner (f q) (mfderiv I2 I3 f q u) (mfderiv I2 I3 f q u) *
        g.inner (f q) (mfderiv I2 I3 f q v) (mfderiv I2 I3 f q v) -
        (g.inner (f q) (mfderiv I2 I3 f q u) (mfderiv I2 I3 f q v)) ^ 2) ≤
      metricRm04StandardAt g (f q)
        (mfderiv I2 I3 f q u) (mfderiv I2 I3 f q v)
        (mfderiv I2 I3 f q v) (mfderiv I2 I3 f q u) := by
  dsimp only
  change EuclideanSpace ℝ (Fin 2) at u v
  let x : nk.cylindricalChart.domain := ⟨(q, s), Set.mem_univ q, hs⟩
  have hsource : (q, s) ∈ nk.map.source := nk.domain ⟨Set.mem_univ q, hs⟩
  have hd (a : TangentSpace I2 q) :
      mfderiv I2 I3 (fun z : Sphere 2 => nk.map (z, s)) q a =
        mfderiv IC I3 nk.map (q, s) (a, 0) := by
    change EuclideanSpace ℝ (Fin 2) at a
    have hinc : ContMDiff I2 IC ∞ (fun z : Sphere 2 => (z, s)) :=
      contMDiff_id.prodMk contMDiff_const
    change mfderiv I2 I3 (nk.map ∘ fun z : Sphere 2 => (z, s)) q a = _
    erw [mfderiv_comp_apply q (nk.map.mdifferentiableAt (by decide) hsource)
      (hinc.mdifferentiableAt (by decide)), mfderiv_prod_left]
    rfl
  erw [hd, hd]
  exact metricRm04_map_horizontal_lower_bound nk heps x u v

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
