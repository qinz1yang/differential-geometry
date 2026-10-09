import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureContinuity
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

/-- A compact terminal ball protects any strictly smaller moving closed ball on
some positive interval ending at the terminal time. The interval depends on the
actual flow and the two radii; no global compactness or completeness is assumed. -/
theorem exists_pos_moving_closedBall_subset_terminal_ball
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b ρ R : ℝ} (hab : a < b)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (p : M) (hρ : 0 < ρ) (hρR : ρ < R)
    (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric b) p R)) :
    ∃ δ > 0, δ ≤ b-a ∧ ∀ s ∈ Icc (b-δ) b,
      riemannianClosedBallOf (S.base.metric s) p ρ ⊆
        riemannianBallOf (S.base.metric b) p R ∧
      IsCompact (riemannianClosedBallOf (S.base.metric s) p ρ) := by
  let C : Set M := riemannianClosedBallOf (S.base.metric b) p R
  let V : Opens M := ⟨riemannianBallOf (S.base.metric b) p R,
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ p) continuous_const⟩
  have hR : 0 < R := hρ.trans hρR
  let pV : V := ⟨p, by
    change riemannianEDistOf (S.base.metric b) p p < ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hR⟩
  let R₁ : ℝ := (ρ+R)/2
  have hρ₁ : ρ < R₁ := by dsimp only [R₁]; linarith
  have h₁R : R₁ < R := by dsimp only [R₁]; linarith
  have h₁ : 0 < R₁ := hρ.trans hρ₁
  have hsub : riemannianClosedBallOf (S.base.metric b) p R₁ ⊆ C :=
    riemannianClosedBallOf_mono _ _ h₁R.le
  have hsource : riemannianClosedBallOf (S.base.metric b) p R₁ ⊆ V := by
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr h₁R)
  have hcompact₁ : IsCompact (riemannianClosedBallOf (S.base.metric b) p R₁) :=
    hcompact.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) hsub
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod hcompact).bddAbove_image
    (hS.continuousOn_rmNormSq.mono (fun z hz => ⟨hcarrier hz.1, mem_univ z.2⟩))
  have hRm (u : ℝ) (hu : u ∈ Icc a b) (x : M) (hx : x ∈ C) :
      normSq0S (S.base.metric u) x 4 (S.base.rm04 u x) ≤ K :=
    hK ⟨(u,x), ⟨hu,hx⟩, rfl⟩
  let c : ℝ := (Module.finrank ℝ E : ℝ)^2 * Real.sqrt K
  have hcont : ContinuousAt (fun d : ℝ => Real.exp (c*d)*ρ) 0 := by fun_prop
  have hnear : {d : ℝ | Real.exp (c*d)*ρ < R₁} ∈ 𝓝 0 :=
    hcont.eventually (Iio_mem_nhds (by simpa only [mul_zero, Real.exp_zero, one_mul] using hρ₁))
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ := min (b-a) (ε/2)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hab) (half_pos hε)
  have hδa : δ ≤ b-a := min_le_left _ _
  have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨δ, hδ, hδa, ?_⟩
  intro s hs
  have hsab : s ∈ Icc a b := ⟨by linarith [hs.1], hs.2⟩
  have htime : |b-s| < ε := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]
    linarith [hs.1]
  let L : ℝ := Real.exp (c*|b-s|)
  have hL : 0 < L := Real.exp_pos _
  have hfit : L*ρ < R₁ := hεball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_abs]
    exact htime)
  have hsmall : ρ < R₁/L := (lt_div_iff₀ hL).mpr (by simpa only [mul_comm] using hfit)
  have hlower (x : V) (hx : x.val ∈ riemannianClosedBallOf (S.base.metric b) p R₁)
      (v : TangentSpace I x) :
      (S.base.metric b).inner x.val v v ≤ L^2 *
        (S.base.metric s).inner x.val
          (mfderiv I I (Subtype.val : V → M) x v)
          (mfderiv I I (Subtype.val : V → M) x v) := by
    rw [mfderiv_subtype_val_apply]
    have hh := (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular x.val
      (fun u hu => hRm u hu x.val (hsub hx)) ⟨hab.le, le_rfl⟩ hsab v).2
    have hexp : Real.exp (2*(Module.finrank ℝ E : ℝ)^2 * Real.sqrt K * |b-s|) = L^2 := by
      dsimp only [L, c]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simpa only [hexp] using hh
  have hcapture := Geometry.Metric.ball_subset_image_of_metric_lower_on_opens
    (S.base.metric s) (S.base.metric b) V (Subtype.val : V → M)
    (isLocalDiffeomorph_subtype_val V) Subtype.val_injective pV
    h₁ hL hcompact₁ hsource hlower
  have hstay : riemannianClosedBallOf (S.base.metric s) p ρ ⊆
      riemannianClosedBallOf (S.base.metric b) p R₁ := by
    intro x hx
    have hx' : x ∈ riemannianBallOf (S.base.metric s) p (R₁/L) :=
      hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (div_pos h₁ hL)).mpr hsmall)
    obtain ⟨z, hz, hzx⟩ := hcapture hx'
    exact hzx ▸ hz
  exact ⟨hstay.trans hsource, hcompact₁.of_isClosed_subset
    (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) hstay⟩

end DifferentialGeometry.PDE.RicciFlow
