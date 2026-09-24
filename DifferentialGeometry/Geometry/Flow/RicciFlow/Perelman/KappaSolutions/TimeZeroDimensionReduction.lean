import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianLineLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedSectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TimeZeroSplitting
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Topology ContDiff Manifold NNReal ENNReal

universe u uE uH

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

local instance timeZeroDimensionReductionOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem spatialRescaledPointedSeq_sectional_nonnegative
    (g : SmoothRiemannianMetric I M)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i) (i : ℕ) (y : M) :
    metricRm04At (I := I)
      ((spatialRescaledPointedSeq g x lam hlam).obj i).metric y ∈
        tensor04SectionalNonnegativeCone (I := I) (M := M) := by
  apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff (I := I)
    ((spatialRescaledPointedSeq g x lam hlam).obj i).metric y).mpr
  intro v w
  change 0 ≤ metricRm04StandardAt (I := I)
    (scaleMetric (lam i ^ 2) (sq_pos_of_pos (hlam i)) g) y v w w v
  rw [metricRmStandard_scale]
  exact mul_nonneg (sq_nonneg _)
    (((metricRm04At_mem_tensor04SectionalNonnegativeCone_iff (I := I) g y).mp
      (hsec y)) v w)

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [ConnectedSpace M]

theorem timeZero_surface_product_in_rescaled_metricCompactness
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (hdim : Module.finrank ℝ E = 3)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) (x : ℕ → M) (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i)
    (hescape : Tendsto (fun i => (riemannianEDistOf (I := I) g p (x i)).toReal)
      atTop atTop)
    (hscaled : Tendsto (fun i => lam i *
      (riemannianEDistOf (I := I) g p (x i)).toReal) atTop atTop)
    (inp : MetricCompactnessAssumptions (I := I) (spatialRescaledPointedSeq g x lam hlam)) :
    let C := inp.metricCompactness (spatialRescaledPointedSeq_complete g hg x lam hlam)
      (spatialRescaledPointedSeq_connected g x lam hlam)
    let L := C.limit
    let _ : TopologicalSpace L.M := L.topology
    let _ : ChartedSpace H L.M := L.charted
    let _ : IsManifold I ∞ L.M := L.smooth
    let _ : T2Space L.M := L.t2
    let _ : SigmaCompactSpace L.M := L.sigmaCompact
    (∀ q : L.M, metricRm04At (I := I) L.metric q ∈
      tensor04SectionalNonnegativeCone (I := I)) ∧
    ∃ gamma : ℝ → L.M, gamma 0 = L.basepoint ∧
      (∀ s t : ℝ, riemannianEDistOf (I := I) L.metric (gamma s) (gamma t) =
        ENNReal.ofReal |s - t|) ∧
      ∃ b : L.M → ℝ, ∃ hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b,
        b L.basepoint = 0 ∧ (∀ t : ℝ≥0, b (gamma t) = (t : ℝ)) ∧
        ∃ p₀ : {q : L.M // b q = 0},
          let V := affineFunctionKernel (I := I) b p₀.1
          let N := {q : L.M // b q = 0}
          ∃ cN : ChartedSpace V N,
            let _ : ChartedSpace V N := cN
            ∃ sN : IsManifold 𝓘(ℝ, V) ∞ N,
              let _ : IsManifold 𝓘(ℝ, V) ∞ N := sN
              let _ : SigmaCompactSpace N :=
                (isClosed_eq hb.continuous continuous_const).sigmaCompactSpace
              ConnectedSpace N ∧ DifferentialGeometry.Geometry.IsEmbeddedSlice I 2
                {q : L.M | b q = 0} ∧ Module.finrank ℝ V = 2 ∧
              ∃ gN : SmoothRiemannianMetric 𝓘(ℝ, V) N,
                RiemannianMetricComplete (I := 𝓘(ℝ, V)) gN ∧
                (∀ (q : N) (v w : TangentSpace 𝓘(ℝ, V) q),
                  gN.inner q v w = L.metric.inner q.1
                    (mfderiv 𝓘(ℝ, V) I (Subtype.val : N → L.M) q v)
                    (mfderiv 𝓘(ℝ, V) I (Subtype.val : N → L.M) q w)) ∧
                ∃ F : (N × ℝ) ≃ₘ⟮𝓘(ℝ, V).prod 𝓘(ℝ, ℝ), I⟯ L.M,
                  (∀ q : N, F (q, 0) = q.1) ∧
                  (∀ (q : N) (t : ℝ), b (F (q, t)) = t) ∧
                  (∀ (q : N) (v w : TangentSpace 𝓘(ℝ, V) q) (t a c : ℝ),
                    L.metric.inner (F (q, t))
                      (mfderiv (𝓘(ℝ, V).prod 𝓘(ℝ, ℝ)) I F (q, t) (v, a))
                      (mfderiv (𝓘(ℝ, V).prod 𝓘(ℝ, ℝ)) I F (q, t) (w, c)) =
                        gN.inner q v w + a * c) := by
  let C := inp.metricCompactness (spatialRescaledPointedSeq_complete g hg x lam hlam)
    (spatialRescaledPointedSeq_connected g x lam hlam)
  let L := C.limit
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : T2Space (TangentBundle I L.M) := L.t2TangentBundle
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  let _ : ConnectedSpace L.M := metricCompactness_limit_connected inp
    (spatialRescaledPointedSeq_complete g hg x lam hlam)
    (spatialRescaledPointedSeq_connected g x lam hlam)
  have hLsec : ∀ q : L.M, metricRm04At (I := I) L.metric q ∈
      tensor04SectionalNonnegativeCone (I := I) :=
    sectional_nonnegative_in_metricCompactness inp
      (spatialRescaledPointedSeq_complete g hg x lam hlam)
      (spatialRescaledPointedSeq_connected g x lam hlam)
      (spatialRescaledPointedSeq_sectional_nonnegative g hsec x lam hlam)
  have hLcomplete : RiemannianMetricComplete (I := I) L.metric :=
    ⟨MetricComplete.complete L C.limit_complete⟩
  let _ : TopologicalSpace.MetrizableSpace L.M := Manifold.metrizableSpace I L.M
  let _ : T3Space L.M := inferInstance
  let _ : RiemannianBundle (fun q : L.M => TangentSpace I q) :=
    ⟨L.metric.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun q : L.M => TangentSpace I q) :=
    ⟨⟨L.metric.inner, L.metric.contMDiff.continuous, by intro q v w; rfl⟩⟩
  let _ : EMetricSpace L.M := EMetricSpace.ofRiemannianMetric I L.M
  let _ : CompleteSpace L.M := hLcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := L.M) L.metric := fun q v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) L.metric q v
  let _ : MetricSpace L.M := riemMetricSpace (I := I) (M := L.M)
  let _ : ProperSpace L.M := properSpace_riemMetric (I := I) hLcomplete.complete
    L.metric hEnorm
  obtain ⟨gamma, _hproperIsometry, hgamma0, hgammaDist⟩ :=
    exists_riemannian_line_in_rescaled_metricCompactness
      g hg hsec p x lam hlam hescape hscaled inp
  have hgamma : Isometry gamma := by
    apply Isometry.of_dist_eq
    intro s t
    rw [riemMetric_dist_eq (I := I),
      ← riemannianEDistOf_eq_riemannianEDist (I := I) L.metric hEnorm,
      hgammaDist, ENNReal.toReal_ofReal (abs_nonneg _), Real.dist_eq]
  have hRic (q : L.M) (v : TangentSpace I q) :
      0 ≤ ricciTensor (I := I) L.metric q v v :=
    Geometry.Riemannian.BonnetMyers.ricci_nonneg_of_sec L.metric q (hLsec q) v
  let b : L.M → ℝ := busemann (fun t : ℝ≥0 => gamma t)
  obtain ⟨hb, hunit, hH, p₀, hNconnected, hNembedded, _hNrank,
    hNcomplete, F, hF, _hFinverse, hFmetric⟩ :=
    timeZero_isometric_product_of_nonnegative_ricci_line L.metric hEnorm hRic hgamma
  have hray : Isometry (fun t : ℝ≥0 => gamma t) := by
    apply Isometry.of_dist_eq
    intro s t
    exact hgamma.dist_eq s t
  have hcal (t : ℝ≥0) : b (gamma t) = (t : ℝ) := busemann_ray hray t
  have hb0 : b L.basepoint = 0 := by
    simpa only [NNReal.coe_zero, hgamma0] using hcal 0
  let N := {q : L.M // b q = 0}
  let V := affineFunctionKernel (I := I) b p₀.1
  let cN := affineZeroLevelChartedSpace (I := I) L.metric hEnorm hb hunit hH p₀
  let _ : ChartedSpace V N := cN
  let sN := affineZeroLevel_isManifold (I := I) L.metric hEnorm hb hunit hH p₀
  let _ : IsManifold 𝓘(ℝ, V) ∞ N := sN
  let _ : SigmaCompactSpace N :=
    (isClosed_eq hb.continuous continuous_const).sigmaCompactSpace
  let gN := affineZeroLevelMetric (I := I) L.metric hEnorm hb hunit hH p₀
  have hNrank : Module.finrank ℝ V = 2 :=
    timeZero_busemann_factor_finrank_two L.metric hEnorm hRic hdim hgamma p₀.1
  have hNembeddedTwo : DifferentialGeometry.Geometry.IsEmbeddedSlice I 2
      {q : L.M | b q = 0} := by
    simpa only [hdim] using hNembedded
  refine ⟨hLsec, gamma, hgamma0, hgammaDist, b, hb, hb0, hcal, p₀, cN, sN,
    hNconnected, hNembeddedTwo, hNrank, gN, hNcomplete, ?_, F, ?_, ?_, hFmetric⟩
  · exact affineZeroLevelMetric_inner (I := I) L.metric hEnorm hb hunit hH p₀
  · intro q
    rw [hF, affineGradientFlow_zero]
  · intro q t
    rw [hF]
    change busemann (fun s => gamma s)
      (affineGradientFlow (I := I) L.metric hEnorm (busemann (fun s => gamma s)) q.1 t) = t
    rw [affineFunction_flow_eq_add (I := I) L.metric hEnorm hb hunit hH]
    change b q.1 + t = t
    rw [q.property, zero_add]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
