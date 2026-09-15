import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Partition
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.DiagonalInverse.IntrinsicConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinates.RootExistence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.RecenterConvergence
import DifferentialGeometry.Topology.Manifold.Gluing.Convergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Overlap
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.SourceRootCompatibility
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.SourceAtoms

set_option autoImplicit false

noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))



theorem IntrinsicBallChart.exists_chart_source_invVelocity_roots [Fintype ι]
    (hJsmooth : ∀ b, ContDiffOn ℝ ∞ (J b) (Metric.ball (0 : E) (ρ / 2)))
    (B : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (Metric.ball 0 ρ))
    (hBconv : ∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball 0 ρ)
      (fun k => intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k)) (B i))
    (hell : ∀ i k, ∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k) z v v ∧
      intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k) z v v ≤ 2 * ‖v‖ ^ 2) :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    ∀ C : ChartedSpace E D.toGlueData.glued, letI := C
      ∀ mu : SmoothPartitionOfUnity ι (modelWithCornersSelf ℝ E) D.toGlueData.glued Set.univ,
        mu.IsSubordinate (fun i => Set.range (D.toGlueData.ι i)) →
        (∀ i : ι, ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
          (fun z : U => D.toGlueData.ι i z)) →
        ∀ (j : ι) (a : E) (ha : a ∈ U),
          let weights := mu.coordinateWeights U (fun z : U => D.toGlueData.ι j z)
          let nc := fun k => (c j k).toNormalBallChart (g k) (hEnorm k) (x j k) hρ
          let hr8 : 0 < 8 * (ρ / 32) := by positivity
          let hball : ∀ k, Metric.ball a (8 * (ρ / 32)) ⊆ Metric.ball (0 : E) (nc k).radius := by
            intro k z hz
            change dist z 0 < ρ
            have ha' : dist a 0 < ρ / 8 := ha
            have hz' : dist z a < 8 * (ρ / 32) := hz
            have htri := dist_triangle z a 0
            linarith
          let cc := fun k => (nc k).recenter a hr8 (hball k)
          ∃ (xi : ℕ → E → ι → E) (q qInner : NNReal) (ε r : ℝ)
              (e : ℕ → OpenPartialHomeomorph (E × E) (E × E))
              (W : Set E) (N : Nat) (F : ∀ k, E → M k) (Phi : Nat → E → E),
            0 < q ∧ 0 < qInner ∧ qInner < q ∧ 0 < ε ∧ 0 < r ∧
            (∀ k, ContDiffOn ℝ ∞ (fun z => (weights z, xi k z)) U) ∧
            CheegerGromovCompactness.MapCInfConvergenceOnCompacts U
              (fun k z => (weights z, xi k z)) (fun z => (weights z, fun _ => z - a)) ∧
            (∀ z : U, ∀ i, weights z i ≠ 0 →
              ∃ h : near j i = true, J ⟨(j, i), h⟩ z ∈ U) ∧
            (∀ k,
              (e k).source = Metric.ball (0 : E × E) q ∧ e k 0 = 0 ∧
              Metric.closedBall (0 : E × E) ε ⊆ (e k).target ∧
              ContDiffOn ℝ ∞ (e k : E × E → E × E) (e k).source ∧
              ContDiffOn ℝ ∞ ((e k).symm : E × E → E × E) (e k).target ∧
              (∀ z ∈ Metric.closedBall (0 : E × E) q,
                (cc k).pair (e k z) = Geometry.Riemannian.Exponential.diagExp (g k) (hEnorm k)
                  ((cc k).tangent z)) ∧
              ∀ z ∈ Metric.closedBall (0 : E × E) q,
                z.1 ∈ Metric.ball (0 : E) (cc k).radius ∧
                (e k z).1 ∈ Metric.ball (0 : E) (cc k).radius ∧
                (e k z).2 ∈ Metric.ball (0 : E) (cc k).radius) ∧
            (∀ᶠ k in atTop, MapsTo (e k).symm (Metric.closedBall 0 ε) (Metric.ball 0 qInner)) ∧
            (∀ᶠ k in atTop, ∀ z : U, ∀ i (h : near j i = true), weights z i ≠ 0 →
              xi k z i = -a + (c j k).hom.symm ((c i k).hom (J ⟨(j, i), h⟩ z))) ∧
            IsOpen W ∧ a ∈ W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧
            (∀ z ∈ closure W, z - a ∈ Metric.ball (0 : E) qInner ∧
              z - a ∈ Metric.ball (0 : E) ε) ∧
            (∀ k z, F k z = (cc k).hom (Phi k z)) ∧
            CheegerGromovCompactness.MapCInfConvergenceOnCompacts W Phi (fun z => z - a) ∧
            CheegerGromovCompactness.MapCInfConvergenceOnCompacts W
              (fun k z => (c j k).hom.symm (F k z)) id ∧
            (∀ k, ContDiffOn ℝ ∞ (Phi k) W) ∧
            (∀ k ≥ N, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F k) W) ∧
            (∀ k ≥ N, ∀ z ∈ closure W,
              Phi k z ∈ Metric.ball (0 : E) (cc k).radius ∧
              F k z ∈ (cc k).restrictBall.target ∧ F k z ∈ (c j k).hom.target ∧
              (c j k).hom.symm (F k z) = a + Phi k z ∧
              dist (Phi k z) (z - a) < r / 2 ∧
              CheegerGromovCompactness.invVelocitySum (e k) (weights z) (xi k z) (Phi k z) = 0 ∧
              ∀ i, (Phi k z, xi k z i) ∈ Metric.ball (0 : E × E) ε) ∧
            (∀ k ≥ N, ∀ z ∈ closure W, ∀ y, dist y (z - a) < r →
              (CheegerGromovCompactness.invVelocitySum (e k) (weights z) (xi k z) y = 0 ↔
                y = Phi k z)) ∧
            ∀ k ≥ N, ∀ z ∈ closure W,
              (∀ i, weights z i ≠ 0 → xi k z i = z - a) →
              (e k).symm (z - a, z - a) = (z - a, 0) →
                F k z = (cc k).hom (z - a) := by
  intro D U C mu hsub hinc j a ha weights nc hr8 hball cc
  obtain ⟨xi, hxiC, hxi, hwpos, hwsum, hactive, hxiEq⟩ :=
    IntrinsicBallChart.exists_chart_active_configuration_sub_const
      g hEnorm x hρ c near hclass J hcont hconv hJsmooth C Set.univ mu hsub hinc j a
  obtain ⟨q, δ, η, flow, e, qInner, δInf, etaInf, eInf, hq, hqbound, hδ, hη, hstage,
      hqInner, hqInnerLt, hδInf, hηInf, hsourceInf, htargetInf, heInfC, hinvInfC,
      hdiagInf, happroxInf, hforward, ε, hε, hεlt, hInfMap, hstageMap, hinvConv⟩ :=
    IntrinsicBallChart.exists_recentered_diagonal_inverse_convergence
      g hEnorm hρ (c j) ha (hell j) (hBsmooth j) (hBconv j)
  have htarget : ∀ k, Metric.closedBall (0 : E × E) ε ⊆ (e k).target := by
    intro k
    exact (Metric.closedBall_subset_closedBall (le_of_lt (lt_of_lt_of_le hεlt (min_le_left _ _)))).trans
      (hstage k).2.2.2.1
  have htargetInf' : Metric.ball (0 : E × E) ε ⊆ eInf.target :=
    (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (le_of_lt (lt_of_lt_of_le hεlt (min_le_right _ _))))).trans
        htargetInf
  have hinvC : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ ((e k).symm : E × E → E × E)
      (Metric.ball (0 : E × E) ε) := Eventually.of_forall fun k =>
    (hstage k).2.2.2.2.2.1.mono (Metric.ball_subset_closedBall.trans (htarget k))
  obtain ⟨W, r, N, F, Phi, hW, haW, hWcompact, hWU, hcenter, hr, hF, hPhi, hcoords,
      hPhiC, hFC, hspec, huniq, hanchor⟩ :=
    CheegerGromovCompactness.NormalBranchHessian.exists_source_invVelocity_root_near cc
      U.isOpen ha weights xi
      (mu.contDiffOn_coordinateWeights U (fun z : U => D.toGlueData.ι j z) (hinc j))
      hxiC hxi (hwpos ⟨a, ha⟩) (hwsum ⟨a, ha⟩ (Set.mem_univ _)) e eInf
      (show (0 : ℝ) < qInner from hqInner) hε hr8 (fun _ => le_rfl)
      hinvConv hinvC hinvInfC htargetInf' (fun z hz => (hdiagInf z hz).2)
      happroxInf (hηInf.trans (by norm_num))
  have hcoordsOriginal : CheegerGromovCompactness.MapCInfConvergenceOnCompacts W
      (fun k z => (c j k).hom.symm (F k z)) id :=
    NormalBallChart.mapCInfConvergence_inv_id_of_recenter nc a hr8 hball hcoords
  refine ⟨xi, q, qInner, ε, r, e, W, N, F, Phi, hq, hqInner, hqInnerLt, hε, hr,
    hxiC, hxi, hactive, ?_, hstageMap, hxiEq, hW, haW, hWcompact, hWU, (fun z hz => ⟨(hcenter z hz).1, (hcenter z hz).2.1⟩), hF, hPhi, hcoordsOriginal,
    hPhiC, hFC, ?_, huniq, hanchor⟩
  · intro k
    obtain ⟨hsource, he, hzero, htarget₀, heC, hinvC₀, hdiag, hfence, hrest⟩ := hstage k
    exact ⟨hsource, hzero, htarget k, heC, hinvC₀, hdiag, hfence⟩
  · intro k hk z hz
    obtain ⟨hPhiBall, hFtarget, hcoord, hdist, hroot, hpairs⟩ := hspec k hk z hz
    have htargetOriginal := (nc k).recenter_restrict_ball_target_subset a hr8 (hball k) hFtarget
    refine ⟨hPhiBall, hFtarget, ?_, ?_, hdist, hroot, hpairs⟩
    · obtain ⟨y, hy, hyF⟩ := htargetOriginal
      rw [← hyF]
      exact (nc k).hom.map_source ((nc k).ball_subset hy)
    · change (nc k).inv (F k z) = a + Phi k z
      rw [(nc k).inv_eq_add_recenter_inv a hr8 (hball k)]
      exact congrArg (a + ·) hcoord

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))



theorem IntrinsicBallChart.exists_local_source_maps_on_compact [Finite ι]
    (hJsmooth : ∀ a, ContDiffOn ℝ ∞ (J a) (Metric.ball (0 : E) (ρ / 2)))
    (B : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (Metric.ball 0 ρ))
    (hBconv : ∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball 0 ρ)
      (fun k => intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k)) (B i))
    (hell : ∀ i k, ∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k) z v v ∧
      intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k) z v v ≤ 2 * ‖v‖ ^ 2)
    (i₀ : ι) :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    let chartDomain : Set D.toGlueData.glued → ι → Set E := fun V i =>
      Subtype.val '' ((fun z : U => D.toGlueData.ι i z) ⁻¹' V)
    let coords : (∀ k, D.toGlueData.glued → M k) → ι → ℕ → E → E := fun F i k z =>
      @dite E (z ∈ U) (Classical.propDecidable _) (fun hz =>
        (c i k).hom.symm (F k (D.toGlueData.ι i ⟨z, hz⟩))) (fun _ => 0)
    ∀ C : ChartedSpace E D.toGlueData.glued, letI := C
      IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued →
      (∀ i : ι, IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (fun z : U => D.toGlueData.ι i z)) →
      ∀ (V : TopologicalSpace.Opens D.toGlueData.glued), IsCompact (closure (V : Set D.toGlueData.glued)) →
      D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩ ∈ V →
      ∃ F : ∀ k, D.toGlueData.glued → M k,
        (∀ k, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F k) V) ∧
        (∀ᶠ k in atTop, F k (D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩) = x i₀ k) ∧
        (∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (chartDomain V i)
          (fun k => coords F i k) id) ∧
        ∀ i (L : Set E), IsCompact L → L ⊆ chartDomain V i →
          ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U), z ∈ L →
            F k (D.toGlueData.ι i ⟨z, hz⟩) ∈ (c i k).hom.target := by
  intro D U chartDomain coords C hman hchart V hV hbase
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : Nonempty ι := ⟨i₀⟩
  let := hman
  have hinc := fun i => (hchart i).contMDiff
  obtain ⟨mu, hsub, ⟨Wbase, hWbase, hbaseW, hone⟩, hcfg⟩ :=
    IntrinsicBallChart.exists_partition_chart_active_configurations
      g hEnorm x hρ c near hclass J hcont hconv hJsmooth i₀ C hman hinc univ isClosed_univ
  have hlocal := fun a : ι × U =>
    IntrinsicBallChart.exists_chart_source_invVelocity_roots
      g hEnorm x hρ c near hclass J hcont hconv hJsmooth B hBsmooth hBconv hell
      C mu hsub hinc a.1 a.2 a.2.property
  choose xi q qInner epsilon rTube e W N f Phi hq hqInner hqInnerLt hepsilon hrTube
    hxiC hxi hactive hstage hcapture hxiEq hW haW hWcompact hWU hcenter hf hPhi
    hcoords hPhiC hfC hspec huniq hanchor using hlocal
  have hWsub (a : ι × U) : W a ⊆ U := subset_closure.trans (hWU a)
  have hfsmooth : ∀ a, ∀ᶠ k in atTop,
      ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (f a k) (W a) := by
    intro a
    exact (eventually_ge_atTop (N a)).mono fun k hk => hfC a k hk
  have hmem : ∀ a (K : Set E), IsCompact K → K ⊆ W a →
      ∀ᶠ k in atTop, MapsTo (f a k) K (c a.1 k).hom.target := by
    intro a K _ hKW
    filter_upwards [eventually_ge_atTop (N a)] with k hk z hz
    exact (hspec a k hk z (subset_closure (hKW hz))).2.2.1
  let weights := fun a : ι × U => mu.coordinateWeights U (fun z : U => D.toGlueData.ι a.1 z)
  let nc := fun (a : ι × U) k => (c a.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1 k) hρ
  have hr8 : 0 < 8 * (ρ / 32) := by positivity
  have hball (a : ι × U) (k : ℕ) :
      Metric.ball (a.2 : E) (8 * (ρ / 32)) ⊆ Metric.ball (0 : E) (nc a k).radius := by
    intro z hz
    change dist z 0 < ρ
    have ha : dist (a.2 : E) 0 < ρ / 8 := a.2.property
    have hz' : dist z a.2 < 8 * (ρ / 32) := hz
    have htri := dist_triangle z a.2 0
    linarith
  let cc := fun (a : ι × U) k => (nc a k).recenter a.2 hr8 (hball a k)
  have hcenterr (a : ι × U) (z : E) (hz : z ∈ U) :
      z - (a.2 : E) ∈ Metric.ball 0 (8 * (ρ / 32)) := by
    have ha : dist (a.2 : E) 0 < ρ / 8 := a.2.property
    have hz' : dist z 0 < ρ / 8 := hz
    have htri := dist_triangle z 0 a.2
    rw [dist_comm 0 (a.2 : E)] at htri
    have hdist : dist z (a.2 : E) < 8 * (ρ / 32) := by linarith
    simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hdist
  have hstage' (a : ι × U) (k : ℕ) :
      (e a k).source = Metric.ball (0 : E × E) (q a) ∧ e a k 0 = 0 ∧
      Metric.closedBall (0 : E × E) (epsilon a) ⊆ (e a k).target ∧
      ContDiffOn ℝ ∞ ((e a k).symm : E × E → E × E) (e a k).target ∧
      (∀ z ∈ (e a k).source,
        (cc a k).pair (e a k z) = Geometry.Riemannian.Exponential.diagExp (g k) (hEnorm k)
          ((cc a k).tangent z)) ∧
      ∀ z ∈ (e a k).source,
        z.1 ∈ Metric.ball (0 : E) (cc a k).radius ∧
        (e a k z).1 ∈ Metric.ball (0 : E) (cc a k).radius ∧
        (e a k z).2 ∈ Metric.ball (0 : E) (cc a k).radius := by
    obtain ⟨hsource, hzero, htarget, _, hinv, hdiag, hfence⟩ := hstage a k
    refine ⟨hsource, hzero, htarget, hinv, ?_, ?_⟩
    · intro z hz
      exact hdiag z (Metric.ball_subset_closedBall (hsource ▸ hz))
    · intro z hz
      exact hfence z (Metric.ball_subset_closedBall (hsource ▸ hz))
  have hcoordCompat : ∀ (a b : ι × U) (hba : near b.1 a.1 = true) (K : Set E),
      IsCompact K → K ⊆ W b → MapsTo (J ⟨(b.1, a.1), hba⟩) K (W a) →
      ∀ᶠ k in atTop, EqOn (fun z => f a k (J ⟨(b.1, a.1), hba⟩ z)) (f b k) K := by
    intro a b hba K hK hKW hJK
    let T := J ⟨(b.1, a.1), hba⟩
    have hKU : K ⊆ U := hKW.trans (hWsub b)
    have hTU : MapsTo T K U := hJK.mono_right (hWsub a)
    have hTK : IsCompact (T '' K) := hK.image_of_continuousOn
      ((hcont ⟨(b.1, a.1), hba⟩).mono (hKU.trans (by
        intro z hz
        exact Metric.ball_subset_ball (by linarith) hz)))
    have himageU : T '' K ⊆ U := image_subset_iff.mpr hTU
    have hrep (z : U) (hz : (z : E) ∈ K) :
        D.toGlueData.ι b.1 z = D.toGlueData.ι a.1 ⟨T z, hTU hz⟩ :=
      (IntrinsicBallChart.bufferedTransitionGlueData_ι_eq_iff_graph
        g hEnorm x hρ c near hclass J hcont hconv b.1 a.1 z ⟨T z, hTU hz⟩).mpr ⟨hba, rfl⟩
    have hweights : EqOn (fun z => weights a (T z)) (weights b) K := by
      intro z hz
      funext i
      change mu.coordinateWeights U (fun w : U => D.toGlueData.ι a.1 w) (T z) i =
        mu.coordinateWeights U (fun w : U => D.toGlueData.ι b.1 w) z i
      rw [mu.coordinateWeights_apply U _ ⟨T z, hTU hz⟩,
        mu.coordinateWeights_apply U _ ⟨z, hKU hz⟩]
      exact congrArg (mu i) (hrep ⟨z, hKU hz⟩ hz).symm
    have hatomsA := IntrinsicBallChart.eventually_chart_active_atoms
      g hEnorm x hρ c near hclass J hcont hconv a.1 a.2 hr8 (hball a)
      (weights a) (xi a) (hxi a) (hactive a) (hxiEq a) (T '' K) hTK himageU
      (fun z hz => hcenterr a z (himageU hz))
    have hatomsB := IntrinsicBallChart.eventually_chart_active_atoms
      g hEnorm x hρ c near hclass J hcont hconv b.1 b.2 hr8 (hball b)
      (weights b) (xi b) (hxi b) (hactive b) (hxiEq b) K hK hKU
      (fun z hz => hcenterr b z (hKU hz))
    let points : ∀ k, E → ι → M k := fun k z i =>
      letI : Nonempty (D.U i) := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
      if hz : z ∈ U then
        D.chartMap i (fun w : U => (c i k).hom w) (D.toGlueData.ι b.1 ⟨z, hz⟩)
      else x i k
    have hatoms : ∀ᶠ k in atTop, ∀ z ∈ K, ∀ i, weights b z i ≠ 0 →
        (cc a k).hom (xi a k (T z) i) = points k z i ∧
        (cc b k).hom (xi b k z i) = points k z i := by
      filter_upwards [hatomsA, hatomsB] with k hkA hkB z hz i hi
      let : Nonempty (D.U i) := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
      have hp : points k z i =
          D.chartMap i (fun w : U => (c i k).hom w) (D.toGlueData.ι b.1 ⟨z, hKU hz⟩) :=
        dif_pos (hKU hz)
      have hiA : weights a (T z) i ≠ 0 := by
        intro hzero
        exact hi ((congrFun (hweights hz) i).symm.trans hzero)
      refine ⟨?_, (hkB ⟨z, hKU hz⟩ hz i hi).2.trans hp.symm⟩
      exact (hkA ⟨T z, hTU hz⟩ (mem_image_of_mem T hz) i hiA).2.trans
        ((congrArg (D.chartMap i (fun w : U => (c i k).hom w))
          (hrep ⟨z, hKU hz⟩ hz).symm).trans hp.symm)
    have hroot : ∀ᶠ k in atTop, ∀ z ∈ W b,
        CheegerGromovCompactness.invVelocitySum (e b k) (weights b z) (xi b k z) (Phi b k z) = 0 := by
      filter_upwards [eventually_ge_atTop (N b)] with k hk z hz
      exact (hspec b k hk z (subset_closure hz)).2.2.2.2.2.1
    have hunique : ∀ᶠ k in atTop, ∀ z ∈ W a, ∀ y, dist y (z - (a.2 : E)) < rTube a →
        CheegerGromovCompactness.invVelocitySum (e a k) (weights a z) (xi a k z) y = 0 →
        y = Phi a k z := by
      filter_upwards [eventually_ge_atTop (N a)] with k hk z hz y hy hrootY
      exact (huniq a k hk z (subset_closure hz) y hy).mp hrootY
    have heq := IntrinsicBallChart.eventually_eqOn_recentered_hom_of_invVelocity_roots
      g hEnorm (x a.1) (x b.1) hρ (c a.1) (c b.1) (hell a.1) (hell b.1)
      ((hclass b.1 a.1).mono fun k hk => hk.1 hba) (hconv ⟨(b.1, a.1), hba⟩)
      (hcont ⟨(b.1, a.1), hba⟩) a.2 b.2 hr8 hr8 (hball a) (hball b)
      (e a) (e b) (q a) (q b) (qInner a) (epsilon a) (epsilon b) (rTube a)
      (hq a) (hq b) (hqInnerLt a) (hrTube a) (hstage' a) (hstage' b) (hcapture a)
      (weights a) (weights b) (xi a) (xi b) (Phi a) (Phi b) points (W a) (W b) K
      (hxi a) (hxi b) (hPhi b) (hWsub b) hK hKW hJK (hWsub a)
      (fun z hz => (hcenter a z (subset_closure hz)).2)
      (fun z hz => ⟨Metric.ball_subset_ball (le_of_lt (hqInnerLt b))
        (hcenter b z (subset_closure hz)).1, (hcenter b z (subset_closure hz)).2⟩)
      hweights hatoms hroot hunique
    filter_upwards [heq] with k hk z hz
    exact (hf a k (T z)).trans ((hk hz).trans (hf b k z).symm)
  let a₀ : ι × U := (i₀, ⟨0, Metric.mem_ball_self (by positivity)⟩)
  obtain ⟨hself, hJzero⟩ :=
    (IntrinsicBallChart.bufferedTransitionGlueData_ι_eq_iff_graph
      g hEnorm x hρ c near hclass J hcont hconv i₀ i₀ a₀.2 a₀.2).mp rfl
  have hweights0 (i : ι) : weights a₀ 0 i = if i = i₀ then 1 else 0 := by
    exact (mu.coordinateWeights_apply U (fun z : U => D.toGlueData.ι i₀ z) a₀.2 i).trans
      (hone _ hbaseW i)
  have hfbase : ∀ᶠ k in atTop, f a₀ k a₀.2 = x i₀ k := by
    filter_upwards [hxiEq a₀, eventually_ge_atTop (N a₀)] with k hk hkN
    have hzero : (0 : E × E) ∈ (e a₀ k).source := by
      rw [(hstage a₀ k).1]
      exact Metric.mem_ball_self (hq a₀)
    have hezero : (e a₀ k).symm (0, 0) = (0, 0) := by
      have h := (e a₀ k).left_inv hzero
      rw [(hstage a₀ k).2.1] at h
      exact h
    have hactive0 (i : ι) (hi : weights a₀ 0 i ≠ 0) : xi a₀ k 0 i = 0 := by
      have hii : i = i₀ := by
        by_contra hne
        exact hi ((hweights0 i).trans (if_neg hne))
      subst i
      have h := hk a₀.2 i₀ hself hi
      change xi a₀ k 0 i₀ = -(0 : E) + (c i₀ k).hom.symm ((c i₀ k).hom (J ⟨(i₀, i₀), hself⟩ 0)) at h
      change J ⟨(i₀, i₀), hself⟩ 0 = 0 at hJzero
      simp only [neg_zero, zero_add, hJzero] at h
      exact h.trans ((c i₀ k).hom.left_inv (by
        rw [(c i₀ k).source_eq]
        exact Metric.mem_ball_self hρ))
    have hFzero := hanchor a₀ k hkN 0 (subset_closure (haW a₀))
      (by simpa only [a₀, sub_zero] using hactive0)
      (by simpa only [a₀, sub_zero] using hezero)
    change f a₀ k 0 = (cc a₀ k).hom (0 - (0 : E)) at hFzero
    rw [sub_self] at hFzero
    exact hFzero.trans ((cc a₀ k).map_zero.trans ((nc a₀ k).map_zero))
  let : T2Space D.toGlueData.glued :=
    IntrinsicBallChart.bufferedTransitionGlueData_t2Space g hEnorm x hρ c near hclass J hcont hconv
  let : LocallyCompactSpace D.toGlueData.glued :=
    ChartedSpace.locallyCompactSpace E D.toGlueData.glued
  have hcover : ∀ p ∈ closure (V : Set D.toGlueData.glued),
      ∃ (i : ι) (z : U), D.toGlueData.ι i z = p := by
    intro p _
    exact D.ι_jointly_surjective p
  have ha₀ : D.toGlueData.ι a₀.1 a₀.2 ∈ V := hbase
  have hcompat := IntrinsicBallChart.eventually_eqOn_extend_of_transition_eqOn_compact
    g hEnorm x hρ c near hclass J hcont hconv atTop W f (x i₀) hcoordCompat
  obtain ⟨F, hFsmooth, hFbase, hFconv, hFtarget, _⟩ :=
    CheegerGromovCompactness.exists_contMDiffOn_mapCInfConvergenceOnCompacts_of_open_coordinate_cover
      U (fun i z => D.toGlueData.ι i z) (fun i => (D.ι_isOpenEmbedding i).injective)
      hchart V hV hcover W hW haW f (x i₀) (fun i k => (c i k).hom.symm)
      (fun i k => (c i k).hom.target) hfsmooth hcoords hmem hcompat a₀ ha₀ hfbase
  exact ⟨F, hFsmooth, hFbase, hFconv, hFtarget⟩

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end
