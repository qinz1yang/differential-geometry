import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SeedVolume

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter _root_.Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private local instance normalizedKLimTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance normalizedKLimCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance normalizedKLimSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance normalizedKLimC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance normalizedKLimT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance normalizedKLimSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance normalizedKLimTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem normalizedKLim_edist_triangle {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (g : SmoothRiemannianMetric I F.M) (x y z : F.M) :
    riemannianEDistOf (I := I) g x z ≤
      riemannianEDistOf (I := I) g x y + riemannianEDistOf (I := I) g y z := by
  let _ : RiemannianBundle (fun q : F.M => TangentSpace I q) := ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist I x z ≤
    Manifold.riemannianEDist I x y + Manifold.riemannianEDist I y z
  exact Manifold.riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z)

theorem klim_buffered_ball_subset {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) {kappa : ℝ}
    (hK : KLim kappa F) {s A rho : ℝ} (hs : s ≤ 0)
    (hA : 0 ≤ A) (hrho : 0 ≤ rho) (x y z : F.M)
    (hy : riemannianEDistOf (I := I) (F.S.base.metric 0) x y ≤ ENNReal.ofReal A)
    (hz : riemannianEDistOf (I := I) (F.S.base.metric s) y z ≤ ENNReal.ofReal rho) :
    riemannianEDistOf (I := I) (F.S.base.metric 0) x z ≤
      ENNReal.ofReal (A + rho) := by
  calc
    _ ≤ riemannianEDistOf (I := I) (F.S.base.metric 0) x y +
        riemannianEDistOf (I := I) (F.S.base.metric 0) y z :=
      normalizedKLim_edist_triangle F _ x y z
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal rho :=
      add_le_add hy ((hK.edist_le hs le_rfl y z).trans hz)
    _ = ENNReal.ofReal (A + rho) := (ENNReal.ofReal_add hA hrho).symm

variable [I.Boundaryless]

theorem exists_normalized_klim_local_curvature_constants
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ) :
    ∃ C : ℝ → ℝ, (∀ A, 0 < C A) ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F → F.S.scalar 0 F.basepoint = 1 →
        ∀ A : ℝ, ∀ y : F.M,
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤
            ENNReal.ofReal A → ∀ t : ℝ, t ≤ 0 →
          (0 ≤ F.S.scalar t y ∧ F.S.scalar t y ≤ C A) ∧
            F.rmNormSq (I := I) t y ≤ 3 * (C A) ^ 2 := by
  classical
  choose C hC hbound using fun A : ℝ =>
    exists_normalized_bounded_distance_scalar_constant (I := I) hdim kappa A
  refine ⟨C, hC, ?_⟩
  intro D F hK hbase A y hy t ht
  have hterminal := hbound A D F hK F.basepoint hbase y hy
  exact ⟨⟨hK.scalar_nonneg ht y, (hK.scalar_le_terminal ht y).trans hterminal⟩,
    hK.rmNormSq_le_of_terminal_scalar_le F hdim ht y hterminal⟩

theorem exists_normalized_klim_buffered_curvature_constants
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ) :
    ∃ C : ℝ → ℝ, (∀ A, 0 < C A) ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F → F.S.scalar 0 F.basepoint = 1 →
        ∀ A : ℝ, 0 ≤ A → ∀ t : ℝ, t ≤ 0 → ∀ y z : F.M,
          riemannianEDistOf (I := I) (F.S.base.metric 0) F.basepoint y ≤
            ENNReal.ofReal A →
          riemannianEDistOf (I := I) (F.S.base.metric t) y z ≤ ENNReal.ofReal 1 →
          (0 ≤ F.S.scalar t z ∧ F.S.scalar t z ≤ C A) ∧
            F.rmNormSq (I := I) t z ≤ 3 * (C A) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_normalized_klim_local_curvature_constants (I := I) hdim kappa
  refine ⟨fun A => C (A + 2), fun A => hC (A + 2), ?_⟩
  intro D F hK hbase A hA t ht y z hy hz
  apply hbound D F hK hbase (A + 2) z _ t ht
  exact (klim_buffered_ball_subset F hK ht hA zero_le_one
    F.basepoint y z hy hz).trans (ENNReal.ofReal_le_ofReal (by linarith))

theorem exists_normalized_klim_base_injectivity [NeZero (Module.finrank ℝ E)]
    (hdim : Module.finrank ℝ E = 3) (kappa : ℝ) (hkappa : 0 < kappa) :
    ∃ iota : ℝ, 0 < iota ∧
      ∀ (D : RealTimeInterval) (F : PointedFlowData.{u, uE, uH} (I := I) D),
        KLim kappa F → F.S.scalar 0 F.basepoint = 1 →
          HasInjRadiusAt (I := I) (F.atTime (I := I) 0) F.basepoint iota := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    exists_normalized_bounded_distance_scalar_constant (I := I) hdim kappa 1
  let rho : ℝ := 1 / (4 * (C + 1))
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  let hscale := exists_uniform_local_jacobi_scale (Module.finrank ℝ E)
    (R := rho) (K := 2 * C + 1) hrho (by linarith)
  let rJ : ℝ := hscale.choose
  let R : ℝ := min rJ (Real.pi / Real.sqrt (2 * C + 1))
  have hR : 0 < R := lt_min hscale.choose_spec.1
    (div_pos Real.pi_pos (by positivity))
  refine ⟨selectedCGTInjRadius E kappa R,
    selectedCGTInjRadius_pos (E := E) hkappa hR, ?_⟩
  intro D F hK hbase
  let X : PointedFlowSeq.{u, uE, uH} (I := I) := { D := D, term := fun _ => F }
  have hunit : ∀ i,
      let _ : TopologicalSpace (X.term i).M := (X.term i).topology
      let _ : ChartedSpace H (X.term i).M := (X.term i).charted
      let _ : IsManifold I ∞ (X.term i).M := (X.term i).smooth
      ∀ z : (X.term i).M,
        riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
          (X.term i).basepoint z < ENNReal.ofReal 1 → (X.term i).S.scalar 0 z ≤ C := by
    intro i
    dsimp only [X]
    intro z hz
    exact hbound D F hK F.basepoint hbase z hz.le
  let B := klim_three_baseInjBound_of_unit_scalar_bound X (fun _ => hK) hdim C hC hunit
  exact B.bound 0

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
