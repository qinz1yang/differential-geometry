import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSpatialCanonicalMargins
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardWindowBallPlacement
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardWindowComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosenessEndpointWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardActionComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSpatialCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessUniformTransport

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

private local instance standardWindowSpatialSigmaCompact (D : ℝ) :
    SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

private theorem nonempty_window_tangentOrientation (D : ℝ) :
    Nonempty (TangentOrientationSection (standardCapWindow D)) := by
  let e := (finCongr (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)).symm
  let o := DifferentialGeometry.Topology.Manifold.euclideanSmoothOrientation
    (EuclideanSpace ℝ (Fin 3))
    (Orientation.reindex ℝ (EuclideanSpace ℝ (Fin 3)) e
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation))
  obtain ⟨O, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      (𝓡 3) o
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  let O₃ : DifferentialGeometry.ManifoldOrientation (𝓡 3) (EuclideanSpace ℝ (Fin 3)) 3 :=
    cast (congrArg (fun n =>
      DifferentialGeometry.ManifoldOrientation (𝓡 3) (EuclideanSpace ℝ (Fin 3)) n) hdim) O
  let oE : TangentOrientationSection (EuclideanSpace ℝ (Fin 3)) :=
    { orientation := O₃.orientation, locally_constant := O₃.locally_constant }
  exact ⟨oE.restrictOpen (standardCapWindow D)⟩

private theorem le_mul_of_half_scalar_lower {τ c₀ T RS RQ : ℝ} (hτ : 0 ≤ τ) (hc₀ : 0 < c₀)
    (hT1 : T < 1) (hQ : c₀ / (1 - T) ≤ RQ) (hS : 1 / 2 * RQ ≤ RS)
    (hT : 2 * τ / (c₀ + 2 * τ) ≤ T) : τ ≤ T * RS := by
  have hden : 0 < c₀ + 2 * τ := by linarith
  have h1T : 0 < 1 - T := by linarith
  have hT0 : 0 ≤ T := le_trans (by positivity) hT
  have hTc : 2 * τ ≤ T * (c₀ + 2 * τ) := by rwa [div_le_iff₀ hden] at hT
  have hQ' : c₀ ≤ RQ * (1 - T) := by rwa [div_le_iff₀ h1T] at hQ
  nlinarith [mul_le_mul_of_nonneg_left hS hT0, mul_le_mul_of_nonneg_left hQ' hT0]

theorem exists_window_spatialCanonicalWitness_of_standard_close {ε : ℝ} (hε : 0 < ε)
    (hε' : ε < 1 / 11) :
    ∃ Cw : ℝ, 1 ≤ Cw ∧ ∀ (Θ r : ℝ), Θ < 1 →
    ∃ (D : ℝ) (N : ℕ) (e : ℝ), r < D ∧ 0 < e ∧
    ∀ (Q : StandardSolution) (T : ℝ) (hT : 0 ≤ T), T ≤ Θ →
    ∀ (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
        (RealTimeInterval.closed 0 T hT)), IsSolutionOn S →
    (∀ τ ∈ Icc 0 T, ∀ i ≤ N, ∀ v : standardCapWindow D,
      metricDerivNorm i (S.base.metric τ)
        ((Q.val.metric τ).restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
    ∀ z : standardCapWindow D, ‖z.val‖ < r →
    ∀ C2 : ℝ, Cw ≤ C2 →
      (∀ v : TangentSpace I3 z,
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (S.base.metric T)) z v)| ≤
          C2 * S.scalar T z * Real.sqrt (S.scalar T z) *
            Real.sqrt ((S.base.metric T).inner z v v)) →
      ∃ W : SpatialCanonicalWitness (S.base.metric T) ε Cw C2 z, W.capTubeHasNeckChart ε := by
  obtain ⟨Cold, δ₀, hCold, hδ₀, hδ₀1, hpipe⟩ :=
    exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts.{0} hε hε' 1
  obtain ⟨τQ, hτQ, hL6⟩ := exists_uniform_orientedWitness_of_standard_close_endpoint hδ₀ hδ₀1
  obtain ⟨c₀, hc₀, hQlow⟩ := exists_standard_scalar_lower_bound
  obtain ⟨τ', hτ'def⟩ : ∃ τ' : ℝ, τ' = max τQ δ₀⁻¹ := ⟨_, rfl⟩
  have hτ' : 0 < τ' := hτ'def ▸ lt_max_of_lt_left hτQ
  obtain ⟨Θ₃, hΘ₃def⟩ : ∃ Θ₃ : ℝ, Θ₃ = 2 * τ' / (c₀ + 2 * τ') := ⟨_, rfl⟩
  have hΘ₃0 : 0 < Θ₃ := by rw [hΘ₃def]; positivity
  have hΘ₃1 : Θ₃ < 1 := by rw [hΘ₃def, div_lt_one (by positivity)]; linarith
  have ha : 0 < ε / 2 := by positivity
  have hsmall : 2 * (ε / 2) < 1 / 11 := by linarith
  have heps₀ : 0 < neckModelTolerance (ε / 2) := neckModelTolerance_pos ha
  have heps₀s : neckModelTolerance (ε / 2) < 1 / 11 :=
    (neckModelTolerance_le _).trans_lt (by linarith)
  obtain ⟨Cs, hCs, hstd⟩ :=
    StandardSolution.exists_spatialCanonicalWitness_with_margins heps₀ heps₀s hΘ₃1
  obtain ⟨δ₄, hδ₄, htr⟩ :=
    SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance
      (P := EuclideanSpace ℝ (Fin 3)) ha hsmall (m := 1 / 20) (by norm_num) (by norm_num) hCs hCs
      one_pos
  obtain ⟨Λ, hΛ, hplace⟩ := StandardSolution.exists_ball_placement hΘ₃1
  obtain ⟨e₂, he₂, hM2⟩ := StandardSolution.exists_window_metricComparisonOn_of_lt hΘ₃0.le hΘ₃1
    (max 2 ⌈(2 * (ε / 2))⁻¹⌉₊) (η := min δ₄ (1 / 2)) (lt_min hδ₄ (by norm_num))
    ((min_le_right _ _).trans_lt (by norm_num))
  refine ⟨max Cold (1000 * Cs), le_max_of_le_left hCold, ?_⟩
  intro Θ r hΘ
  obtain ⟨eta, heta, hlower⟩ :=
    exists_uniform_standard_metric_scalar_lower_comparison (max Θ 0) (le_max_right _ _)
      (max_lt hΘ one_pos)
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 8 * Cs + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt Cs := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  obtain ⟨D, NL, eL, hrD, heL, hwit⟩ := hL6 Θ (r + Λ * (L + 1) + 1) hΘ
  have hΛL : 0 ≤ Λ * (L + 1) := by positivity
  refine ⟨D, max NL (max 2 ⌈(2 * (ε / 2))⁻¹⌉₊), min eL (min eta e₂), by linarith,
    lt_min heL (lt_min heta he₂), ?_⟩
  intro Q T hT0 hTΘ S hS hclose z hz C2 hC2 hgrad
  have hTT : T ∈ Icc 0 T := ⟨hT0, le_rfl⟩
  by_cases hold : Θ₃ ≤ T
  · have hT1 : T < 1 := hTΘ.trans_lt hΘ
    have hlow := (hlower Q (standardCapWindow D) (S.base.metric T) T
      ⟨hT0, hTΘ.trans (le_max_left _ _)⟩ z (fun j hj =>
        ((hclose T hTT j (hj.trans ((le_max_left _ _).trans (le_max_right _ _))) z).le.trans
          ((min_le_right _ _).trans (min_le_left _ _))))).2
    rw [metricScalarAt_restrictOpen] at hlow
    have hτ : τ' ≤ T * S.scalar T z :=
      le_mul_of_half_scalar_lower hτ'.le hc₀ hT1 (hQlow Q z.val T ⟨hT0, hT1⟩) hlow
        (hΘ₃def ▸ hold)
    obtain ⟨o⟩ := nonempty_window_tangentOrientation D
    have hOW := hwit Q T hT0 hTΘ S hS
      (fun τ hτ i hi v => (hclose τ hτ i (hi.trans (le_max_left _ _)) v).trans_le
        (min_le_left _ _)) o z (by linarith) ((hτ'def ▸ le_max_left τQ δ₀⁻¹).trans hτ)
    have hRpos : 0 < S.scalar T z := by
      have h1 : 0 < metricScalarAt (Q.val.metric T) z.val :=
        lt_of_lt_of_le (by positivity) (hQlow Q z.val T ⟨hT0, hT1⟩)
      change 0 < metricScalarAt (S.base.metric T) z
      linarith
    have hwin : Ioo (T - (δ₀ * S.scalar T z)⁻¹) T ⊆ (RealTimeInterval.closed 0 T hT0).regular := by
      have h1 : δ₀⁻¹ ≤ T * S.scalar T z := (hτ'def ▸ le_max_right τQ δ₀⁻¹).trans hτ
      have h2 : (δ₀ * S.scalar T z)⁻¹ ≤ T := by
        rw [inv_le_iff_one_le_mul₀ (mul_pos hδ₀ hRpos)]
        have h3 := mul_le_mul_of_nonneg_left h1 hδ₀.le
        rw [mul_inv_cancel₀ hδ₀.ne'] at h3
        linarith [show T * (δ₀ * S.scalar T z) = δ₀ * (T * S.scalar T z) by ring]
      intro σ hσ
      exact ⟨by linarith [hσ.1], hσ.2⟩
    obtain ⟨B, hB⟩ := hpipe standardModelKappa (standardCapWindow D)
      (RealTimeInterval.closed 0 T hT0) S hS δ₀ o z T le_rfl hwin hOW
    have h1 : Cold ≤ max Cold (1000 * Cs) := le_max_left _ _
    have h2 : Cold ≤ C2 := h1.trans hC2
    exact ⟨((B.canonicalWitnessMono B.tolerance_lt.le hε').enlargeConstants h1 h2).toSpatial,
      CanonicalWitness.capTubeHasNeckChart_toSpatial
        ((hB.mono_eps B.tolerance_lt.le hε').enlarge_constants h1 h2)⟩
  · have hTy : T ∈ Icc 0 Θ₃ := ⟨hT0, (not_le.mp hold).le⟩
    obtain ⟨W0, hW0, hM0⟩ := hstd Q z.val T hTy
    have hR1 : 1 ≤ metricScalarAt (Q.val.metric T) z.val :=
      Q.val.one_le_scalar T (Q.mem_domain_of_mem_Icc hΘ₃1 hTy) z.val
    have hsR : 1 ≤ Real.sqrt (metricScalarAt (Q.val.metric T) z.val) := Real.one_le_sqrt.mpr hR1
    have hne : Nonempty (standardCapWindow D) := ⟨z⟩
    set F := (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3)
      (standardCapWindow D) hne).symm with hFdef
    have hFsrc : F.source = (standardCapWindow D : Set (EuclideanSpace ℝ (Fin 3))) :=
      (standardCapWindow D).openPartialHomeomorphSubtypeCoe_target hne
    have hUF : ((standardCapWindow (D - 1) : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3))) :
        Set (EuclideanSpace ℝ (Fin 3))) ⊆ F.source := by
      rw [hFsrc]
      intro y hy
      change ‖y‖ < D + 1
      have : ‖y‖ < D - 1 + 1 := hy
      linarith
    have hFz : F z.val = z := Subtype.ext ((DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
      (I := I3) (standardCapWindow D) hne).right_inv' (by
        change z.val ∈ F.source
        rw [hFsrc]
        exact z.2))
    have hRbL : (8 * Cs + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt Cs) /
        Real.sqrt (metricScalarAt (Q.val.metric T) z.val) ≤ L := by
      rw [← hLdef]
      exact div_le_self hL0 hsR
    have hsubL := riemannianClosedBallOf_mono (Q.val.metric T) z.val hRbL
    obtain ⟨hcptL, hplL⟩ := hplace Q T hTy L z.val hL0
    have hcpt := hcptL.of_isClosed_subset
      (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) hsubL
    have hsub : riemannianClosedBallOf (I := I3) (Q.val.metric T) z.val
        ((8 * Cs + 3 * ((ε / 2)⁻¹ + 7) * Real.sqrt Cs) /
          Real.sqrt (metricScalarAt (Q.val.metric T) z.val)) ⊆
        (standardCapWindow (D - 1) : Set (EuclideanSpace ℝ (Fin 3))) := by
      intro y hy
      have h := hplL y (hsubL hy)
      change ‖y‖ < D - 1 + 1
      linarith
    obtain ⟨Cmp⟩ := hM2 D hne Q T hTy (S.base.metric T) (fun i hi v =>
      (hclose T hTT i (hi.trans (le_max_right _ _)) v).trans_le
        ((min_le_right _ _).trans (min_le_right _ _))) (D - 1) (by linarith)
    have hC2' : 1000 * Cs ≤ C2 := (le_max_right _ _).trans hC2
    have hgrad' : ∀ v : TangentSpace I3 (F z.val),
        |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (S.base.metric T)) (F z.val) v)| ≤
          C2 * metricScalarAt (S.base.metric T) (F z.val) *
            Real.sqrt (metricScalarAt (S.base.metric T) (F z.val)) *
            Real.sqrt ((S.base.metric T).inner (F z.val) v v) := by
      rw [hFz]
      exact hgrad
    obtain ⟨W', hW', -⟩ := htr (Q.val.metric T) z.val W0 hW0 hM0 hR1 (standardCapWindow (D - 1))
      hcpt hsub (standardCapWindow D) (S.base.metric T) F hUF
      (Cmp.mono subset_rfl le_rfl (min_le_left _ _)) C2 hC2' hgrad'
    have hCw : 2 * Cs ≤ max Cold (1000 * Cs) := (by linarith : 2 * Cs ≤ 1000 * Cs).trans
      (le_max_right _ _)
    rw [← hFz, show ε = 2 * (ε / 2) by ring]
    exact ⟨W'.enlargeConstants hCw le_rfl, hW'.enlarge_constants hCw le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow
