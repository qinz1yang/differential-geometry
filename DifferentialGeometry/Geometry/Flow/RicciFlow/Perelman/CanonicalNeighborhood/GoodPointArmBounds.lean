import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedArmCrossings
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckArmCrossing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckDiameter

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem exists_good_point_neck_arm_bounds
    (kappa : ℝ) {alpha theta : ℝ} (halpha : 0 < alpha) (hsmall : alpha < 1 / 44)
    (htheta : 0 < theta) :
    ∃ Lmin Lmax epsStar C : ℝ,
      0 < Lmin ∧ Lmin < Lmax ∧ 0 < epsStar ∧ epsStar < alpha ∧ 1 ≤ C ∧
      ∀ (D : RealTimeInterval) (P : PointedFlowData.{u, 0, 0} I3 D),
        TangentOrientationSection P.M → ∀ (eps : ℝ) (x : P.M) (t : ℝ),
          WindowedModelWitness eps kappa P.S x t → eps ≤ epsStar →
          Ioo (t - (eps * P.S.scalar t x)⁻¹) t ⊆ D.regular →
          ∀ (a b : MinimizingArm (P.S.base.metric t) x) (s v : ℝ),
            s ∈ Ioc 0 a.length → v ∈ Ioc 0 b.length →
            Real.sqrt (P.S.scalar t x) * s ∈ Icc Lmin Lmax →
            Real.sqrt (P.S.scalar t x) * v ∈ Icc Lmin Lmax →
            theta ≤ comparisonAngle s v (metricDistance (P.S.base.metric t) (a.point s) (b.point v)) →
            ∃ (neck : StrongNeck P.S (2 * alpha) x t)
              (path : TransversePath (a.point a.length) (b.point b.length)
                (neck.map '' (univ ×ˢ ({0} : Set ℝ)))),
              (path.intersection = 1 ∨ path.intersection = -1) ∧
              (∀ w ∈ Icc s a.length, a.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ w ∈ Icc v b.length, b.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
              ∀ y ∈ neck.map '' (univ ×ˢ Icc (-10 : ℝ) 10),
                ∀ z ∈ neck.map '' (univ ×ˢ Icc (-10 : ℝ) 10),
                  metricDistance (P.S.base.metric t) y z ≤ C / Real.sqrt (P.S.scalar t x) := by
  classical
  obtain ⟨C, hC, hdiam⟩ := metricDistance_core_le_of_neckCoreDiameterBound neckCoreDiameterBound_holds.{u}
  let C' := max 1 C
  have hC' : 1 ≤ C' := le_max_left _ _
  suffices hresult : ∃ Lmin Lmax epsStar : ℝ,
      0 < Lmin ∧ Lmin < Lmax ∧ 0 < epsStar ∧ epsStar < alpha ∧
      ∀ (D : RealTimeInterval) (P : PointedFlowData.{u, 0, 0} I3 D),
        TangentOrientationSection P.M → ∀ (eps : ℝ) (x : P.M) (t : ℝ),
          WindowedModelWitness eps kappa P.S x t → eps ≤ epsStar →
          Ioo (t - (eps * P.S.scalar t x)⁻¹) t ⊆ D.regular →
          ∀ (a b : MinimizingArm (P.S.base.metric t) x) (s v : ℝ),
            s ∈ Ioc 0 a.length → v ∈ Ioc 0 b.length →
            Real.sqrt (P.S.scalar t x) * s ∈ Icc Lmin Lmax →
            Real.sqrt (P.S.scalar t x) * v ∈ Icc Lmin Lmax →
            theta ≤ comparisonAngle s v (metricDistance (P.S.base.metric t) (a.point s) (b.point v)) →
            ∃ (neck : StrongNeck P.S (2 * alpha) x t)
              (path : TransversePath (a.point a.length) (b.point b.length)
                (neck.map '' (univ ×ˢ ({0} : Set ℝ)))),
              (path.intersection = 1 ∨ path.intersection = -1) ∧
              (∀ w ∈ Icc s a.length, a.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ w ∈ Icc v b.length, b.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) by
    obtain ⟨Lmin, Lmax, epsStar, hLmin, hLmax, heps, hepsAlpha, hbody⟩ := hresult
    refine ⟨Lmin, Lmax, epsStar, C', hLmin, hLmax, heps, hepsAlpha, hC', ?_⟩
    intro D P o eps x t W heps' hreg a b s v hs hv hsa hvb hang
    obtain ⟨nk, path, hinter, hano, hbno⟩ := hbody D P o eps x t W heps' hreg a b s v hs hv hsa hvb hang
    refine ⟨nk, path, hinter, hano, hbno, ?_⟩
    intro y hy z hz
    exact (hdiam P.M D P.S (2 * alpha) x t nk y hy z hz).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
  obtain ⟨delta, hdelta, _hdeltaZero, hcrossings⟩ := exists_windowed_tolerances_for_original_arm_opposite_slices.{u}
  by_contra! h
  have hbad (n : ℕ) := h ((n : ℝ) + 1) (2 * ((n : ℝ) + 1))
    (min (delta n) (alpha / 2)) (by positivity) (by linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n])
    (lt_min (hdelta n) (half_pos halpha)) ((min_le_right _ _).trans_lt (half_lt_self halpha))
  choose D P o eps x t W heps hreg a b s v hs hv hsa hvb hangle hnone using hbad
  let arms := fun i => ![a i, b i]
  let ell := fun i => ![s i, v i]
  have hell (i : ℕ) (j : Fin 2) : ell i j ∈ Ioc 0 (arms i j).length := by
    fin_cases j
    · exact hs i
    · exact hv i
  have hlength (i : ℕ) (j : Fin 2) : Real.sqrt ((P i).S.scalar (t i) (x i)) * ell i j ∈
      Icc ((i : ℝ) + 1) (2 * ((i : ℝ) + 1)) := by
    fin_cases j
    · exact hsa i
    · exact hvb i
  obtain ⟨phi, hphi, r, _hr, hfreq⟩ := hcrossings (fun i => (P i).M) D (fun i => (P i).S)
    (fun i => (P i).isSolution) o kappa x t eps W
    (fun i => (heps i).trans (min_le_left _ _)) hreg arms ell hell hlength
    theta htheta (Eventually.of_forall hangle) alpha halpha (by linarith) 20 (by norm_num)
  have hafter : ∀ᶠ i in atTop, ∀ j : Fin 2,
      (r : ℝ) / Real.sqrt ((P (phi i)).S.scalar (t (phi i)) (x (phi i))) ≤ ell (phi i) j := by
    have hnat : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
      tendsto_atTop_mono (fun i : ℕ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
    filter_upwards [(hnat.comp hphi.tendsto_atTop).eventually_ge_atTop (r : ℝ)] with i hi
    intro j
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (W (phi i)).scalar_pos)).mpr
    simpa only [mul_comm] using hi.trans (hlength (phi i) j).1
  obtain ⟨i, hcross, hafteri⟩ := (hfreq.and_eventually hafter).exists
  obtain ⟨_modelMap, nk, _hmap, hmem, _htarget, sa, sb, hsa', hsb', pa, pb, hsides⟩ := hcross
  have hasa : sa ∈ Icc 0 (a (phi i)).length := ⟨hsa'.1.le, hsa'.2.trans (hmem 0).2.le⟩
  have hbsb : sb ∈ Icc 0 (b (phi i)).length := ⟨hsb'.1.le, hsb'.2.trans (hmem 1).2.le⟩
  have hreserve : 17 ≤ Real.sqrt (1 - 2 * alpha) * 19 := by
    have hh : (18 : ℝ) / 19 < Real.sqrt (1 - 2 * alpha) := by
      apply (Real.lt_sqrt (by norm_num)).mpr
      nlinarith
    nlinarith
  have hins : (20 : ℝ) < (2 * alpha)⁻¹ :=
    (lt_inv_comm₀ (by norm_num) (by positivity)).mpr (by linarith)
  obtain ⟨hano, hbno, path, hinter⟩ := exists_transversePath_of_opposite_slices_of_radial_reserve
    nk (R := 19) (H := 20) (by norm_num) (by norm_num) hreserve hins
    (a (phi i)) (b (phi i)) hasa hbsb hsides
  obtain ⟨w, hw, hwin⟩ := hnone (phi i) nk path hinter
    (fun w hw => hano w ⟨hsa'.2.trans ((hafteri 0).trans hw.1), hw.2⟩)
  exact hbno w ⟨hsb'.2.trans ((hafteri 1).trans hw.1), hw.2⟩ hwin


theorem good_point_neck_arm_bounds
    (kappa : ℝ) {alpha theta : ℝ} (halpha : 0 < alpha) (hsmall : alpha < 1 / 44)
    (htheta : 0 < theta) :
    ∃ Lmin Lmax epsStar C : ℝ,
      0 < Lmin ∧ Lmin < Lmax ∧ 0 < epsStar ∧ epsStar < alpha ∧ 1 ≤ C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (o : TangentOrientationSection M) (x : M) (t : ℝ),
          Ioo (t - (epsStar * S.scalar t x)⁻¹) t ⊆ D.regular →
          OrientedWitness S o epsStar kappa x t →
          ∀ (a b : MinimizingArm (S.base.metric t) x) (s v : ℝ),
            s ∈ Ioc 0 a.length → v ∈ Ioc 0 b.length →
            Real.sqrt (S.scalar t x) * s ∈ Icc Lmin Lmax →
            Real.sqrt (S.scalar t x) * v ∈ Icc Lmin Lmax →
            theta ≤ comparisonAngle s v (metricDistance (S.base.metric t) (a.point s) (b.point v)) →
            ∃ (neck : StrongNeck S (2 * alpha) x t)
              (path : TransversePath (a.point a.length) (b.point b.length)
                (neck.map '' (univ ×ˢ ({0} : Set ℝ)))),
              (path.intersection = 1 ∨ path.intersection = -1) ∧
              (∀ w ∈ Icc s a.length, a.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
              (∀ w ∈ Icc v b.length, b.point w ∉ neck.map '' (univ ×ˢ ({0} : Set ℝ))) ∧
              ∀ y ∈ neck.map '' (univ ×ˢ Icc (-10 : ℝ) 10),
                ∀ z ∈ neck.map '' (univ ×ˢ Icc (-10 : ℝ) 10),
                  metricDistance (S.base.metric t) y z ≤ C / Real.sqrt (S.scalar t x) := by
  obtain ⟨Lmin, Lmax, epsStar, C, hLmin, hLmax, heps, hepsAlpha, hC, hbody⟩ :=
    exists_good_point_neck_arm_bounds kappa halpha hsmall htheta
  refine ⟨Lmin, Lmax, epsStar, C, hLmin, hLmax, heps, hepsAlpha, hC, ?_⟩
  intro M _ _ _ _ _ D S hS o x t hreg hW
  let P : PointedFlowData.{u, 0, 0} I3 D := { M := M, basepoint := x, S := S, isSolution := hS }
  exact hbody D P o epsStar x t hW.choose le_rfl hreg

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
