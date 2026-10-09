import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorRicciBall
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPositiveRayDistance
import DifferentialGeometry.Geometry.Comparison.Volume.RadialComparison

/-!
Actual original-ball Ricci bounds imply model-ratio monotonicity on each G77 birth interval.
The proof uses physical distance control and the actual interior metric's local Ricci transport.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

private theorem physicalBirthRatio_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryInterior_birth_ratio_antitone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [ambientDimension : NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (κ L η : ℝ)
    (hdim : Module.finrank ℝ E = 3)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hL : 0 < L) (hηL : η < L) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      physicalBirthRatio_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞
      (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞
      (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ (_hRic : ∀ (x : U) (z : TangentSpace I x),
        DifferentialGeometry.riemannianEDistOf g p (x : M) < ENNReal.ofReal L →
        -2 * κ ^ 2 * (g.restrictOpen U).inner x z z ≤
          ricciTensor (g.restrictOpen U) x z z)
      (γ : ℝ → U)
      (V : ι →
        ∀ t, TangentSpace (𝓘(ℝ, E)) (γ t))
      (_hphysical : ∀ t ∈ Ioc (0 : ℝ) η,
        ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) ∞ γ t ∧
        k.inner (γ t) (curveVelocity γ t) (curveVelocity γ t) = 1 ∧
        (∀ i, ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞
          (fun s => (⟨γ s, V i s⟩ : TangentBundle (𝓘(ℝ, E)) U)) t) ∧
        (∀ i, IsJacobiAt k γ (V i) t) ∧
        (∀ i, k.inner (γ t) (curveVelocity γ t) (V i t) = 0) ∧
        (∀ i, k.inner (γ t) (covDerivAlong k γ (V i) t)
          (curveVelocity γ t) = 0) ∧
        (∀ i j, jacobiWronskian k γ (V i) (V j) t = 0))
      (_hLI : ∀ t ∈ Ioo (0 : ℝ) η,
        LinearIndependent ℝ (fun i => V i t))
      (_hpole : Tendsto (fun t : ℝ => (γ t : M))
        (𝓝[>] (0 : ℝ)) (𝓝 p))
      (_hlim : Tendsto
        (fun t => curveDensity k γ V t / modelRadius (-(κ ^ 2)) t ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 1)),
      AntitoneOn
        (fun t => curveDensity k γ V t / modelRadius (-(κ ^ 2)) t ^ 2)
        (Ioo (0 : ℝ) η) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    physicalBirthRatio_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞
    (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞
    (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro _hRic γ V _hphysical _hLI _hpole _hlim
  have hdim' : Module.finrank ℝ E - 1 = 2 := by omega
  have hgammaOn : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) 1 γ (Ioc 0 η) := by
    intro t ht
    exact ((_hphysical t ht).1.of_le
      (WithTop.coe_le_coe.2 (by norm_num : (1 : ℕ∞) ≤ ⊤))).contMDiffWithinAt
  have hunit : ∀ t ∈ Ioo (0 : ℝ) η,
      k.inner (γ t) (curveVelocity γ t) (curveVelocity γ t) = 1 := by
    intro t ht
    exact (_hphysical t ⟨ht.1, ht.2.le⟩).2.1
  obtain ⟨_, hdistPole⟩ :=
    boundaryInterior_positive_ray_distance g p γ η hgammaOn hunit _hpole
  have hball : ∀ t ∈ Ioo (0 : ℝ) η,
      DifferentialGeometry.riemannianEDistOf g p (γ t : M) < ENNReal.ofReal L := by
    intro t ht
    have htL : t < L := ht.2.trans hηL
    exact (hdistPole t ⟨ht.1, ht.2.le⟩).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hL).mpr htL)
  have hRicAtlas := boundaryInteriorAtlas_ricci_ball_lower g p κ L _hRic
  have hRicK : ∀ t ∈ Ioo (0 : ℝ) η,
      -2 * κ ^ 2 * k.inner (γ t) (curveVelocity γ t) (curveVelocity γ t) ≤
        ricciTensor k (γ t) (curveVelocity γ t) (curveVelocity γ t) := by
    intro t ht
    exact hRicAtlas (γ t) (curveVelocity γ t) (hball t ht)
  have hRicDimension : ∀ t ∈ Ioo (0 : ℝ) η,
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-κ ^ 2)) *
          k.inner (γ t) (curveVelocity γ t) (curveVelocity γ t) ≤
        ricciTensor k (γ t) (curveVelocity γ t) (curveVelocity γ t) := by
    intro t ht
    have hcoeff :
        ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-κ ^ 2) = -2 * κ ^ 2 := by
      rw [hdim']
      norm_num
    rw [hcoeff]
    exact hRicK t ht
  have hadm : ∀ t ∈ Ioo (0 : ℝ) η,
      modelRadiusAdmissible (-κ ^ 2) t := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    intro hpositive
    exact False.elim ((not_lt_of_ge (neg_nonpos.mpr (sq_nonneg κ))) hpositive)
  have hgammaTwo : ∀ t ∈ Ioo (0 : ℝ) η,
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E)) (2 : WithTop ℕ∞) γ t := by
    intro t ht
    exact (_hphysical t ⟨ht.1, ht.2.le⟩).1.of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hVdiff : ∀ t ∈ Ioo (0 : ℝ) η, ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := 𝓘(ℝ, E)) γ (V i) t) t := by
    intro t ht i
    rcases _hphysical t ⟨ht.1, ht.2.le⟩ with
      ⟨_, _, hV, _, _, _, _⟩
    exact (mdifferentiableAt_tangentField_iff.mp
      ((hV i).mdifferentiableAt (by simp))).2
  have hDVdiff : ∀ t ∈ Ioo (0 : ℝ) η, ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := 𝓘(ℝ, E)) γ
          (fun s => covDerivAlong k γ (V i) s) t) t := by
    intro t ht i
    rcases _hphysical t ⟨ht.1, ht.2.le⟩ with
      ⟨_, _, hV, _, _, _, _⟩
    have hDV := contMDiffAt_covDerivAlong (I := 𝓘(ℝ, E)) k
      (m := ⊤) (n := ⊤) (by simp) (hV i)
    exact (mdifferentiableAt_tangentField_iff.mp
      (hDV.mdifferentiableAt (by simp))).2
  have hVperp : ∀ t ∈ Ioo (0 : ℝ) η, ∀ i,
      k.inner (γ t) (curveVelocity γ t) (V i t) = 0 := by
    intro t ht i
    rcases _hphysical t ⟨ht.1, ht.2.le⟩ with
      ⟨_, _, _, _, hperp, _, _⟩
    exact hperp i
  have hDVperp : ∀ t ∈ Ioo (0 : ℝ) η, ∀ i,
      k.inner (γ t) (curveVelocity γ t)
        (covDerivAlong k γ (V i) t) = 0 := by
    intro t ht i
    rcases _hphysical t ⟨ht.1, ht.2.le⟩ with
      ⟨_, _, _, _, _, hperp, _⟩
    exact (k.symm (γ t) (curveVelocity γ t)
      (covDerivAlong k γ (V i) t)).trans (hperp i)
  have hJac : ∀ t ∈ Ioo (0 : ℝ) η, ∀ i,
      IsJacobiAt k γ (V i) t := by
    intro t ht i
    rcases _hphysical t ⟨ht.1, ht.2.le⟩ with
      ⟨_, _, _, hJac, _, _, _⟩
    exact hJac i
  have hW : ∀ t ∈ Ioo (0 : ℝ) η, ∀ i j,
      jacobiWronskian k γ (V i) (V j) t = 0 := by
    intro t ht i j
    rcases _hphysical t ⟨ht.1, ht.2.le⟩ with
      ⟨_, _, _, _, _, _, hW⟩
    exact hW i j
  have hratioLower : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), C ≤
        curveDensity k γ V t / modelDensity (-κ ^ 2)
          (Module.finrank ℝ E - 1) t := by
    have hevent := Filter.Tendsto.eventually_const_lt
      (by norm_num : (1 / 2 : ℝ) < 1) _hlim
    refine ⟨1 / 2, by norm_num, ?_⟩
    filter_upwards [hevent] with t ht
    simpa only [modelDensity, hdim, Nat.reduceSub] using ht.le
  have hmean : ∀ t ∈ Ioo (0 : ℝ) η,
      curveMean k γ V t ≤ modelMeanCurv (-κ ^ 2)
        (Module.finrank ℝ E - 1) t := by
    have hd : 0 < Module.finrank ℝ E - 1 := by omega
    have hadmScaled : ∀ t ∈ Ioo (0 : ℝ) η,
        modelRadiusAdmissible (-κ ^ 2 * 1 ^ 2) t := by
      intro t ht
      simpa only [one_pow, mul_one] using hadm t ht
    have hratioLowerScaled : ∃ C : ℝ, 0 < C ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ), C ≤
          curveDensity k γ V t /
            modelDensity (-κ ^ 2 * 1 ^ 2) (Module.finrank ℝ E - 1) t := by
      simpa only [one_pow, mul_one] using hratioLower
    simpa only [one_pow, mul_one] using
      curveMean_le_model_on (I := 𝓘(ℝ, E)) (n := (2 : WithTop ℕ∞))
        (by norm_num) k γ V (-κ ^ 2) 1 η zero_lt_one hcard hd hadmScaled hgammaTwo
        (fun t ht => by simpa only [one_pow] using
          (_hphysical t ⟨ht.1, ht.2.le⟩).2.1)
        hVperp hDVperp hVdiff hDVdiff _hLI hW hJac hRicDimension hratioLowerScaled
  have hanti := curveModelRatio_anti (I := 𝓘(ℝ, E))
    (n := (2 : WithTop ℕ∞)) (by norm_num) k γ V (-κ ^ 2) η
      (Module.finrank ℝ E - 1) hadm hgammaTwo hVdiff _hLI hW hmean
  simpa only [modelDensity, hdim, Nat.reduceSub] using hanti

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
