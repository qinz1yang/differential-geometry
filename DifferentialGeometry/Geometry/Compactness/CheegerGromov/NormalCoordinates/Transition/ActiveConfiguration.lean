import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.CenterMap.Construction.Fill
import DifferentialGeometry.Geometry.Exponential.NormalBall.Chart

section

noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [HasContDiffBump E]

theorem stageFill_fixed_convergence
    (lam : ℝ) (hlam : 0 < lam) {U : Set E} (hU : IsOpen U)
    {J Jbar : E → E} {R : ℕ → E → E}
    (hJ : ContDiffOn ℝ ∞ J U)
    (hJbar : ContDiffOn ℝ ∞ Jbar (Metric.ball 0 (8 * lam)))
    (hR : MapCInfConvergenceOnCompacts (Metric.ball 0 (8 * lam)) R Jbar)
    (hRC : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (R k) (Metric.ball 0 (8 * lam)))
    (hinv : ∀ z ∈ U, J z ∈ Metric.ball 0 (8 * lam) → Jbar (J z) = z) :
    MapCInfConvergenceOnCompacts U (fun k => stageFill lam hlam J (R k)) id ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (stageFill lam hlam J (R k)) U := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hRC
  let R' : ℕ → E → E := fun k => if N ≤ k then R k else Jbar
  have hR' : MapCInfConvergenceOnCompacts (Metric.ball 0 (8 * lam)) R' Jbar := by
    apply hR.congr_eventually Metric.isOpen_ball
    · filter_upwards [eventually_ge_atTop N] with k hk z hz
      simp only [R', if_pos hk]
    · exact eqOn_refl _ _
  have hR'C : ∀ k, ContDiffOn ℝ ∞ (R' k) (Metric.ball 0 (8 * lam)) := by
    intro k
    by_cases hk : N ≤ k
    · simpa only [R', if_pos hk] using hN k hk
    · simpa only [R', if_neg hk] using hJbar
  have hfill := stageFill_convergence lam hlam hU
    (mapCInfConvergence_const J) hR' (fun _ => hJ) hJ hR'C hJbar hinv
    id id tendsto_id tendsto_id
  constructor
  · apply hfill.congr_eventually hU
    · filter_upwards [eventually_ge_atTop N] with k hk z hz
      simp only [R', if_pos hk, id_eq]
    · exact eqOn_refl _ _
  · filter_upwards [hRC] with k hk
    exact safeFill_smooth (activityBump lam hlam).contDiff
      (safetyBump lam hlam).radial_contDiff hJ hk
      (fun z _ => stageClamp_mapsTo lam hlam (mem_univ (J z)))

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

noncomputable section
open Filter Set
open scoped ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [HasContDiffBump E]
  {ι : Type*} [Fintype ι]

theorem exists_smooth_active_coordinate_fill
    (lam : ℝ) (hlam : 0 < lam) {U : Set E} (hU : IsOpen U)
    (mu : E → ι → ℝ) (J Jbar : ι → E → E) (R : ι → ℕ → E → E)
    (hJ : ∀ i, ContDiffOn ℝ ∞ (J i) U)
    (hJbar : ∀ i, ContDiffOn ℝ ∞ (Jbar i) (Metric.ball 0 (8 * lam)))
    (hR : ∀ i, MapCInfConvergenceOnCompacts (Metric.ball 0 (8 * lam)) (R i) (Jbar i))
    (hRC : ∀ i, ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (R i k) (Metric.ball 0 (8 * lam)))
    (hinv : ∀ i z, z ∈ U → J i z ∈ Metric.ball 0 (8 * lam) → Jbar i (J i z) = z)
    (hactive : ∀ z ∈ U, ∀ i, mu z i ≠ 0 → J i z ∈ Metric.closedBall 0 (6 * lam)) :
    ∃ xi : ℕ → E → ι → E,
      (∀ k, ContDiffOn ℝ ∞ (xi k) U) ∧
      MapCInfConvergenceOnCompacts U xi (fun z _ => z) ∧
      ∀ᶠ k in atTop, ∀ z ∈ U, ∀ i, mu z i ≠ 0 → xi k z i = R i k (J i z) := by
  have hfill : ∀ i, MapCInfConvergenceOnCompacts U
      (fun k => stageFill lam hlam (J i) (R i k)) id ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (stageFill lam hlam (J i) (R i k)) U :=
    fun i => stageFill_fixed_convergence lam hlam hU (hJ i) (hJbar i) (hR i) (hRC i) (hinv i)
  have htail : ∀ᶠ k in atTop, ∀ i,
      ContDiffOn ℝ ∞ (stageFill lam hlam (J i) (R i k)) U :=
    Filter.eventually_all.mpr (fun i => (hfill i).2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  let xi : ℕ → E → ι → E := fun k z i =>
    if N ≤ k then stageFill lam hlam (J i) (R i k) z else z
  have hxic : ∀ i k, ContDiffOn ℝ ∞ (fun z => xi k z i) U := by
    intro i k
    by_cases hk : N ≤ k
    · simpa only [xi, if_pos hk] using hN k hk i
    · simp only [xi, if_neg hk]
      exact contDiffOn_id
  have hxiconv : ∀ i, MapCInfConvergenceOnCompacts U (fun k z => xi k z i) id := by
    intro i
    apply (hfill i).1.congr_eventually hU
    · filter_upwards [eventually_ge_atTop N] with k hk z hz
      simp only [xi, if_pos hk]
    · exact eqOn_refl _ _
  refine ⟨xi, (fun k => contDiffOn_pi.mpr (fun i => hxic i k)),
    mapCInfConvergence_pi hU hxiconv hxic (fun _ => contDiffOn_id), ?_⟩
  filter_upwards [eventually_ge_atTop N] with k hk z hz i hi
  simp only [xi, if_pos hk]
  exact stageFill_eq_of_image_mem_closedBall lam hlam (J i) (R i k) (hactive z hz i hi)

theorem exists_smooth_active_configuration
    (lam : ℝ) (hlam : 0 < lam) {U : Set E} (hU : IsOpen U)
    (mu : E → ι → ℝ) (hmu : ContDiffOn ℝ ∞ mu U)
    (J Jbar : ι → E → E) (R : ι → ℕ → E → E)
    (hJ : ∀ i, ContDiffOn ℝ ∞ (J i) U)
    (hJbar : ∀ i, ContDiffOn ℝ ∞ (Jbar i) (Metric.ball 0 (8 * lam)))
    (hR : ∀ i, MapCInfConvergenceOnCompacts (Metric.ball 0 (8 * lam)) (R i) (Jbar i))
    (hRC : ∀ i, ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (R i k) (Metric.ball 0 (8 * lam)))
    (hinv : ∀ i z, z ∈ U → J i z ∈ Metric.ball 0 (8 * lam) → Jbar i (J i z) = z)
    (hactive : ∀ z ∈ U, ∀ i, mu z i ≠ 0 → J i z ∈ Metric.closedBall 0 (6 * lam)) :
    ∃ xi : ℕ → E → ι → E,
      (∀ k, ContDiffOn ℝ ∞ (fun z => (mu z, xi k z)) U) ∧
      MapCInfConvergenceOnCompacts U (fun k z => (mu z, xi k z))
        (fun z => (mu z, fun _ => z)) ∧
      ∀ᶠ k in atTop, ∀ z ∈ U, ∀ i, mu z i ≠ 0 → xi k z i = R i k (J i z) := by
  obtain ⟨xi, hxiC, hxi, hactive⟩ := exists_smooth_active_coordinate_fill
    lam hlam hU mu J Jbar R hJ hJbar hR hRC hinv hactive
  refine ⟨xi, (fun k => hmu.prodMk (hxiC k)), ?_, hactive⟩
  exact mapCInfConvergence_prodMk hU (mapCInfConvergence_const mu) hxi
    (fun _ => hmu) hmu hxiC (contDiffOn_pi.mpr fun _ => contDiffOn_id)

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

noncomputable section
open Set Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open DifferentialGeometry.CheegerGromovCompactness

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  {ι : Type*} [Fintype ι] (p : ∀ k, M k) (q : ι → ∀ k, M k)
  (c : ∀ k, NormalBallChart (I := I) (p k))
  (d : ∀ i k, NormalBallChart (I := I) (q i k))

theorem exists_smooth_active_configuration
    (lam : ℝ) (hlam : 0 < lam) {U : Set E} (hU : IsOpen U)
    (mu : E → ι → ℝ) (hmu : ContDiffOn ℝ ∞ mu U)
    (J Jbar : ι → E → E)
    (hJ : ∀ i, ContDiffOn ℝ ∞ (J i) U)
    (hJbar : ∀ i, ContDiffOn ℝ ∞ (Jbar i) (Metric.ball 0 (8 * lam)))
    (hR : ∀ i, MapCInfConvergenceOnCompacts (Metric.ball 0 (8 * lam))
      (fun k => (d i k).transition (c k)) (Jbar i))
    (hRC : ∀ i, ∀ᶠ k in atTop, ContDiffOn ℝ ∞
      ((d i k).transition (c k)) (Metric.ball 0 (8 * lam)))
    (hinv : ∀ i z, z ∈ U → J i z ∈ Metric.ball 0 (8 * lam) → Jbar i (J i z) = z)
    (hactive : ∀ z ∈ U, ∀ i, mu z i ≠ 0 → J i z ∈ Metric.closedBall 0 (6 * lam)) :
    ∃ xi : ℕ → E → ι → E,
      (∀ k, ContDiffOn ℝ ∞ (fun z => (mu z, xi k z)) U) ∧
      MapCInfConvergenceOnCompacts U (fun k z => (mu z, xi k z))
        (fun z => (mu z, fun _ => z)) ∧
      ∀ᶠ k in atTop, ∀ z ∈ U, ∀ i, mu z i ≠ 0 →
        xi k z i = (c k).hom.symm ((d i k).hom (J i z)) := by
  exact CheegerGromovCompactness.exists_smooth_active_configuration lam hlam hU mu hmu
    J Jbar (fun i k => (d i k).transition (c k)) hJ hJbar hR hRC hinv hactive

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end

end

section

noncomputable section
open Filter Set
open scoped ContDiff Topology Manifold

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

theorem exists_smooth_active_configuration_sub_const
    (a : E) (lam : ℝ) (hlam : 0 < lam) {U : Set E} (hU : IsOpen U)
    (mu : E → ι → ℝ) (hmu : ContDiffOn ℝ ∞ mu U)
    (J Jbar : ι → E → E) (R : ι → ℕ → E → E)
    (hJ : ∀ i, ContDiffOn ℝ ∞ (J i) U)
    (hJbar : ∀ i, ContDiffOn ℝ ∞ (Jbar i) (Metric.ball 0 (8 * lam)))
    (hR : ∀ i, MapCInfConvergenceOnCompacts (Metric.ball 0 (8 * lam)) (R i) (Jbar i))
    (hRC : ∀ i, ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (R i k) (Metric.ball 0 (8 * lam)))
    (hinv : ∀ i z, z ∈ U → J i z ∈ Metric.ball 0 (8 * lam) → Jbar i (J i z) = z)
    (hactive : ∀ z ∈ U, ∀ i, mu z i ≠ 0 → J i z ∈ Metric.closedBall 0 (6 * lam)) :
    ∃ xi : ℕ → E → ι → E,
      (∀ k, ContDiffOn ℝ ∞ (fun z => (mu z, xi k z)) U) ∧
      MapCInfConvergenceOnCompacts U (fun k z => (mu z, xi k z))
        (fun z => (mu z, fun _ => z - a)) ∧
      ∀ᶠ k in atTop, ∀ z ∈ U, ∀ i, mu z i ≠ 0 →
        xi k z i = -a + R i k (J i z) := by
  obtain ⟨xi, hxiC, hxi, hxiActive⟩ := exists_smooth_active_configuration
    lam hlam hU mu hmu J Jbar R hJ hJbar hR hRC hinv hactive
  let A : (ι → ℝ) × (ι → E) → (ι → ℝ) × (ι → E) :=
    fun q => (q.1, (fun _ => -a) + q.2)
  have hA : ContDiff ℝ ∞ A := contDiff_fst.prodMk (contDiff_const.add contDiff_snd)
  have hInf : ContDiffOn ℝ ∞ (fun z : E => (mu z, fun _ : ι => z)) U :=
    hmu.prodMk (contDiffOn_pi.mpr fun _ => contDiffOn_id)
  refine ⟨fun k z i => -a + xi k z i, ?_, ?_, ?_⟩
  · intro k
    exact hA.comp_contDiffOn (hxiC k)
  · have hconv := hxi.comp_of_finiteDimensional hU isOpen_univ
      (mapCInfConvergence_const A) hxiC hInf
      (fun _ => hA.contDiffOn) hA.contDiffOn
      (fun _ _ => mem_univ _) (fun _ _ _ => mem_univ _)
    convert hconv using 1
    · funext k z
      apply Prod.ext
      · rfl
      · funext i
        simp only [A, Pi.add_apply, add_comm]
    · funext z
      apply Prod.ext
      · rfl
      · funext i
        simp only [A, Pi.add_apply, sub_eq_add_neg, add_comm]
  · filter_upwards [hxiActive] with k hk z hz i hi
    exact congrArg (fun y => -a + y) (hk z hz i hi)

end DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

open DifferentialGeometry.CheegerGromovCompactness

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  {ι : Type*} [Fintype ι] (p : ∀ k, M k) (q : ι → ∀ k, M k)
  (c : ∀ k, NormalBallChart (I := I) (p k))
  (d : ∀ i k, NormalBallChart (I := I) (q i k))

theorem exists_smooth_active_configuration_sub_const
    (a : E) (lam : ℝ) (hlam : 0 < lam) {U : Set E} (hU : IsOpen U)
    (mu : E → ι → ℝ) (hmu : ContDiffOn ℝ ∞ mu U)
    (J Jbar : ι → E → E)
    (hJ : ∀ i, ContDiffOn ℝ ∞ (J i) U)
    (hJbar : ∀ i, ContDiffOn ℝ ∞ (Jbar i) (Metric.ball 0 (8 * lam)))
    (hR : ∀ i, MapCInfConvergenceOnCompacts (Metric.ball 0 (8 * lam))
      (fun k => (d i k).transition (c k)) (Jbar i))
    (hRC : ∀ i, ∀ᶠ k in atTop, ContDiffOn ℝ ∞
      ((d i k).transition (c k)) (Metric.ball 0 (8 * lam)))
    (hinv : ∀ i z, z ∈ U → J i z ∈ Metric.ball 0 (8 * lam) → Jbar i (J i z) = z)
    (hactive : ∀ z ∈ U, ∀ i, mu z i ≠ 0 → J i z ∈ Metric.closedBall 0 (6 * lam)) :
    ∃ xi : ℕ → E → ι → E,
      (∀ k, ContDiffOn ℝ ∞ (fun z => (mu z, xi k z)) U) ∧
      MapCInfConvergenceOnCompacts U (fun k z => (mu z, xi k z))
        (fun z => (mu z, fun _ => z - a)) ∧
      ∀ᶠ k in atTop, ∀ z ∈ U, ∀ i, mu z i ≠ 0 →
        xi k z i = -a + (c k).inv ((d i k).hom (J i z)) := by
  exact CheegerGromovCompactness.exists_smooth_active_configuration_sub_const
    a lam hlam hU mu hmu J Jbar (fun i k => (d i k).transition (c k))
    hJ hJbar hR hRC hinv hactive

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end

end

section

noncomputable section
open Filter Set
open scoped ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
theorem exists_translated_active_configuration_of_near
    (a : E) (j : ι) (rho : ℝ) (hrho : 0 < rho) (near : ι → ι → Bool)
    (Jraw JbarRaw : ∀ i, near j i = true → E → E) (Rraw : ∀ i, near j i = true → ℕ → E → E)
    (mu : E → ι → ℝ) (hmu : ContDiffOn ℝ ∞ mu (Metric.ball 0 (rho / 8)))
    (hJraw : ∀ i h, ContDiffOn ℝ ∞ (Jraw i h) (Metric.ball 0 (rho / 2)))
    (hJbarRaw : ∀ i h, ContDiffOn ℝ ∞ (JbarRaw i h) (Metric.ball 0 (rho / 2)))
    (hRraw : ∀ i h, MapCInfConvergenceOnCompacts (Metric.ball 0 (rho / 2)) (Rraw i h) (JbarRaw i h))
    (hRrawC : ∀ i h, ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (Rraw i h k) (Metric.ball 0 (rho / 2)))
    (hinverse : ∀ i h z, z ∈ Metric.ball 0 (rho / 8) → JbarRaw i h (Jraw i h z) = z)
    (hactive : ∀ z ∈ Metric.ball 0 (rho / 8), ∀ i, mu z i ≠ 0 → ∃ h : near j i = true, Jraw i h z ∈ Metric.ball 0 (rho / 8)) :
    ∃ xi : ℕ → E → ι → E,
      (∀ k, ContDiffOn ℝ ∞ (fun z => (mu z, xi k z)) (Metric.ball 0 (rho / 8))) ∧
      MapCInfConvergenceOnCompacts (Metric.ball 0 (rho / 8)) (fun k z => (mu z, xi k z)) (fun z => (mu z, fun _ => z - a)) ∧
      ∀ᶠ k in atTop, ∀ z ∈ Metric.ball 0 (rho / 8), ∀ i (h : near j i = true), mu z i ≠ 0 → xi k z i = -a + Rraw i h k (Jraw i h z) := by
  let lam : ℝ := rho / 16
  have hlam : 0 < lam := div_pos hrho (by norm_num)
  have hlam8 : 8 * lam = rho / 2 := by dsimp only [lam]; ring
  have hlam6 : 6 * lam = 3 * rho / 8 := by dsimp only [lam]; ring
  have hball : Metric.ball (0 : E) (rho / 8) ⊆ Metric.ball 0 (rho / 2) := Metric.ball_subset_ball (by linarith)
  let U : Set E := Metric.ball 0 (rho / 8)
  let J : ι → E → E := fun i => if h : near j i = true then Jraw i h else id
  let Jbar : ι → E → E := fun i => if h : near j i = true then JbarRaw i h else id
  let R : ι → ℕ → E → E := fun i k => if h : near j i = true then Rraw i h k else id
  have hJ : ∀ i, ContDiffOn ℝ ∞ (J i) U := by
    intro i; by_cases hi : near j i = true
    · simpa only [J, dif_pos hi] using (hJraw i hi).mono hball
    · simpa only [J, dif_neg hi] using (contDiffOn_id : ContDiffOn ℝ ∞ (id : E → E) U)
  have hJbar : ∀ i, ContDiffOn ℝ ∞ (Jbar i) (Metric.ball 0 (8 * lam)) := by
    intro i; by_cases hi : near j i = true
    · simpa only [Jbar, dif_pos hi, hlam8] using hJbarRaw i hi
    · simpa only [Jbar, dif_neg hi] using (contDiffOn_id : ContDiffOn ℝ ∞ (id : E → E) (Metric.ball 0 (8 * lam)))
  have hR : ∀ i, MapCInfConvergenceOnCompacts (Metric.ball 0 (8 * lam)) (R i) (Jbar i) := by
    intro i; by_cases hi : near j i = true
    · simpa only [R, Jbar, dif_pos hi, hlam8] using hRraw i hi
    · simpa only [R, Jbar, dif_neg hi] using (mapCInfConvergence_const (U := Metric.ball 0 (8 * lam)) (id : E → E))
  have hRC : ∀ i, ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (R i k) (Metric.ball 0 (8 * lam)) := by
    intro i; by_cases hi : near j i = true
    · simpa only [R, dif_pos hi, hlam8] using hRrawC i hi
    · exact Filter.Eventually.of_forall fun k => by simpa only [R, dif_neg hi] using (contDiffOn_id : ContDiffOn ℝ ∞ (id : E → E) (Metric.ball 0 (8 * lam)))
  have hinv : ∀ i z, z ∈ U → J i z ∈ Metric.ball 0 (8 * lam) → Jbar i (J i z) = z := by
    intro i z hz _; by_cases hi : near j i = true
    · simpa only [J, Jbar, dif_pos hi] using hinverse i hi z hz
    · simp only [J, Jbar, dif_neg hi, id_eq]
  have hact : ∀ z ∈ U, ∀ i, mu z i ≠ 0 → J i z ∈ Metric.closedBall 0 (6 * lam) := by
    intro z hz i hmi; obtain ⟨hi, hJi⟩ := hactive z hz i hmi
    simp only [J, dif_pos hi, hlam6]
    exact Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hJi
  obtain ⟨xi, hxiC, hxiconv, hxiActive⟩ := exists_smooth_active_configuration_sub_const a lam hlam (show IsOpen U from Metric.isOpen_ball) mu hmu J Jbar R hJ hJbar hR hRC hinv hact
  refine ⟨xi, hxiC, hxiconv, ?_⟩
  filter_upwards [hxiActive] with k hk z hz i hi hmi
  simpa only [R, J, dif_pos hi] using hk z hz i hmi
end DifferentialGeometry.CheegerGromovCompactness

end

end
