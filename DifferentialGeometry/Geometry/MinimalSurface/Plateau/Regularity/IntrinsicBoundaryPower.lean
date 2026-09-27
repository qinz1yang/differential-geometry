import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.IntrinsicBoundaryEnergy
import DifferentialGeometry.Analysis.Asymptotics.LimsupDecay
import DifferentialGeometry.Analysis.Calculus.Manifold.LinearEquiv
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Rotation

section

noncomputable section

open Set Filter MeasureTheory Metric Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_uniform_boundary_dyadic_limsup_energy_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (u : ι → ℕ → C(closedDisk, M)) (L : ι → ℕ → ℝ≥0)
    (hL : ∀ i n z w, riemannianEDistOf g (u i n z) (u i n w) ≤
      (L i n : ℝ≥0∞) * edist z w)
    {B : ℝ} (hB : 0 ≤ B) (henergy : ∀ i n, riemannianDiskEnergy g (u i n) ≤ B)
    (hmin : ∀ i, Tendsto (fun n => riemannianDiskEnergy g (u i n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ι → ℕ → CircleDeg1Lift) (hψ : ∀ i n, Continuous (ψ i n))
    (htrace : ∀ i n (t : ℝ), u i n (diskBoundary (t : loopCircle)) =
      γ ((ψ i n t : ℝ) : loopCircle))
    (hshort : ∀ i n ρ, 0 < ρ → ρ < 1 →
      ψ i n (1 - Real.arccos (ρ / 2) / Real.pi) -
        ψ i n (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3) :
    ∃ δ θ A : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ 0 ≤ θ ∧ θ < 1 ∧ 0 ≤ A ∧
      ∀ i k, limsup (fun n => ∫ z in boundaryLens (δ / (2 : ℝ) ^ k),
        diskMapEnergyDensity g (diskExtension (u i n)) z) atTop ≤ θ ^ k * A := by
  obtain ⟨ε₀, C, hε₀, hC, hθ1, hrec⟩ :=
    exists_uniform_intrinsic_boundary_energy_contraction g γ hγ
  obtain ⟨δ, hδ, hsmall⟩ := exists_uniform_boundary_cap_radius_of_intrinsic_energy_bound
    g γ hγ hB (half_pos hε₀) (by norm_num : (0 : ℝ) < 1 / 4)
  have hδ0 : 0 < δ := hδ.1
  have hδquarter : δ < 1 / 4 := hδ.2.trans_le (min_le_left _ _)
  let θ := C / (1 + C)
  have hθ : 0 ≤ θ := div_nonneg hC (by linarith)
  let R (k : ℕ) : ℝ := δ / (2 : ℝ) ^ k
  have hRpos (k : ℕ) : 0 < R k := div_pos hδ0 (by positivity)
  have hRle (k : ℕ) : R k ≤ δ := div_le_self hδ0.le
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hRstep (k : ℕ) : 2 * R (k + 1) = R k := by
    dsimp [R]
    rw [pow_succ]
    field_simp
  refine ⟨δ, θ, ε₀, hδ0, hδquarter, hθ, hθ1, hε₀.le, ?_⟩
  intro i k
  let a (j n : ℕ) : ℝ := ∫ z in boundaryLens (R j),
    diskMapEnergyDensity g (diskExtension (u i n)) z
  let d (n : ℕ) : ℝ := riemannianDiskEnergy g (u i n) -
    sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
      weaklyMonotoneDiskCompetitors g γ)
  let err (_ n : ℕ) := d n / (1 + C)
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [d, sub_self] using (hmin i).sub_const
      (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))
  have herr (j : ℕ) : Tendsto (err j) atTop (𝓝 0) := by
    simpa only [err, zero_div] using hd.div_const (1 + C)
  have hnonneg (n : ℕ) (z : ℂ) : 0 ≤ diskMapEnergyDensity g (diskExtension (u i n)) z := by
    unfold diskMapEnergyDensity
    exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  have hai (n : ℕ) : IntegrableOn (diskMapEnergyDensity g (diskExtension (u i n)))
      (closedBall (0 : ℂ) 1) := integrable_diskMapEnergyDensity g (hL i n)
  have ha0 (j n : ℕ) : 0 ≤ a j n := integral_nonneg (hnonneg n)
  have hmono (j n : ℕ) : a j n ≤ a 0 n := by
    apply setIntegral_mono_set ((hai n).mono_set inter_subset_right)
      (Eventually.of_forall (hnonneg n))
    apply Eventually.of_forall
    intro z hz
    refine ⟨?_, hz.2⟩
    exact (closedBall_subset_closedBall (by simpa only [R, pow_zero, div_one] using hRle j)) hz.1
  have hzero : ∀ᶠ n in atTop, a 0 n ≤ ε₀ := by
    filter_upwards [hd.eventually (gt_mem_nhds (half_pos hε₀))] with n hn
    have h := hsmall (u i n) (L i n) (hL i n) (ψ i n) (hψ i n) (htrace i n)
      (hshort i n) (henergy i n)
    change (∫ z in boundaryLens δ, diskMapEnergyDensity g (diskExtension (u i n)) z) ≤
      ε₀ / 2 + d n at h
    have hsum : ε₀ / 2 + d n ≤ ε₀ := by linarith
    simpa only [a, R, pow_zero, div_one] using h.trans hsum
  have hrecur (j : ℕ) : ∀ᶠ n in atTop, a (j + 1) n ≤ θ * a j n + err j n := by
    filter_upwards [hzero] with n hn
    have hsquarter : R (j + 1) < 1 / 4 := (hRle _).trans_lt hδquarter
    have hsm : (∫ z in boundaryLens (2 * R (j + 1)),
        diskMapEnergyDensity g (diskExtension (u i n)) z) ≤ ε₀ := by
      rw [hRstep]
      exact (hmono j n).trans hn
    have h := hrec (u i n) (L i n) (hL i n) (ψ i n) (hψ i n) (htrace i n)
      (R (j + 1)) (hRpos _) hsquarter
      (fun ρ hρ => hshort i n ρ ((hRpos _).trans hρ.1)
        (hρ.2.trans (by linarith))) hsm
    rw [hRstep] at h
    exact h
  have hlim := limsup_le_pow_mul_limsup_of_eventually_le_succ a err hθ
    (fun j => Eventually.of_forall (ha0 j))
    (isBoundedUnder_of_eventually_le hzero) herr hrecur k
  have hbase : limsup (a 0) atTop ≤ ε₀ :=
    limsup_le_of_le (isBoundedUnder_of_eventually_ge
      (Eventually.of_forall (ha0 0))).isCoboundedUnder_le hzero
  exact hlim.trans (mul_le_mul_of_nonneg_left hbase (pow_nonneg hθ k))

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_uniform_intrinsic_boundary_dyadic_limsup_energy_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) =
      γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3) :
    ∃ δ θ A : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ 0 ≤ θ ∧ θ < 1 ∧ 0 ≤ A ∧
      ∀ c ∈ sphere (0 : ℂ) 1, ∀ k : ℕ,
        limsup (fun n => ∫ z in closedBall c (δ / (2 : ℝ) ^ k) ∩ closedBall (0 : ℂ) 1,
          diskMapEnergyDensity g (diskExtension (u n)) z) atTop ≤ θ ^ k * A := by
  choose L hL using fun n => (hu n).2
  obtain ⟨B₀, hB₀⟩ := hmin.bddAbove_range
  let B := max 0 B₀
  have hB : 0 ≤ B := le_max_left _ _
  have henergy (n : ℕ) : riemannianDiskEnergy g (u n) ≤ B :=
    (hB₀ (mem_range_self n)).trans (le_max_right _ _)
  let ζ : ℝ → Circle := fun d => Circle.exp (2 * Real.pi * d)
  let v : ℝ → ℕ → C(closedDisk, M) := fun d n => rotatedDiskMap (u n) (ζ d)
  let Ψ : ℝ → ℕ → CircleDeg1Lift := fun d n =>
    ψ n * (CircleDeg1Lift.translate (Multiplicative.ofAdd d) : CircleDeg1Lift)
  have hΨcont (d : ℝ) (n : ℕ) : Continuous (Ψ d n) :=
    (ψ n).continuous_mul_translate (hψ n) d
  have hvLip (d : ℝ) (n : ℕ) (x y : closedDisk) :
      riemannianEDistOf g (v d n x) (v d n y) ≤ (L n : ℝ≥0∞) * edist x y :=
    riemannian_lipschitz_rotatedDiskMap g (hL n) (ζ d) x y
  have hvtrace (d : ℝ) (n : ℕ) (t : ℝ) :
      v d n (diskBoundary (t : loopCircle)) = γ ((Ψ d n t : ℝ) : loopCircle) :=
    rotatedDiskMap_trace_lift (u n) γ (ψ n) (htrace n) d t
  have hvtotal (d : ℝ) (n : ℕ) :
      riemannianDiskEnergy g (v d n) = riemannianDiskEnergy g (u n) :=
    integral_diskMapEnergyDensity_rotatedDiskMap g (u n) (ζ d)
  have hvenergy (d : ℝ) (n : ℕ) : riemannianDiskEnergy g (v d n) ≤ B := by
    rw [hvtotal]
    exact henergy n
  have hvmin (d : ℝ) : Tendsto (fun n => riemannianDiskEnergy g (v d n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))) := by
    simpa only [hvtotal] using hmin
  have hΨshort (d : ℝ) (n : ℕ) (ρ : ℝ) (hρ1 : ρ < 1) :
      Ψ d n (1 - Real.arccos (ρ / 2) / Real.pi) -
        Ψ d n (Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3 := by
    change ψ n (d + (1 - Real.arccos (ρ / 2) / Real.pi)) -
      ψ n (d + Real.arccos (ρ / 2) / Real.pi) ≤ 2 / 3
    exact (ψ n).sub_shifted_arccos_endpoints_le_two_thirds
      (hthird n) (htwothird n) d hρ1
  obtain ⟨δ, θ, A, hδ, hδquarter, hθ, hθ1, hA, hdec⟩ :=
    exists_uniform_boundary_dyadic_limsup_energy_bound g γ hγ v (fun _ n => L n)
      hvLip hB hvenergy hvmin Ψ hΨcont hvtrace (fun d n ρ _ hρ1 => hΨshort d n ρ hρ1)
  refine ⟨δ, θ, A, hδ, hδquarter, hθ, hθ1, hA, ?_⟩
  intro c hc k
  let ξ : Circle := ⟨-c, by
    apply mem_sphere_zero_iff_norm.mpr
    simpa only [mem_sphere, dist_zero_right, norm_neg] using hc⟩
  obtain ⟨α, hα⟩ := Circle.exp_surjective ξ
  let d := α / (2 * Real.pi)
  have hζ : ζ d = ξ := by
    change Circle.exp (2 * Real.pi * (α / (2 * Real.pi))) = ξ
    rw [mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0), hα]
  have hcenter : rotation (ζ d) (-1) = c := by
    rw [hζ, rotation_apply]
    change (-c) * (-1) = c
    ring
  have heq (n : ℕ) : (∫ z in boundaryLens (δ / (2 : ℝ) ^ k),
      diskMapEnergyDensity g (diskExtension (v d n)) z) =
      ∫ z in closedBall c (δ / (2 : ℝ) ^ k) ∩ closedBall (0 : ℂ) 1,
        diskMapEnergyDensity g (diskExtension (u n)) z := by
    have h := integral_diskMapEnergyDensity_rotatedDiskMap_boundaryLens g (u n) (ζ d)
      (δ / (2 : ℝ) ^ k)
    simpa only [hcenter] using h
  simpa only [heq] using hdec d k

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem exists_uniform_intrinsic_boundary_power_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (u : ℕ → C(closedDisk, M)) (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (ψ : ℕ → CircleDeg1Lift) (hψ : ∀ n, Continuous (ψ n))
    (htrace : ∀ n (t : ℝ), u n (diskBoundary (t : loopCircle)) =
      γ ((ψ n t : ℝ) : loopCircle))
    (hthird : ∀ n, ψ n (1 / 3 : ℝ) = ψ n 0 + 1 / 3)
    (htwothird : ∀ n, ψ n (2 / 3 : ℝ) = ψ n 0 + 2 / 3) :
    ∃ β C δ : ℝ, 0 < β ∧ β ≤ 2 ∧ 0 ≤ C ∧ 0 < δ ∧
      ∀ c ∈ sphere (0 : ℂ) 1, ∀ s : ℝ, 0 < s → s ≤ δ →
        limsup (fun n => ∫ z in ball (0 : ℂ) 1 ∩ closedBall c s,
          diskMapEnergyDensity g (diskExtension (u n)) z) atTop ≤ C * s ^ β := by
  obtain ⟨δ, θ, A, hδ, _, hθ, hθ1, hA, hdec⟩ :=
    exists_uniform_intrinsic_boundary_dyadic_limsup_energy_bound g γ hγ u hu hmin
      ψ hψ htrace hthird htwothird
  obtain ⟨B, hB⟩ := hmin.bddAbove_range
  let e (n : ℕ) := diskMapEnergyDensity g (diskExtension (u n))
  have h0 (n : ℕ) (z : ℂ) : 0 ≤ e n z := by
    unfold e diskMapEnergyDensity
    exact div_nonneg (add_nonneg (metric_inner_self_nonneg g _ _)
      (metric_inner_self_nonneg g _ _)) (by norm_num)
  have hi (n : ℕ) : IntegrableOn (e n) (closedBall (0 : ℂ) 1) :=
    weaklyMonotoneDiskCompetitor_integrable_energy g (hu n)
  have htotal (n : ℕ) : (∫ z in closedBall (0 : ℂ) 1, e n z) ≤ B :=
    hB (mem_range_self n)
  have hmono {S T : Set ℂ} (hST : S ⊆ T) (hTD : T ⊆ closedBall (0 : ℂ) 1) :
      limsup (fun n => ∫ z in S, e n z) atTop ≤ limsup (fun n => ∫ z in T, e n z) atTop := by
    have hle (n : ℕ) : (∫ z in S, e n z) ≤ ∫ z in T, e n z :=
      setIntegral_mono_set ((hi n).mono_set hTD) (Eventually.of_forall (h0 n))
        (Eventually.of_forall hST)
    have hb (n : ℕ) : (∫ z in T, e n z) ≤ B :=
      (setIntegral_mono_set (hi n) (Eventually.of_forall (h0 n))
        (Eventually.of_forall hTD)).trans (htotal n)
    exact limsup_le_limsup (Eventually.of_forall hle)
      (isBoundedUnder_of_eventually_ge
        (Eventually.of_forall fun n => integral_nonneg (h0 n))).isCoboundedUnder_le
      (isBoundedUnder_of_eventually_le (Eventually.of_forall hb))
  let F (c : sphere (0 : ℂ) 1) (s : ℝ) :=
    limsup (fun n => ∫ z in closedBall (c : ℂ) s ∩ closedBall (0 : ℂ) 1, e n z) atTop
  have hFmono (c : sphere (0 : ℂ) 1) : MonotoneOn (F c) (Ioc (0 : ℝ) δ) := by
    intro a _ b _ hab
    exact hmono (inter_subset_inter_left _ (closedBall_subset_closedBall hab)) inter_subset_right
  have hFdec (c : sphere (0 : ℂ) 1) (k : ℕ) : F c (δ / (2 : ℝ) ^ k) ≤ θ ^ k * A :=
    hdec c c.property k
  obtain ⟨α, C, hα, hα1, hC, hpower⟩ := exists_radius_power_bound_of_dyadic_decay F
    hδ hθ hθ1 hA hFmono hFdec
  refine ⟨2 * α, C, δ, by positivity, by linarith, hC, hδ, ?_⟩
  intro c hc s hs hsδ
  have hcap : ball (0 : ℂ) 1 ∩ closedBall c s ⊆ closedBall c s ∩ closedBall (0 : ℂ) 1 :=
    fun z hz => ⟨hz.2, ball_subset_closedBall hz.1⟩
  exact (hmono hcap inter_subset_right).trans (hpower ⟨c, hc⟩ s ⟨hs, hsδ⟩)

end DifferentialGeometry.Geometry

end

end
