import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.GradientHolder
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Classical
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.WeakHarmonicMap
import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakLaplacian.HolderRegularity
import DifferentialGeometry.Analysis.Schauder.Holder.QuadraticSource
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Divergence.Local
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative
import DifferentialGeometry.Analysis.Elliptic.Euclidean.SemilinearRegularity
import DifferentialGeometry.Geometry.HarmonicMap.ChartSource
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Laplacian
import DifferentialGeometry.Geometry.HarmonicMap.ChartTension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskLocality

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_contDiffOn_one_chart_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (Metric.ball 0 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    {x₀ : V} (hx₀ : x₀ ∈ Metric.ball (0 : V) 1)
    : let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let z₀ := χ (v x₀)
    let z : V → H := fun x => χ (v x) - z₀
    ∃ ρ η : ℝ, 0 < ρ ∧ 0 < η ∧
      Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      ∃ hz : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => z x k) (Metric.ball x₀ ρ),
        (∀ x ∈ Metric.ball x₀ ρ, ∀ j,
          WithLp.toLp 2 (fun k => (hz k).weakGrad x j) =
            fderiv ℝ χ (v x) (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) ∧
        Metric.ball x₀ η ⊆ Metric.ball x₀ ρ ∧
        ContDiffOn ℝ 1 z (Metric.ball x₀ η) ∧
        ∃ (G : Fin (Module.finrank ℝ E) → V → V) (C : Fin (Module.finrank ℝ E) → ℝ),
          (∀ k, 0 ≤ C k) ∧
          (∀ k, G k =ᵐ[volume.restrict (Metric.ball x₀ η)] (hz k).weakGrad) ∧
          (∀ k, ∀ x ∈ Metric.ball x₀ η,
            HasFDerivAt (fun y => z y k) (innerSL ℝ (G k x)) x) ∧
          ∀ k, ∀ x ∈ Metric.ball x₀ η, ∀ y ∈ Metric.ball x₀ η,
            ‖G k x - G k y‖ ≤ C k * ‖x - y‖ ^ ((1 : ℝ) / 8) := by
  let z : V → H := fun x =>
    toEuclidean (extChartAt 𝓘(ℝ, E) (r (v x₀)) (r (v x))) -
      toEuclidean (extChartAt 𝓘(ℝ, E) (r (v x₀)) (r (v x₀)))
  obtain ⟨ρ, σ, hρ, hσ, hρB, hz, hzgrad, hσρ, G, C, hC, hG, hGc, hHolder⟩ :=
    exists_chart_holder_weak_gradient_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀
  obtain ⟨ρc, ηc, Kc, hρc, _, _, _, _, hzc, hzcW, _, _⟩ :=
    exists_chart_weak_gradient_power_bound_of_exponent_lt_two
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
  let η := min (σ / 2) ρc
  have hη : 0 < η := lt_min (half_pos hσ) hρc
  have hησ : Metric.ball x₀ η ⊆ Metric.ball x₀ (σ / 2) :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hηρ : Metric.ball x₀ η ⊆ Metric.ball x₀ ρ := hησ.trans
    ((Metric.ball_subset_ball (by linarith)).trans hσρ)
  have hηρc : Metric.ball x₀ η ⊆ Metric.closedBall x₀ ρc :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (min_le_right _ _))
  let hza (k : Fin (Module.finrank ℝ E)) :=
    DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hηρ (hz k)
  have hGη (k : Fin (Module.finrank ℝ E)) :
      G k =ᵐ[volume.restrict (Metric.ball x₀ η)] (hza k).weakGrad :=
    ae_restrict_of_ae_restrict_of_subset
      (hησ.trans (Metric.ball_subset_ball (by linarith))) (hG k)
  have hzkc (k : Fin (Module.finrank ℝ E)) :=
    (PiLp.continuous_apply 2 _ k).comp_continuousOn (hzc.mono hηρc)
  have hzk (k : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ 1 (fun x => z x k) (Metric.ball x₀ η) :=
    (hza k).contDiffOn_one_of_continuousOn_weakGrad Metric.isOpen_ball (hzkc k)
      ((hGc k).mono hησ) (hGη k)
  refine ⟨ρ, η, hρ, hη, hρB, hz, hzgrad, hηρ, ?_, G, C, hC, hGη, ?_, ?_⟩
  · exact PiLp.contDiff_toLp.comp_contDiffOn (contDiffOn_pi.mpr hzk)
  · exact fun k x hx => (hza k).hasFDerivAt_of_continuousOn_weakGrad
      Metric.isOpen_ball (hzkc k) ((hGc k).mono hησ) (hGη k) hx
  · exact fun k x hx y hy => hHolder k x (hησ hx) y (hησ hy)

end DifferentialGeometry.Geometry

end

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_contDiffOn_two_chart_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (Metric.ball 0 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    {x₀ : V} (hx₀ : x₀ ∈ Metric.ball (0 : V) 1)
    : let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let z : V → H := χ ∘ v
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      ContDiffOn ℝ 2 z (Metric.ball x₀ ρ) ∧
      ∃ C : Fin (Module.finrank ℝ E) → ℝ≥0, ∀ k,
        HolderOnWith (C k) (1 / 8) (iteratedFDeriv ℝ 2 (fun x => z x k))
          (Metric.ball x₀ ρ) := by
  let p := r (v x₀)
  let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
  let z : V → H := χ ∘ v
  let z₀ : H := χ (v x₀)
  let vm (i : Fin n) : DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1) :=
    (hw i).congr (hvw.symm.mono fun x hx => congrArg (fun a : F => a i) hx)
  obtain ⟨ρp, hρp, hρpB, hzmap, _, _, hz, _, _, hPDE⟩ :=
    exists_weak_chart_harmonic_map_equation_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v vm hvc hvw hvK
      (fun _ => rfl) hx₀
  obtain ⟨_, ηc, _, hηc, _, _, _, _, hzC1, G, C, hC, _, hD, hHolder⟩ :=
    exists_contDiffOn_one_chart_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀
  have hz1 : ContDiffOn ℝ 1 z (Metric.ball x₀ ηc) := by
    have heq : z = fun x => (χ (v x) - z₀) + z₀ := by funext x; dsimp only [z]; abel
    rw [heq]
    exact hzC1.add contDiffOn_const
  have hDz (k : Fin (Module.finrank ℝ E)) (x : V) (hx : x ∈ Metric.ball x₀ ηc) :
      HasFDerivAt (fun y => z y k) (innerSL ℝ (G k x)) x := by
    have hh := (hD k x hx).add_const (z₀ k)
    have heq : (fun y => (χ (v y) - z₀) k + z₀ k) = fun y => z y k := by
      funext y
      simp only [PiLp.sub_apply, sub_add_cancel, z, Function.comp_def]
    rwa [heq] at hh
  let ρ := min (ηc / 2) (ρp / 2)
  have hρ : 0 < ρ := lt_min (half_pos hηc) (half_pos hρp)
  have hρc : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ ηc :=
    Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hηc))
  have hρp' : Metric.closedBall x₀ ρ ⊆ Metric.ball x₀ ρp :=
    Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρp))
  have hballp : Metric.ball x₀ ρ ⊆ Metric.ball x₀ ρp := Metric.ball_subset_closedBall.trans hρp'
  have hballc : Metric.ball x₀ ρ ⊆ Metric.ball x₀ ηc := Metric.ball_subset_closedBall.trans hρc
  let hza (k : Fin (Module.finrank ℝ E)) :=
    DeGiorgi.MemW1pWitness.restrict Metric.isOpen_ball hballp (hz k)
  have hZk (k : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ 1 (fun x => z x k) (Metric.ball x₀ ηc) :=
    (contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn hz1
  have hGeq (k : Fin (Module.finrank ℝ E)) :
      G k =ᵐ[volume.restrict (Metric.ball x₀ ρ)] (hza k).weakGrad := by
    have hcomp (j : Fin 2) : (fun x => (hza k).weakGrad x j) =ᵐ[
        volume.restrict (Metric.ball x₀ ρ)] (fun x => G k x j) := by
      have hweakC := hasWeakPartialDeriv_of_contDiffOn Metric.isOpen_ball ((hZk k).mono hballc) j
      have hGc : ContinuousOn (fun x => G k x j) (Metric.closedBall x₀ ρ) := by
        have hh : ContinuousOn (fun x => fderiv ℝ (fun y => z y k) x
            (EuclideanSpace.single j 1)) (Metric.ball x₀ ηc) :=
          ((hZk k).continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl).clm_apply
            continuousOn_const
        apply (hh.mono hρc).congr
        intro x hx
        change G k x j = fderiv ℝ (fun y => z y k) x (EuclideanSpace.single j 1)
        rw [(hDz k x (hρc hx)).fderiv]
        simp only [innerSL_apply_apply, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
      have hi : IntegrableOn (fun x => G k x j) (Metric.ball x₀ ρ) :=
        (hGc.integrableOn_compact (isCompact_closedBall _ _)).mono_set Metric.ball_subset_closedBall
      have hder : (fun x => fderiv ℝ (fun y => z y k) x (EuclideanSpace.single j 1)) =ᵐ[
          volume.restrict (Metric.ball x₀ ρ)] (fun x => G k x j) := by
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
        rw [(hDz k x (hballc hx)).fderiv]
        simp only [innerSL_apply_apply, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
      exact DeGiorgi.HasWeakPartialDeriv.ae_eq Metric.isOpen_ball ((hza k).isWeakGrad j)
        (hweakC.congr_ae EventuallyEq.rfl hder)
        ((hza k).weakGrad_component_memLp j |>.locallyIntegrable (by norm_num)) hi.locallyIntegrable
    filter_upwards [ae_all_iff.mpr hcomp] with x hx
    ext j
    exact (hx j).symm
  let α : ℝ≥0 := 1 / 8
  have hα : 0 < α := by norm_num [α]
  have hα1 : α < 1 := by norm_num [α]
  obtain ⟨Kz, hzH⟩ := exists_holderWith_restrict_of_contDiffOn_isCompact
    (isCompact_closedBall x₀ ρ) (convex_closedBall _ _) (hz1.mono hρc) hα1.le
  have hzH' : HolderOnWith Kz α z (Metric.closedBall x₀ ρ) := HolderWith.restrict_iff.mp hzH
  let CG (k : Fin (Module.finrank ℝ E)) : ℝ≥0 := ⟨C k, hC k⟩
  have hGH (k : Fin (Module.finrank ℝ E)) (j : Fin 2) :
      HolderOnWith (CG k) α (fun x => G k x j) (Metric.closedBall x₀ ρ) := by
    intro x hx y hy
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg]
    have hcoe : (CG k : ℝ≥0∞) = ENNReal.ofReal (C k) := by
      change (CG k : ℝ≥0∞) = ENNReal.ofReal (CG k : ℝ)
      exact ENNReal.ofReal_coe_nnreal.symm
    rw [hcoe, ← ENNReal.ofReal_mul (hC k)]
    apply ENNReal.ofReal_le_ofReal
    norm_num only [α, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    have hn := PiLp.norm_apply_le (G k x - G k y) j
    simpa only [Real.dist_eq, dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs, α] using
      hn.trans (hHolder k x (hρc hx) y (hρc hy))
  let a (k i j : Fin (Module.finrank ℝ E)) (y : H) :=
    chartChristoffel g p i j k ((toEuclidean (E := E)).symm y)
  let T := chartTargetEuclid (I := 𝓘(ℝ, E)) p
  have hT : IsOpen T := chartTargetEuclid_isOpen p
  have ha (k i j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ 1 (a k i j) T := by
    have hh := chartChristoffel_contDiffOn_interior g p i j k
    have ht : ContDiffOn ℝ ∞ (chartChristoffel g p i j k) (extChartAt 𝓘(ℝ, E) p).target := by
      simpa only [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).interior_eq] using hh
    exact (ht.of_le (by norm_cast)).comp (toEuclidean (E := E)).symm.contDiff.contDiffOn
      (fun y hy => toEuclidean_symm_mem_target hy)
  have hzT : MapsTo z (Metric.closedBall x₀ ρ) T :=
    hzmap.mono (hρp'.trans Metric.ball_subset_closedBall) Subset.rfl
  let Fk (k : Fin (Module.finrank ℝ E)) (x : V) :=
    -(∑ j : Fin 2, ∑ i, ∑ l, a k i l (z x) * G i x j * G l x j)
  have hFH (k : Fin (Module.finrank ℝ E)) :
      ∃ K : ℝ≥0, HolderOnWith K α (Fk k) (Metric.closedBall x₀ ρ) := by
    obtain ⟨K, hK⟩ := exists_holderOnWith_quadratic_sum_of_contDiffOn_coefficients
      (isCompact_closedBall x₀ ρ) hT hα hzH' hzT (ha k) hGH
    refine ⟨K, ?_⟩
    intro x hx y hy
    simpa only [Fk, edist_neg_neg] using hK x hx y hy
  choose KF hKF using hFH
  let : IsFiniteMeasure (volume.restrict (Metric.ball x₀ ρ)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hFLp (k : Fin (Module.finrank ℝ E)) :
      MemLp (Fk k) 2 (volume.restrict (Metric.ball x₀ ρ)) := by
    have hc := (hKF k).continuousOn hα
    obtain ⟨B, hB⟩ := (isCompact_closedBall x₀ ρ).exists_bound_of_continuousOn hc
    apply MemLp.of_bound ((hc.mono Metric.ball_subset_closedBall).aestronglyMeasurable
      Metric.isOpen_ball.measurableSet) B
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hB x (Metric.ball_subset_closedBall hx)
  have hdivp (k : Fin (Module.finrank ℝ E)) :
      DeGiorgi.HasWeakDiv (fun x => -(∑ j : Fin 2, ∑ i, ∑ l,
        a k i l (z x) * (hz i).weakGrad x j * (hz l).weakGrad x j))
        (hz k).weakGrad (Metric.ball x₀ ρp) := by
    intro φ hφ hφc hφs
    have hh := hPDE k φ hφ hφs
    simp only [neg_mul, integral_neg, neg_neg]
    simpa only [DeGiorgi.weakGradientColumn, PiLp.toLp_apply,
      mul_comm, a, z, χ, p, Function.comp_def] using hh
  have hdivF (k : Fin (Module.finrank ℝ E)) : DeGiorgi.HasWeakDiv (Fk k)
      (hza k).weakGrad (Metric.ball x₀ ρ) := by
    apply (hdivp k |>.restrict hballp).congr_ae _ EventuallyEq.rfl
    filter_upwards [ae_all_iff.mpr hGeq] with x hx
    simp only [Fk, hx]
    rfl
  have huHs (k : Fin (Module.finrank ℝ E)) : ∃ K : ℝ≥0,
      HolderOnWith K α (fun x => z x k) (Metric.closedBall x₀ ρ) := by
    obtain ⟨K, hK⟩ := exists_holderWith_restrict_of_contDiffOn_isCompact
      (isCompact_closedBall x₀ ρ) (convex_closedBall _ _) ((hZk k).mono hρc) hα1.le
    exact ⟨K, HolderWith.restrict_iff.mp hK⟩
  choose Ku hKu using huHs
  have hsub : Metric.closedBall x₀ (ρ / 2) ⊆ Metric.ball x₀ ρ :=
    Metric.closedBall_subset_ball (half_lt_self hρ)
  have hsubc : Metric.closedBall x₀ (ρ / 2) ⊆ Metric.closedBall x₀ ρ :=
    hsub.trans Metric.ball_subset_closedBall
  have hresult (k : Fin (Module.finrank ℝ E)) : ∃ K : ℝ≥0,
      ContDiffOn ℝ 2 (fun x => z x k) (Metric.ball x₀ (ρ / 4)) ∧
      HolderOnWith K α (iteratedFDeriv ℝ 2 (fun x => z x k)) (Metric.ball x₀ (ρ / 4)) := by
    have hh := exists_holder_iteratedFDeriv_two_of_holder_weak_laplacian_on_ball
      Metric.isOpen_ball (hza k) (hFLp k) (hdivF k) (hGeq k) (half_pos hρ) hsub
      hα hα1 ((hKu k).mono hsubc) ((hKF k).mono hsubc) (fun j => (hGH k j).mono hsubc)
    simpa only [show ρ / 2 / 2 = ρ / 4 by ring] using hh
  choose K hK2 hKH using hresult
  refine ⟨ρ / 4, by positivity, ?_, contDiffOn_piLp' 2 hK2, K, hKH⟩
  exact (Metric.closedBall_subset_closedBall (by linarith : ρ / 4 ≤ ρ)).trans
    (hρp'.trans (Metric.ball_subset_closedBall.trans hρpB))

end DifferentialGeometry.Geometry

end

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_contDiffOn_chart_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (Metric.ball 0 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    {x₀ : V} (hx₀ : x₀ ∈ Metric.ball (0 : V) 1)
    : let p := r (v x₀)
    let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
    let z : V → H := χ ∘ v
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall x₀ ρ ⊆ Metric.ball (0 : V) 1 ∧
      ContDiffOn ℝ ∞ z (Metric.ball x₀ ρ) := by
  let p := r (v x₀)
  let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
  let z : V → H := χ ∘ v
  let vm (i : Fin n) : DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1) :=
    (hw i).congr (hvw.symm.mono fun x hx => congrArg (fun a : F => a i) hx)
  obtain ⟨ρp, hρp, hρpB, hzmap, _, _, hz, _, _, hPDE⟩ :=
    exists_weak_chart_harmonic_map_equation_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v vm hvc hvw hvK
      (fun _ => rfl) hx₀
  obtain ⟨ρc, hρc, _, hz2, C, hC⟩ := exists_contDiffOn_two_chart_of_minimizing_sequence
    g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀
  let R := min (ρp / 2) (ρc / 2)
  have hR : 0 < R := lt_min (half_pos hρp) (half_pos hρc)
  have hBp : Metric.closedBall x₀ R ⊆ Metric.ball x₀ ρp :=
    Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρp))
  have hBc : Metric.closedBall x₀ R ⊆ Metric.ball x₀ ρc :=
    Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρc))
  have hsubp : Metric.ball x₀ R ⊆ Metric.ball x₀ ρp := Metric.ball_subset_closedBall.trans hBp
  have hsubc : Metric.ball x₀ R ⊆ Metric.ball x₀ ρc := Metric.ball_subset_closedBall.trans hBc
  have hzR : ContDiffOn ℝ 2 z (Metric.ball x₀ R) := hz2.mono hsubc
  obtain ⟨K, hK⟩ := exists_holderOnWith_iteratedFDeriv_of_components Metric.isOpen_ball hzR
    (fun k => ⟨C k, (hC k).mono hsubc⟩)
  let A (q : V × H × (V →L[ℝ] H)) : H := WithLp.toLp 2 (fun k => -(∑ j : Fin 2,
    ∑ a, ∑ b, chartChristoffel g p a b k ((toEuclidean (E := E)).symm q.2.1) *
      (q.2.2 (EuclideanSpace.single j 1)) a * (q.2.2 (EuclideanSpace.single j 1)) b))
  let T : Set (V × H × (V →L[ℝ] H)) := Set.univ ×ˢ (chartTargetEuclid (I := 𝓘(ℝ, E)) p) ×ˢ Set.univ
  have hT : IsOpen T := isOpen_univ.prod ((chartTargetEuclid_isOpen p).prod isOpen_univ)
  have hzT : MapsTo (fun x => (x, z x, fderiv ℝ z x)) (Metric.ball x₀ R) T :=
    fun x hx => ⟨mem_univ _, hzmap (Metric.ball_subset_closedBall (hsubp hx)), mem_univ _⟩
  have hpartial (k : Fin (Module.finrank ℝ E)) :
      (fun x => (hz k).weakGrad x) =ᵐ[volume.restrict (Metric.ball x₀ R)]
        DeGiorgi.smoothGradField (fun x => z x k) := by
    let S := Metric.ball x₀ ρp ∩ Metric.ball x₀ ρc
    have hS : IsOpen S := Metric.isOpen_ball.inter Metric.isOpen_ball
    let hwk := DeGiorgi.MemW1pWitness.restrict hS inter_subset_left (hz k)
    have hzk : ContDiffOn ℝ 1 (fun x => z x k) S :=
      (contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn
        ((hz2.of_le (by norm_num)).mono inter_subset_right)
    exact hwk.weakGrad_ae_eq_smoothGradField_on_ball (by norm_num) hS hzk
      (fun x hx => ⟨hBp hx, hBc hx⟩)
  have hcolumn (k : Fin (Module.finrank ℝ E)) (x : V) (hx : x ∈ Metric.ball x₀ R) (j : Fin 2) :
      DeGiorgi.smoothGradField (fun y => z y k) x j =
        (fderiv ℝ z x (EuclideanSpace.single j 1)) k := by
    let L : H →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin (Module.finrank ℝ E) => ℝ) k
    have hd := L.hasFDerivAt.comp x
      ((hzR.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
    change fderiv ℝ (L ∘ z) x (EuclideanSpace.single j 1) = _
    rw [hd.fderiv]
    rfl
  have hdivp (k : Fin (Module.finrank ℝ E)) :
      DeGiorgi.HasWeakDiv (fun x => -(∑ j : Fin 2, ∑ a, ∑ b,
        chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x)) *
          (hz a).weakGrad x j * (hz b).weakGrad x j))
        (hz k).weakGrad (Metric.ball x₀ ρp) := by
    intro φ hφ hφc hφs
    have hh := hPDE k φ hφ hφs
    simp only [neg_mul, integral_neg, neg_neg]
    simpa only [DeGiorgi.weakGradientColumn, PiLp.toLp_apply, mul_comm,
      z, χ, p, Function.comp_def] using hh
  have hdiv (k : Fin (Module.finrank ℝ E)) :
      DeGiorgi.HasWeakDiv (fun x => A (x, z x, fderiv ℝ z x) k)
        (DeGiorgi.smoothGradField (fun x => z x k)) (Metric.ball x₀ R) := by
    apply ((hdivp k).restrict hsubp).congr_ae _ (hpartial k)
    filter_upwards [ae_all_iff.mpr hpartial, ae_restrict_mem Metric.isOpen_ball.measurableSet]
      with x hx hxB
    change -(∑ j : Fin 2, ∑ a, ∑ b,
      chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x)) *
        (hz a).weakGrad x j * (hz b).weakGrad x j) = A (x, z x, fderiv ℝ z x) k
    simp only [A, hx, hcolumn _ x hxB]
  refine ⟨R, hR, hBp.trans (Metric.ball_subset_closedBall.trans hρpB), ?_⟩
  exact contDiffOn_of_semilinear_weak_laplacian hzR (by norm_num : (0 : ℝ≥0) < 1 / 8)
    (by norm_num : (1 / 8 : ℝ≥0) < 1) hK hT hzT (contDiffOn_chart_harmonic_map_source g p) hdiv

end DifferentialGeometry.Geometry

end

noncomputable section
open Manifold Set Filter MeasureTheory
open DifferentialGeometry.Topology
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Schauder
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry

local notation "V" => EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem contMDiffOn_representative_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (Metric.ball 0 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (r ∘ v) (Metric.ball 0 1) ∧
      ContDiffOn ℝ ∞ v (Metric.ball 0 1) := by
  have hrv : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (r ∘ v) (Metric.ball 0 1) := by
    intro x₀ hx₀
    obtain ⟨ρ, hρ, _, hz⟩ := exists_contDiffOn_chart_of_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀
    have hcont : ContinuousAt (r ∘ v) x₀ :=
      (hr.continuousOn.continuousAt (hU.mem_nhds (hΦU (hvK hx₀)))).comp
        (hvc.continuousAt (Metric.isOpen_ball.mem_nhds hx₀))
    have hchart : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, E) ∞
        (extChartAt 𝓘(ℝ, E) (r (v x₀)) ∘ (r ∘ v)) x₀ := by
      have hc := (toEuclidean (E := E)).symm.contDiff.contDiffAt.comp x₀
        (hz.contDiffAt (Metric.ball_mem_nhds x₀ hρ))
      have heq : ((toEuclidean (E := E)).symm ∘
          ((fun y => toEuclidean (extChartAt 𝓘(ℝ, E) (r (v x₀)) (r y))) ∘ v)) =
          extChartAt 𝓘(ℝ, E) (r (v x₀)) ∘ (r ∘ v) := by
        funext x
        simp only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply]
      rw [heq] at hc
      exact hc.contMDiffAt
    exact (contMDiffAt_iff_target.mpr ⟨hcont, hchart⟩).contMDiffWithinAt
  refine ⟨hrv, ?_⟩
  have hvsm : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, F) ∞ (Φ ∘ (r ∘ v)) (Metric.ball 0 1) :=
    hΦ.comp_contMDiffOn hrv
  have heq (x : V) (hx : x ∈ Metric.ball (0 : V) 1) : v x = Φ (r (v x)) := by
    obtain ⟨p, hp⟩ := hvK hx
    rw [← hp, hleft p]
  exact (hvsm.congr heq).contDiffOn

theorem exists_smooth_weak_representative_of_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (Metric.ball 0 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    : ∃ (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1)),
      ContDiffOn ℝ ∞ v (Metric.ball (0 : V) 1) ∧
      ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (r ∘ v) (Metric.ball (0 : V) 1) ∧
      (v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w) ∧
      MapsTo v (Metric.ball (0 : V) 1) (range Φ) ∧
      (∀ i, (hv i).weakGrad = (hw i).weakGrad) := by
  obtain ⟨v, hv, hvc, hvw, hvK, hgrad, _⟩ :=
    exists_continuous_weak_representative_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak
  have hh := contMDiffOn_representative_of_minimizing_sequence
    g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK
  exact ⟨v, hv, hh.2, hh.1, hvw, hvK, hgrad⟩

end DifferentialGeometry.Geometry

end

noncomputable section
open Set Filter MeasureTheory Manifold InnerProductSpace
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped ContDiff Topology Manifold ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem diskMapTension_representative_eq_zero_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (Metric.ball 0 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    : ∀ ζ ∈ Metric.ball (0 : ℂ) 1,
      diskMapTension g (fun z => r (v (Complex.orthonormalBasisOneI.repr z))) ζ = 0 := by
  let e := Complex.orthonormalBasisOneI.repr
  let W : ℂ → M := fun z => r (v (e z))
  have hrv := (contMDiffOn_representative_of_minimizing_sequence
    g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK).1
  have hW : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ W (Metric.ball 0 1) :=
    hrv.comp e.toContinuousLinearEquiv.contDiff.contMDiff.contMDiffOn (fun z hz => by
      change e z ∈ Metric.ball (0 : V) 1
      simpa only [Metric.mem_ball, dist_zero_right, e.norm_map] using hz)
  intro ζ hζ
  let x₀ := e ζ
  have hx₀ : x₀ ∈ Metric.ball (0 : V) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right, x₀, e.norm_map] using hζ
  let p := r (v x₀)
  let χ : F → H := fun y => toEuclidean (extChartAt 𝓘(ℝ, E) p (r y))
  let Z : V → H := χ ∘ v
  let vm (i : Fin n) : DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1) :=
    (hw i).congr (hvw.symm.mono fun x hx => congrArg (fun a : F => a i) hx)
  obtain ⟨ρp, hρp, _, hzmap, _, _, hz, _, _, hPDE⟩ :=
    exists_weak_chart_harmonic_map_equation_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v vm hvc hvw hvK
      (fun _ => rfl) hx₀
  obtain ⟨ρc, hρc, _, hZsmooth⟩ := exists_contDiffOn_chart_of_minimizing_sequence
    g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK hx₀
  let R := min (ρp / 2) (ρc / 2)
  have hR : 0 < R := lt_min (half_pos hρp) (half_pos hρc)
  have hBp : Metric.closedBall x₀ R ⊆ Metric.ball x₀ ρp :=
    Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρp))
  have hBc : Metric.closedBall x₀ R ⊆ Metric.ball x₀ ρc :=
    Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρc))
  have hsubp := Metric.ball_subset_closedBall.trans hBp
  have hsubc := Metric.ball_subset_closedBall.trans hBc
  have hZ2 : ContDiffOn ℝ 2 Z (Metric.ball x₀ R) :=
    (hZsmooth.of_le (by norm_cast)).mono hsubc
  let Γ (k a b : Fin (Module.finrank ℝ E)) (y : H) :=
    chartChristoffel g p a b k ((toEuclidean (E := E)).symm y)
  let D (k : Fin (Module.finrank ℝ E)) (x : V) := DeGiorgi.smoothGradField (fun y => Z y k) x
  have hDae (k : Fin (Module.finrank ℝ E)) :
      (hz k).weakGrad =ᵐ[volume.restrict (Metric.ball x₀ R)] D k := by
    let S := Metric.ball x₀ ρp ∩ Metric.ball x₀ ρc
    have hS : IsOpen S := Metric.isOpen_ball.inter Metric.isOpen_ball
    let hwk := DeGiorgi.MemW1pWitness.restrict hS inter_subset_left (hz k)
    have hzk : ContDiffOn ℝ 1 (fun x => Z x k) S :=
      (contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn
        ((hZsmooth.of_le (by norm_cast)).mono inter_subset_right)
    exact hwk.weakGrad_ae_eq_smoothGradField_on_ball (by norm_num) hS hzk
      (fun x hx => ⟨hBp hx, hBc hx⟩)
  have hcolumn (k : Fin (Module.finrank ℝ E)) (x : V) (hx : x ∈ Metric.ball x₀ R) (j : Fin 2) :
      D k x j = (fderiv ℝ Z x (EuclideanSpace.single j 1)) k := by
    let L : H →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin (Module.finrank ℝ E) => ℝ) k
    have hh := L.hasFDerivAt.comp x
      ((hZ2.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
    change fderiv ℝ (L ∘ Z) x (EuclideanSpace.single j 1) = _
    rw [hh.fderiv]
    rfl
  let Fk (k : Fin (Module.finrank ℝ E)) (x : V) :=
    -(∑ j : Fin 2, ∑ a, ∑ b, Γ k a b (Z x) * D a x j * D b x j)
  have hFk (k : Fin (Module.finrank ℝ E)) : ContinuousOn (Fk k) (Metric.ball x₀ R) := by
    have hc : ContDiffOn ℝ 1 (fun x => (Z x, fderiv ℝ Z x)) (Metric.ball x₀ R) :=
      (hZ2.of_le (by norm_num)).prodMk
        (hZ2.fderiv_of_isOpen (m := 1) Metric.isOpen_ball (by norm_num))
    have ha := contDiffOn_chart_harmonic_map_source g p
    have hm : MapsTo (fun x => (x, Z x, fderiv ℝ Z x)) (Metric.ball x₀ R)
        (Set.univ ×ˢ (chartTargetEuclid (I := 𝓘(ℝ, E)) p) ×ˢ Set.univ) :=
      fun x hx => ⟨mem_univ _, hzmap (Metric.ball_subset_closedBall (hsubp hx)), mem_univ _⟩
    have hcomp := (ha.of_le (by norm_cast)).comp (contDiffOn_id.prodMk hc) hm
    have hscalar := (contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn hcomp
    apply hscalar.continuousOn.congr
    intro x hx
    dsimp only [Fk, Γ]
    simp only [hcolumn _ x hx, Function.comp_def, id_eq]
  have hdiv0 (k : Fin (Module.finrank ℝ E)) : DeGiorgi.HasWeakDiv
      (fun x => -(∑ j : Fin 2, ∑ a, ∑ b, Γ k a b (Z x) *
        (hz a).weakGrad x j * (hz b).weakGrad x j)) (hz k).weakGrad (Metric.ball x₀ ρp) := by
    intro φ hφ hφc hφs
    have hh := hPDE k φ hφ hφs
    simp only [neg_mul, integral_neg, neg_neg]
    simpa only [DeGiorgi.weakGradientColumn, PiLp.toLp_apply, mul_comm,
      Γ, Z, χ, p, Function.comp_def] using hh
  have hdiv (k : Fin (Module.finrank ℝ E)) :
      DeGiorgi.HasWeakDiv (Fk k) (D k) (Metric.ball x₀ R) := by
    apply ((hdiv0 k).restrict hsubp).congr_ae _ (hDae k)
    filter_upwards [ae_all_iff.mpr hDae] with x hx
    simp only [Fk, hx]
  have hLap (k : Fin (Module.finrank ℝ E)) :
      EqOn (Laplacian.laplacian (fun x => Z x k)) (Fk k) (Metric.ball x₀ R) := by
    have hk : ContDiffOn ℝ 2 (fun x => Z x k) (Metric.ball x₀ R) :=
      (contDiff_piLp_apply (p := 2) (i := k)).comp_contDiffOn hZ2
    exact laplacian_eq_of_contDiffOn_of_hasWeakDiv Metric.isOpen_ball hk (hFk k)
      (fun j => ((hk.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)).clm_apply
        continuousOn_const).locallyIntegrableOn Metric.isOpen_ball.measurableSet)
      (fun j => hasWeakPartialDeriv_of_contDiffOn Metric.isOpen_ball (hk.of_le (by norm_num)) j)
      (hdiv k)
  have hU2 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 W ζ :=
    (hW.contMDiffAt (Metric.isOpen_ball.mem_nhds hζ)).of_le (by norm_cast)
  apply diskMapTension_eq_zero_of_chart_laplacian g hU2 (p := p)
    (show W ζ ∈ (chartAt E p).source from mem_chart_source E p)
  dsimp only
  intro k
  have hcenter : x₀ ∈ Metric.ball x₀ R := Metric.mem_ball_self hR
  have hds (j : Fin 2) : fderiv ℝ (Z ∘ e) ζ (Complex.orthonormalBasisOneI j) =
      fderiv ℝ Z x₀ (EuclideanSpace.single j 1) := by
    rw [show Z ∘ e = Z ∘ e.toContinuousLinearEquiv from rfl,
      e.toContinuousLinearEquiv.comp_right_fderiv]
    change fderiv ℝ Z x₀ (e (Complex.orthonormalBasisOneI j)) = _
    rw [Complex.orthonormalBasisOneI.repr_self]
  change Laplacian.laplacian ((fun x => Z x k) ∘ e) ζ =
    -(∑ j : Fin 2, ∑ a, ∑ b,
      chartChristoffel g p a b k ((toEuclidean (E := E)).symm (Z (e ζ))) *
        (fderiv ℝ (Z ∘ e) ζ (Complex.orthonormalBasisOneI j)) a *
        (fderiv ℝ (Z ∘ e) ζ (Complex.orthonormalBasisOneI j)) b)
  rw [LinearIsometryEquiv.laplacian_comp]
  have hh := hLap k hcenter
  change Laplacian.laplacian (fun x => Z x k) x₀ = _ at hh
  simpa only [Fk, Γ, hcolumn _ x₀ hcenter, hds, Function.comp_apply] using hh

theorem diskMapTension_diskExtension_eq_zero_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (Metric.ball 0 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1))
    (hvc : ContinuousOn v (Metric.ball (0 : V) 1))
    (hvw : v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w)
    (hvK : MapsTo v (Metric.ball (0 : V) 1) (range Φ))
    (q : C(closedDisk, M))
    (hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      diskExtension q z = r (v (Complex.orthonormalBasisOneI.repr z))) :
    ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension q) z = 0 := by
  have hmain := diskMapTension_representative_eq_zero_of_minimizing_sequence
    g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvc hvw hvK
  intro z hz
  have hgerm : diskExtension q =ᶠ[𝓝 z]
      (fun z => r (v (Complex.orthonormalBasisOneI.repr z))) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact hq y hy
  exact (diskMapTension_congr_of_eventuallyEq g hgerm).trans (hmain z hz)

theorem exists_smooth_harmonic_weak_representative_of_disk_energy_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F}
    (hΦ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun v : C(closedDisk, M) => riemannianDiskEnergy g v) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (hs : ∀ n i, DeGiorgi.MemW1pWitness 2
      (fun x => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) i)
      (Metric.ball 0 1))
    (w : V → F) (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (Metric.ball 0 1))
    (hrep : ∀ n i j, (fun x => (hs n i).weakGrad x j) =ᵐ[
      volume.restrict (Metric.ball (0 : V) 1)]
      (fun x => fderiv ℝ
        (fun y => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm y)) i)
        x (EuclideanSpace.single j 1)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x =>
      Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)) - w x)
      2 (volume.restrict (Metric.ball 0 1))) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : V) 1),
      Tendsto (fun n => Φ (diskExtension (u n) (Complex.orthonormalBasisOneI.repr.symm x)))
        atTop (𝓝 (w x)))
    (hweak : ∀ i (z : Lp V 2 (volume.restrict (Metric.ball 0 1))),
      Tendsto (fun n => inner ℝ (DeGiorgi.gradLpOfWitness (hs n i)) z) atTop
        (𝓝 (inner ℝ (DeGiorgi.gradLpOfWitness (hw i)) z)))
    : ∃ (v : V → F) (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (Metric.ball 0 1)),
      ContDiffOn ℝ ∞ v (Metric.ball (0 : V) 1) ∧
      ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (r ∘ v) (Metric.ball (0 : V) 1) ∧
      (v =ᵐ[volume.restrict (Metric.ball (0 : V) 1)] w) ∧
      MapsTo v (Metric.ball (0 : V) 1) (range Φ) ∧
      (∀ i, (hv i).weakGrad = (hw i).weakGrad) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1,
        diskMapTension g (fun z => r (v (Complex.orthonormalBasisOneI.repr z))) z = 0 := by
  obtain ⟨v, hv, hvs, hrvs, hvw, hvK, hgrad⟩ :=
    exists_smooth_weak_representative_of_disk_energy_minimizing_sequence
      g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak
  refine ⟨v, hv, hvs, hrvs, hvw, hvK, hgrad, ?_⟩
  exact diskMapTension_representative_eq_zero_of_minimizing_sequence
    g hΦ hU hr hΦU hleft u hu hmin hs w hw hrep hL2 hae hweak v hv hvs.continuousOn hvw hvK

end DifferentialGeometry.Geometry

end
