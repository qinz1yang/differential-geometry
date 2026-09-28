import DifferentialGeometry.Analysis.Sobolev.Chart.ChartDensityCutoff
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.NirenbergEstimate
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SmoothTimeMultiplier
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.FormMeasurability
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.ForcedTimeH1Energy
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergSourceIntegral

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

private theorem inner_bilinearComp_id {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (J : X →L[ℝ] Y) (L : X →L[ℝ] X) :
    ((innerSL ℝ).bilinearComp J J).bilinearComp (ContinuousLinearMap.id ℝ X) L =
      (innerSL ℝ).bilinearComp J (J.comp L) := by
  ext x z
  rfl

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem integral_heat_nirenberg_energy_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, chartDensity q α
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ z, |η z| ≤ 1) (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hroomh : Metric.cthickening |h| (tsupport η) ⊆ Ω)
    {T : ℝ} (hT : 0 ≤ T)
    (F : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ)
    (hFm : ∀ x y, AEStronglyMeasurable (fun t => F t x y) (timeMeasure T))
    {CF : ℝ} (hCF : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ CF)
    (u : timeL2 (H1ComplDirichlet q) T)
    (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T)
    (hwmass : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z))
    (hwderiv : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.deriv t z = F t (u t) z + inner ℝ (f t) (H1ComplDirichletToLp q z))
    {lam C₀ Cm C₁ N : ℝ} (hlam : 0 < lam)
    (hNd : ∀ z, |fderiv ℝ η z (EuclideanSpace.single k 1)| ≤ N) :
    let L := (smoothMulH1ComplDirichlet q φ).comp
      (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroomh)
    let J := H1ComplDirichletToLp q
    let B := (innerSL ℝ).bilinearComp J J
    let E := fun t => ∑ i, ∫ z, (η z * Sobolev.diffQuot k h
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2
    let V := fun t => ∫ z in tsupport η, (Sobolev.diffQuot k h
      (fun z => J (u t) ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) z)^2
    (∀ᵐ t ∂timeMeasure T, lam / 2 * E t ≤ F t (u t) (L (u t)) + C₀ * ‖u t‖^2) →
    (∀ v, -(B v (L v)) ≤ Cm * ‖v‖^2) → (∀ t, V t ≤ C₁ * ‖u t‖^2) →
    ∀ (ζ : ℝ → ℝ) (K : ℝ≥0), ContDiff ℝ 1 ζ → MemLp ζ ∞ volume →
      (∀ᵐ t ∂volume, 0 ≤ ζ t) → LipschitzWith K ζ → ζ 0 = 0 → ζ T = 0 →
      (∫ t, ζ t * E t ∂timeMeasure T) ≤ (4 / lam) *
        ((3 * (K : ℝ) / 2) * Cm * (∫ t, ‖u t‖^2 ∂timeMeasure T) +
          (C₀ + lam * N^2 * C₁) * (∫ t, ζ t * ‖u t‖^2 ∂timeMeasure T) +
          (2 * (lam / 4))⁻¹ * (∫ t, ζ t * (∫ z in Ω,
            (f t ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))^2) ∂timeMeasure T)) := by
  intro L J B E V hcoerF hmassbound hVbound ζ K hζsmooth hζ hζpos hζlip hζ0 hζT
  let Cf := (2 * (lam / 4))⁻¹
  let Cr := lam * N^2 * C₁
  let Q : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q) →L[ℝ]
      H1ComplDirichlet q →L[ℝ] ℝ := (ContinuousLinearMap.precomp ℝ J).comp (innerSL ℝ)
  let β := Q.compLpL 2 (timeMeasure T) f
  have hβ : ∀ᵐ t ∂timeMeasure T, β t = Q (f t) := Q.coeFn_compLpL f
  have hmass : w.toFun =ᵐ[timeMeasure T] fun t => B (u t) := by
    filter_upwards [hwmass] with t ht
    ext z
    exact ht z
  have hderiv : w.deriv =ᵐ[timeMeasure T] fun t => F t (u t) + β t := by
    filter_upwards [hwderiv, hβ] with t ht hβt
    ext z
    rw [add_apply, hβt]
    exact ht z
  have htest := dirichletNirenbergTest_symmetric_nonpos_of_mul_chartDensity
    q α hΩ hΩc hΩs hη hηc φ k h hroomh (fun z hz => hφ z (hroomh hz))
  have hsymm := htest.1
  have hpos := htest.2.1
  have hBL : (-(B.bilinearComp (ContinuousLinearMap.id ℝ (H1ComplDirichlet q)) L)).flip =
      -(B.bilinearComp (ContinuousLinearMap.id ℝ (H1ComplDirichlet q)) L) := by
    change (-(((innerSL ℝ).bilinearComp J J).bilinearComp (ContinuousLinearMap.id ℝ _) L)).flip = _
    rw [inner_bilinearComp_id]
    exact hsymm
  have he := u.integral_mul_bilinear_comp_le_of_timeH1_mass_dual hT F hFm hCF
    B β w hmass hderiv L hBL hpos hζsmooth hζ hζpos hζlip hζ0 hζT
  let Ei := fun i t => ∫ z, (η z * Sobolev.diffQuot k h
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2
  let P := fun t => ∫ z in Ω, (f t ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))^2
  have hEi (i) : Integrable (Ei i) (timeMeasure T) :=
    Sobolev.integrable_integral_sq_cutoff_diffQuot_comp hΩ.measurableSet
      (hη.continuous.memLp_of_hasCompactSupport hηc) k h hroomh
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i) (Lp.memLp u)
  have hEI : Integrable E (timeMeasure T) := integrable_finsetSum _ (fun i _ => hEi i)
  have hχ : MemLp ζ ∞ (timeMeasure T) := hζ.restrict _
  have hχpos : ∀ᵐ t ∂timeMeasure T, 0 ≤ ζ t :=
    hζpos.filter_mono (ae_mono Measure.restrict_le_self)
  have hsource := abs_integral_mul_integral_mul_smoothMul_dirichletNirenbergTest_le_of_mul_chartDensity
    q α hΩ hΩc hΩs φ hφ u f hη hηc hηb k hNd
      (show 0 < lam / 4 by positivity) h hroomh hχ hχpos
  have hpair : (∫ t, ζ t * β t (L (u t)) ∂timeMeasure T) =
      ∫ t, ζ t * (∫ y, f t y * H1ComplDirichletToLp q (L (u t)) y
        ∂riemannianVolumeMeasure (I := I_hs) (M := M) q) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [hβ] with t ht
    rw [ht]
    change ζ t * inner ℝ (f t) (J (L (u t))) = _
    rw [L2.inner_def]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by simp only [Real.inner_apply, J]
  have hEik : (∫ t, ζ t * Ei k t ∂timeMeasure T) ≤ ∫ t, ζ t * E t ∂timeMeasure T := by
    apply integral_mono_ae ((hEi k).mul_of_top_right hχ) (hEI.mul_of_top_right hχ)
    filter_upwards [hχpos] with t ht
    change ζ t * Ei k t ≤ ζ t * ∑ i, Ei i t
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
      (f := fun i => Ei i t) (fun i _ => integral_nonneg fun _ => sq_nonneg _)
        (Finset.mem_univ k)) ht
  have hVI : Integrable V (timeMeasure T) := by
    let R := chartRestrictionLp q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2
    let A := R.comp J
    have hv := Sobolev.integrable_integral_sq_diffQuot_on_comp hΩ.measurableSet
      (isClosed_tsupport η).measurableSet k h hroomh A (Lp.memLp u)
    apply hv.congr
    filter_upwards [] with t
    apply integral_congr_ae
    have hc := chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2 (J (u t))
    exact (Sobolev.diffQuot_congr_ae_on hΩ.measurableSet
      (isClosed_tsupport η).measurableSet k h hroomh hc).mono fun z hz => congrArg (fun r : ℝ => r^2) hz
  have huI := (Lp.memLp u).norm.integrable_sq
  have hVb : (∫ t, ζ t * V t ∂timeMeasure T) ≤ C₁ * ∫ t, ζ t * ‖u t‖^2 ∂timeMeasure T := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hVI.mul_of_top_right hχ) ((huI.mul_of_top_right hχ).const_mul C₁)
    filter_upwards [hχpos] with t ht
    simpa only [Pi.mul_apply, mul_assoc, mul_left_comm (ζ t)] using mul_le_mul_of_nonneg_left (hVbound t) ht
  have hs : |∫ t, ζ t * β t (L (u t)) ∂timeMeasure T| ≤
      lam / 4 * (∫ t, ζ t * E t ∂timeMeasure T) +
        Cf * (∫ t, ζ t * P t ∂timeMeasure T) + Cr * (∫ t, ζ t * ‖u t‖^2 ∂timeMeasure T) := by
    rw [hpair]
    apply hsource.trans
    have hb := add_le_add
      (add_le_add_right (mul_le_mul_of_nonneg_left hEik (show 0 ≤ lam / 4 by positivity))
        (Cf * ∫ t, ζ t * P t ∂timeMeasure T))
      (mul_le_mul_of_nonneg_left hVb (show 0 ≤ 4 * (lam / 4) * N^2 by positivity))
    convert hb using 1 <;> dsimp only [Cr, Cf, Ei, E, V, P, J] <;> ring
  have hLE : MemLp (fun t => L (u t)) 2 (timeMeasure T) := (Lp.memLp u).continuousLinearMap_comp L
  have hFI : Integrable (fun t => F t (u t) (L (u t))) (timeMeasure T) :=
    integrable_bilinear_of_apply_aestronglyMeasurable F hFm hCF (Lp.memLp u) hLE
  have hBI : Integrable (fun t => -(B (u t) (L (u t)))) (timeMeasure T) :=
    (integrable_bilinear_of_apply_aestronglyMeasurable (fun _ => B)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl)
      (Lp.memLp u) hLE).neg
  have hmassI := integral_mono_ae hBI (huI.const_mul Cm)
    (Eventually.of_forall fun t => hmassbound (u t))
  rw [integral_const_mul] at hmassI
  have hcoerI := integral_mono_ae ((hEI.mul_of_top_right hχ).const_mul (lam / 2))
    ((hFI.mul_of_top_right hχ).add ((huI.mul_of_top_right hχ).const_mul C₀))
      (by
        filter_upwards [hcoerF, hχpos] with t ht hζt
        simpa only [Pi.mul_apply, Pi.add_apply, mul_add, mul_assoc, mul_left_comm (ζ t)]
          using mul_le_mul_of_nonneg_left ht hζt)
  simp only [Pi.mul_apply, Pi.add_apply] at hcoerI
  rw [integral_add (show Integrable (fun t => ζ t * F t (u t) (L (u t))) (timeMeasure T) from
    hFI.mul_of_top_right hχ)
    (show Integrable (fun t => C₀ * (ζ t * ‖u t‖^2)) (timeMeasure T) from
      (huI.mul_of_top_right hχ).const_mul C₀),
    integral_const_mul, integral_const_mul] at hcoerI
  have hnegative := neg_le_abs (∫ t, ζ t * β t (L (u t)) ∂timeMeasure T)
  have hmassIb := mul_le_mul_of_nonneg_left hmassI (show 0 ≤ 3 * (K : ℝ) / 2 by positivity)
  have hb : (∫ t, ζ t * E t ∂timeMeasure T) ≤ (4 / lam) *
      ((3 * (K : ℝ) / 2) * Cm * (∫ t, ‖u t‖^2 ∂timeMeasure T) +
        (C₀ + Cr) * (∫ t, ζ t * ‖u t‖^2 ∂timeMeasure T) +
          Cf * (∫ t, ζ t * P t ∂timeMeasure T)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hlam).mpr
    nlinarith only [he, hcoerI, hnegative, hs, hmassIb]
  exact hb

private theorem exists_bounded_dirichlet_heat_form
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {T : ℝ} (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (G.metric t).inner x w w ∧
        (G.metric t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q) :
    ∃ (F : ℝ → H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q →L[ℝ] ℝ) (C : ℝ),
      0 ≤ C ∧ (∀ y z, AEStronglyMeasurable (fun t => F t y z) (timeMeasure T)) ∧
      (∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ C) ∧
      ∀ t (ht : t ∈ Ico (0 : ℝ) T) (u v : H1ComplDirichlet q),
        F t u v = dirichletWeakFormCompl (G.metric t) 0 0 0 (by intro x; simp)
          hCg (hequiv t ⟨ht.1, ht.2.le⟩) Cv hCv0 hCvtop (hvol t ⟨ht.1, ht.2.le⟩) u
          (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q) v) := by
  let hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (0 : TangentSpace I_hs x) 0 ≤ (0 : ℝ) := by
    intro t ht x
    simp
  let F₀ := dirichletWeakFormComplOnIco G.metric (fun _ => 0) (fun _ => 0) 0 hX
    hCg hequiv Cv hCv0 hCvtop hvol
  let S := fun t => smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q)
  let : NormedAddCommGroup (H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q) :=
    ContinuousLinearMap.toNormedAddCommGroup
  have hS : ContinuousOn S (Icc (0 : ℝ) T) :=
    ((contDiffOn_one_smoothMulH1ComplDirichlet q _ D.regular_isOpen
      (riemannianVolumeDensity_swap_contMDiffOn_of_metricFamilySmoothOn hG q)).mono hreg).continuousOn
  obtain ⟨CS, hCS⟩ := isCompact_Icc.exists_bound_of_continuousOn hS
  have hzero : ContinuousOn
      (fun p : ℝ × M => (⟨p.2, (0 : TangentSpace I_hs p.2)⟩ : TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)) := by
    exact ((continuous_zeroSection ℝ).comp continuous_snd).continuousOn
  have hF₀ : ∀ y z, AEStronglyMeasurable (fun t => F₀ t y z) (timeMeasure T) :=
    dirichletWeakFormComplOnIco_aestronglyMeasurable hG hreg (fun _ => 0) hzero
      (fun _ => 0) continuousOn_const 0 hX hCg hequiv Cv hCv0 hCvtop hvol
  have hF₀b (t : ℝ) : ‖F₀ t‖ ≤ Cv.toReal * Cg := by
    simpa only [max_self, Real.sqrt_zero, add_zero, one_mul] using
      norm_dirichletWeakFormComplOnIco_le G.metric (fun _ => 0) (fun _ => 0) 0 0
        le_rfl (by intro s hs; simp) hX hCg hequiv Cv hCv0 hCvtop hvol t
  let F := fun t => (F₀ t).bilinearComp (ContinuousLinearMap.id ℝ _) (S t)
  refine ⟨F, Cv.toReal * Cg * max CS 0, by positivity, ?_, ?_, ?_⟩
  · intro y z
    exact AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable
      (fun t => F₀ t y) (hF₀ y) (fun t => S t z)
      (memLp_of_continuousOn (hS.clm_apply continuousOn_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp only [F]
    rw [ContinuousLinearMap.bilinearComp, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.opNorm_flip]
    exact ((F₀ t).flip.opNorm_comp_le (S t)).trans (by
      rw [ContinuousLinearMap.opNorm_flip]
      exact mul_le_mul (hF₀b t) ((hCS t ht).trans (le_max_left _ _))
        (norm_nonneg _) (by positivity))
  · intro t ht u v
    dsimp only [F, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply, F₀]
    rw [dirichletWeakFormComplOnIco, dite_eq_left ht]

private theorem exists_heat_nirenberg_energy_bound
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (G.metric t).inner x w w ∧
        (G.metric t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (hηb : ∀ z, |η z| ≤ 1)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, chartDensity q α
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ω, ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j,
        Laplacian.MetricExtension.invGramOnEuclid (G.metric t) α i j y * ξ i * ξ j) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ Metric.cthickening δ (tsupport η) ⊆ Ω ∧
      ∀ (u : timeL2 (H1ComplDirichlet q) T)
        (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
        (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T),
      (∀ᵐ t ∂timeMeasure T, ∀ z,
        w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z)) →
      (∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
        w.deriv t z = dirichletWeakFormCompl (G.metric t) 0 0 0 (by intro x; simp)
          hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
          (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q) z) +
            inner ℝ (f t) (H1ComplDirichletToLp q z)) →
      ∀ k h, |h| ≤ δ → ∀ (ζ : ℝ → ℝ) (K : ℝ≥0), ContDiff ℝ 1 ζ → MemLp ζ ∞ volume →
        (∀ᵐ t ∂volume, 0 ≤ ζ t) → LipschitzWith K ζ → ζ 0 = 0 → ζ T = 0 →
        (∫ t, ζ t * (∑ i, ∫ z, (η z * Sobolev.diffQuot k h
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2) ∂timeMeasure T) ≤
          C * ((K : ℝ) * (∫ t, ‖u t‖^2 ∂timeMeasure T) +
            (∫ t, ζ t * ‖u t‖^2 ∂timeMeasure T) +
            (∫ t, ζ t * (∫ z in Ω, (f t
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))^2) ∂timeMeasure T)) := by
  have hzero : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuN)) ∞
      (fun p : ℝ × M => (⟨p.2, (0 : TangentSpace I_hs p.2)⟩ : TangentBundle I_hs M))
      (D.regular ×ˢ (trivializationAt EuN (TangentSpace I_hs) α).baseSet) :=
    ((contMDiff_zeroSection ℝ (TangentSpace I_hs : M → Type _)).comp contMDiff_snd).contMDiffOn
  have he₀ :=
    exists_uniform_dirichletWeakFormCompl_nirenberg_lower_bound hG isCompact_Icc hreg q α hΩ hΩc hΩs
      (fun _ => 0) hzero (fun _ => 0) continuousOn_const 0 (by intro t ht x; simp)
      hCg hequiv Cv hCv0 hCvtop hvol φ hφ hη hηc hηs hηb hlam hcoer
  let δ₀ := he₀.choose
  have hδ₀ := he₀.choose_spec.1
  let C₀ := he₀.choose_spec.2.choose
  have hC₀ := he₀.choose_spec.2.choose_spec.1
  have hroom₀ := he₀.choose_spec.2.choose_spec.2.choose
  have hc₀ := he₀.choose_spec.2.choose_spec.2.choose_spec
  have he₁ :=
    exists_integral_sq_weakPartial_diffQuot_chartInverse_le q α hΩ hΩc hΩs hηc hηs
  let δ₁ := he₁.choose
  have hδ₁ := he₁.choose_spec.1
  let C₁ := he₁.choose_spec.2.choose
  have hC₁ := he₁.choose_spec.2.choose_spec.1
  have hc₁ := he₁.choose_spec.2.choose_spec.2.2
  obtain ⟨Ω', hΩ', hηΩ', hΩ'Ω, hΩ'c⟩ :=
    exists_open_between_and_isCompact_closure hηc hΩ hηs
  obtain ⟨Ω'', hΩ'', hηΩ'', hΩ''Ω', hΩ''c⟩ :=
    exists_open_between_and_isCompact_closure hηc hΩ' hηΩ'
  obtain ⟨r, hr, hrroom⟩ := hΩ''c.exists_cthickening_subset_open hΩ' hΩ''Ω'
  obtain ⟨Cm, hCm, hmb⟩ := exists_integral_cutoff_sq_diffQuot_chartInverse_le q α hΩ hΩc hΩs
    hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c hη.continuous hηc hηΩ'' hr hrroom
  obtain ⟨N, hN⟩ := (hηc.fderiv ℝ).exists_bound_of_continuous (hη.continuous_fderiv (by simp))
  have hNd k z : |fderiv ℝ η z (EuclideanSpace.single k 1)| ≤ N := by
    calc
      _ = ‖fderiv ℝ η z (EuclideanSpace.single k 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ η z‖ * ‖EuclideanSpace.single k (1 : ℝ)‖ := (fderiv ℝ η z).le_opNorm _
      _ = ‖fderiv ℝ η z‖ := by rw [PiLp.norm_single, norm_one, mul_one]
      _ ≤ N := hN z
  have hexF :=
    exists_bounded_dirichlet_heat_form hG hreg q hCg hequiv Cv hCv0 hCvtop hvol
  let F := hexF.choose
  let CF := hexF.choose_spec.choose
  have hFm := hexF.choose_spec.choose_spec.2.1
  have hCF := hexF.choose_spec.choose_spec.2.2.1
  have hF := hexF.choose_spec.choose_spec.2.2.2
  let δ := min δ₀ (min δ₁ r)
  let Cr := lam * N^2 * C₁
  let Cf := (2 * (lam / 4))⁻¹
  let C := (4 / lam) * max (3 / 2 * Cm) (max (C₀ + Cr) Cf)
  have hd₀ : δ ≤ δ₀ := min_le_left _ _
  have hd₁ : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hdr : δ ≤ r := (min_le_right _ _).trans (min_le_right _ _)
  have hroom := (Metric.cthickening_mono hd₀ _).trans hroom₀
  refine ⟨δ, lt_min hδ₀ (lt_min hδ₁ hr), C, by dsimp only [C, Cr, Cf]; positivity, hroom, ?_⟩
  intro u f w hwmass hwderiv k h hh ζ K hζsmooth hζ hζpos hζlip hζ0 hζT
  have hroomh := (Metric.cthickening_mono hh _).trans hroom
  let J := H1ComplDirichletToLp q
  let B := (innerSL ℝ).bilinearComp J J
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ico (0 : ℝ) T := by
    unfold timeMeasure
    rw [← restrict_Ico_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ico
  have hderivF : ∀ᵐ t ∂timeMeasure T, ∀ z,
      w.deriv t z = F t (u t) z + inner ℝ (f t) (H1ComplDirichletToLp q z) := by
    filter_upwards [hwderiv, hmem] with t ht htm
    intro z
    rw [hF t htm]
    exact ht ⟨htm.1, htm.2.le⟩ z
  let L := (smoothMulH1ComplDirichlet q φ).comp
    (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroomh)
  have htest := dirichletNirenbergTest_symmetric_nonpos_of_mul_chartDensity
    q α hΩ hΩc hΩs hη hηc φ k h hroomh (fun z hz => hφ z (hroomh hz))
  have hval := htest.2.2
  have hmassbound (v : H1ComplDirichlet q) : -(B v (L v)) ≤ Cm * ‖v‖^2 := by
    change (-(innerSL ℝ).bilinearComp J (J.comp L)) v v ≤ _
    rw [hval v v]
    convert hmb k h (hh.trans hdr) v using 1
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  let Ei := fun i t => ∫ z, (η z * Sobolev.diffQuot k h
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2
  let E := fun t => ∑ i, Ei i t
  let P := fun t => ∫ z in Ω, (f t ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))^2
  have hcoerF : ∀ᵐ t ∂timeMeasure T, lam / 2 * E t ≤ F t (u t) (L (u t)) + C₀ * ‖u t‖^2 := by
    filter_upwards [hmem] with t ht
    rw [hF t ht]
    have hm (v : H1ComplDirichlet q) :
        smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q) (L v) =
          smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (G.metric t) q * φ)
            (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroomh v) := by
      change ((smoothMulH1ComplDirichlet q _).comp (smoothMulH1ComplDirichlet q φ)) _ = _
      rw [smoothMulH1ComplDirichlet_mul]
      rfl
    rw [hm]
    exact hc₀ t ⟨ht.1, ht.2.le⟩ k h (hh.trans hd₀) (u t)
  let V := fun t => ∫ z in tsupport η, (Sobolev.diffQuot k h
    (fun z => H1ComplDirichletToLp q (u t)
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) z)^2
  have hVbound (t) : V t ≤ C₁ * ‖u t‖^2 :=
    (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)).trans
      (hc₁ k h (hh.trans hd₁) (u t))
  have hb := integral_heat_nirenberg_energy_le q α hΩ hΩc hΩs φ hφ hη hηc hηb
    k h hroomh hT F hFm hCF u f w hwmass hderivF hlam (hNd k)
      hcoerF hmassbound hVbound ζ K hζsmooth hζ hζpos hζlip hζ0 hζT
  have hχpos : ∀ᵐ t ∂timeMeasure T, 0 ≤ ζ t :=
    hζpos.filter_mono (ae_mono Measure.restrict_le_self)
  have hA : 0 ≤ (K : ℝ) * ∫ t, ‖u t‖^2 ∂timeMeasure T :=
    mul_nonneg K.coe_nonneg (integral_nonneg fun _ => sq_nonneg _)
  have hUn : 0 ≤ ∫ t, ζ t * ‖u t‖^2 ∂timeMeasure T :=
    integral_nonneg_of_ae (hχpos.mono fun t ht => mul_nonneg ht (sq_nonneg _))
  have hPn : 0 ≤ ∫ t, ζ t * P t ∂timeMeasure T :=
    integral_nonneg_of_ae (hχpos.mono fun t ht => mul_nonneg ht (integral_nonneg fun _ => sq_nonneg _))
  have hb₀ := mul_le_mul_of_nonneg_right (le_max_left (3/2*Cm) (max (C₀+Cr) Cf)) hA
  have hb₁ := mul_le_mul_of_nonneg_right
    ((le_max_left (C₀+Cr) Cf).trans (le_max_right (3/2*Cm) (max (C₀+Cr) Cf))) hUn
  have hb₂ := mul_le_mul_of_nonneg_right
    ((le_max_right (C₀+Cr) Cf).trans (le_max_right (3/2*Cm) (max (C₀+Cr) Cf))) hPn
  apply hb.trans
  dsimp only [C, E, Ei, P]
  nlinarith only [mul_le_mul_of_nonneg_left (add_le_add (add_le_add hb₀ hb₁) hb₂)
    (show 0 ≤ 4 / lam by positivity)]


theorem exists_integral_cutoff_diffQuot_weakPartial_le_of_heat_timeH1
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I_hs M}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D g)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M)
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ w : TangentSpace I_hs x,
      Cg⁻¹ * q.inner x w w ≤ (g t).inner x w w ∧
        (g t).inner x w w ≤ Cg * q.inner x w w)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_hs) (M := M) (g t) ≤
        Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q)
    (α : M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (hηb : ∀ z, |η z| ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ Metric.cthickening δ (tsupport η) ⊆ Ω ∧
      ∀ (u : timeL2 (H1ComplDirichlet q) T)
        (f : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)) T)
        (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) T),
      (∀ᵐ t ∂timeMeasure T, ∀ z,
        w.toFun t z = inner ℝ (H1ComplDirichletToLp q (u t)) (H1ComplDirichletToLp q z)) →
      (∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ z,
        w.deriv t z = dirichletWeakFormCompl (g t) 0 0 0 (by intro x; simp)
          hCg (hequiv t ht) Cv hCv0 hCvtop (hvol t ht) (u t)
          (smoothMulH1ComplDirichlet q (riemannianVolumeDensitySmoothMap (g t) q) z) +
            inner ℝ (f t) (H1ComplDirichletToLp q z)) →
      ∀ k h, |h| ≤ δ → ∀ (ζ : ℝ → ℝ) (K : ℝ≥0), ContDiff ℝ 1 ζ → MemLp ζ ∞ volume →
        (∀ᵐ t ∂volume, 0 ≤ ζ t) → LipschitzWith K ζ → ζ 0 = 0 → ζ T = 0 →
        (∫ t, ζ t * (∑ i, ∫ z, (η z * Sobolev.diffQuot k h
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z)^2) ∂timeMeasure T) ≤
          C * ((K : ℝ) * (∫ t, ‖u t‖^2 ∂timeMeasure T) +
            (∫ t, ζ t * ‖u t‖^2 ∂timeMeasure T) +
            (∫ t, ζ t * (∫ z in Ω, (f t
              ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))^2) ∂timeMeasure T)) := by
  let G : MetricConnectionFamilyOn (I := I_hs) (M := M) D :=
    { metric := g
      connection := fun t => Geometry.Connection.leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  obtain ⟨φ, _, hφ₀⟩ := Sobolev.Chart.exists_smoothMap_mul_chartDensity_eq_one
    q α hU (Subset.rfl : U ⊆ U) hΩc hΩs
  have hφ (z) (hz : z ∈ Ω) := hφ₀ z (subset_closure hz)
  obtain ⟨lam, hlam, hcoer₀⟩ :=
    Laplacian.MetricExtension.exists_uniform_inv_gram_quadratic_lower_bound
      (G := G) hG isCompact_Icc hreg α hΩc (hΩs.trans (image_mono interior_subset))
  have hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ω, ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j,
        Laplacian.MetricExtension.invGramOnEuclid (g t) α i j y * ξ i * ξ j := by
    intro t ht y hy ξ
    have hb := hcoer₀ t ht y (subset_closure hy) (WithLp.toLp 2 ξ)
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
      PiLp.inner_apply, DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Real.inner_apply] at hb
    convert hb using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  exact exists_heat_nirenberg_energy_bound (G := G) hG hT hreg q hCg hequiv Cv hCv0 hCvtop hvol
    α hΩ hΩc hΩs hη hηc hηs hηb φ hφ hlam hcoer

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
