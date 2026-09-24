import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ChartMinimality
import DifferentialGeometry.Geometry.HarmonicMap.ChartRegularity
import DifferentialGeometry.Geometry.HarmonicMap.ChartTension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.NoncompactContinuousRepresentative

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
local notation "D" => EuclideanSpace ℝ (Fin 2)
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_smooth_canonical_chart_of_continuous_component_limit
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (V : ℂ → connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))
    (hV : ContinuousOn V (ball (0 : ℂ) 1))
    (hae : ∀ᵐ y ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) y) atTop (𝓝 (V y : M)))
    (b : D) (hb : ‖b‖ < 1) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    let p : M := V (e b)
    let w : D → H := fun x => toEuclidean (extChartAt 𝓘(ℝ, E) p (V (e (b + x)) : M))
    ∃ r : ℝ, 0 < r ∧ ‖b‖ + r < 1 ∧
      MapsTo (fun x => (V (e (b + x)) : M)) (ball (0 : D) r) (extChartAt 𝓘(ℝ, E) p).source ∧
      ContDiffOn ℝ ∞ w (ball (0 : D) r) ∧
      ∃ hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) (ball (0 : D) r),
        ∀ k, DeGiorgi.HasWeakDiv (fun x => -(∑ j : Fin 2, ∑ i, ∑ l,
          chartChristoffel g p i l k ((toEuclidean (E := E)).symm (w x)) *
            (hw i).weakGrad x j * (hw l).weakGrad x j)) (hw k).weakGrad (ball (0 : D) r) := by
  classical
  let e := Complex.orthonormalBasisOneI.repr.symm
  let p : M := V (e b)
  let c := extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ p
  let L := toEuclidean (E := E)
  let y₀ : H := L (c p)
  let T := translateDiffeomorph (c p)
  let Φ := T.toPartialDiffeomorph.trans c.symm
  have hc : p ∈ c.source := mem_extChartAt_source p
  have hT0 : T 0 = c p := by change (0 : E) + c p = c p; exact zero_add _
  have hΦsource : (0 : E) ∈ Φ.source := by
    refine ⟨mem_univ _, ?_⟩
    change T 0 ∈ c.target
    rw [hT0]
    exact c.toOpenPartialHomeomorph.map_source hc
  have hΦcenter : Φ 0 = p := by
    change c.symm (T 0) = p
    rw [hT0]
    exact c.toOpenPartialHomeomorph.left_inv hc
  have hΦeq (y : H) : Φ (L.symm y) = (extChartAt 𝓘(ℝ, E) p).symm (L.symm (y + y₀)) := by
    change c.symm (L.symm y + c p) = c.symm (L.symm (y + L (c p)))
    rw [map_add, L.symm_apply_apply]
  obtain ⟨a, R, ha, hR, hbR, hKsource, hzrange, hz, hminz⟩ :=
    exists_local_chart_minimality_in_centered_chart_of_component_limit
      g L γ u hu hmin V hV hae b hb Φ hΦsource hΦcenter
  let z : D → H := fun x => L (Φ.symm (V (e (b + x)) : M))
  let w : D → H := fun x => L (extChartAt 𝓘(ℝ, E) p (V (e (b + x)) : M))
  have hwz (x : D) : w x = z x + y₀ := by
    change L (c (V (e (b + x)) : M)) =
      L ((c (V (e (b + x)) : M)) + -(c p)) + L (c p)
    rw [L.map_add, L.map_neg]
    abel
  have hz0 : z 0 = 0 := by
    have hi : Φ.symm (Φ 0) = 0 := Φ.toOpenPartialHomeomorph.left_inv hΦsource
    change L (Φ.symm (V (e (b + 0)) : M)) = 0
    rw [add_zero]
    change L (Φ.symm p) = 0
    rw [← hΦcenter, hi, map_zero]
  have hmap (x) (hx : x ∈ ball (0 : D) R) : e (b + x) ∈ ball (0 : ℂ) 1 := by
    apply mem_ball_zero_iff.mpr
    rw [e.norm_map]
    have hn := norm_add_le b x
    have hxnorm := mem_ball_zero_iff.mp hx
    linarith
  have hUc : ContinuousOn (fun x => (V (e (b + x)) : M)) (ball (0 : D) R) :=
    continuous_subtype_val.comp_continuousOn
      (hV.comp (e.continuous.comp (continuous_const.add continuous_id)).continuousOn hmap)
  have hnear : {x : D | (V (e (b + x)) : M) ∈ c.source} ∈ 𝓝 0 := by
    have hh := (hUc.continuousAt (ball_mem_nhds _ hR)).preimage_mem_nhds
      (c.open_source.mem_nhds (by simpa only [add_zero] using hc))
    exact hh
  obtain ⟨r₀, hr₀, hr₀map⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  let R₁ := min r₀ (R / 2)
  have hR₁ : 0 < R₁ := lt_min hr₀ (half_pos hR)
  have hR₁R : R₁ < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hsub : ball (0 : D) R₁ ⊆ ball 0 R := ball_subset_ball hR₁R.le
  have hsource (x) (hx : x ∈ ball (0 : D) R₁) : (V (e (b + x)) : M) ∈ c.source :=
    hr₀map (closedBall_subset_closedBall (min_le_left _ _) (ball_subset_closedBall hx))
  have htarget (x) (hx : x ∈ ball (0 : D) R₁) : (V (e (b + x)) : M) ∈ Φ.target := by
    change (V (e (b + x)) : M) ∈
      c.symm.toOpenPartialHomeomorph.symm.symm.target ∩
        c.symm.toOpenPartialHomeomorph.symm.symm.symm ⁻¹' T.toPartialDiffeomorph.target
    exact ⟨hsource x hx, mem_univ _⟩
  have hzc : ContinuousOn z (ball (0 : D) R₁) :=
    L.continuous.comp_continuousOn (Φ.contMDiffOn_invFun.continuousOn.comp
      (hUc.mono hsub) htarget)
  have hwmap (x) (hx : x ∈ ball (0 : D) R₁) : z x + y₀ ∈ chartTargetEuclid (I := 𝓘(ℝ, E)) p := by
    rw [← hwz x]
    exact ⟨_, c.toOpenPartialHomeomorph.map_source (hsource x hx), rfl⟩
  let hz₁ (i : Fin (Module.finrank ℝ E)) := (hz i).restrict isOpen_ball hsub
  obtain ⟨r, hr, hrR₁, hzsm, hdiv⟩ := exists_smooth_centered_chart_of_local_minimality g p y₀ Φ hΦeq
    hR₁ ha hKsource hz₁ hzc hz0 (hzrange.mono_left hsub) hwmap
    (fun s hs hsR q hq hqz hqK => hminz s hs (hsR.trans hR₁R) q hq hqz hqK)
  have hrr : ball (0 : D) r ⊆ ball 0 R₁ := ball_subset_ball hrR₁.le
  let hzr (i : Fin (Module.finrank ℝ E)) := (hz₁ i).restrict isOpen_ball hrr
  let : IsFiniteMeasure (volume.restrict (ball (0 : D) r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨hw₀, hgrad⟩ := exists_memW1pWitness_add_const isOpen_ball hzr y₀
  have heq : (fun x => z x + y₀) = w := funext fun x => (hwz x).symm
  let hw (i : Fin (Module.finrank ℝ E)) := (hw₀ i).congr
    (Eventually.of_forall fun x => congrArg (fun y : H => y i) (congrFun heq x))
  have hwsm : ContDiffOn ℝ ∞ w (ball (0 : D) r) := by
    rw [← heq]
    exact hzsm.add contDiffOn_const
  refine ⟨r, hr, by linarith, fun x hx => hsource x (hrr hx), hwsm, hw, ?_⟩
  intro k
  have hg (i : Fin (Module.finrank ℝ E)) : (hw i).weakGrad = (hz₁ i).weakGrad := hgrad i
  change DeGiorgi.HasWeakDiv (fun x => -(∑ j : Fin 2, ∑ i, ∑ l,
    chartChristoffel g p i l k (L.symm (w x)) *
      (hw i).weakGrad x j * (hw l).weakGrad x j)) (hw k).weakGrad (ball (0 : D) r)
  have hdiv' : DeGiorgi.HasWeakDiv (fun x => -(∑ j : Fin 2, ∑ i, ∑ l,
    chartChristoffel g p i l k (L.symm (z x + y₀)) *
      (hz₁ i).weakGrad x j * (hz₁ l).weakGrad x j)) (hz₁ k).weakGrad (ball (0 : D) r) := hdiv k
  simpa only [hg, hwz] using hdiv'

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem contMDiffOn_of_continuous_component_minimizing_limit
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (V : ℂ → connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))
    (hV : ContinuousOn V (ball (0 : ℂ) 1))
    (hae : ∀ᵐ y ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) y) atTop (𝓝 (V y : M))) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun y => (V y : M)) (ball (0 : ℂ) 1) := by
  intro y hy
  let e := Complex.orthonormalBasisOneI.repr.symm
  let b := e.symm y
  have hb : ‖b‖ < 1 := by
    simpa only [b, e.symm.norm_map] using mem_ball_zero_iff.mp hy
  obtain ⟨r, hr, _, _, hw, _⟩ :=
    exists_smooth_canonical_chart_of_continuous_component_limit g γ u hu hmin V hV hae b hb
  let p : M := V y
  let w : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun x => toEuclidean (extChartAt 𝓘(ℝ, E) p (V (e (b + x)) : M))
  have hw0 : ContDiffAt ℝ ∞ w 0 := by
    have h := hw.contDiffAt (ball_mem_nhds _ hr)
    change ContDiffAt ℝ ∞ (fun x => toEuclidean
      (extChartAt 𝓘(ℝ, E) (V (e b) : M) (V (e (b + x)) : M))) 0 at h
    have he : e b = y := e.apply_symm_apply y
    rw [he] at h
    exact h
  let a : ℂ → EuclideanSpace ℝ (Fin 2) := fun z => e.symm z - b
  have ha : ContDiffAt ℝ ∞ a y :=
    (e.symm.contDiff.sub contDiff_const).contDiffAt
  have hay : a y = 0 := sub_self _
  have hcomp : ContDiffAt ℝ ∞ (w ∘ a) y :=
    (hay.symm ▸ hw0).comp y ha
  have hfun : w ∘ a = fun z => toEuclidean (extChartAt 𝓘(ℝ, E) p (V z : M)) := by
    funext z
    simp only [Function.comp_apply, w, a, add_sub_cancel, e.apply_symm_apply]
  rw [hfun] at hcomp
  have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
      (extChartAt 𝓘(ℝ, E) p ∘ fun z => (V z : M)) y := by
    have h := (toEuclidean (E := E)).symm.contDiff.contDiffAt.comp y hcomp
    have heq : ((toEuclidean (E := E)).symm ∘
        fun z => toEuclidean (extChartAt 𝓘(ℝ, E) p (V z : M))) =
        extChartAt 𝓘(ℝ, E) p ∘ fun z => (V z : M) := by
      funext z
      simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [heq] at h
    exact h.contMDiffAt
  have hcont : ContinuousAt (fun z => (V z : M)) y :=
    continuous_subtype_val.continuousAt.comp (hV.continuousAt (isOpen_ball.mem_nhds hy))
  exact (contMDiffAt_iff_target.mpr ⟨hcont, hchart⟩).contMDiffWithinAt

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem diskMapTension_eq_zero_of_continuous_component_minimizing_limit
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (V : ℂ → connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))
    (hV : ContinuousOn V (ball (0 : ℂ) 1))
    (hae : ∀ᵐ y ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) y) atTop (𝓝 (V y : M))) :
    ∀ y ∈ ball (0 : ℂ) 1, diskMapTension g (fun x => (V x : M)) y = 0 := by
  have hsm := contMDiffOn_of_continuous_component_minimizing_limit g γ u hu hmin V hV hae
  intro y hy
  let e := Complex.orthonormalBasisOneI.repr.symm
  let b := e.symm y
  have hb : ‖b‖ < 1 := by
    simpa only [b, e.symm.norm_map] using mem_ball_zero_iff.mp hy
  obtain ⟨r, hr, _, hsource, hwsm, hw, hPDE⟩ :=
    exists_smooth_canonical_chart_of_continuous_component_limit g γ u hu hmin V hV hae b hb
  have hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 2 (fun x => (V x : M)) y :=
    (hsm.contMDiffAt (isOpen_ball.mem_nhds hy)).of_le (by norm_cast)
  have heq (x : EuclideanSpace ℝ (Fin 2)) : e (b + x) = y + e x := by
    rw [map_add]
    change e (e.symm y) + e x = y + e x
    rw [e.apply_symm_apply]
  have heby : e b = y := e.apply_symm_apply y
  let p : M := V y
  have hsrc : MapsTo (fun x : EuclideanSpace ℝ (Fin 2) => (V (y + e x) : M))
      (ball (0 : EuclideanSpace ℝ (Fin 2)) r) (extChartAt 𝓘(ℝ, E) p).source := by
    intro x hx
    have h : (V (e (b + x)) : M) ∈ (extChartAt 𝓘(ℝ, E) (V (e b) : M)).source := hsource hx
    simpa only [heby, heq, p] using h
  have hwsm' : ContDiffOn ℝ 2
      (fun x : EuclideanSpace ℝ (Fin 2) => toEuclidean
        (extChartAt 𝓘(ℝ, E) p (V (y + e x) : M))) (ball 0 r) := by
    have h : ContDiffOn ℝ 2 (fun x : EuclideanSpace ℝ (Fin 2) => toEuclidean
      (extChartAt 𝓘(ℝ, E) (V (e b) : M) (V (e (b + x)) : M))) (ball 0 r) :=
      hwsm.of_le (by norm_cast)
    simpa only [heby, heq, p] using h
  have hfun (i : Fin (Module.finrank ℝ E)) :
      (fun x : EuclideanSpace ℝ (Fin 2) => toEuclidean
        (extChartAt 𝓘(ℝ, E) (V (e b) : M) (V (e (b + x)) : M)) i) =ᵐ[
          volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) r)]
        (fun x => toEuclidean (extChartAt 𝓘(ℝ, E) p (V (y + e x) : M)) i) := by
    filter_upwards [] with x
    rw [heby, heq]
  let hw' (i : Fin (Module.finrank ℝ E)) := (hw i).congr (hfun i)
  apply diskMapTension_eq_zero_of_shifted_chart_weak_divergence g hU hr hsrc hwsm' hw'
  intro k
  have h : DeGiorgi.HasWeakDiv (fun x => -(∑ j : Fin 2, ∑ i, ∑ l,
      chartChristoffel g (V (e b) : M) i l k ((toEuclidean (E := E)).symm
        (toEuclidean (extChartAt 𝓘(ℝ, E) (V (e b) : M) (V (e (b + x)) : M)))) *
        (hw i).weakGrad x j * (hw l).weakGrad x j)) (hw k).weakGrad
          (ball (0 : EuclideanSpace ℝ (Fin 2)) r) := hPDE k
  simpa only [heby, heq, p, hw', DeGiorgi.MemW1pWitness.congr] using h

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_smooth_harmonic_component_limit_of_minimizing_sequence
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g)
    (hregular : HomogeneouslyRegularMetric g)
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M))
    (hu : ∀ n, u n ∈ weaklyMonotoneDiskCompetitors g γ)
    (hmin : Tendsto (fun n => riemannianDiskEnergy g (u n)) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (v : ℂ → connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0))
    (hae : ∀ᵐ y ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) y) atTop (𝓝 (v y : M))) :
    ∃ V : ℂ → connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0),
      V =ᵐ[volume.restrict (ball (0 : ℂ) 1)] v ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun y => (V y : M)) (ball (0 : ℂ) 1) ∧
      ∀ y ∈ ball (0 : ℂ) 1, diskMapTension g (fun x => (V x : M)) y = 0 := by
  obtain ⟨V, hV, hVae⟩ := exists_continuous_component_representative_of_minimizing_sequence
    g hg hregular γ u hu hmin v hae
  have haeV : ∀ᵐ y ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) y) atTop (𝓝 (V y : M)) := by
    filter_upwards [hae, hVae] with y hy hyeq
    rwa [hyeq]
  exact ⟨V, hVae, contMDiffOn_of_continuous_component_minimizing_limit g γ u hu hmin V hV haeV,
    diskMapTension_eq_zero_of_continuous_component_minimizing_limit g γ u hu hmin V hV haeV⟩

end DifferentialGeometry.Geometry

end

end
