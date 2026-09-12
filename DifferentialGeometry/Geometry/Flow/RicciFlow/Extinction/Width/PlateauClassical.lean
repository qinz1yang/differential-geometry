import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Plateau
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ComponentHarmonic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ComponentDifferential
import DifferentialGeometry.Geometry.Metric.UniformCharts
import DifferentialGeometry.Topology.Connected.FiniteEDistance
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Extinction
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]


def closedCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ i, |y i| ≤ 1}

def openCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ i, |y i| < 1}

structure CubeChart (n : ℕ) where
  chart : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) Q
  closedCube_subset_source : closedCube n ⊆ chart.source
  smooth : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I ∞ chart chart.source
  smooth_inverse : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ chart.symm chart.target

def CubeChart.pullMetric (g : SmoothRiemannianMetric I Q)
    {n : ℕ} (psi : CubeChart (I := I) (Q := Q) n)
    (y v w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  g.inner (psi.chart y)
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I psi.chart y v)
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I psi.chart y w)

structure HomogeneousCoordinates (g : SmoothRiemannianMetric I Q) (n : ℕ) where
  atPoint : Q → CubeChart (I := I) (Q := Q) n
  centered : ∀ p : Q, (atPoint p).chart 0 = p
  lowerBound : ℝ
  upperBound : ℝ
  lower_pos : 0 < lowerBound
  lower_le_upper : lowerBound ≤ upperBound
  ellipticity : ∀ (p : Q) (y : EuclideanSpace ℝ (Fin n)), y ∈ openCube n →
    ∀ v : EuclideanSpace ℝ (Fin n),
      lowerBound * ‖v‖ ^ 2 ≤ (atPoint p).pullMetric g y v v ∧
        (atPoint p).pullMetric g y v v ≤ upperBound * ‖v‖ ^ 2
  derivative_bounds : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (p : Q) (y : EuclideanSpace ℝ (Fin n)), y ∈ closedCube n →
    ∀ i j : Fin n,
      ‖iteratedFDeriv ℝ k (fun x => (atPoint p).pullMetric g x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) y‖ ≤ C

structure InteriorSmoothDisk where
  map : C(Width.Disk, Q)
  smooth : ∀ z : Width.Disk, (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 →
    Nonempty (Width.DiskLocalExtension (I := I) map z)

def InteriorSmoothDisk.differential (u : InteriorSmoothDisk (I := I) (Q := Q))
    (z : Width.Disk) (v : ℂ) : TangentSpace I (u.map z) := by
  simpa only [Width.diskExtension_coe] using
    mfderivWithin 𝓘(ℝ, ℂ) I (Width.diskExtension u.map)
      (Metric.closedBall (0 : ℂ) 1) (z : ℂ) v

def InteriorSmoothDisk.IsConformal (u : InteriorSmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) : Prop :=
  ∀ z : Width.Disk, (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 →
    g.inner (u.map z) (u.differential z 1) (u.differential z Complex.I) = 0 ∧
    g.inner (u.map z) (u.differential z 1) (u.differential z 1) =
      g.inner (u.map z) (u.differential z Complex.I) (u.differential z Complex.I)

variable [FiniteDimensional ℝ E] [CompleteSpace E]

def InteriorSmoothDisk.IsHarmonic (u : InteriorSmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) : Prop :=
  ∀ z : Width.Disk, (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 →
    ∀ F : Width.DiskLocalExtension (I := I) u.map z,
      Width.diskLocalTension g F.map (z : ℂ) = 0

private theorem closedCube_subset_closedBall_finrank (n : ℕ) (hn : 1 ≤ n) :
    closedCube n ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (n : ℝ) := by
  intro y hy
  rw [EuclideanSpace.closedBall_zero_eq (n : ℝ) (by positivity)]
  change ∑ i : Fin n, y i ^ 2 ≤ (n : ℝ) ^ 2
  have h1 : ∑ i : Fin n, y i ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    have := abs_le.mp (hy i)
    nlinarith
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one] at h1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

private theorem openCube_subset_closedCube (n : ℕ) : openCube n ⊆ closedCube n :=
  fun _ hy i => (hy i).le

omit [CompleteSpace E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem compact_homogeneous_regularity
    [I.Boundaryless] [T2Space Q] [CompactSpace Q] [ConnectedSpace Q] [Nonempty Q]
    (g : SmoothRiemannianMetric I Q) (n : ℕ) (hn : 1 ≤ n)
    (hdim : Module.finrank ℝ E = n) :
    ∃ d : MetricSpace Q,
      d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace Q) ∧
      (∀ p q : Q, @edist Q d.toEDist p q = riemannianEDistOf g p q) ∧
      @CompleteSpace Q d.toUniformSpace ∧
      Nonempty (HomogeneousCoordinates g n) := by
  have hT3 : T3Space Q := inferInstance
  let : T3Space Q := hT3
  let : RiemannianBundle (TangentSpace I : Q → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : Q → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace Q := EMetricSpace.ofRiemannianMetric I Q
  have hfin : ∀ p q : Q, edist p q ≠ ⊤ := fun p q =>
    DifferentialGeometry.Analysis.edist_ne_top_of_preconnected p q
  have hcomplete : @CompleteSpace Q (EMetricSpace.toMetricSpace hfin).toUniformSpace :=
    (DifferentialGeometry.RiemannianMetricComplete.of_compact (I := I) g).complete
  let c : Geometry.Topology.StandardModelCopy I Q E :=
    Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ c.Q := c.equiv
  let : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  let : Nonempty c.Q := ⟨c.equiv (Classical.arbitrary Q)⟩
  let g' : SmoothRiemannianMetric 𝓘(ℝ, E) c.Q :=
    Diffeomorph.pullbackMetricCross g Φ.symm
  let V := EuclideanSpace ℝ (Fin n)
  let e : V ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin]; exact hdim.symm)
  obtain ⟨m, A, hm, hmA, ψ, hψ, hC⟩ :=
    DifferentialGeometry.Geometry.exists_uniform_metric_charts g' e (n : ℝ)
      (fun i : Fin n => EuclideanSpace.single i 1)
  have hcube : closedCube n ⊆ Metric.closedBall (0 : V) (n : ℝ) :=
    closedCube_subset_closedBall_finrank n hn
  let chart : Q → OpenPartialHomeomorph V Q := fun p =>
    (ψ (Φ p)).trans (Φ.symm.toHomeomorph.toOpenPartialHomeomorph)
  have hchart (p : Q) : (chart p : V → Q) = Φ.symm ∘ (ψ (Φ p)) :=
    OpenPartialHomeomorph.coe_trans _ _
  have hpt (p : Q) (y : V) : (chart p) y = Φ.symm ((ψ (Φ p)) y) := by
    rw [hchart p]
    rfl
  have hsrc (p : Q) : closedCube n ⊆ (chart p).source := by
    intro y hy
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨(hψ (Φ p)).1 (hcube hy), by simp⟩
  have hsmooth (p : Q) :
      ContMDiffOn 𝓘(ℝ, V) I ∞ (chart p) (chart p).source := by
    have h1 : ContMDiffOn 𝓘(ℝ, V) I ∞ (Φ.symm ∘ (ψ (Φ p))) (ψ (Φ p)).source :=
      (Diffeomorph.contMDiff Φ.symm).comp_contMDiffOn (hψ (Φ p)).2.2.1
    rw [hchart p, OpenPartialHomeomorph.trans_source]
    simp only [Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    exact h1
  have hdiff (p : Q) (z : V) (hz : z ∈ (ψ (Φ p)).source) :
      MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ (Φ p)) z :=
    (((hψ (Φ p)).2.2.1 z hz).contMDiffAt ((ψ (Φ p)).open_source.mem_nhds hz)).mdifferentiableAt
      (by simp)
  have hdΦ (z : c.Q) : MDifferentiableAt 𝓘(ℝ, E) I (Φ.symm : c.Q → Q) z :=
    (Diffeomorph.mdifferentiable Φ.symm (by simp)) z
  have hchain (p : Q) {y : V} (hy : y ∈ (ψ (Φ p)).source) :
      mfderiv 𝓘(ℝ, V) I (chart p) y =
        (mfderiv 𝓘(ℝ, E) I (Φ.symm : c.Q → Q) ((ψ (Φ p)) y)).comp
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ (Φ p)) y) := by
    rw [hchart p]
    exact mfderiv_comp y (hdΦ ((ψ (Φ p)) y)) (hdiff p y hy)
  have hmfv (p : Q) {y : V} (hy : y ∈ (ψ (Φ p)).source) (v : V) :
      mfderiv 𝓘(ℝ, V) I (chart p) y v =
        mfderiv 𝓘(ℝ, E) I (Φ.symm : c.Q → Q) ((ψ (Φ p)) y)
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ (Φ p)) y v) := by
    erw [hchain p hy]
    rfl
  have hsymm (p : Q) :
      ContMDiffOn I 𝓘(ℝ, V) ∞ (chart p).symm (chart p).target := by
    have h1 : ContMDiffOn I 𝓘(ℝ, V) ∞ ((ψ (Φ p)).symm ∘ (Φ : Q → c.Q))
        (Φ ⁻¹' (ψ (Φ p)).target) :=
      ContMDiffOn.comp (I' := 𝓘(ℝ, E)) (hψ (Φ p)).2.2.2.1
        ((Diffeomorph.contMDiff Φ).contMDiffOn) (fun _ hy => hy)
    have h2 : ((chart p).symm : Q → V) = (ψ (Φ p)).symm ∘ (Φ : Q → c.Q) := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans]
      ext y
      simp [Homeomorph.toOpenPartialHomeomorph_apply]
    have h3 : (Φ.symm.toHomeomorph.toOpenPartialHomeomorph).symm ⁻¹' (ψ (Φ p)).target
        = Φ ⁻¹' (ψ (Φ p)).target := by
      congr 1
    rw [h2, OpenPartialHomeomorph.trans_target]
    rw [h3]
    simp only [Homeomorph.toOpenPartialHomeomorph_target, univ_inter]
    exact h1
  let atPoint : Q → CubeChart (I := I) (Q := Q) n := fun p => {
    chart := chart p
    closedCube_subset_source := hsrc p
    smooth := hsmooth p
    smooth_inverse := hsymm p }
  have hident (p : Q) {y : V} (hy : y ∈ (chart p).source) (v w : V) :
      (atPoint p).pullMetric g y v w
        = g'.inner ((ψ (Φ p)) y)
            (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ (Φ p)) y v)
            (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ (Φ p)) y w) := by
    have hys : y ∈ (ψ (Φ p)).source := by
      rw [OpenPartialHomeomorph.trans_source] at hy
      exact hy.1
    have hpb := Diffeomorph.pullbackMetricCross_inner (g := g) (Φ := Φ.symm)
      ((ψ (Φ p)) y)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ (Φ p)) y v)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ (Φ p)) y w)
    unfold CubeChart.pullMetric
    erw [hmfv p hys v, hmfv p hys w, hpt p y]
    exact hpb.symm
  refine ⟨EMetricSpace.toMetricSpace hfin, rfl, ?_, hcomplete, ?_⟩
  · intro p q
    rfl
  · refine ⟨{
      atPoint := atPoint
      centered := ?_
      lowerBound := m
      upperBound := A
      lower_pos := hm
      lower_le_upper := hmA
      ellipticity := ?_
      derivative_bounds := ?_ }⟩
    · intro p
      rw [OpenPartialHomeomorph.trans_apply, (hψ (Φ p)).2.1]
      simp [Diffeomorph.symm_apply_apply]
    · intro p y hy v
      have hys : y ∈ (chart p).source := hsrc p (openCube_subset_closedCube n hy)
      rw [hident p hys v v]
      exact (hψ (Φ p)).2.2.2.2 y (hcube (openCube_subset_closedCube n hy)) v
    · intro k
      obtain ⟨C, hC0, hCb⟩ := hC k
      refine ⟨C, hC0, fun p y hy i j => ?_⟩
      have hys : y ∈ (chart p).source := hsrc p hy
      have hfun : (fun z => (atPoint p).pullMetric g z (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1))
          =ᶠ[𝓝 y] (fun z => g'.inner (ψ (Φ p) z)
              (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ (Φ p)) z (EuclideanSpace.single i 1))
              (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (ψ (Φ p)) z (EuclideanSpace.single j 1))) := by
        filter_upwards [((chart p).open_source.mem_nhds hys)] with z hz
        exact hident p hz _ _
      have hiter := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hfun k).eq_of_nhds
      rw [hiter]
      exact hCb (Φ p) i j y (hcube hy)


private theorem classical_plateau_morrey_of_finite_lipschitz
    [I.Boundaryless] [T2Space Q]
    (g : SmoothRiemannianMetric I Q) (hdim : Module.finrank ℝ E = 3)
    (d : EMetricSpace Q)
    (htop : d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace Q))
    (hdist : ∀ p q : Q, @edist Q d.toEDist p q = riemannianEDistOf g p q)
    (hcomplete : @CompleteSpace Q d.toUniformSpace)
    (hcoords : HomogeneousCoordinates g 3)
    (gamma : Width.RegularLoop I Q)
    (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (Width.loopLift gamma.toContinuousLoop))
    (hemb : Topology.IsEmbedding (gamma : Surgery.Topology.Circle → Q))
    (himm : ∀ t, Width.loopVelocity (I := I) gamma.toContinuousLoop t ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop gamma.toContinuousLoop)
    (v : Width.LipschitzDisk g) (htracev : ∀ theta, v.map (Width.diskBoundary theta) = gamma theta)
    (hvfinite : IntegrableOn (Width.diskJacobian g v.map) (Metric.closedBall (0 : ℂ) 1)) :
    ∃ u : InteriorSmoothDisk (I := I) (Q := Q),
      u.IsConformal g ∧ u.IsHarmonic g ∧
      Width.IsSignedWeaklyMonotoneTrace u.map gamma.toContinuousLoop ∧
      IntegrableOn (Width.diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ w : Width.LipschitzDisk g,
        (∀ theta, w.map (Width.diskBoundary theta) = gamma theta) →
        Width.diskArea g u.map ≤ Width.diskArea g w.map) ∧
      ∀ w : Width.SmoothDisk (I := I) (Q := Q),
        (∀ theta, w.map (Width.diskBoundary theta) = gamma theta) →
        Width.diskArea g u.map ≤ Width.diskArea g w.map := by
  sorry

omit [CompleteSpace E] in
theorem finite_lipschitz_spanning_disk [I.Boundaryless] [T2Space Q] [CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (gamma : Width.RegularLoop I Q)
    (hctr : Surgery.Topology.IsContractibleLoop gamma.toContinuousLoop) :
    ∃ v : Width.LipschitzDisk g,
      (∀ theta, v.map (Width.diskBoundary theta) = gamma theta) ∧
      IntegrableOn (Width.diskJacobian g v.map) (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨v⟩ := Width.rfs_disk_competitor_exists g gamma.toContinuousLoop hctr
    (Width.RegularLoop.isLipschitz (I := I) g gamma)
  exact ⟨v.1, v.2, v.1.integrable_jacobian g⟩

theorem classical_plateau_morrey
    [I.Boundaryless] [T2Space Q] [CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (hdim : Module.finrank ℝ E = 3)
    (d : EMetricSpace Q)
    (htop : d.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace Q))
    (hdist : ∀ p q : Q, @edist Q d.toEDist p q = riemannianEDistOf g p q)
    (hcomplete : @CompleteSpace Q d.toUniformSpace)
    (hcoords : HomogeneousCoordinates g 3)
    (gamma : Width.RegularLoop I Q)
    (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (Width.loopLift gamma.toContinuousLoop))
    (hemb : Topology.IsEmbedding (gamma : Surgery.Topology.Circle → Q))
    (himm : ∀ t, Width.loopVelocity (I := I) gamma.toContinuousLoop t ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop gamma.toContinuousLoop) :
    ∃ u : InteriorSmoothDisk (I := I) (Q := Q),
      u.IsConformal g ∧ u.IsHarmonic g ∧
      Width.IsSignedWeaklyMonotoneTrace u.map gamma.toContinuousLoop ∧
      IntegrableOn (Width.diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ w : Width.LipschitzDisk g,
        (∀ theta, w.map (Width.diskBoundary theta) = gamma theta) →
        Width.diskArea g u.map ≤ Width.diskArea g w.map) ∧
      ∀ w : Width.SmoothDisk (I := I) (Q := Q),
        (∀ theta, w.map (Width.diskBoundary theta) = gamma theta) →
        Width.diskArea g u.map ≤ Width.diskArea g w.map := by
  obtain ⟨v, hvtrace, hvfinite⟩ := finite_lipschitz_spanning_disk g gamma hctr
  exact classical_plateau_morrey_of_finite_lipschitz g hdim d htop hdist hcomplete
    hcoords gamma hsmooth hemb himm hctr v hvtrace hvfinite

theorem classical_plateau_boundary_regularity
    [I.Boundaryless] [T2Space Q]
    (g : SmoothRiemannianMetric I Q) (hdim : Module.finrank ℝ E = 3)
    (gamma : Width.RegularLoop I Q)
    (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (Width.loopLift gamma.toContinuousLoop))
    (hemb : Topology.IsEmbedding (gamma : Surgery.Topology.Circle → Q))
    (himm : ∀ t, Width.loopVelocity (I := I) gamma.toContinuousLoop t ≠ 0)
    (u : InteriorSmoothDisk (I := I) (Q := Q))
    (hconf : u.IsConformal g) (hharm : u.IsHarmonic g)
    (htrace : Width.IsSignedWeaklyMonotoneTrace u.map gamma.toContinuousLoop)
    (hfinite : IntegrableOn (Width.diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1))
    (hmin : ∀ w : Width.SmoothDisk (I := I) (Q := Q),
      (∀ theta, w.map (Width.diskBoundary theta) = gamma theta) →
      Width.diskArea g u.map ≤ Width.diskArea g w.map) :
    ∃ w : Width.SmoothDisk (I := I) (Q := Q),
      w.map = u.map ∧ w.IsConformal g ∧ w.IsHarmonic g := by
  sorry

namespace ComponentTopology

open Surgery.Topology

private theorem image_in_component {A Q : Type*} [TopologicalSpace A]
    [ConnectedSpace A] [TopologicalSpace Q] (f : C(A, Q)) (a : A) :
    ∀ x, f x ∈ connectedComponent (f a) := by
  intro x
  exact (isPreconnected_range f.continuous).subset_connectedComponent
    (mem_range_self a) (mem_range_self x)


private theorem component_topology {Q : Type*} [TopologicalSpace Q]
    [LocallyConnectedSpace Q] [CompactSpace Q]
    (gamma : ContinuousFreeLoop Q) (hctr : IsContractibleLoop gamma) :
    ∃ U : TopologicalSpace.Opens Q,
      (U : Set Q) = connectedComponent (gamma (0 : Surgery.Topology.Circle)) ∧
      IsClosed (U : Set Q) ∧ IsCompact (U : Set Q) ∧ IsConnected (U : Set Q) ∧
      (∀ u : C(Disk, Q),
        ((∀ theta, u (diskBoundary theta) = gamma theta) ∨
          IsSignedWeaklyMonotoneTrace u gamma) → ∀ z, u z ∈ U) ∧
      ∃ gamma0 : C(Surgery.Topology.Circle, U),
        (∀ theta, (gamma0 theta : Q) = gamma theta) ∧ IsContractibleLoop gamma0 := by
  let U : TopologicalSpace.Opens Q :=
    ⟨connectedComponent (gamma (0 : Surgery.Topology.Circle)), isOpen_connectedComponent⟩
  have hgamma : ∀ theta, gamma theta ∈ U := image_in_component gamma 0
  refine ⟨U, rfl, isClosed_connectedComponent, isClosed_connectedComponent.isCompact,
    isConnected_connectedComponent, ?_, ?_⟩
  · intro u hu
    let : ConnectedSpace Disk := isConnected_iff_connectedSpace.mp
      ⟨⟨(0 : ℂ), by norm_num⟩, (convex_closedBall (0 : ℂ) 1).isPreconnected⟩
    have hboundary : u (diskBoundary (0 : Surgery.Topology.Circle)) ∈ U := by
      rcases hu with hexact | hsigned
      · rw [hexact]
        exact hgamma 0
      · obtain ⟨phi, _hcont, _hmono, htrace⟩ := hsigned
        have he := htrace (0 : ℝ)
        simp only [AddCircle.coe_zero] at he
        rw [he]
        exact hgamma (phi 0 : Surgery.Topology.Circle)
    intro z
    have hz := image_in_component u (diskBoundary (0 : Surgery.Topology.Circle)) z
    have heq : connectedComponent (u (diskBoundary (0 : Surgery.Topology.Circle))) =
        connectedComponent (gamma (0 : Surgery.Topology.Circle)) :=
      (connectedComponent_eq hboundary).symm
    rwa [heq] at hz
  · obtain ⟨q, ⟨F⟩⟩ := hctr
    have hF : ∀ p, F p ∈ U := by
      intro p
      have h := image_in_component F.toContinuousMap (0, (0 : Surgery.Topology.Circle)) p
      change F p ∈ connectedComponent (F (0, (0 : Surgery.Topology.Circle))) at h
      rw [F.apply_zero] at h
      exact h
    have hq : q ∈ U := by
      have h := hF (1, (0 : Surgery.Topology.Circle))
      rw [F.apply_one] at h
      exact h
    let gamma0 : C(Surgery.Topology.Circle, U) :=
      ⟨fun theta => ⟨gamma theta, hgamma theta⟩, gamma.continuous.subtype_mk _⟩
    refine ⟨gamma0, fun _ => rfl, ⟨⟨q, hq⟩, ?_⟩⟩
    refine ⟨{
      toFun := fun p => ⟨F p, hF p⟩
      continuous_toFun := F.continuous.subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro theta
      apply Subtype.ext
      exact F.apply_zero theta
    · intro theta
      apply Subtype.ext
      exact F.apply_one theta

end ComponentTopology

omit [IsManifold I ∞ Q] [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem plateau_component_topology
    [I.Boundaryless] [CompactSpace Q]
    (gamma : Width.RegularLoop I Q)
    (hctr : Surgery.Topology.IsContractibleLoop gamma.toContinuousLoop) :
    ∃ U : TopologicalSpace.Opens Q,
      (U : Set Q) = connectedComponent (gamma (0 : Surgery.Topology.Circle)) ∧
      IsClosed (U : Set Q) ∧ IsCompact (U : Set Q) ∧ IsConnected (U : Set Q) ∧
      (∀ u : C(Width.Disk, Q),
        ((∀ theta, u (Width.diskBoundary theta) = gamma theta) ∨
          Width.IsSignedWeaklyMonotoneTrace u gamma.toContinuousLoop) →
        ∀ z, u z ∈ U) ∧
      ∃ gamma0 : C(Surgery.Topology.Circle, U),
        (∀ theta, (gamma0 theta : Q) = gamma theta) ∧
        Surgery.Topology.IsContractibleLoop gamma0 := by
  let : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  let : LocallyConnectedSpace Q := ChartedSpace.locallyConnectedSpace H Q
  exact ComponentTopology.component_topology gamma.toContinuousLoop hctr

theorem plateau_component_disk_geometry
    [I.Boundaryless] [T2Space Q]
    (g : SmoothRiemannianMetric I Q) (U : TopologicalSpace.Opens Q)
    (hclosed : IsClosed (U : Set Q)) (hconnected : IsConnected (U : Set Q)) :
    letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    (∀ v : C(Width.Disk, U),
      ((∃ u : Width.SmoothDisk (I := I) (Q := U), u.map = v) ↔
        ∃ u : Width.SmoothDisk (I := I) (Q := Q), ∀ z, u.map z = (v z : Q))) ∧
    (∀ v : C(Width.Disk, U), Width.diskArea (g.restrictOpen U) v =
      Width.diskArea g (fun z => (v z : Q))) ∧
    ∀ (v : Width.SmoothDisk (I := I) (Q := U))
      (u : Width.SmoothDisk (I := I) (Q := Q)),
      (∀ z, u.map z = (v.map z : Q)) →
      (∀ z X, (v.differential z X : E) = (u.differential z X : E)) ∧
      (v.IsConformal (g.restrictOpen U) ↔ u.IsConformal g) ∧
      (v.IsHarmonic (g.restrictOpen U) ↔ u.IsHarmonic g) := by
  let _ := (inferInstance : CompleteSpace E)
  let _ := hclosed
  let _ := hconnected
  let : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact Width.smoothDisk_subtypeVal_iff U v
  · intro v
    exact Width.diskArea_subtypeVal g U v
  · intro v u hmap
    exact ⟨Width.differential_subtypeVal U v u hmap,
      Width.conformal_subtypeVal g U v u hmap, Width.harmonic_subtypeVal g U v u hmap⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
