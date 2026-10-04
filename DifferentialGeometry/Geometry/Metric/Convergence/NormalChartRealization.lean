import DifferentialGeometry.Geometry.Metric.Convergence.PointedAtlasRealization
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
noncomputable section
open Bundle Set Filter Topology Manifold Metric
open scoped ContDiff NNReal ENNReal
open DifferentialGeometry.Geometry (pullbackMetricCoefficients)
open DifferentialGeometry.CheegerGromovCompactness (MapCPConvergenceOn
  tendstoUniformlyOn_of_cPConvergence)
namespace GC.MetricGeometry

private theorem exists_extension_of_closedBall {E X : Type*} [NormedAddCommGroup E]
    (x₀ : X) {δ : ℝ} (g : closedBall (0 : E) δ → X) :
    ∃ L : E → X, ∀ u (hu : u ∈ closedBall (0 : E) δ), L u = g ⟨u, hu⟩ := by
  classical
  refine ⟨fun u => if hu : u ∈ closedBall (0 : E) δ then g ⟨u, hu⟩ else x₀, fun u hu => ?_⟩
  exact dite_eq_left hu

private theorem tendstoUniformlyOn_closedBall_of_tendstoUniformly
    {E X : Type*} [NormedAddCommGroup E] [MetricSpace X]
    {δ : ℝ} {G : ℕ → E → X} {g : closedBall (0 : E) δ → X} {L : E → X}
    (hconv : TendstoUniformly (fun i (u : closedBall (0 : E) δ) => G i u) g atTop)
    (hL : ∀ u (hu : u ∈ closedBall (0 : E) δ), L u = g ⟨u, hu⟩) :
    TendstoUniformlyOn G L atTop (closedBall 0 δ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [Metric.tendstoUniformly_iff.mp hconv η hη] with i hi
  intro u hu
  have h := hi ⟨u, hu⟩
  rw [hL u hu]
  exact h

private theorem tendstoUniformlyOn_of_mapCPConvergenceOn_subset
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D S : Set E} {p : ℕ} {Φ : ℕ → E → F} {Φinf : E → F}
    (h : MapCPConvergenceOn D p Φ Φinf) (hSD : S ⊆ D) :
    TendstoUniformlyOn Φ Φinf atTop S :=
  (tendstoUniformlyOn_of_cPConvergence (h.mono_order (Nat.zero_le p))).mono hSD

private theorem contMDiffOn_and_ball_image_of_radial_partialDiffeomorph
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace M] [ChartedSpace E M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) (z : M) {r ρ : ℝ} (hρr : ρ ≤ r)
    (hΦs : Φ.source = ball 0 r) (hΦ0 : Φ 0 = z)
    (hrad : ∀ w ∈ ball (0 : E) r, dist (Φ w) z = ‖w‖)
    (himage : ∀ t ≤ r, (Φ : E → M) '' ball 0 t = ball z t) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1 Φ.toOpenPartialHomeomorph
        Φ.toOpenPartialHomeomorph.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1 Φ.toOpenPartialHomeomorph.symm
        Φ.toOpenPartialHomeomorph.target ∧
      ball (0 : E) ρ ⊆ Φ.toOpenPartialHomeomorph.source ∧
      (Φ.toOpenPartialHomeomorph : E → M) '' ball 0 ρ =
        ball (Φ.toOpenPartialHomeomorph 0) ρ ∧
      ∀ x ∈ ball (0 : E) ρ,
        dist (Φ.toOpenPartialHomeomorph x) (Φ.toOpenPartialHomeomorph 0) = ‖x‖ := by
  refine ⟨Φ.contMDiffOn_toFun.of_le (by decide), Φ.contMDiffOn_invFun.of_le (by decide),
    fun x hx => ?_, ?_, fun x hx => ?_⟩
  · have hx' : x ∈ Φ.source := by
      rw [hΦs]
      exact ball_subset_ball hρr hx
    exact hx'
  · exact (himage ρ hρr).trans (congrArg (fun y => ball y ρ) hΦ0.symm)
  · exact (congrArg (fun y => dist (Φ x) y) hΦ0).trans (hrad x (ball_subset_ball hρr hx))

theorem exists_unique_metric_of_normal_chart_limits
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace X]
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)]
    (hX : ∀ x y : X, Metric.intrinsicEDist x y = edist x y) (K : ℕ)
    (p : X) (o : ∀ i, Y i) {R ε : ℕ → ℝ}
    (F : ∀ i, PointedBallApprox (o i) p (R i) (ε i)) (hε : Tendsto ε atTop (𝓝 0))
    (g : ∀ i, DifferentialGeometry.SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    (hg : ∀ i, letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : Y i → Type _) :=
      ⟨(g i).toRiemannianMetric⟩; IsRiemannianManifold 𝓘(ℝ, E) (Y i))
    (a : ι → ℝ) (ha : ∀ j, 0 < a j)
    (Φ : ι → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞) (z : ι → ∀ i, Y i)
    (hΦs : ∀ j i, (Φ j i).source = ball 0 (2 * a j)) (hΦ0 : ∀ j i, Φ j i 0 = z j i)
    (hrad : ∀ j i, ∀ w ∈ ball (0 : E) (2 * a j), dist (Φ j i w) (z j i) = ‖w‖)
    (himage : ∀ j i, ∀ t ≤ 2 * a j, (Φ j i : E → Y i) '' ball 0 t = ball (z j i) t)
    (hlower : ∀ j i, ∀ w ∈ closedBall (0 : E) (a j), ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients (g i) (Φ j i) w v v)
    (gl : ∀ j, closedBall (0 : E) (a j / 8) → X)
    (hmem : ∀ j, ∀ᶠ i in atTop, ∀ u : closedBall (0 : E) (a j / 8),
      Φ j i u ∈ closedBall (o i) (R i))
    (hconv : ∀ j, TendstoUniformly (fun i (u : closedBall (0 : E) (a j / 8)) =>
      (F i).extendToWholeSpace (Φ j i u)) (gl j) atTop)
    (ψ : ι → OpenPartialHomeomorph E X) (hψs : ∀ j, (ψ j).source = ball 0 (a j / 16))
    (hcover : ∀ x, ∃ j, x ∈ (ψ j).target)
    (hψmap : ∀ j, ∀ u : ball (0 : E) (a j / 16), ψ j u = gl j ⟨u, (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith [ha j]))) u.property⟩)
    (b : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ j, ContDiffOn ℝ (K - 1 : ℕ) (b j) (ball 0 (a j)))
    (hbconv : ∀ j, ∀ D : Set E, IsCompact D → D ⊆ ball 0 (a j) →
      MapCPConvergenceOn D (K - 1) (fun i => pullbackMetricCoefficients (g i) (Φ j i)) (b j))
    (hcompat : ∀ j d u, u ∈ ((ψ j).symm.symm.trans (ψ d).symm).source →
      b j u = (b d (((ψ j).symm.symm.trans (ψ d).symm) u)).bilinearComp
        (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u)
        (fderiv ℝ ((ψ j).symm.symm.trans (ψ d).symm) u))
    (htrans : ∀ j d, ContDiffOn ℝ ((K - 1 + 1 : ℕ) : ℕ∞ω) ((ψ j).symm.symm.trans (ψ d).symm)
      ((ψ j).symm.symm.trans (ψ d).symm).source) :
    letI := DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover
      (fun j => (ψ j).symm) hcover
    letI := DifferentialGeometry.Topology.Manifold.isManifold_chartedSpaceOfOpenCover
      (fun j => (ψ j).symm) hcover htrans
    letI : IsManifold 𝓘(ℝ, E) 1 X := IsManifold.of_le (n := ((K - 1 + 1 : ℕ) : ℕ∞ω))
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (K - 1)))
    ∃! G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
        (TangentSpace 𝓘(ℝ, E) : X → Type _),
      (∀ j x, x ∈ (ψ j).symm.source → ∀ v w : E,
        G.inner x v w = b j ((ψ j).symm x)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm x v)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (ψ j).symm x w)) ∧
      (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : X → Type _) :=
        ⟨G.toRiemannianMetric⟩
       IsRiemannianManifold 𝓘(ℝ, E) X) := by
  have hin (j : ι) (i : ℕ) := contMDiffOn_and_ball_image_of_radial_partialDiffeomorph (Φ j i) (z j i)
    (by linarith [ha j] : a j / 2 ≤ 2 * a j) (hΦs j i) (hΦ0 j i) (hrad j i) (himage j i)
  choose L hL using fun j : ι => exists_extension_of_closedBall p (gl j)
  have htgt (j : ι) : (ψ j).symm.target ⊆ ball (0 : E) (a j / 2 / 8) := by
    intro u hu
    have hu' : u ∈ (ψ j).source := hu
    rw [hψs j] at hu'
    exact ball_subset_ball (le_of_eq (by ring)) hu'
  have hbs (j : ι) : ContDiffOn ℝ (K - 1 : ℕ) (b j) (ball (0 : E) (a j / 2)) :=
    (hb j).mono (ball_subset_ball (by linarith [ha j]))
  have hcv (j : ι) : TendstoUniformlyOn
      (fun i => pullbackMetricCoefficients (g i) (Φ j i).toOpenPartialHomeomorph) (b j) atTop
      (ball (0 : E) (a j / 2)) :=
    tendstoUniformlyOn_of_mapCPConvergenceOn_subset
      (hbconv j (closedBall 0 (a j / 2)) (isCompact_closedBall 0 (a j / 2))
        (closedBall_subset_ball (by linarith [ha j]))) ball_subset_closedBall
  have hlow (j : ι) : ∀ᶠ i in atTop, ∀ x ∈ ball (0 : E) (a j / 2), ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
        pullbackMetricCoefficients (g i) (Φ j i).toOpenPartialHomeomorph x v v :=
    Eventually.of_forall fun i x hx v => hlower j i x
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [ha j]))) hx) v
  have hdom (j : ι) : ∀ᶠ i in atTop, ∀ w ∈ closedBall (0 : E) (a j / 2 / 4),
      (Φ j i).toOpenPartialHomeomorph w ∈ closedBall (o i) (R i) := by
    filter_upwards [hmem j] with i hi w hw
    exact hi ⟨w, closedBall_subset_closedBall (le_of_eq (by ring)) hw⟩
  have hmap (j : ι) : TendstoUniformlyOn
      (fun i w => (F i).extendToWholeSpace ((Φ j i).toOpenPartialHomeomorph w)) (L j) atTop
      (closedBall (0 : E) (a j / 2 / 4)) := by
    have h8 : a j / 2 / 4 = a j / 8 := by ring
    rw [h8]
    exact tendstoUniformlyOn_closedBall_of_tendstoUniformly
      (G := fun i w => (F i).extendToWholeSpace (Φ j i w)) (hconv j) (hL j)
  have hch (j : ι) : EqOn (ψ j).symm.symm (L j) (ψ j).symm.target := by
    intro u hu
    have hu' : u ∈ ball (0 : E) (a j / 16) := by
      have h : u ∈ (ψ j).source := hu
      rw [hψs j] at h
      exact h
    have hm := hψmap j ⟨u, hu'⟩
    have hl := hL j u ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith [ha j]))) hu')
    exact hm.trans hl.symm
  exact DifferentialGeometry.Geometry.Metric.exists_unique_contMDiffMetric_of_pointed_atlas_limits
    (l := atTop) (M := Y) (I := 𝓘(ℝ, E)) hX (K - 1) (fun j => (ψ j).symm) hcover htrans
    (fun j => a j / 2) (fun j => div_pos (ha j) two_pos) htgt g hg
    (fun j i => (Φ j i).toOpenPartialHomeomorph)
    (fun j => Eventually.of_forall fun i => (hin j i).1)
    (fun j => Eventually.of_forall fun i => (hin j i).2.1)
    (fun j => Eventually.of_forall fun i => (hin j i).2.2.1)
    (fun j => Eventually.of_forall fun i => (hin j i).2.2.2.1)
    (fun j => Eventually.of_forall fun i => (hin j i).2.2.2.2)
    b hbs hcv (fun _ => 1 / 2) (fun _ => one_half_pos) hlow hcompat o p F hε L hdom hmap hch

end GC.MetricGeometry
