import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz
import DifferentialGeometry.Analysis.Calculus.Interpolation.FiniteClosedCover
import DifferentialGeometry.Analysis.Integration.Measure.SmoothNullImage
import DifferentialGeometry.Geometry.Measure.Area.LocalReparametrization
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

private theorem chart_disk_properties {n : WithTop ℕ∞}
    (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ n) (hn : 1 ≤ n)
    (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source) :
    let K := e '' Metric.closedBall (0 : ℂ) 1
    IsCompact K ∧
      e '' Metric.ball (0 : ℂ) 1 = interior K ∧
      e '' Metric.sphere (0 : ℂ) 1 = frontier K ∧
      volume (frontier K) = 0 ∧
      ∃ A B : ℝ≥0, LipschitzOnWith A e (Metric.closedBall (0 : ℂ) 1) ∧
        LipschitzOnWith B e.symm K := by
  dsimp only
  let K := e '' Metric.closedBall (0 : ℂ) 1
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn
    (e.contMDiffOn_toFun.continuousOn.mono hsrc)
  have htarget : K ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.map_source' (hsrc hz)
  have himage : e.toOpenPartialHomeomorph.IsImage
      (Metric.closedBall (0 : ℂ) 1) K := by
    apply OpenPartialHomeomorph.IsImage.of_image_eq
    change e '' (e.source ∩ Metric.closedBall (0 : ℂ) 1) = e.target ∩ K
    rw [inter_eq_right.mpr hsrc, inter_eq_right.mpr htarget]
  have hinterior : e '' Metric.ball (0 : ℂ) 1 = interior K := by
    have h := himage.interior.image_eq
    change e '' (e.source ∩ interior (Metric.closedBall (0 : ℂ) 1)) =
      e.target ∩ interior K at h
    rw [inter_eq_right.mpr (interior_subset.trans hsrc),
      inter_eq_right.mpr (interior_subset.trans htarget),
      interior_closedBall (0 : ℂ) one_ne_zero] at h
    exact h
  have hfrontier : e '' Metric.sphere (0 : ℂ) 1 = frontier K := by
    simpa only [frontier_closedBall (0 : ℂ) one_ne_zero] using
      e.image_frontier_of_isCompact (isCompact_closedBall (0 : ℂ) 1) hsrc
  have he : ContDiffOn ℝ 1 e e.source :=
    contMDiffOn_iff_contDiffOn.mp (e.contMDiffOn_toFun.of_le hn)
  have hei : ContDiffOn ℝ 1 e.symm e.target :=
    contMDiffOn_iff_contDiffOn.mp (e.symm.contMDiffOn_toFun.of_le hn)
  have hnull : volume (frontier K) = 0 := by
    rw [← hfrontier]
    exact DifferentialGeometry.Analysis.volume_image_sphere_eq_zero_of_contDiffOn
      e.open_source he 0 1 (Metric.sphere_subset_closedBall.trans hsrc)
  obtain ⟨A, hA⟩ := he.exists_lipschitzOnWith_of_isCompact e.open_source
    (isCompact_closedBall (0 : ℂ) 1) hsrc
  obtain ⟨B, hB⟩ := hei.exists_lipschitzOnWith_of_isCompact e.open_target hK htarget
  exact ⟨hK, hinterior, hfrontier, hnull, A, B, hA, hB⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- The literal restriction of the original disk through a supplied local
source chart. No extension of that chart outside its source is chosen. -/
def diskThroughSourceChart (u : C(closedDisk, M)) {n : WithTop ℕ∞}
    (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ n)
    (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source) : C(closedDisk, M) :=
  ⟨fun z => diskExtension u (e z),
    (u.continuous.comp diskRetraction_lipschitz.continuous).comp
      (e.contMDiffOn_toFun.continuousOn.mono hsrc).domRestrict⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] in
theorem diskThroughSourceChart_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {L : ℝ≥0} (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    {n : WithTop ℕ∞} (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ n)
    (hn : 1 ≤ n) (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source) :
    ∃ K : ℝ≥0, ∀ z w, riemannianEDistOf g
      (diskThroughSourceChart u e hsrc z) (diskThroughSourceChart u e hsrc w) ≤
        (K : ℝ≥0∞) * edist z w := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  obtain ⟨_, _, _, _, A, _, hA, _⟩ := chart_disk_properties e hn hsrc
  have hU : LipschitzWith L (diskExtension u) := diskExtension_riemannian_lipschitz g huLip
  have hcomp : LipschitzOnWith (L * A) (diskExtension u ∘ e) (Metric.closedBall (0 : ℂ) 1) :=
    hU.comp_lipschitzOnWith hA
  exact ⟨L * A, fun z w => hcomp z.property w.property⟩

omit [T3Space M] in
theorem diskThroughSourceChart_range
    (u : C(closedDisk, M)) {n : WithTop ℕ∞}
    (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ n)
    (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    {W : Set M} (huW : Set.range u ⊆ W) : Set.range (diskThroughSourceChart u e hsrc) ⊆ W := by
  rintro _ ⟨z, rfl⟩
  exact huW (mem_range_self (diskRetraction (e z)))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianDiskArea_diskThroughSourceChart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {L : ℝ≥0} (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    {n : WithTop ℕ∞} (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ n)
    (hn : 1 ≤ n) (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source) :
    riemannianDiskArea g (diskThroughSourceChart u e hsrc) =
      riemannianArea g (diskExtension u) (e '' Metric.closedBall (0 : ℂ) 1) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  obtain ⟨_, hint, _, hnull, A, B, hA, hB⟩ := chart_disk_properties e hn hsrc
  have hU : LipschitzWith L (diskExtension u) := diskExtension_riemannian_lipschitz g huLip
  have hlower : ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
      edist x y ≤ (B : ℝ≥0∞) * edist (e x) (e y) := by
    intro x hx y hy
    have h := hB (mem_image_of_mem e (Metric.ball_subset_closedBall hx))
      (mem_image_of_mem e (Metric.ball_subset_closedBall hy))
    change edist (e.toPartialEquiv.symm (e x)) (e.toPartialEquiv.symm (e y)) ≤
      (B : ℝ≥0∞) * edist (e x) (e y) at h
    simpa only [e.toPartialEquiv.left_inv (hsrc (Metric.ball_subset_closedBall hx)),
      e.toPartialEquiv.left_inv (hsrc (Metric.ball_subset_closedBall hy))] using h
  change riemannianArea g (diskExtension (diskThroughSourceChart u e hsrc))
    (Metric.closedBall (0 : ℂ) 1) = _
  rw [riemannianArea_closedBall_eq_ball]
  calc
    _ = riemannianArea g (diskExtension u ∘ e) (Metric.ball (0 : ℂ) 1) := by
      apply riemannianArea_congr_on_open g Metric.isOpen_ball
      intro z hz
      exact diskExtension_coe (diskThroughSourceChart u e hsrc)
        ⟨z, Metric.ball_subset_closedBall hz⟩
    _ = riemannianArea g (diskExtension u) (e '' Metric.ball (0 : ℂ) 1) :=
      riemannianArea_precomp_on g hU Metric.isOpen_ball (hA.mono Metric.ball_subset_closedBall) hlower
    _ = riemannianArea g (diskExtension u) (interior (e '' Metric.closedBall (0 : ℂ) 1)) := by rw [hint]
    _ = _ := setIntegral_congr_set (interior_ae_eq_of_null_frontier hnull)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Paste an arbitrary genuine disk filling through one local source chart.
The metric, exact outer trace and exterior are unchanged. The area is the old
area minus the actual chart patch plus the actual filling area. -/
theorem exists_sourceChart_disk_replacement
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u d : C(closedDisk, M))
    {L C : ℝ≥0}
    (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hdLip : ∀ z w, riemannianEDistOf g (d z) (d w) ≤ (C : ℝ≥0∞) * edist z w)
    {n : WithTop ℕ∞} (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ n)
    (hn : 1 ≤ n) (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hinside : e '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension d z = diskExtension u (e z))
    {W : Set M} (huW : Set.range u ⊆ W) (hdW : Set.range d ⊆ W) :
    let K := e '' Metric.closedBall (0 : ℂ) 1
    ∃ (v : C(closedDisk, M)) (A : ℝ≥0),
      (∀ z w, riemannianEDistOf g (v z) (v w) ≤ (A : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      (∀ z : closedDisk, (z : ℂ) ∈ K → v z = diskExtension d (e.symm z)) ∧
      (∀ z : closedDisk, (z : ℂ) ∉ interior K → v z = u z) ∧
      riemannianDiskArea g v = riemannianDiskArea g u -
        riemannianArea g (diskExtension u) K + riemannianDiskArea g d := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let U := diskExtension u
  let D := diskExtension d
  let K := e '' Metric.closedBall (0 : ℂ) 1
  obtain ⟨hK, hint, hfront, hnull, A, B, hA, hB⟩ := chart_disk_properties e hn hsrc
  have hinv : MapsTo e.symm K (Metric.closedBall (0 : ℂ) 1) := by
    rintro _ ⟨z, hz, rfl⟩
    change e.toPartialEquiv.symm (e z) ∈ Metric.closedBall (0 : ℂ) 1
    simpa only [e.toPartialEquiv.left_inv (hsrc hz)] using hz
  have heinv (z : ℂ) (hz : z ∈ K) : e (e.symm z) = z := by
    obtain ⟨q, hq, rfl⟩ := hz
    exact congrArg (e : ℂ → ℂ) (e.toPartialEquiv.left_inv (hsrc hq))
  have hlower : ∀ x ∈ K, ∀ y ∈ K,
      edist x y ≤ (A : ℝ≥0∞) * edist (e.symm x) (e.symm y) := by
    intro x hx y hy
    simpa only [heinv x hx, heinv y hy] using hA (hinv hx) (hinv hy)
  have hinvinterior : e.symm '' interior K = Metric.ball (0 : ℂ) 1 := by
    rw [← hint]
    ext z
    constructor
    · rintro ⟨x, ⟨q, hq, rfl⟩, heq⟩
      change e.toPartialEquiv.symm (e q) = z at heq
      rw [e.toPartialEquiv.left_inv (hsrc (Metric.ball_subset_closedBall hq))] at heq
      exact heq ▸ hq
    · intro hz
      exact ⟨e z, ⟨z, hz, rfl⟩, e.toPartialEquiv.left_inv (hsrc (Metric.ball_subset_closedBall hz))⟩
  have hmatch : EqOn (D ∘ e.symm) U (frontier K) := by
    intro x hx
    rw [← hfront] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    change D (e.toPartialEquiv.symm (e z)) = U (e z)
    rw [e.toPartialEquiv.left_inv (hsrc (Metric.sphere_subset_closedBall hz))]
    exact hboundary z hz
  have hULip : LipschitzWith L U := diskExtension_riemannian_lipschitz g huLip
  have hDLip : LipschitzWith C D := diskExtension_riemannian_lipschitz g hdLip
  have hcopiedLip : LipschitzOnWith (C * B) (D ∘ e.symm) K :=
    hDLip.comp_lipschitzOnWith hB
  let F : ℂ → M := K.piecewise (D ∘ e.symm) U
  have hFinner : EqOn F (D ∘ e.symm) K := fun _ hz => piecewise_eq_of_mem _ _ _ hz
  have hFouter : EqOn F U (interior K)ᶜ := by
    intro z hz
    by_cases hzK : z ∈ K
    · exact (hFinner hzK).trans (hmatch ((mem_frontier_iff_notMem_interior hzK).mpr hz))
    · exact piecewise_eq_of_notMem _ _ _ hzK
  let cells : Bool → Set ℂ := fun b => if b then (interior K)ᶜ else K
  let constants : Bool → ℝ≥0 := fun b => if b then L else C * B
  have hcellsClosed : ∀ b, IsClosed ((Subtype.val : closedDisk → ℂ) ⁻¹' cells b) := by
    intro b
    cases b
    · exact hK.isClosed.preimage continuous_subtype_val
    · exact isOpen_interior.isClosed_compl.preimage continuous_subtype_val
  have hcover : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∃ b, z ∈ cells b := by
    intro z _
    by_cases hz : z ∈ K
    · exact ⟨false, hz⟩
    · exact ⟨true, fun hi => hz (interior_subset hi)⟩
  have hcellLip : ∀ b, LipschitzOnWith (constants b) F
      (Metric.closedBall (0 : ℂ) 1 ∩ cells b) := by
    intro b
    cases b
    · intro x hx y hy
      rw [hFinner hx.2, hFinner hy.2]
      exact hcopiedLip hx.2 hy.2
    · intro x hx y hy
      rw [hFouter hx.2, hFouter hy.2]
      exact hULip x y
  have hFLip : LipschitzOnWith (Finset.univ.sup constants) F
      (Metric.closedBall (0 : ℂ) 1) :=
    DifferentialGeometry.Analysis.lipschitzOnWith_of_finite_closed_cover
      (convex_closedBall (0 : ℂ) 1) cells hcellsClosed hcover constants hcellLip
  let v : C(closedDisk, M) := ⟨fun z => F z, hFLip.to_restrict.continuous⟩
  have hvLip : ∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤
      ((Finset.univ.sup constants : ℝ≥0) : ℝ≥0∞) * edist z w :=
    fun z w => hFLip z.property w.property
  have hvinner (z : closedDisk) (hz : (z : ℂ) ∈ K) : v z = D (e.symm z) :=
    hFinner hz
  have hvouter (z : closedDisk) (hz : (z : ℂ) ∉ interior K) : v z = u z :=
    (hFouter hz).trans (diskExtension_coe u z)
  have hvtrace : diskTrace v = diskTrace u := by
    ext θ
    change v (diskBoundary θ) = u (diskBoundary θ)
    apply hvouter
    intro hz
    have hin := hinside (interior_subset hz)
    have hn : ‖(diskBoundary θ : ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hin
    have heq : ‖((diskBoundary θ : closedDisk) : ℂ)‖ = 1 := Circle.norm_coe _
    exact (not_lt_of_ge heq.ge) hn
  have hvW : Set.range v ⊆ W := by
    rintro _ ⟨z, rfl⟩
    by_cases hz : (z : ℂ) ∈ K
    · rw [hvinner z hz]
      let q : closedDisk := ⟨e.symm z, hinv hz⟩
      have heq : D (e.symm z) = d q := diskExtension_coe d q
      rw [heq]
      exact hdW (mem_range_self q)
    · rw [hvouter z (fun hi => hz (interior_subset hi))]
      exact huW (mem_range_self z)
  have hKD : K ⊆ Metric.closedBall (0 : ℂ) 1 := hinside.trans Metric.ball_subset_closedBall
  have hinsArea : riemannianArea g (diskExtension v) K = riemannianDiskArea g d := by
    calc
      _ = riemannianArea g (diskExtension v) (interior K) :=
        setIntegral_congr_set (interior_ae_eq_of_null_frontier hnull).symm
      _ = riemannianArea g (D ∘ e.symm) (interior K) := by
        apply riemannianArea_congr_on_open g isOpen_interior
        intro z hz
        let q : closedDisk := ⟨z, hKD (interior_subset hz)⟩
        exact (diskExtension_coe v q).trans (hvinner q (interior_subset hz))
      _ = riemannianArea g D (e.symm '' interior K) :=
        riemannianArea_precomp_on g hDLip isOpen_interior (hB.mono interior_subset)
          (fun x hx y hy => hlower x (interior_subset hx) y (interior_subset hy))
      _ = riemannianArea g D (Metric.ball (0 : ℂ) 1) := by rw [hinvinterior]
      _ = riemannianDiskArea g d := (riemannianArea_closedBall_eq_ball g D 0 1).symm
  have hiu : IntegrableOn (riemannianAreaDensity g U) (Metric.closedBall (0 : ℂ) 1) :=
    integrable_riemannianDiskAreaDensity g huLip
  have hiv : IntegrableOn (riemannianAreaDensity g (diskExtension v))
      (Metric.closedBall (0 : ℂ) 1) := integrable_riemannianDiskAreaDensity g hvLip
  have houtArea :
      (∫ z in Metric.closedBall (0 : ℂ) 1 \ K,
        riemannianAreaDensity g (diskExtension v) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1 \ K, riemannianAreaDensity g U z := by
    have hzint : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1 \ K),
        z ∈ Metric.ball (0 : ℂ) 1 :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset ae_disk_interior
    apply integral_congr_ae
    filter_upwards [hzint,
      ae_restrict_mem (measurableSet_closedBall.diff hK.measurableSet)] with z hz hzd
    apply riemannianAreaDensity_congr g
    filter_upwards [(Metric.isOpen_ball.inter hK.isClosed.isOpen_compl).mem_nhds
      ⟨hz, hzd.2⟩] with y hy
    let q : closedDisk := ⟨y, Metric.ball_subset_closedBall hy.1⟩
    exact (diskExtension_coe v q).trans
      ((hvouter q (fun hi => hy.2 (interior_subset hi))).trans (diskExtension_coe u q).symm)
  have harea : riemannianDiskArea g v = riemannianDiskArea g u -
      riemannianArea g U K + riemannianDiskArea g d := by
    have hsu := setIntegral_sdiff hK.measurableSet hiu hKD
    have hsv := setIntegral_sdiff hK.measurableSet hiv hKD
    change (∫ z in K, riemannianAreaDensity g (diskExtension v) z) =
      riemannianDiskArea g d at hinsArea
    rw [houtArea, hinsArea, hsu] at hsv
    change (∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity g (diskExtension v) z) =
      (∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity g U z) -
        (∫ z in K, riemannianAreaDensity g U z) + riemannianDiskArea g d
    linarith
  exact ⟨v, Finset.univ.sup constants, hvLip, hvtrace, hvW, hvinner, hvouter, harea⟩

omit [T3Space M] in
private theorem diskExtension_eq_on_sphere_of_trace_eq
    {u v : C(closedDisk, M)} (htrace : diskTrace u = diskTrace v) :
    EqOn (diskExtension u) (diskExtension v) (Metric.sphere (0 : ℂ) 1) := by
  intro z hz
  let c : Circle := ⟨z, hz⟩
  obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
  have hc : AddCircle.toCircle θ = c :=
    (AddCircle.homeomorphCircle_apply one_ne_zero θ).symm.trans hθ
  let q : closedDisk := ⟨z, Metric.sphere_subset_closedBall hz⟩
  have hq : diskBoundary θ = q := by
    apply Subtype.ext
    exact congrArg (fun a : Circle => (a : ℂ)) hc
  have heq := congrArg (fun γ : freeLoop M => γ θ) htrace
  change u (diskBoundary θ) = v (diskBoundary θ) at heq
  rw [hq] at heq
  exact (diskExtension_coe u q).trans (heq.trans (diskExtension_coe v q).symm)

/-- Strict improvement of the literal chart restriction transfers to the
original disk without choosing any global source reparameterization. -/
theorem exists_disk_area_lt_of_sourceChart_competitor
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u d : C(closedDisk, M))
    {L C : ℝ≥0}
    (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (hdLip : ∀ z w, riemannianEDistOf g (d z) (d w) ≤ (C : ℝ≥0∞) * edist z w)
    {n : WithTop ℕ∞} (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ n)
    (hn : 1 ≤ n) (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hinside : e '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (htrace : diskTrace d = diskTrace (diskThroughSourceChart u e hsrc))
    {W : Set M} (huW : Set.range u ⊆ W) (hdW : Set.range d ⊆ W)
    (harea : riemannianDiskArea g d < riemannianDiskArea g (diskThroughSourceChart u e hsrc)) :
    ∃ (v : C(closedDisk, M)) (K : ℝ≥0),
      (∀ z w, riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      riemannianDiskArea g v < riemannianDiskArea g u := by
  have hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension d z = diskExtension u (e z) := by
    intro z hz
    exact (diskExtension_eq_on_sphere_of_trace_eq htrace hz).trans
      (diskExtension_coe (diskThroughSourceChart u e hsrc)
        ⟨z, Metric.sphere_subset_closedBall hz⟩)
  obtain ⟨v, K, hvLip, hvtrace, hvW, _, _, hvarea⟩ :=
    exists_sourceChart_disk_replacement g u d huLip hdLip e hn hsrc hinside hboundary huW hdW
  have hlocalArea := riemannianDiskArea_diskThroughSourceChart g u huLip e hn hsrc
  exact ⟨v, K, hvLip, hvtrace, hvW, by linarith⟩

end DifferentialGeometry.Geometry
