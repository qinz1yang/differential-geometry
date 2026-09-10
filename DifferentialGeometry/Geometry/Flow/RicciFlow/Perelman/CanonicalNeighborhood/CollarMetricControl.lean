import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold MeasureTheory Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

section Maps

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricPathELength_map_le (h : SmoothRiemannianMetric J N)
    (g : SmoothRiemannianMetric I M) (F : N → M)
    {gamma : ℝ → N} {a b L : ℝ} (hL : 0 ≤ L)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) J 1 gamma (Icc a b))
    (hF : ∀ s ∈ Ioo a b, MDifferentiableAt J I F (gamma s))
    (hupper : ∀ s ∈ Ioo a b, ∀ v : TangentSpace J (gamma s),
      g.inner (F (gamma s)) (mfderiv J I F (gamma s) v)
        (mfderiv J I F (gamma s) v) ≤ L ^ 2 * h.inner (gamma s) v v) :
    metricPathELength g (F ∘ gamma) a b ≤
      ENNReal.ofReal L * metricPathELength h gamma a b := by
  rw [metricPathELength_eq, metricPathELength_eq,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  have hgd := (hgamma.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  rw [← ENNReal.ofReal_mul hL]
  apply ENNReal.ofReal_le_ofReal
  change Real.sqrt (g.inner (F (gamma s))
    (mfderiv 𝓘(ℝ, ℝ) I (F ∘ gamma) s 1)
    (mfderiv 𝓘(ℝ, ℝ) I (F ∘ gamma) s 1)) ≤ _
  rw [mfderiv_comp_apply s (hF s hs) hgd]
  calc
    _ ≤ Real.sqrt (L ^ 2 * h.inner (gamma s)
        (mfderiv 𝓘(ℝ, ℝ) J gamma s 1) (mfderiv 𝓘(ℝ, ℝ) J gamma s 1)) :=
      Real.sqrt_le_sqrt (hupper s hs _)
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricPathELength_map_ge (h : SmoothRiemannianMetric J N)
    (g : SmoothRiemannianMetric I M) (F : N → M)
    {gamma : ℝ → N} {a b L : ℝ} (hL : 0 ≤ L)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) J 1 gamma (Icc a b))
    (hF : ∀ s ∈ Ioo a b, MDifferentiableAt J I F (gamma s))
    (hlower : ∀ s ∈ Ioo a b, ∀ v : TangentSpace J (gamma s),
      L ^ 2 * h.inner (gamma s) v v ≤
        g.inner (F (gamma s)) (mfderiv J I F (gamma s) v)
          (mfderiv J I F (gamma s) v)) :
    ENNReal.ofReal L * metricPathELength h gamma a b ≤
      metricPathELength g (F ∘ gamma) a b := by
  rw [metricPathELength_eq, metricPathELength_eq,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  have hgd := (hgamma.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  rw [← ENNReal.ofReal_mul hL]
  apply ENNReal.ofReal_le_ofReal
  change _ ≤ Real.sqrt (g.inner (F (gamma s))
    (mfderiv 𝓘(ℝ, ℝ) I (F ∘ gamma) s 1)
    (mfderiv 𝓘(ℝ, ℝ) I (F ∘ gamma) s 1))
  rw [mfderiv_comp_apply s (hF s hs) hgd]
  calc
    _ = Real.sqrt (L ^ 2 * h.inner (gamma s)
        (mfderiv 𝓘(ℝ, ℝ) J gamma s 1) (mfderiv 𝓘(ℝ, ℝ) J gamma s 1)) := by
      rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]
    _ ≤ _ := Real.sqrt_le_sqrt (hlower s hs _)

end Maps

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CylinderReference.height_edist_le (C : CylinderReference) (x y : Cylinder) :
    ENNReal.ofReal |x.2 - y.2| ≤ riemannianEDistOf (C.metric 0) x y := by
  apply ofReal_abs_sub_le_riemannianEDistOf (C.metric 0) Prod.snd contMDiff_snd
  intro z v
  change (show ℝ from mfderiv IC 𝓘(ℝ, ℝ) Prod.snd z v) *
    (show ℝ from mfderiv IC 𝓘(ℝ, ℝ) Prod.snd z v) ≤ _
  rw [mfderiv_snd, C.inner_eq 0 le_rfl]
  change v.2 * v.2 ≤ 2 * (1 - 0) * inner ℝ
    (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) z.1 v.1)
    (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) z.1 v.1) + v.2 * v.2
  nlinarith [real_inner_self_nonneg (x :=
    (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) z.1 v.1))]

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem collar_pathELength_bounds (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hzero : 0 ∈ times)
    (hsource : U ⊆ F.source) {gamma : ℝ → Cylinder} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) IC 1 gamma (Icc a b))
    (hU : ∀ s ∈ Icc a b, gamma s ∈ U) :
    ENNReal.ofReal (Real.sqrt (1 - eps)) * metricPathELength (C.metric 0) gamma a b ≤
        metricPathELength (g 0) ((F : Cylinder → M) ∘ gamma) a b ∧
      metricPathELength (g 0) ((F : Cylinder → M) ∘ gamma) a b ≤
        ENNReal.ofReal (Real.sqrt (1 + eps)) * metricPathELength (C.metric 0) gamma a b := by
  have hFd : ∀ s ∈ Ioo a b, MDifferentiableAt IC I3 F (gamma s) := by
    intro s hs
    exact (F.contMDiffOn_toFun.contMDiffAt
      (F.open_source.mem_nhds (hsource (hU s ⟨hs.1.le, hs.2.le⟩)))).mdifferentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  constructor
  · apply metricPathELength_map_ge (C.metric 0) (g 0) (F : Cylinder → M)
      (Real.sqrt_nonneg _) hgamma hFd
    intro s hs v
    rw [Real.sq_sqrt (sub_nonneg.mpr heps1)]
    have hh := (cmp.equivalence 0 hzero (gamma s) (hU s ⟨hs.1.le, hs.2.le⟩) v).1
    rwa [hmetric, cmp.pullback_eq 0 (gamma s) (hU s ⟨hs.1.le, hs.2.le⟩)] at hh
  · apply metricPathELength_map_le (C.metric 0) (g 0) (F : Cylinder → M)
      (Real.sqrt_nonneg _) hgamma hFd
    intro s hs v
    rw [Real.sq_sqrt (by linarith : 0 ≤ 1 + eps)]
    have hh := (cmp.equivalence 0 hzero (gamma s) (hU s ⟨hs.1.le, hs.2.le⟩) v).2
    rwa [hmetric, cmp.pullback_eq 0 (gamma s) (hU s ⟨hs.1.le, hs.2.le⟩)] at hh

theorem collar_crossing_length_lower (C : CylinderReference)
    (g : ℝ → SmoothRiemannianMetric I3 M) (F : PartialDiffeomorph IC I3 Cylinder M ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    {h : ℝ → SmoothRiemannianMetric IC Cylinder}
    (cmp : MetricComparisonOn h g F U times order eps) (hmetric : h 0 = C.metric 0)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hzero : 0 ∈ times)
    (hsource : U ⊆ F.source) {gamma : ℝ → Cylinder} {a b : ℝ} (hab : a ≤ b)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) IC 1 gamma (Icc a b))
    (hU : ∀ s ∈ Icc a b, gamma s ∈ U) :
    ENNReal.ofReal (Real.sqrt (1 - eps) * |(gamma a).2 - (gamma b).2|) ≤
      metricPathELength (g 0) ((F : Cylinder → M) ∘ gamma) a b := by
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact (mul_le_mul' le_rfl ((C.height_edist_le (gamma a) (gamma b)).trans
    (edistOf_le_metricPathELength (C.metric 0) hab hgamma))).trans
      (collar_pathELength_bounds C g F cmp hmetric heps heps1 hzero hsource hgamma hU).1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CylinderReference.transverse_length_le (C : CylinderReference)
    (z : ℝ) {gamma : ℝ → Sphere 2} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I2 1 gamma (Icc a b)) :
    metricPathELength (C.metric 0) (fun s => (gamma s, z)) a b ≤
      ENNReal.ofReal (Real.sqrt 2) *
        metricPathELength (Geometry.roundMetric (E := ThreeSpace) (n := 2)) gamma a b := by
  apply metricPathELength_map_le
    (Geometry.roundMetric (E := ThreeSpace) (n := 2)) (C.metric 0)
    (fun y : Sphere 2 => (y, z)) (Real.sqrt_nonneg _) hgamma
    (fun _ _ => mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  intro s _hs v
  let w : TangentSpace IC (gamma s, z) := (v, (0 : ℝ))
  have hder : mfderiv I2 IC (fun y : Sphere 2 => (y, z)) (gamma s) v = w := by
    rw [mfderiv_prod_left]
    rfl
  have hinner : (C.metric 0).inner (gamma s, z) w w =
      2 * (Geometry.roundMetric (E := ThreeSpace) (n := 2)).inner (gamma s) v v := by
    rw [C.inner_eq 0 le_rfl, Geometry.roundMetric_inner]
    change 2 * (1 - 0) * inner ℝ (Geometry.dIncl (E := ThreeSpace) (n := 2) (gamma s) v)
      (Geometry.dIncl (E := ThreeSpace) (n := 2) (gamma s) v) + (0 : ℝ) * 0 =
      2 * inner ℝ (Geometry.dIncl (E := ThreeSpace) (n := 2) (gamma s) v)
        (Geometry.dIncl (E := ThreeSpace) (n := 2) (gamma s) v)
    ring
  rw [hder, hinner,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_roundSphere_path_length_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ x y : Sphere 2,
      ∃ gamma : ℝ → Sphere 2, gamma 0 = x ∧ gamma 1 = y ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I2 1 gamma (Icc (0 : ℝ) 1) ∧
        metricPathELength (Geometry.roundMetric (E := ThreeSpace) (n := 2)) gamma 0 1 <
          ENNReal.ofReal B := by
  let h := Geometry.roundMetric (E := ThreeSpace) (n := 2)
  let : RiemannianBundle (fun x : Sphere 2 => TangentSpace I2 x) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 2))
      (fun x : Sphere 2 => TangentSpace I2 x) :=
    ⟨⟨h.inner, h.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
      (by simp [ThreeSpace] : 1 < Module.finrank ℝ ThreeSpace)) (0 : ThreeSpace)
      (by norm_num : (0 : ℝ) ≤ 1))
  let p : Sphere 2 := Classical.arbitrary _
  have hfinite (x y : Sphere 2) : Manifold.riemannianEDist I2 x y ≠ ⊤ :=
    Geometry.Riemannian.Exponential.riemannianEDist_ne_top (I := I2) x y
  have hcont : Continuous (fun x : Sphere 2 => (Manifold.riemannianEDist I2 p x).toReal) := by
    have hc : Continuous (fun x : Sphere 2 => Manifold.riemannianEDist I2 p x) :=
      (Geometry.Riemannian.Exponential.continuous_riemannianEDist_to (I := I2) p).congr
        (fun _ => Manifold.riemannianEDist_comm)
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ENNReal.continuousAt_toReal (hfinite p x)).comp hc.continuousAt
  obtain ⟨B, hB⟩ := (isCompact_univ : IsCompact (univ : Set (Sphere 2))).bddAbove_image hcont.continuousOn
  have hradial (x : Sphere 2) : Manifold.riemannianEDist I2 p x ≤ ENNReal.ofReal (max B 0) := by
    rw [← ENNReal.ofReal_toReal (hfinite p x)]
    exact ENNReal.ofReal_le_ofReal ((hB ⟨x, mem_univ _, rfl⟩).trans (le_max_left B 0))
  refine ⟨2 * max B 0 + 1, by positivity, ?_⟩
  intro x y
  apply exists_lt_of_edistOf_lt h
  change Manifold.riemannianEDist I2 x y < _
  calc
    _ ≤ Manifold.riemannianEDist I2 x p + Manifold.riemannianEDist I2 p y :=
      Manifold.riemannianEDist_triangle
    _ = Manifold.riemannianEDist I2 p x + Manifold.riemannianEDist I2 p y := by
      rw [Manifold.riemannianEDist_comm (I := I2) (x := x) (y := p)]
    _ ≤ ENNReal.ofReal (max B 0) + ENNReal.ofReal (max B 0) := add_le_add (hradial x) (hradial y)
    _ = ENNReal.ofReal (2 * max B 0) := by
      rw [two_mul, ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)

theorem exists_uniform_transverse_shortcuts :
    ∃ D : ℝ, 0 < D ∧ ∀ (C : CylinderReference) (h : ℝ → SmoothRiemannianMetric IC Cylinder)
      (g : ℝ → SmoothRiemannianMetric I3 M)
      (F : PartialDiffeomorph IC I3 Cylinder M ∞)
      (U : Set Cylinder) (times : Set ℝ) (order : ℕ) (eps z : ℝ),
      MetricComparisonOn h g F U times order eps → h 0 = C.metric 0 →
      0 ≤ eps → eps ≤ 1 → 0 ∈ times → U ⊆ F.source →
      (∀ y : Sphere 2, (y, z) ∈ U) → ∀ x y : Sphere 2,
      ∃ gamma : ℝ → M, gamma 0 = F (x, z) ∧ gamma 1 = F (y, z) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I3 1 gamma (Icc (0 : ℝ) 1) ∧
        (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ F '' (univ ×ˢ ({z} : Set ℝ))) ∧
        metricPathELength (g 0) gamma 0 1 ≤ ENNReal.ofReal D := by
  obtain ⟨B, hB, hpaths⟩ := exists_roundSphere_path_length_bound
  refine ⟨2 * B, by positivity, ?_⟩
  intro C h g F U times order eps z cmp hmetric heps heps1 hzero hsource hlevel x y
  obtain ⟨gamma, hstart, hend, hgamma, hlength⟩ := hpaths x y
  have hcyl : ContMDiffOn 𝓘(ℝ, ℝ) IC 1 (fun s => (gamma s, z)) (Icc (0 : ℝ) 1) :=
    hgamma.prodMk contMDiffOn_const
  have hinside : ∀ s ∈ Icc (0 : ℝ) 1, (gamma s, z) ∈ U := fun _ _ => hlevel _
  refine ⟨fun s => F (gamma s, z), by dsimp; rw [hstart], by dsimp; rw [hend], ?_, ?_, ?_⟩
  · exact (F.contMDiffOn_toFun.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by decide)).comp hcyl
      (fun s hs => hsource (hinside s hs))
  · intro s _hs
    exact ⟨(gamma s, z), ⟨mem_univ _, rfl⟩, rfl⟩
  · have hupper := (collar_pathELength_bounds C g F cmp hmetric heps heps1 hzero hsource hcyl hinside).2
    have htransverse := C.transverse_length_le z hgamma
    have hsqrt : ENNReal.ofReal (Real.sqrt (1 + eps)) ≤ ENNReal.ofReal (Real.sqrt 2) :=
      ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by linarith))
    calc
      _ ≤ _ := hupper
      _ ≤ ENNReal.ofReal (Real.sqrt 2) *
          (ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal B) :=
        mul_le_mul' hsqrt (htransverse.trans (mul_le_mul' le_rfl hlength.le))
      _ = ENNReal.ofReal (2 * B) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← pow_two,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.ofReal_mul (by norm_num)]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
