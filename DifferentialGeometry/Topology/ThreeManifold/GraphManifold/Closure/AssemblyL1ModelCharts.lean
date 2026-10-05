import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelBall

/-!
# Chapter-14 assembly, item L1, group G3a: the charts of the model cycle in `S³`

The handle zone maps and the model balls, followed by the model map `modelSphere len` into `S³`,
are injective local diffeomorphisms on the zone domain and on the ball of radius `6/5`; this gives
the partial diffeomorphisms of the model cycle normal form: `zoneChart` (restricted to any open
subset of the zone domain, through an affine reparametrization, for the necks) and `ballChart'`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped ContDiff Topology Manifold

universe u

namespace GC.GraphManifold.Assembly

variable {ε : ℝ}

/-- An injective endomorphism between finite-dimensional spaces of equal dimension is
invertible. -/
theorem isInvertible_of_injective_of_finrank_eq {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hEF : Module.finrank ℝ E = Module.finrank ℝ F) {A : E →L[ℝ] F}
    (hA : Injective A) : A.IsInvertible := by
  have hAs : Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hEF (f := (A : E →ₗ[ℝ] F))).mp hA
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hA)
    (LinearMap.range_eq_top.mpr hAs), rfl⟩

/-- A smooth map between open sets of spaces of equal finite dimension with injective
differential is a local diffeomorphism. -/
theorem isLocalDiffeomorphOn_of_injective_fderiv' {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (hEF : Module.finrank ℝ E = Module.finrank ℝ F) {f : E → F}
    {S : Set E} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    (hd : ∀ x ∈ S, Injective (fderiv ℝ f x)) :
    IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f S := by
  apply hf.contMDiffOn.isLocalDiffeomorphOn_of_isInvertible_mfderiv hS (by simp)
  intro x hx
  rw [mfderiv_eq_fderiv]
  exact isInvertible_of_injective_of_finrank_eq hEF (hd x hx)

/-! ## The model map on slabs -/

theorem modelSphere_injOn_slab {len : ℕ} (hlen : 0 < len) (a : ℝ) :
    InjOn (modelSphere.{u} len) (modelSlab len a) := by
  intro p hp p' hp' h
  obtain ⟨hw, m, hm⟩ := (modelSphere_eq_iff hlen (norm_sq_lt_two_of_mem_modelSlab hp)
    (norm_sq_lt_two_of_mem_modelSlab hp')).mp h
  have hL : (0 : ℝ) < 4 * len := by
    have : (0 : ℝ) < len := Nat.cast_pos.mpr hlen
    linarith
  have hm0 : m = 0 := by
    obtain ⟨-, h1, h2⟩ := hp
    obtain ⟨-, h1', h2'⟩ := hp'
    have hlt : |(4 * len : ℝ) * m| < 4 * len := by
      rw [abs_lt]
      constructor <;> linarith
    rw [abs_mul, abs_of_pos hL] at hlt
    have : |(m : ℝ)| < 1 := by
      by_contra hc
      have := mul_le_mul_of_nonneg_left (not_lt.mp hc) hL.le
      linarith
    have : |m| < 1 := by exact_mod_cast this
    exact Int.abs_lt_one_iff.mp this
  rw [hm0] at hm
  exact Prod.ext hw (by simpa using hm.symm)

theorem isLocalDiffeomorphAt_modelSphere {len : ℕ} (hlen : 0 < len) {a : ℝ} {p : ModelSpace}
    (hp : p ∈ modelSlab len a) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ModelSpace) (𝓡 3) ∞ (modelSphere.{u} len) p :=
  (modelSphereChart.{u} hlen a).isLocalDiffeomorphAt _ _ _ hp

/-! ## The zone charts -/

theorem zoneChartMap_mem_modelSlab (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {len : ℕ} (hlen : 0 < len)
    (c : ℝ) {y : ModelSpace} (hy : y ∈ zoneDomain) : zoneChartMap ε c y ∈ modelSlab len c := by
  have hU := zoneHeight_mem (norm_nonneg y.1) hy.1 hy.2.1 hy.2.2
  have hL : (4 : ℝ) ≤ 4 * len := by
    have : (1 : ℝ) ≤ len := Nat.one_le_cast.mpr hlen
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_zoneChartMap_fst hε hε' c hy]
    exact (zoneRadius_le hε hε' (norm_nonneg _) (by linarith [hy.1]) (by linarith [hU.1])
      (by linarith [hU.2])).trans_lt hy.1
  · rw [zoneChartMap_apply]
    simp only
    linarith [hU.1]
  · rw [zoneChartMap_apply]
    simp only
    linarith [hU.2]

/-- The zone map into `S³`. -/
def zoneSphere (len : ℕ) (ε c : ℝ) (y : ModelSpace) : SphereCarrier.{u} :=
  modelSphere.{u} len (zoneChartMap ε c y)

theorem zoneSphere_injOn (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {len : ℕ} (hlen : 0 < len) (c : ℝ) :
    InjOn (zoneSphere.{u} len ε c) zoneDomain := fun _ hy _ hy' h =>
  zoneChartMap_injOn hε hε' c hy hy'
    (modelSphere_injOn_slab hlen c (zoneChartMap_mem_modelSlab hε hε' hlen c hy)
      (zoneChartMap_mem_modelSlab hε hε' hlen c hy') h)

theorem isLocalDiffeomorphAt_zoneSphere (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {len : ℕ}
    (hlen : 0 < len) (c : ℝ) {y : ModelSpace} (hy : y ∈ zoneDomain) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ModelSpace) (𝓡 3) ∞ (zoneSphere.{u} len ε c) y :=
  (isLocalDiffeomorphOn_zoneChartMap hε hε' c ⟨y, hy⟩).comp (𝓡 3) SphereCarrier.{u}
    (isLocalDiffeomorphAt_modelSphere hlen (zoneChartMap_mem_modelSlab hε hε' hlen c hy))

/-- A partial diffeomorphism from an injective local diffeomorphism on an open set. -/
theorem exists_chart_of_injOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → SphereCarrier.{u}} {S : Set E} (hS : IsOpen S)
    (hloc : ∀ x ∈ S, IsLocalDiffeomorphAt 𝓘(ℝ, E) (𝓡 3) ∞ f x) (hinj : InjOn f S) :
    ∃ d : PartialDiffeomorph 𝓘(ℝ, E) (𝓡 3) E SphereCarrier.{u} ∞,
      d.source = S ∧ d.target = f '' S ∧ (d : E → SphereCarrier.{u}) = f :=
  DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn hS
    (fun x => hloc x.1 x.2) hinj

/-- The zone chart restricted to an open set `S` read through a map `g` into the zone domain
which is an injective local diffeomorphism of the model space. -/
def zoneChart (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {len : ℕ} (hlen : 0 < len) (c : ℝ)
    (g : ModelSpace ≃ₜ ModelSpace) (hg : ∀ x, IsLocalDiffeomorphAt 𝓘(ℝ, ModelSpace)
      𝓘(ℝ, ModelSpace) ∞ g x) {S : Set ModelSpace} (hS : IsOpen S) (hSz : MapsTo g S zoneDomain) :
    PartialDiffeomorph 𝓘(ℝ, ModelSpace) (𝓡 3) ModelSpace SphereCarrier.{u} ∞ :=
  (exists_chart_of_injOn (f := zoneSphere.{u} len ε c ∘ g) hS
    (fun x hx => (hg x).comp (𝓡 3) SphereCarrier.{u}
      (isLocalDiffeomorphAt_zoneSphere hε hε' hlen c (hSz hx)))
    (fun _ hx _ hx' h => g.injective (zoneSphere_injOn hε hε' hlen c (hSz hx) (hSz hx') h))).choose

theorem zoneChart_spec (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {len : ℕ} (hlen : 0 < len) (c : ℝ)
    (g : ModelSpace ≃ₜ ModelSpace) (hg : ∀ x, IsLocalDiffeomorphAt 𝓘(ℝ, ModelSpace)
      𝓘(ℝ, ModelSpace) ∞ g x) {S : Set ModelSpace} (hS : IsOpen S) (hSz : MapsTo g S zoneDomain) :
    (zoneChart.{u} hε hε' hlen c g hg hS hSz).source = S ∧
      (zoneChart.{u} hε hε' hlen c g hg hS hSz).target = (zoneSphere.{u} len ε c ∘ g) '' S ∧
      ((zoneChart.{u} hε hε' hlen c g hg hS hSz : ModelSpace → SphereCarrier.{u})) =
        zoneSphere.{u} len ε c ∘ g :=
  (exists_chart_of_injOn (f := zoneSphere.{u} len ε c ∘ g) hS
    (fun x hx => (hg x).comp (𝓡 3) SphereCarrier.{u}
      (isLocalDiffeomorphAt_zoneSphere hε hε' hlen c (hSz hx)))
    (fun _ hx _ hx' h => g.injective (zoneSphere_injOn hε hε' hlen c (hSz hx) (hSz hx') h))).choose_spec

/-! ## The ball charts -/

/-- The model ball into `S³`. -/
def ballSphere (len : ℕ) (ε c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : SphereCarrier.{u} :=
  modelSphere.{u} len (ballMap ε c x)

theorem ballMap_mem_modelSlab (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {len : ℕ} (hlen : 0 < len)
    (c : ℝ) {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ < 6 / 5) :
    ballMap ε c x ∈ modelSlab len (c - 2) := by
  have hL : (4 : ℝ) ≤ 4 * len := by
    have : (1 : ℝ) ≤ len := Nat.one_le_cast.mpr hlen
    linarith
  have hh := abs_ballCoord_snd_le x
  have hh' := abs_le.mp hh
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_ballMap_fst hε hε', ballRadius_eq hε hε' (norm_nonneg _)]
    refine (neckRadius_le_right hε _ _).trans_lt ?_
    rw [add_sub_cancel, norm_sq_ballCoord, ballCutSq, Real.sqrt_sq (norm_nonneg x)]
    rcases le_total ‖x‖ (ballCutCentre + ballCutWidth) with h2 | h2
    · have hm : max ‖x‖ ballCutCentre ≤ ballCutCentre + ballCutWidth :=
        max_le h2 (by norm_num [ballCutCentre, ballCutWidth])
      have := (ballCut_le ‖x‖).trans (add_le_add_left hm ballCutWidth)
      norm_num [ballCutCentre, ballCutWidth] at this ⊢
      linarith
    · rw [ballCut_eq_self h2]
      linarith
  · rw [ballMap_snd]
    linarith
  · rw [ballMap_snd]
    linarith

theorem ballSphere_injOn (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {len : ℕ} (hlen : 0 < len) (c : ℝ) :
    InjOn (ballSphere.{u} len ε c) (ball 0 (6 / 5)) := fun _ hx _ hx' h =>
  ballMap_injective hε hε' c
    (modelSphere_injOn_slab hlen (c - 2)
      (ballMap_mem_modelSlab hε hε' hlen c (mem_ball_zero_iff.mp hx))
      (ballMap_mem_modelSlab hε hε' hlen c (mem_ball_zero_iff.mp hx')) h)

theorem isLocalDiffeomorphAt_ballSphere (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {len : ℕ}
    (hlen : 0 < len) (c : ℝ) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball (0 : EuclideanSpace ℝ
      (Fin 3)) (6 / 5)) :
    IsLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) ∞ (ballSphere.{u} len ε c) x := by
  have hloc : IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ModelSpace) ∞
      (ballMap ε c) univ :=
    isLocalDiffeomorphOn_of_injective_fderiv' (by simp) isOpen_univ
      (contDiff_ballMap hε hε' c).contDiffOn (fun x _ => injective_fderiv_ballMap hε hε' c x)
  exact (hloc ⟨x, mem_univ x⟩).comp (𝓡 3) SphereCarrier.{u} (isLocalDiffeomorphAt_modelSphere hlen
    (ballMap_mem_modelSlab hε hε' hlen c (mem_ball_zero_iff.mp hx)))

/-- The ball chart. -/
def ballChart' (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {len : ℕ} (hlen : 0 < len) (c : ℝ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) SphereCarrier.{u} ∞ :=
  (exists_chart_of_injOn (f := ballSphere.{u} len ε c) isOpen_ball
    (fun _ hx => isLocalDiffeomorphAt_ballSphere hε hε' hlen c hx)
    (ballSphere_injOn hε hε' hlen c)).choose

theorem ballChart'_spec (hε : 0 < ε) (hε' : ε ≤ 1 / 8) {len : ℕ} (hlen : 0 < len) (c : ℝ) :
    (ballChart'.{u} hε hε' hlen c).source = ball 0 (6 / 5) ∧
      (ballChart'.{u} hε hε' hlen c).target = ballSphere.{u} len ε c '' ball 0 (6 / 5) ∧
      ((ballChart'.{u} hε hε' hlen c : EuclideanSpace ℝ (Fin 3) → SphereCarrier.{u})) =
        ballSphere.{u} len ε c :=
  (exists_chart_of_injOn (f := ballSphere.{u} len ε c) isOpen_ball
    (fun _ hx => isLocalDiffeomorphAt_ballSphere hε hε' hlen c hx)
    (ballSphere_injOn hε hε' hlen c)).choose_spec

end GC.GraphManifold.Assembly
