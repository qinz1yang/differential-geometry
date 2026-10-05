import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCellChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecLift
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42Models
import DifferentialGeometry.Topology.ThreeManifold.NestedBallRecapping
import DifferentialGeometry.Topology.Manifold.CompactLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# FC42 sphere recursion, packet S3a (tools): a shell glued to a ball is a ball

Lane ASM-SPH. For an injective full-rank map `F₀ : S² × [0, 1] → N` into a three-manifold without
boundary (smooth, injective, bijective differential everywhere — the data of a lifted `S² × I`
vertex):

* `exists_partialDiffeomorph_of_sphereIcc`: `F₀` extends to a partial diffeomorphism of `S² × ℝ`
  defined on an open set containing `S² × [0, 1]`. Pieces: a two-sided collar at each end extending
  the half collars `F₀ (z, τ)` and `F₀ (z, 1 - τ)` (`exists_smoothTwoSidedCollar_of_halfClosedInterval`),
  the middle `S² × (0, 1)` (an injective local diffeomorphism there, by the inverse function theorem
  for manifolds without boundary), glued over the compact `S² × [0, 1]`
  (`PartialDiffeomorph.exists_gluing_of_isCompact`).
* `exists_ballChart_of_shell_cap`: if a ball chart `G` of `N` has as boundary sphere the end
  `F₀ (S² × {0})` and meets the shell only there, then `range F₀ ∪ G (closed ball)` is the closed ball
  of a ball chart whose boundary sphere is the other end `F₀ (S² × {1})`
  (`exists_ball_chart_of_recapped_nested_ball_shell`, in polar coordinates `x ↦ (x/‖x‖, 2 - ‖x‖)`).
  No condition on how the shell and the ball are glued.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance sphereDimShell_ASMSPH :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

local instance halfChartsShell_ASMSPH :
    ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (1 / 2)) :=
  halfClosedIntervalChartedSpace (by norm_num : (0 : ℝ) < 1 / 2)

local instance halfSmoothShell_ASMSPH : IsManifold (𝓡∂ 1) ∞ (Ico (0 : ℝ) (1 / 2)) :=
  halfClosedInterval_isManifold (by norm_num : (0 : ℝ) < 1 / 2)

/-- The left end of the unit interval. -/
def iccZero : Icc (0 : ℝ) 1 :=
  ⟨0, le_rfl, zero_le_one⟩

/-- The right end of the unit interval. -/
def iccOne : Icc (0 : ℝ) 1 :=
  ⟨1, zero_le_one, le_rfl⟩

/-- The inclusion of the half-closed interval `[0, 1/2)` into `[0, 1]`. -/
def icoToIcc (τ : Ico (0 : ℝ) (1 / 2)) : Icc (0 : ℝ) 1 :=
  ⟨τ.val, τ.2.1, by linarith [τ.2.2]⟩

theorem contMDiff_icoToIcc : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ icoToIcc :=
  contMDiff_iff_comp_subtypeVal_Icc.mpr ⟨continuous_subtype_val.subtype_mk _,
    (isSmoothEmbedding_halfClosedInterval_inclusion (by norm_num : (0 : ℝ) < 1 / 2)).contMDiff⟩

theorem mfderiv_icoToIcc_bijective (τ : Ico (0 : ℝ) (1 / 2)) :
    Bijective (mfderiv (𝓡∂ 1) (𝓡∂ 1) icoToIcc τ) := by
  have hs := isSmoothEmbedding_halfClosedInterval_inclusion (by norm_num : (0 : ℝ) < 1 / 2)
  have hcomp := mfderiv_comp τ
    ((contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞)).mdifferentiableAt (by simp))
    (contMDiff_icoToIcc.mdifferentiableAt (by simp))
  have hval : ((fun z : Icc (0 : ℝ) 1 => (z : ℝ)) ∘ icoToIcc) =
      (Subtype.val : Ico (0 : ℝ) (1 / 2) → ℝ) := rfl
  rw [hval] at hcomp
  have hinj : Injective (mfderiv (𝓡∂ 1) (𝓡∂ 1) icoToIcc τ) := by
    intro v w hvw
    apply hs.isImmersion.mfderiv_injective (by simp) τ
    rw [DFunLike.congr_fun hcomp v, DFunLike.congr_fun hcomp w]
    exact congrArg (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) (icoToIcc τ)) hvw
  exact bijective_of_injective_continuousLinearMap (V := EuclideanSpace ℝ (Fin 1)) hinj

section Shell

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N]

/-- **The collar at the end `0`** of an injective full-rank `S² × [0, 1]`. -/
theorem exists_collar_of_sphereIcc_zero
    (F₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 → N)
    (hF : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ F₀) (hinj : Injective F₀)
    (hbij : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) F₀ p)) :
    ∃ d : SmoothTwoSidedCollar (𝓡 2) (𝓡 3)
        (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => F₀ (z, iccZero)),
      ∃ _hw : d.radius ≤ 1 / 2,
      ∀ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × symmetricOpenInterval d.radius)
        (hp : 0 ≤ p.2.val), d.toFun p = F₀ (p.1, ⟨p.2.val, hp, by
          linarith [p.2.property.2]⟩) := by
  let k : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Ico (0 : ℝ) (1 / 2) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 := Prod.map id icoToIcc
  have hk : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1)) ∞ k :=
    contMDiff_id.prodMap contMDiff_icoToIcc
  let c := F₀ ∘ k
  have hc : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ c := hF.comp hk
  let τ₀ : Ico (0 : ℝ) (1 / 2) := ⟨0, le_rfl, by norm_num⟩
  have hk0 : ∀ z, k (z, τ₀) = (z, iccZero) := fun _ => rfl
  have hinj0 : Injective (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => c (z, τ₀)) := by
    intro z w h
    have h' := hinj h
    exact congrArg Prod.fst h'
  have hderiv : ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) c (z, τ₀)) := by
    intro z
    rw [show c = F₀ ∘ k from rfl, mfderiv_comp _ (hF.mdifferentiableAt (by simp))
      (hk.mdifferentiableAt (by simp))]
    refine (hbij _).comp ?_
    rw [mfderiv_prodMap mdifferentiableAt_id
      (contMDiff_icoToIcc.mdifferentiableAt (by simp)), mfderiv_id]
    exact Function.bijective_id.prodMap (mfderiv_icoToIcc_bijective _)
  obtain ⟨d, hwidth, hd⟩ := exists_smoothTwoSidedCollar_of_halfClosedInterval
    (J := 𝓡 2) (I := 𝓡 3) (by norm_num : (0 : ℝ) < 1 / 2) c hc hinj0 hderiv
  let d' : SmoothTwoSidedCollar (𝓡 2) (𝓡 3)
      (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 => F₀ (z, iccZero)) :=
    { radius := d.radius
      radius_pos := d.radius_pos
      neighborhood := d.neighborhood
      toDiffeomorph := d.toDiffeomorph
      zero_eq := fun z => (d.zero_eq z).trans (congrArg F₀ (hk0 z)) }
  exact ⟨d', hwidth, fun p hp => hd p hp⟩

omit [T2Space N] in
/-- **The middle part**: on `S² × (0, 1)` the map `F₀` is an injective local diffeomorphism. -/
theorem exists_partialDiffeomorph_of_sphereIcc_middle
    (F₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 → N)
    (hF : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ F₀) (hinj : Injective F₀)
    (hbij : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) F₀ p)) :
    ∃ φ : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) N ∞,
      φ.source = {p | 0 < p.2 ∧ p.2 < 1} ∧
      ∀ p (hp : p.2 ∈ Icc (0 : ℝ) 1), p ∈ φ.source → φ p = F₀ (p.1, ⟨p.2, hp⟩) := by
  let V : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) := {p | 0 < p.2 ∧ p.2 < 1}
  have hV : IsOpen V := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd continuous_const)
  let ι : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 :=
    Prod.map id (Set.projIcc (0 : ℝ) 1 zero_le_one)
  let g := F₀ ∘ ι
  have hpr : ∀ s : ℝ, 0 < s → s < 1 →
      ContMDiffAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (Set.projIcc (0 : ℝ) 1 zero_le_one) s := fun s h0 h1 =>
    (contMDiffOn_projIcc (x := (0 : ℝ)) (y := 1)).contMDiffAt
      (Icc_mem_nhds h0 h1)
  have hι : ∀ p ∈ V, ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod (𝓡∂ 1)) ∞ ι p := fun p hp =>
    contMDiffAt_id.prodMap (hpr p.2 hp.1 hp.2)
  have hg : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ g V := fun p hp =>
    ((hF.contMDiffAt).comp p (hι p hp)).contMDiffWithinAt
  have hprBij : ∀ s : ℝ, 0 < s → s < 1 →
      Bijective (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) (Set.projIcc (0 : ℝ) 1 zero_le_one) s) := by
    intro s h0 h1
    have hev : (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) ∘ Set.projIcc (0 : ℝ) 1 zero_le_one =ᶠ[𝓝 s] id := by
      filter_upwards [Icc_mem_nhds h0 h1] with t ht
      exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ht)
    have hcomp := mfderiv_comp s
      ((contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1) (n := ∞)).mdifferentiableAt (by simp))
      ((hpr s h0 h1).mdifferentiableAt (by simp))
    rw [hev.mfderiv_eq, mfderiv_id] at hcomp
    have hinj' : Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) (Set.projIcc (0 : ℝ) 1 zero_le_one) s) := by
      intro v w hvw
      have h := congrArg (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ))
        (Set.projIcc (0 : ℝ) 1 zero_le_one s)) hvw
      have hv := DFunLike.congr_fun hcomp v
      have hw := DFunLike.congr_fun hcomp w
      exact hv.trans (h.trans hw.symm)
    let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
      mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) (Set.projIcc (0 : ℝ) 1 zero_le_one) s
    have hL : Injective L := hinj'
    have hd : Module.finrank ℝ ℝ = Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) := by simp
    exact ⟨hinj', (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hL⟩
  have hgBij : ∀ p ∈ V, Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) g p) := by
    intro p hp
    rw [show g = F₀ ∘ ι from rfl, mfderiv_comp p (hF.mdifferentiableAt (by simp))
      ((hι p hp).mdifferentiableAt (by simp))]
    refine (hbij _).comp ?_
    rw [mfderiv_prodMap mdifferentiableAt_id ((hpr p.2 hp.1 hp.2).mdifferentiableAt (by simp)),
      mfderiv_id]
    exact Function.bijective_id.prodMap (hprBij p.2 hp.1 hp.2)
  have hlocal : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ g V := by
    intro p
    have hb := hgBij p.val p.property
    have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by simp
    let A : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (LinearEquiv.ofBijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) g p.val).toLinearMap
        hb).toContinuousLinearEquiv
    exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv g hg hV p.val p.property A
      ((hg.contMDiffAt (hV.mem_nhds p.property)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hinjOn : InjOn g V := by
    intro p hp q hq h
    have h' := hinj h
    have h2 : ((Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : Icc (0 : ℝ) 1) : ℝ) =
        Set.projIcc (0 : ℝ) 1 zero_le_one q.2 := congrArg (fun r => (r.2 : ℝ)) h'
    rw [Set.projIcc_of_mem _ ⟨hp.1.le, hp.2.le⟩, Set.projIcc_of_mem _ ⟨hq.1.le, hq.2.le⟩] at h2
    have h1 := congrArg Prod.fst h'
    exact Prod.ext h1 h2
  have hne : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :=
    ⟨(⟨EuclideanSpace.single 0 1, by simp⟩, 0)⟩
  obtain ⟨φ, hsrc, -, hφ⟩ := exists_partialDiffeomorph_of_injOn hV hlocal hinjOn
  refine ⟨φ, hsrc, fun p hp _ => ?_⟩
  rw [hφ]
  change F₀ (p.1, Set.projIcc (0 : ℝ) 1 zero_le_one p.2) = _
  rw [Set.projIcc_of_mem _ hp]

/-- **An injective full-rank `S² × [0, 1]` extends to a partial diffeomorphism of `S² × ℝ`.** -/
theorem exists_partialDiffeomorph_of_sphereIcc
    (F₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 → N)
    (hF : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ F₀) (hinj : Injective F₀)
    (hbij : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) F₀ p)) :
    ∃ ψ : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) N ∞,
      univ ×ˢ Icc (0 : ℝ) 1 ⊆ ψ.source ∧
      ∀ (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (t : Icc (0 : ℝ) 1),
        ψ (z, t.val) = F₀ (z, t) := by
  -- the collar at the end `0`
  obtain ⟨d₀, hw₀, hd₀⟩ := exists_collar_of_sphereIcc_zero F₀ hF hinj hbij
  -- the collar at the end `1`, from the reflected shell
  let R : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 := Prod.map id iccReflect
  let F₁ := F₀ ∘ R
  let RD := (Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
    iccReflect
  have hRD : ∀ p, RD p = R p := fun _ => rfl
  have hF₁ : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ F₁ := hF.comp RD.contMDiff
  have hinj₁ : Injective F₁ := hinj.comp RD.injective
  have hbij₁ : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) F₁ p) := by
    intro p
    change Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) (F₀ ∘ RD) p)
    rw [mfderiv_comp p (hF.mdifferentiableAt (by simp)) (RD.contMDiff.mdifferentiableAt (by simp))]
    exact (hbij _).comp (RD.mfderivToContinuousLinearEquiv (by simp) p).bijective
  obtain ⟨d₁, hw₁, hd₁⟩ := exists_collar_of_sphereIcc_zero F₁ hF₁ hinj₁ hbij₁
  -- the middle
  obtain ⟨φm, hφms, hφm⟩ := exists_partialDiffeomorph_of_sphereIcc_middle F₀ hF hinj hbij
  -- the two end charts
  let φ₀ := d₀.toPartialDiffeomorph
  let L : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ∞ :=
    (Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
      reverseLine
  let φ₁ := L.toPartialDiffeomorph.trans d₁.toPartialDiffeomorph
  -- the glued map
  let g : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → N := fun p =>
    if h : p.2 ∈ Icc (0 : ℝ) 1 then F₀ (p.1, ⟨p.2, h⟩) else if p.2 < 0 then φ₀ p else φ₁ p
  let U₀ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :=
    {p | -d₀.radius < p.2 ∧ p.2 < d₀.radius}
  let U₁ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :=
    {p | 1 - d₁.radius < p.2 ∧ p.2 < 1 + d₁.radius}
  have hU₀ : IsOpen U₀ := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd continuous_const)
  have hU₁ : IsOpen U₁ := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd continuous_const)
  have hU₀s : U₀ ⊆ φ₀.source := by
    intro p hp
    rw [SmoothTwoSidedCollar.toPartialDiffeomorph_source]
    exact ⟨mem_univ _, hp⟩
  have hU₁s : U₁ ⊆ φ₁.source := by
    intro p hp
    refine ⟨mem_univ _, ?_⟩
    change L p ∈ d₁.toPartialDiffeomorph.source
    rw [SmoothTwoSidedCollar.toPartialDiffeomorph_source]
    refine ⟨mem_univ _, ?_⟩
    change -d₁.radius < 1 - p.2 ∧ 1 - p.2 < d₁.radius
    constructor <;> linarith [hp.1, hp.2]
  have hφ₀ : ∀ p ∈ U₀, g p = φ₀ p := by
    intro p hp
    by_cases h : p.2 ∈ Icc (0 : ℝ) 1
    · have hp0 : 0 ≤ p.2 := h.1
      simp only [g, dite_eq_left h]
      have := hd₀ (p.1, ⟨p.2, hp⟩) hp0
      rw [← SmoothTwoSidedCollar.toPartialDiffeomorph_apply] at this
      exact this.symm
    · have hlt : p.2 < 0 := by
        by_contra hge
        exact h ⟨le_of_not_gt hge, by linarith [hp.2, hw₀]⟩
      simp only [g, dite_eq_right h, ite_eq_left hlt]
  have hφ₁ : ∀ p ∈ U₁, g p = φ₁ p := by
    intro p hp
    have hL : L p = (p.1, 1 - p.2) := rfl
    have hsrc : 1 - p.2 ∈ symmetricOpenInterval d₁.radius := by
      change -d₁.radius < 1 - p.2 ∧ 1 - p.2 < d₁.radius
      constructor <;> linarith [hp.1, hp.2]
    have happ : φ₁ p = d₁.toFun (p.1, ⟨1 - p.2, hsrc⟩) := by
      change d₁.toPartialDiffeomorph (L p) = _
      rw [hL]
      exact SmoothTwoSidedCollar.toPartialDiffeomorph_apply d₁ (p.1, ⟨1 - p.2, hsrc⟩)
    by_cases h : p.2 ∈ Icc (0 : ℝ) 1
    · have h1 : 0 ≤ 1 - p.2 := by linarith [h.2]
      simp only [g, dite_eq_left h]
      rw [happ, hd₁ (p.1, ⟨1 - p.2, hsrc⟩) h1]
      change F₀ (p.1, ⟨p.2, h⟩) = F₀ (p.1, iccReflect ⟨1 - p.2, _⟩)
      congr 2
      apply Subtype.ext
      rw [iccReflect_val]
      ring
    · have hgt : ¬ p.2 < 0 := by
        intro hlt
        linarith [hp.1, hw₁]
      simp only [g, dite_eq_right h, ite_eq_right hgt]
  have hφm' : ∀ p ∈ φm.source, g p = φm p := by
    intro p hp
    have hp' : p ∈ {p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ | 0 < p.2 ∧ p.2 < 1} :=
      hφms ▸ hp
    have h : p.2 ∈ Icc (0 : ℝ) 1 := ⟨hp'.1.le, hp'.2.le⟩
    simp only [g, dite_eq_left h]
    exact (hφm p h hp).symm
  have hloc : ∀ p ∈ (univ ×ˢ Icc (0 : ℝ) 1 : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)),
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ g p := by
    rintro p ⟨-, hp0, hp1⟩
    rcases hp0.eq_or_lt with h0 | h0
    · have hpU : p ∈ U₀ := ⟨by rw [← h0]; linarith [d₀.radius_pos], by rw [← h0]; exact d₀.radius_pos⟩
      exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hU₀.mem_nhds hpU) hφ₀)
        (φ₀.isLocalDiffeomorphAt _ _ _ (hU₀s hpU))
    rcases hp1.eq_or_lt with h1 | h1
    · have hpU : p ∈ U₁ := ⟨by rw [h1]; linarith [d₁.radius_pos], by rw [h1]; linarith [d₁.radius_pos]⟩
      exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.eventuallyEq_of_mem (hU₁.mem_nhds hpU) hφ₁)
        (φ₁.isLocalDiffeomorphAt _ _ _ (hU₁s hpU))
    · have hpm : p ∈ φm.source := by rw [hφms]; exact ⟨h0, h1⟩
      exact DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.eventuallyEq_of_mem (φm.open_source.mem_nhds hpm) hφm')
        (φm.isLocalDiffeomorphAt _ _ _ hpm)
  have hK : IsCompact (univ ×ˢ Icc (0 : ℝ) 1 :
      Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)) :=
    isCompact_univ.prod isCompact_Icc
  have hinjK : InjOn g (univ ×ˢ Icc (0 : ℝ) 1) := by
    rintro p ⟨-, hp⟩ q ⟨-, hq⟩ h
    simp only [g, dite_eq_left hp, dite_eq_left hq] at h
    have h' := hinj h
    have h1 := congrArg Prod.fst h'
    have h2 := congrArg (fun r => (r.2 : ℝ)) h'
    exact Prod.ext h1 h2
  obtain ⟨ψ, hψs, -, hψ⟩ := exists_partialDiffeomorph_of_injOn_compact hK hinjK hloc
    isOpen_univ (subset_univ _)
  refine ⟨ψ, hψs, fun z t => ?_⟩
  rw [hψ]
  simp only [g, dite_eq_left t.2]

/-- The reflection `r ↦ 2 - r` of the line. -/
def reverseLineTwo : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun t := 2 - t
  invFun t := 2 - t
  left_inv t := by dsimp; ring
  right_inv t := by dsimp; ring
  contMDiff_toFun := contMDiff_const.sub contMDiff_id
  contMDiff_invFun := contMDiff_const.sub contMDiff_id

/-- The homothety by `2` of `ℝ³`. -/
def homothetyTwo : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
    (EuclideanSpace ℝ (Fin 3)) ∞ :=
  Diffeomorph.toPartialDiffeomorph
    { toFun x := (2 : ℝ) • x
      invFun x := (1 / 2 : ℝ) • x
      left_inv x := by simp [smul_smul]
      right_inv x := by simp [smul_smul]
      contMDiff_toFun := (contDiff_const_smul (2 : ℝ)).contMDiff
      contMDiff_invFun := (contDiff_const_smul (1 / 2 : ℝ)).contMDiff }

theorem homothetyTwo_apply (x : EuclideanSpace ℝ (Fin 3)) : homothetyTwo x = (2 : ℝ) • x :=
  rfl

/-- **A shell glued to a ball is a ball.** If a ball chart `G` has as boundary sphere the end
`F₀ (S² × {0})` of an injective full-rank `S² × [0, 1]` and meets it only on its boundary sphere,
then the shell and the ball together are the closed ball of a ball chart whose boundary sphere is
the other end `F₀ (S² × {1})`. -/
theorem exists_ballChart_of_shell_cap
    (F₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 → N)
    (hF : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ F₀) (hinj : Injective F₀)
    (hbij : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) F₀ p))
    (G : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) N ∞)
    (hG : Metric.closedBall 0 1 ⊆ G.source)
    (hGs : G '' Metric.sphere 0 1 = range fun z => F₀ (z, iccZero))
    (hinter : range F₀ ∩ G '' Metric.closedBall 0 1 ⊆ G '' Metric.sphere 0 1) :
    ∃ A : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) N ∞,
      Metric.closedBall 0 1 ⊆ A.source ∧
      A '' Metric.closedBall 0 1 = range F₀ ∪ G '' Metric.closedBall 0 1 ∧
      A '' Metric.sphere 0 1 = range fun z => F₀ (z, iccOne) := by
  obtain ⟨ψ, hψs, hψ⟩ := exists_partialDiffeomorph_of_sphereIcc F₀ hF hinj hbij
  let v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let P := (spherePolarChart (n := 2) v).symm
  let L2 := ((Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
    reverseLineTwo).toPartialDiffeomorph
  let F := (P.trans L2).trans ψ
  have hFapp : ∀ x, F x = ψ (sphereDirection v x, 2 - ‖x‖) := fun _ => rfl
  have hshell : ∀ x : EuclideanSpace ℝ (Fin 3), ∀ (h1 : 1 ≤ ‖x‖) (h2 : ‖x‖ ≤ 2),
      x ∈ F.source ∧ F x = F₀ (sphereDirection v x, ⟨2 - ‖x‖, by linarith, by linarith⟩) := by
    intro x h1 h2
    have hx0 : x ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
    refine ⟨⟨⟨?_, mem_univ _⟩, hψs ⟨mem_univ _, ?_⟩⟩, ?_⟩
    · change x ∈ (spherePolarChart (n := 2) v).target
      rw [spherePolarChart_target]
      exact hx0
    · change 2 - ‖x‖ ∈ Icc (0 : ℝ) 1
      constructor <;> linarith
    · rw [hFapp]
      exact hψ _ ⟨2 - ‖x‖, by linarith, by linarith⟩
  have hpolar : ∀ (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {r : ℝ}, 0 < r →
      sphereDirection v (r • (z : EuclideanSpace ℝ (Fin 3))) = z ∧
        ‖r • (z : EuclideanSpace ℝ (Fin 3))‖ = r := by
    intro z r hr
    refine ⟨sphereDirection_pos_smul v z hr, ?_⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  -- the images of the shell and of its two boundary spheres
  have himShell : F '' (Metric.closedBall 0 2 \ Metric.ball 0 1) = range F₀ := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx2, hx1⟩, rfl⟩
      have h1 : 1 ≤ ‖x‖ := by simpa using hx1
      have h2 : ‖x‖ ≤ 2 := by simpa using hx2
      exact ⟨_, ((hshell x h1 h2).2).symm⟩
    · rintro ⟨⟨z, t⟩, rfl⟩
      have ht : 0 < 2 - (t : ℝ) := by linarith [t.2.2]
      obtain ⟨hd, hn⟩ := hpolar z ht
      have h1 : 1 ≤ ‖(2 - (t : ℝ)) • (z : EuclideanSpace ℝ (Fin 3))‖ := by rw [hn]; linarith [t.2.2]
      have h2 : ‖(2 - (t : ℝ)) • (z : EuclideanSpace ℝ (Fin 3))‖ ≤ 2 := by rw [hn]; linarith [t.2.1]
      refine ⟨(2 - (t : ℝ)) • (z : EuclideanSpace ℝ (Fin 3)), ⟨by simpa using h2, by simpa using h1⟩, ?_⟩
      rw [(hshell _ h1 h2).2]
      congr 1
      refine Prod.ext hd (Subtype.ext ?_)
      change 2 - ‖(2 - (t : ℝ)) • (z : EuclideanSpace ℝ (Fin 3))‖ = t
      rw [hn]
      ring
  have himSphere : ∀ (r : ℝ) (t : Icc (0 : ℝ) 1), (t : ℝ) = 2 - r →
      F '' Metric.sphere 0 r = range fun z => F₀ (z, t) := by
    intro r t hrt
    have hr1 : 1 ≤ r := by linarith [t.2.2]
    have hr2 : r ≤ 2 := by linarith [t.2.1]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxn : ‖x‖ = r := by simpa using hx
      refine ⟨sphereDirection v x, ?_⟩
      rw [(hshell x (by rw [hxn]; exact hr1) (by rw [hxn]; exact hr2)).2]
      have hp : (sphereDirection v x, (⟨2 - ‖x‖, by rw [hxn]; linarith, by rw [hxn]; linarith⟩ :
          Icc (0 : ℝ) 1)) = (sphereDirection v x, t) := by
        rw [Prod.mk.injEq]
        refine ⟨rfl, Subtype.ext ?_⟩
        change 2 - ‖x‖ = (t : ℝ)
        rw [hxn, hrt]
      exact (congrArg F₀ hp).symm
    · rintro ⟨z, rfl⟩
      obtain ⟨hd, hn⟩ := hpolar z (by linarith : (0 : ℝ) < r)
      refine ⟨r • (z : EuclideanSpace ℝ (Fin 3)), by simpa using hn, ?_⟩
      rw [(hshell _ (by rw [hn]; exact hr1) (by rw [hn]; exact hr2)).2]
      have hp : (sphereDirection v (r • (z : EuclideanSpace ℝ (Fin 3))),
          (⟨2 - ‖r • (z : EuclideanSpace ℝ (Fin 3))‖, by rw [hn]; linarith, by rw [hn]; linarith⟩ :
            Icc (0 : ℝ) 1)) = (z, t) := by
        rw [Prod.mk.injEq]
        refine ⟨hd, Subtype.ext ?_⟩
        change 2 - ‖r • (z : EuclideanSpace ℝ (Fin 3))‖ = (t : ℝ)
        rw [hn, hrt]
      exact congrArg F₀ hp
  -- the homothety and the identity
  let C : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ∞ :=
    (Diffeomorph.refl (𝓡 3) (EuclideanSpace ℝ (Fin 3)) ∞).toPartialDiffeomorph
  have hCimg : ∀ s : Set (EuclideanSpace ℝ (Fin 3)), C '' s = s := fun s => image_id s
  have hBimg : ∀ (r : ℝ), homothetyTwo '' Metric.closedBall 0 r = Metric.closedBall 0 (2 * r) ∧
      homothetyTwo '' Metric.ball 0 r = Metric.ball 0 (2 * r) ∧
      homothetyTwo '' Metric.sphere 0 r = Metric.sphere 0 (2 * r) := by
    intro r
    have hmem : ∀ (x : EuclideanSpace ℝ (Fin 3)), ‖(2 : ℝ) • x‖ = 2 * ‖x‖ := fun x => by
      rw [norm_smul]; norm_num
    have hpre : ∀ (y : EuclideanSpace ℝ (Fin 3)), (2 : ℝ) • ((1 / 2 : ℝ) • y) = y := fun y => by
      rw [smul_smul]; norm_num
    refine ⟨?_, ?_, ?_⟩ <;> ext y <;> constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [mem_closedBall_zero_iff] at hx ⊢
      rw [homothetyTwo_apply, hmem]
      linarith
    · intro hy
      refine ⟨(1 / 2 : ℝ) • y, ?_, by rw [homothetyTwo_apply, hpre]⟩
      simp only [mem_closedBall_zero_iff] at hy ⊢
      have := hmem ((1 / 2 : ℝ) • y)
      rw [hpre] at this
      linarith
    · rintro ⟨x, hx, rfl⟩
      simp only [mem_ball_zero_iff] at hx ⊢
      rw [homothetyTwo_apply, hmem]
      linarith
    · intro hy
      refine ⟨(1 / 2 : ℝ) • y, ?_, by rw [homothetyTwo_apply, hpre]⟩
      simp only [mem_ball_zero_iff] at hy ⊢
      have := hmem ((1 / 2 : ℝ) • y)
      rw [hpre] at this
      linarith
    · rintro ⟨x, hx, rfl⟩
      simp only [mem_sphere_zero_iff_norm] at hx ⊢
      rw [homothetyTwo_apply, hmem, hx]
    · intro hy
      refine ⟨(1 / 2 : ℝ) • y, ?_, by rw [homothetyTwo_apply, hpre]⟩
      simp only [mem_sphere_zero_iff_norm] at hy ⊢
      have := hmem ((1 / 2 : ℝ) • y)
      rw [hpre] at this
      linarith
  obtain ⟨hBcl, hBb, hBs⟩ := hBimg 1
  rw [mul_one] at hBcl hBb hBs
  have hshellSet : homothetyTwo '' Metric.closedBall 0 1 \ C '' Metric.ball 0 1 =
      Metric.closedBall 0 2 \ Metric.ball 0 1 := by
    rw [hBcl, hCimg]
  obtain ⟨A, hA, hAimg, hAs, -⟩ :=
    DifferentialGeometry.Topology.ThreeManifold.exists_ball_chart_of_recapped_nested_ball_shell
      C homothetyTwo F G (fun _ _ => trivial) (fun _ _ => trivial) hG
      (by
        rw [hCimg, hBb]
        exact Metric.closedBall_subset_ball (by norm_num))
      (by
        rw [hshellSet]
        rintro x ⟨hx2, hx1⟩
        exact (hshell x (by simpa using hx1) (by simpa using hx2)).1)
      (by
        rw [hBs, hGs]
        exact himSphere 2 iccZero (by simp [iccZero]))
      (by
        rw [hshellSet, himShell]
        exact hinter)
  refine ⟨A, hA, ?_, ?_⟩
  · rw [hAimg, hshellSet, himShell]
  · rw [hAs, hCimg]
    exact himSphere 1 iccOne (by simp [iccOne]; norm_num)

end Shell

end GC.GraphManifold.Assembly
