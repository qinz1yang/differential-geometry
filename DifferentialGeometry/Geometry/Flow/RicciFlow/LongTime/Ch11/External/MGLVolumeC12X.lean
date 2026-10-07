import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Lattices.ThickPartCompactness
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Manifold
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryVolume
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianDistance
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Boost
import DifferentialGeometry.Geometry.Collapse.CutPieceBallsImage
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
# MGL 后半 (B)：thick 点 ⇒ 一致 ball-volume 下界（O-C12X-MGLB，后缀 `_C12X`）

`exists_ballVolume_lower_of_thick_C12X`：给定 `ε > 0`，存在只依赖 `ε` 的 `c > 0`，使对每个
`H : FiniteVolumeHyperbolicModel`、每个 uniformization 数据 `(Γ, e)`（`e ∘ π[Γ]` local diffeo，
度量拉回 = `4 ×` hyperboloid 度量）与每个 `x ∈ thickPart Γ ε`，
`ofReal c ≤ ballVolume H.metric (e (π[Γ] x)) 1`。

证明（绕开 ball-lifting）：源流形取 hyperboloid `𝕃 = Hyperboloid E₃`，度量 `g₄ = 4 g_hyp`，
`f = (e ∘ π[Γ]) ∘ ψ⁻¹`（`ψ = hUpperDiffeomorph 3`，一个等距）。

1. `f` 在 `ball (ψ x) ρ` 上单射（`2ρ ≤ ε`，thick + PO 作用等距）。
2. 单射 local diffeo ⇒ `PartialDiffeomorph`，`f^* H.metric = g₄` ⇒ 体积相等
   （`riemannianVolumeMeasure_image_of_partialIsometry`）。
3. 齐性：`boost z` 是 `g₄` 的 Riemannian 等距 ⇒ `vol_{g₄} (ball z ρ)` 与 `z` 无关。
4. `riemannianBallOf g₄ z (√4 ρ) = ball z ρ`（`riemannianEDistOf_eq_edist` + scale），
   局部等距不增距离（`riemannianEDistOf_map_le_of_isometricOn`）⇒ 像落在 `H` 的 1-球里。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Bundle ENNReal

open MeasureTheory
open DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.ProjectiveOrthogonalGroup (PO)
open DifferentialGeometry.Hyperbolic (HUpper)
open DifferentialGeometry.LatticeCompactness (thickPart)
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure
  riemannianVolumeMeasure_image_of_partialIsometry riemannianVolumeMeasure_isOpenPosMeasure)

namespace GC.LongTime.Ch11.External

universe u

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private local instance (Δ : Subgroup (PO 3 1)) : MulAction Δ (HUpper 3) :=
  EquivariantMap.subAction (Nat.le_add_left 1 2) Δ

local notation "Q[" G "]" => MulAction.orbitRel.Quotient G (HUpper 3)
local notation "π[" G "]" => Quotient.mk (MulAction.orbitRel G (HUpper 3))

local notation "ψ" => Hyperboloid.hUpperDiffeomorph 3

local notation "g₄" => scaleMetric (I := 𝓡 3) 4 (by norm_num : (0 : ℝ) < 4)
  (Hyperboloid.riemannianMetric (E := E₃))

private local instance : MeasurableSpace (Hyperboloid E₃) := borel (Hyperboloid E₃)
private local instance : BorelSpace (Hyperboloid E₃) := ⟨rfl⟩

/-- 链式法则：`F^* g = 4 ψ^* g_hyp` ⇒ `(F ∘ ψ⁻¹)^* g = 4 g_hyp`
（照抄 `Cusps/Metric.lean` 的 private `metric_inner_comp_hUpperDiffeomorph_symm`，维数 3）。 -/
private theorem mglB_inner_comp_symm {N : Type*} [TopologicalSpace N] [ChartedSpace E₃ N]
    [IsManifold (𝓡 3) ∞ N] (g : SmoothRiemannianMetric (𝓡 3) N) (F : HUpper 3 → N)
    (hF : ContMDiff (𝓡 3) (𝓡 3) ∞ F)
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      g.inner (F p) (mfderiv (𝓡 3) (𝓡 3) F p v) (mfderiv (𝓡 3) (𝓡 3) F p w) =
        4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
          (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
          (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    (x : Hyperboloid E₃) (v w : TangentSpace (𝓡 3) x) :
    g.inner ((F ∘ (ψ).symm) x) (mfderiv (𝓡 3) (𝓡 3) (F ∘ (ψ).symm) x v)
        (mfderiv (𝓡 3) (𝓡 3) (F ∘ (ψ).symm) x w) =
      4 * Hyperboloid.riemannianMetric.inner x v w := by
  let J := Hyperboloid.hUpperDiffeomorph 3
  have hJ : (J : HUpper 3 → Hyperboloid E₃) ∘ J.symm = id := by
    funext y
    exact J.apply_symm_apply y
  change g.inner ((F ∘ J.symm) x) (mfderiv _ _ (F ∘ J.symm) x v)
    (mfderiv _ _ (F ∘ J.symm) x w) = _
  rw [mfderiv_comp_apply x (hF.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp_apply x (hF.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp))]
  change g.inner (F (J.symm x)) _ _ = _
  rw [hmetric]
  have he : 4 * Hyperboloid.riemannianMetric.inner ((J ∘ J.symm) x)
      (mfderiv (𝓡 3) (𝓡 3) (J ∘ J.symm) x v) (mfderiv (𝓡 3) (𝓡 3) (J ∘ J.symm) x w) =
      4 * Hyperboloid.riemannianMetric.inner x v w := by
    rw [hJ, mfderiv_id]
    rfl
  rw [mfderiv_comp_apply x (J.contMDiff.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp_apply x (J.contMDiff.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp))] at he
  exact he

/-- `ψ⁻¹` 把 hyperboloid 上的球映成 `HUpper 3` 上的同半径球。 -/
private theorem mglB_symm_image_ball (x : HUpper 3) (ρ : ℝ) :
    (ψ).symm '' Metric.ball ((ψ) x) ρ = Metric.ball x ρ := by
  have h := (Hyperboloid.hUpperIsometryEquiv 3).symm.image_ball
    (Hyperboloid.hUpperIsometryEquiv 3 x) ρ
  rw [IsometryEquiv.symm_apply_apply] at h
  exact h

/-- 第 1 步：thick 点附近 `f = (e ∘ π[Γ]) ∘ ψ⁻¹` 在半径 `ρ`（`2ρ ≤ ε`）的球上单射。 -/
private theorem mglB_injOn {Γ : Subgroup (PO 3 1)} {X : Type*} [TopologicalSpace X]
    (e : Q[Γ] ≃ₜ X) {ε ρ : ℝ} (hρ : 2 * ρ ≤ ε) {x : HUpper 3}
    (hx : x ∈ thickPart (Nat.le_add_left 1 2) Γ ε) :
    Set.InjOn ((e ∘ π[Γ]) ∘ (ψ).symm) (Metric.ball ((ψ) x) ρ) := by
  intro a ha b hb hab
  have hq : π[Γ] ((ψ).symm a) = π[Γ] ((ψ).symm b) := e.injective hab
  obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hq)
  have hγ' : γ • (ψ).symm b = (ψ).symm a := hγ
  have hda : dist ((ψ).symm a) x < ρ := by
    have h := Set.mem_image_of_mem (ψ).symm ha
    rw [mglB_symm_image_ball x ρ] at h
    exact h
  have hdb : dist ((ψ).symm b) x < ρ := by
    have h := Set.mem_image_of_mem (ψ).symm hb
    rw [mglB_symm_image_ball x ρ] at h
    exact h
  by_cases h1 : γ = 1
  · subst h1
    rw [one_smul] at hγ'
    exact (ψ).symm.injective hγ'.symm
  · exfalso
    have hthick := hx γ h1
    have hiso := HyperbolicAction.po_dist_smul (Nat.le_add_left 1 2) (γ : PO 3 1) ((ψ).symm b) x
    have hγa : (HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul (γ : PO 3 1)
        ((ψ).symm b) = (ψ).symm a := hγ'
    have htri := dist_triangle x ((ψ).symm a)
      ((HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul (γ : PO 3 1) x)
    change dist ((HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul (γ : PO 3 1)
        ((ψ).symm b)) ((HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul (γ : PO 3 1)
        x) = _ at hiso
    rw [hγa] at hiso
    rw [dist_comm x ((ψ).symm a)] at htri
    linarith

/-- 第 3 步（齐性）：`boost z` 是 `g₄` 的 Riemannian 等距，所以 `g₄`-球体积与中心无关。 -/
private theorem mglB_volume_ball_eq (z : Hyperboloid E₃) (ρ : ℝ) :
    riemannianVolumeMeasure (𝓡 3) (Hyperboloid E₃) g₄ (Metric.ball z ρ) =
      riemannianVolumeMeasure (𝓡 3) (Hyperboloid E₃) g₄ (Metric.ball Hyperboloid.origin ρ) := by
  let D := Hyperboloid.isometryDiffeomorph (Hyperboloid.boost z) (n := ∞)
  have hmetric : ∀ (y : Hyperboloid E₃) (u v : TangentSpace (𝓡 3) y),
      (g₄).inner y u v = (g₄).inner (D y) (mfderiv (𝓡 3) (𝓡 3) D y u)
        (mfderiv (𝓡 3) (𝓡 3) D y v) := by
    intro y u v
    simp only [scaleMetric_inner]
    exact congrArg (4 * ·)
      (Hyperboloid.riemannianMetric_inner_mfderiv_isometryEquiv (Hyperboloid.boost z) y u v).symm
  have hmap := Geometry.Measure.riemannianVolumeMeasure_map_of_injective_local_isometry
    g₄ g₄ D D.isLocalDiffeomorph D.injective hmetric
  have hr : Set.range (D : Hyperboloid E₃ → Hyperboloid E₃) = Set.univ :=
    Set.range_eq_univ.mpr D.surjective
  rw [hr, Measure.restrict_univ] at hmap
  have hpre : (D : Hyperboloid E₃ → Hyperboloid E₃) ⁻¹' Metric.ball z ρ =
      Metric.ball Hyperboloid.origin ρ := by
    change (Hyperboloid.boost z) ⁻¹' Metric.ball z ρ = _
    rw [IsometryEquiv.preimage_ball]
    congr 1
    rw [IsometryEquiv.symm_apply_eq, Hyperboloid.boost_origin]
  conv_lhs => rw [← hmap]
  rw [Measure.map_apply D.continuous.measurable Metric.isOpen_ball.measurableSet, hpre]

/-- `g₄`-Riemannian 球 = hyperboloid 度量球（半径 `√4 ρ` 对 `ρ`）。 -/
private theorem mglB_riemannianBallOf_eq (z : Hyperboloid E₃) (ρ : ℝ) :
    riemannianBallOf g₄ z (Real.sqrt 4 * ρ) = Metric.ball z ρ := by
  rw [riemannianBallOf_scaleMetric]
  ext y
  change riemannianEDistOf Hyperboloid.riemannianMetric z y < ENNReal.ofReal ρ ↔ _
  rw [Hyperboloid.riemannianEDistOf_eq_edist, edist_lt_ofReal, Metric.mem_ball, dist_comm]

/-- 第 1–2 步合起来：thick 点附近有一个 source = `ball (ψ x) ρ`、函数 = `(e ∘ π[Γ]) ∘ ψ⁻¹`
的 `PartialDiffeomorph`。 -/
private theorem mglB_exists_partialDiffeomorph {ε ρ : ℝ} (hρ0 : 0 < ρ) (hρ : 2 * ρ ≤ ε)
    (H : FiniteVolumeHyperbolicModel.{u}) {Γ : Subgroup (PO 3 1)} (e : Q[Γ] ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ])) {x : HUpper 3}
    (hx : x ∈ thickPart (Nat.le_add_left 1 2) Γ ε) :
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) (Hyperboloid E₃) H.Carrier ∞,
      Φ.toPartialEquiv.source = Metric.ball ((ψ) x) ρ ∧
        (Φ : Hyperboloid E₃ → H.Carrier) = (e ∘ π[Γ]) ∘ (ψ).symm := by
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ((e ∘ π[Γ]) ∘ (ψ).symm) :=
    isLocalDiffeomorph_comp he (ψ).symm.isLocalDiffeomorph
  obtain ⟨Φ, hΦs, _, hΦf⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (hf.isLocalDiffeomorphOn (Metric.ball ((ψ) x) ρ)) Metric.isOpen_ball
    ⟨(ψ) x, Metric.mem_ball_self hρ0⟩ (mglB_injOn e hρ hx)
  exact ⟨Φ, hΦs, hΦf⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- 第 1–3 步：thick 点 `x` 处半径 `ρ`（`0 < ρ`，`2ρ ≤ ε`）的球在 `H` 中的像，体积恰为
`g₄`-球在 origin 处的体积（与 `H`、`Γ`、`x` 无关）。 -/
theorem mglB_volume_image_ball_C12X {ε ρ : ℝ} (hρ0 : 0 < ρ) (hρ : 2 * ρ ≤ ε)
    (H : FiniteVolumeHyperbolicModel.{u}) (Γ : Subgroup (PO 3 1)) (e : Q[Γ] ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]))
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      H.metric.inner ((e ∘ π[Γ]) p)
          (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p v)
          (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p w) =
        4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
          (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
          (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    {x : HUpper 3} (hx : x ∈ thickPart (Nat.le_add_left 1 2) Γ ε) :
    riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric ((e ∘ π[Γ]) '' Metric.ball x ρ) =
      riemannianVolumeMeasure (𝓡 3) (Hyperboloid E₃) g₄ (Metric.ball Hyperboloid.origin ρ) := by
  obtain ⟨Φ, hΦs, hΦf⟩ := mglB_exists_partialDiffeomorph hρ0 hρ H e he hx
  let Φ₁ : PartialDiffeomorph (𝓡 3) (𝓡 3) (Hyperboloid E₃) H.Carrier 1 :=
    { Φ with
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num) }
  have hΦ₁ : (Φ₁ : Hyperboloid E₃ → H.Carrier) = (e ∘ π[Γ]) ∘ (ψ).symm := hΦf
  have hmet : ∀ y ∈ Φ₁.source, ∀ v w, (g₄).inner y v w =
      H.metric.inner (Φ₁ y) (mfderiv (𝓡 3) (𝓡 3) Φ₁ y v) (mfderiv (𝓡 3) (𝓡 3) Φ₁ y w) := by
    intro y _ v w
    rw [hΦ₁, scaleMetric_inner]
    exact (mglB_inner_comp_symm H.metric (e ∘ π[Γ]) he.contMDiff hmetric y v w).symm
  have hvol := riemannianVolumeMeasure_image_of_partialIsometry g₄ H.metric Φ₁ hmet
    (A := Metric.ball ((ψ) x) ρ) Metric.isOpen_ball.measurableSet (by
      change Metric.ball ((ψ) x) ρ ⊆ Φ.toPartialEquiv.source
      rw [hΦs])
  rw [hΦ₁, Set.image_comp, mglB_symm_image_ball] at hvol
  rw [← hvol, mglB_volume_ball_eq]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- 第 4 步：thick 点 `x` 处半径 `ρ`（`0 < ρ`，`2ρ ≤ ε`，`2ρ ≤ 1`）的球的像落在
`riemannianBallOf H.metric (e (π[Γ] x)) 1` 里（局部等距不增 Riemannian 距离）。 -/
theorem mglB_image_ball_subset_C12X {ε ρ : ℝ} (hρ0 : 0 < ρ) (hρ : 2 * ρ ≤ ε) (hρ1 : 2 * ρ ≤ 1)
    (H : FiniteVolumeHyperbolicModel.{u}) (Γ : Subgroup (PO 3 1)) (e : Q[Γ] ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]))
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      H.metric.inner ((e ∘ π[Γ]) p)
          (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p v)
          (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p w) =
        4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
          (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
          (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    {x : HUpper 3} (hx : x ∈ thickPart (Nat.le_add_left 1 2) Γ ε) :
    (e ∘ π[Γ]) '' Metric.ball x ρ ⊆ riemannianBallOf H.metric (e (π[Γ] x)) 1 := by
  obtain ⟨Φ, hΦs, hΦf⟩ := mglB_exists_partialDiffeomorph hρ0 hρ H e he hx
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hball := mglB_riemannianBallOf_eq ((ψ) x) ρ
  have hsource : riemannianBallOf g₄ ((ψ) x) (Real.sqrt 4 * ρ) ⊆ Φ.source := by
    rw [hball]
    exact hΦs.symm.subset
  have hmet : ∀ y ∈ riemannianBallOf g₄ ((ψ) x) (Real.sqrt 4 * ρ), ∀ v : TangentSpace (𝓡 3) y,
      H.metric.inner (Φ y) (mfderiv (𝓡 3) (𝓡 3) Φ y v) (mfderiv (𝓡 3) (𝓡 3) Φ y v) =
        (g₄).inner y v v := by
    intro y _ v
    rw [hΦf, scaleMetric_inner]
    exact mglB_inner_comp_symm H.metric (e ∘ π[Γ]) he.contMDiff hmetric y v v
  rintro _ ⟨y, hy, rfl⟩
  have hyb : (ψ) y ∈ riemannianBallOf g₄ ((ψ) x) (Real.sqrt 4 * ρ) := by
    rw [← mglB_symm_image_ball x ρ] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    rw [hball, ← hwy, Diffeomorph.apply_symm_apply]
    exact hw
  have hle := riemannianEDistOf_map_le_of_isometricOn g₄ H.metric Φ hsource hmet hyb
  have hΦx : Φ ((ψ) x) = e (π[Γ] x) := by
    rw [hΦf]
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]
  have hΦy : Φ ((ψ) y) = (e ∘ π[Γ]) y := by
    rw [hΦf]
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]
  rw [hΦx, hΦy] at hle
  change riemannianEDistOf H.metric (e (π[Γ] x)) ((e ∘ π[Γ]) y) < ENNReal.ofReal 1
  refine lt_of_le_of_lt hle (lt_of_lt_of_le hyb (ENNReal.ofReal_le_ofReal ?_))
  rw [h4]
  exact hρ1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **(B)** thick 点 ⇒ 一致 ball-volume 下界：`c` 只依赖 `ε`（取 `ρ = min (ε/2) (1/4)`，
`c = (min (vol_{g₄} (ball origin ρ)) 1).toReal`），对每个 `H`、每个 uniformization 数据与每个
`ε`-thick 点 `x` 都有 `ofReal c ≤ ballVolume H.metric (e (π[Γ] x)) 1`。 -/
theorem exists_ballVolume_lower_of_thick_C12X {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (H : FiniteVolumeHyperbolicModel.{u}) (Γ : Subgroup (PO 3 1))
      (e : Q[Γ] ≃ₜ H.Carrier),
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ π[Γ]) →
      (∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
        H.metric.inner ((e ∘ π[Γ]) p)
            (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p v)
            (mfderiv (𝓡 3) (𝓡 3) (e ∘ π[Γ]) p w) =
          4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
            (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
            (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w)) →
      ∀ x : HUpper 3, x ∈ thickPart (Nat.le_add_left 1 2) Γ ε →
        ENNReal.ofReal c ≤ ballVolume H.metric (e (π[Γ] x)) 1 := by
  have hρ0 : 0 < min (ε / 2) (1 / 4 : ℝ) := lt_min (half_pos hε) (by norm_num)
  have hρε : 2 * min (ε / 2) (1 / 4 : ℝ) ≤ ε := by
    have h := min_le_left (ε / 2) (1 / 4 : ℝ)
    linarith
  have hρ1 : 2 * min (ε / 2) (1 / 4 : ℝ) ≤ 1 := by
    have h := min_le_right (ε / 2) (1 / 4 : ℝ)
    linarith
  let V := riemannianVolumeMeasure (𝓡 3) (Hyperboloid E₃) g₄
    (Metric.ball Hyperboloid.origin (min (ε / 2) (1 / 4 : ℝ)))
  let _ := riemannianVolumeMeasure_isOpenPosMeasure (I := 𝓡 3) (M := Hyperboloid E₃) g₄
  have hVpos : 0 < V :=
    Metric.isOpen_ball.measure_pos _ ⟨_, Metric.mem_ball_self hρ0⟩
  have hfin : min V 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨(min V 1).toReal, ENNReal.toReal_pos (lt_min hVpos one_pos).ne' hfin, ?_⟩
  intro H Γ e he hmetric x hx
  rw [ENNReal.ofReal_toReal hfin]
  calc min V 1 ≤ V := min_le_left _ _
    _ = riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
        ((e ∘ π[Γ]) '' Metric.ball x (min (ε / 2) (1 / 4 : ℝ))) :=
      (mglB_volume_image_ball_C12X hρ0 hρε H Γ e he hmetric hx).symm
    _ ≤ ballVolume H.metric (e (π[Γ] x)) 1 :=
      measure_mono (mglB_image_ball_subset_C12X hρ0 hρε hρ1 H Γ e he hmetric hx)

end GC.LongTime.Ch11.External
