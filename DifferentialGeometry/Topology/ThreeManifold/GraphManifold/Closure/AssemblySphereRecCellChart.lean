import DifferentialGeometry.Topology.Manifold.ClosedBall.Extension
import DifferentialGeometry.Topology.Manifold.ClosedBall.BallChart
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.SphereDirection
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutBallChart
import DifferentialGeometry.Topology.ThreeManifold.TwoBallCover

/-!
# FC42 sphere recursion, packet S3a (tools): ball charts of full-rank closed cells, two-cell spheres

Lane ASM-SPH. The tree extends a SMOOTH EMBEDDING (Mathlib's `IsSmoothEmbedding`, an immersion in
the chart-normal-form sense) of the closed `3`-cell to a ball chart
(`exists_partialDiffeomorph_extension_closedCell`, `Manifold/ClosedBall/Extension.lean`;
`exists_ballChart_of_closedCell_interior`, `Closure/AssemblySphereCutBallChart.lean`). The lifted
ball vertex of a sphere cut is only known to be smooth, injective and of bijective differential
(a `PieceEmbedding`), and the chart-normal-form immersion property is not available at boundary
points of a manifold with boundary. The proofs of those two lemmas use the embedding only through
these three properties; here they are redone with exactly those hypotheses:

* `exists_ballChart_of_closedCell_bijective`: into a manifold without boundary (model `𝓡 3`);
  the interior part is the injective local diffeomorphism on the open ball
  (`exists_partialDiffeomorph_of_injOn`), the boundary part a two-sided collar extending the radial
  half collar (`exists_smoothTwoSidedCollar_of_halfClosedInterval`), glued over the compact closed
  ball (`PartialDiffeomorph.exists_gluing_of_isCompact`). The radial half-cell map and the closed
  cell insertion are copied from `Manifold/ClosedBall/Collar.lean` and `…/BallChart.lean`, where
  they are private.
* `nonempty_sphereDiffeomorph_of_closedCell_cover`: an open set of interior points that is the union
  of the images of two such cells is diffeomorphic to the round `S³` (two ball charts,
  `exists_sphere_diffeomorph_of_ball_chart_cover`, `TwoBallCover.lean`). No condition on how the two
  cells meet: this absorbs an arbitrary attaching map.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASMSPH : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASMSPH : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance ballChartsSucc_ASMSPH : ChartedSpace (EuclideanHalfSpace (2 + 1)) (ClosedCell (2 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothSucc_ASMSPH : IsManifold (𝓡∂ (2 + 1)) ∞ (ClosedCell (2 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance sphereDim_ASMSPH : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

local instance sphereDimFour_ASMSPH :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

local instance halfCharts_ASMSPH : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) (1 / 2)) :=
  halfClosedIntervalChartedSpace (by norm_num : (0 : ℝ) < 1 / 2)

local instance halfSmooth_ASMSPH : IsManifold (𝓡∂ 1) ∞ (Ico (0 : ℝ) (1 / 2)) :=
  halfClosedInterval_isManifold (by norm_num : (0 : ℝ) < 1 / 2)

/-! ## The closed cell insertion and the radial half cell (copies of private tree helpers) -/

/-- The insertion of `ℝ³` into the closed cell: the identity on the closed ball. -/
def cellInsertion (x : EuclideanSpace ℝ (Fin 3)) : ClosedCell 3 :=
  if hx : ‖x‖ ≤ 1 then ⟨x, hx⟩ else ⟨0, by simp⟩

theorem cellInsertion_val {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ < 1) :
    (cellInsertion x).val = x := by
  rw [cellInsertion, dite_eq_left hx.le]

theorem cellInsertion_eventually {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ < 1) :
    (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ∘ cellInsertion =ᶠ[𝓝 x] id := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
  exact cellInsertion_val hy

theorem cellInsertion_contMDiffAt {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ < 1) :
    ContMDiffAt (𝓡 3) (𝓡∂ 3) ∞ cellInsertion x := by
  have hi := cellInsertion_eventually hx
  apply (ContMDiffAt.iff_comp_isImmersionAt
    ((isSmoothEmbedding_closedCell_inclusion 2).isImmersion.isImmersionAt
      (cellInsertion x))).mpr
  refine ⟨?_, hi.contMDiffAt_iff.mpr contMDiffAt_id⟩
  exact _root_.Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (continuousAt_id.congr hi.symm)

theorem cellInsertion_injective_mfderiv {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ < 1) :
    Injective (mfderiv (𝓡 3) (𝓡∂ 3) cellInsertion x) := by
  have hc := mfderiv_comp x
    ((isSmoothEmbedding_closedCell_inclusion 2).contMDiff.mdifferentiableAt (by simp))
    ((cellInsertion_contMDiffAt hx).mdifferentiableAt (by simp))
  rw [(cellInsertion_eventually hx).mfderiv_eq, mfderiv_id] at hc
  intro v w hvw
  have h := congrArg (mfderiv (𝓡∂ 3) (𝓡 3)
    (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) (cellInsertion x)) hvw
  have heq (u : TangentSpace (𝓡 3) x) :=
    congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => L u) hc
  exact (heq v).trans (h.trans (heq w).symm)

theorem norm_radial_le (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {t : ℝ} (ht : 0 ≤ t)
    (ht' : t ≤ 1) : ‖(1 - t) • z.val‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht'), norm_eq_of_mem_sphere,
    mul_one]
  linarith

/-- The radial half cell `(z, t) ↦ (1 - t) z`, near the boundary sphere. -/
def radialHalf (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Ico (0 : ℝ) (1 / 2)) :
    ClosedCell 3 :=
  ⟨(1 - p.2.val) • p.1.val, norm_radial_le p.1 p.2.property.1 (by linarith [p.2.property.2])⟩

theorem contMDiff_radialHalf : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ radialHalf := by
  have hi : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (Subtype.val : Ico (0 : ℝ) (1 / 2) → ℝ) :=
    (isSmoothEmbedding_halfClosedInterval_inclusion (by norm_num : (0 : ℝ) < 1 / 2)).contMDiff
  have hrad : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Ico (0 : ℝ) (1 / 2) =>
        (1 - p.2.val) • p.1.val) :=
    (contMDiff_const.sub (hi.comp contMDiff_snd)).smul
      (contMDiff_coe_sphere.comp contMDiff_fst)
  apply (ContMDiff.iff_comp_isImmersion (isSmoothEmbedding_closedCell_inclusion 2).isImmersion).mpr
  exact ⟨hrad.continuous.subtype_mk _, hrad⟩

/-- The reflection `t ↦ 1 - t` of the line. -/
def reverseLine : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun t := 1 - t
  invFun t := 1 - t
  left_inv t := by dsimp; ring
  right_inv t := by dsimp; ring
  contMDiff_toFun := contMDiff_const.sub contMDiff_id
  contMDiff_invFun := contMDiff_const.sub contMDiff_id

theorem mfderiv_radialHalf_bijective
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Ico (0 : ℝ) (1 / 2)) :
    Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) radialHalf p) := by
  let e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Ico (0 : ℝ) (1 / 2) →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ := Prod.map id Subtype.val
  have hs : IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (Subtype.val : Ico (0 : ℝ) (1 / 2) → ℝ) :=
    isSmoothEmbedding_halfClosedInterval_inclusion (by norm_num : (0 : ℝ) < 1 / 2)
  have he : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e :=
    contMDiff_id.prodMap hs.contMDiff
  have hBe : Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e p) := by
    have hBs : Bijective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Ico (0 : ℝ) (1 / 2) → ℝ) p.2) :=
      bijective_mfderiv_of_isImmersionAt (𝓡∂ 1) 𝓘(ℝ, ℝ) Subtype.val p.2
        (hs.isImmersion.isImmersionAt p.2) (by simp)
    rw [mfderiv_prodMap mdifferentiableAt_id (hs.contMDiff.mdifferentiable (by simp) _), mfderiv_id]
    exact Function.bijective_id.prodMap hBs
  let R : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ∞ :=
    (Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
      reverseLine
  let g : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun q => (R q).2 • ((R q).1 : EuclideanSpace ℝ (Fin 3))
  have hpos : 0 < (R (e p)).2 := by
    change 0 < 1 - p.2.val
    linarith [p.2.property.2]
  have hg : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ g (e p) :=
    (R.isLocalDiffeomorph (e p)).comp (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      (isLocalDiffeomorphAt_sphere_smul (R (e p)) hpos)
  have hBg : Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) g (e p)) :=
    (hg.mfderivToContinuousLinearEquiv (by simp)).bijective
  have hcomp : mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3)
      ((Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ∘ radialHalf) p =
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) g (e p)).comp
        (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e p) :=
    mfderiv_comp p (hg.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))
  have hB : Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3)
      ((Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ∘ radialHalf) p) := by
    rw [hcomp]
    exact hBg.comp hBe
  have hchain := mfderiv_comp p
    ((isSmoothEmbedding_closedCell_inclusion 2).contMDiff.mdifferentiableAt (by simp))
    (contMDiff_radialHalf.mdifferentiableAt (by simp))
  rw [hchain] at hB
  change Bijective
    ((mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) (radialHalf p)) ∘
      (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) radialHalf p)) at hB
  exact Bijective.of_comp_left hB
    (((isSmoothEmbedding_closedCell_inclusion 2).isImmersion.isImmersionAt _).mfderiv_injective
      (by simp))

/-! ## Ball charts of full-rank closed cells in a manifold without boundary -/

section Boundaryless

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N]

omit [T2Space N] in
/-- The interior part: an injective full-rank closed cell restricts to a partial diffeomorphism on
the open unit ball. -/
theorem exists_partialDiffeomorph_of_closedCell_bijective (f : ClosedCell 3 → N)
    (hf : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ f) (hinj : Injective f)
    (hbij : ∀ x, Bijective (mfderiv (𝓡∂ 3) (𝓡 3) f x)) :
    ∃ φ : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) N ∞,
      φ.source = Metric.ball 0 1 ∧ ∀ (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ < 1),
        φ x = f ⟨x, hx.le⟩ := by
  let g : EuclideanSpace ℝ (Fin 3) → N := f ∘ cellInsertion
  have hs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g (Metric.ball 0 1) := by
    intro x hx
    have hx' : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    exact (hf.contMDiffAt.comp x (cellInsertion_contMDiffAt hx')).contMDiffWithinAt
  have hlocal : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ g (Metric.ball 0 1) := by
    intro x
    have hx : ‖x.val‖ < 1 := mem_ball_zero_iff.mp x.property
    have hder : Injective (mfderiv (𝓡 3) (𝓡 3) g x.val) := by
      rw [show g = f ∘ cellInsertion from rfl,
        mfderiv_comp x.val (hf.mdifferentiableAt (by simp))
          ((cellInsertion_contMDiffAt hx).mdifferentiableAt (by simp))]
      exact (hbij _).1.comp (cellInsertion_injective_mfderiv hx)
    let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      mfderiv (𝓡 3) (𝓡 3) g x.val
    have hD : Injective D := hder
    let A : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (D.toLinearMap.linearEquivOfInjective hD rfl).toContinuousLinearEquiv
    exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv g hs Metric.isOpen_ball
      x.val x.property A
      ((hs.contMDiffAt (Metric.isOpen_ball.mem_nhds x.property)).mdifferentiableAt
        (by simp)).hasMFDerivAt
  have hinjOn : InjOn g (Metric.ball 0 1) := by
    intro x hx y hy h
    have hx' : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    have hy' : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
    have h' := congrArg Subtype.val (hinj h)
    simpa only [cellInsertion_val hx', cellInsertion_val hy'] using h'
  have hne : Nonempty (EuclideanSpace ℝ (Fin 3)) := ⟨0⟩
  obtain ⟨φ, hsource, -, hφ⟩ :=
    exists_partialDiffeomorph_of_injOn Metric.isOpen_ball hlocal hinjOn
  refine ⟨φ, hsource, fun x hx => ?_⟩
  rw [hφ]
  change f (cellInsertion x) = f ⟨x, hx.le⟩
  congr 1
  exact Subtype.ext (cellInsertion_val hx)

/-- The boundary part: a two-sided collar of the boundary sphere extending the radial half cell. -/
theorem exists_collar_of_closedCell_bijective (f : ClosedCell 3 → N)
    (hf : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ f) (hinj : Injective f)
    (hbij : ∀ x, Bijective (mfderiv (𝓡∂ 3) (𝓡 3) f x)) :
    ∃ d : SmoothTwoSidedCollar (𝓡 2) (𝓡 3)
        (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
          f ⟨z.val, (norm_eq_of_mem_sphere z).le⟩),
      ∃ _hwidth : d.radius ≤ 1 / 2,
      ∀ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × symmetricOpenInterval d.radius)
        (hp : 0 ≤ p.2.val),
        d.toFun p = f ⟨(1 - p.2.val) • p.1.val, by
          apply norm_radial_le p.1 hp
          linarith [p.2.property.2]⟩ := by
  let c := f ∘ radialHalf
  have hc : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ c := hf.comp contMDiff_radialHalf
  have hinj0 : Injective (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      c (z, (⟨0, by constructor <;> norm_num⟩ : Ico (0 : ℝ) (1 / 2)))) := by
    intro z w h
    have h' := congrArg Subtype.val (hinj h)
    apply Subtype.ext
    simpa only [radialHalf, sub_zero, one_smul] using h'
  have hderiv : ∀ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) c
        (z, (⟨0, by constructor <;> norm_num⟩ : Ico (0 : ℝ) (1 / 2)))) := by
    intro z
    rw [show c = f ∘ radialHalf from rfl, mfderiv_comp _ (hf.mdifferentiableAt (by simp))
      (contMDiff_radialHalf.mdifferentiableAt (by simp))]
    exact (hbij _).comp (mfderiv_radialHalf_bijective _)
  have hzero : (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      c (z, (⟨0, by constructor <;> norm_num⟩ : Ico (0 : ℝ) (1 / 2)))) =
      fun z => f ⟨z.val, (norm_eq_of_mem_sphere z).le⟩ := by
    funext z
    change f ⟨(1 - 0) • z.val, _⟩ = _
    congr 1
    exact Subtype.ext (by simp)
  obtain ⟨d, hwidth, hd⟩ := exists_smoothTwoSidedCollar_of_halfClosedInterval
    (J := 𝓡 2) (I := 𝓡 3) (by norm_num : (0 : ℝ) < 1 / 2) c hc hinj0 hderiv
  let d' : SmoothTwoSidedCollar (𝓡 2) (𝓡 3)
      (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        f ⟨z.val, (norm_eq_of_mem_sphere z).le⟩) :=
    { radius := d.radius
      radius_pos := d.radius_pos
      neighborhood := d.neighborhood
      toDiffeomorph := d.toDiffeomorph
      zero_eq := fun z => (d.zero_eq z).trans (congrFun hzero z) }
  exact ⟨d', hwidth, hd⟩

/-- **Ball chart of an injective full-rank closed cell** in a manifold without boundary. -/
theorem exists_ballChart_of_closedCell_bijective (f : ClosedCell 3 → N)
    (hf : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ f) (hinj : Injective f)
    (hbij : ∀ x, Bijective (mfderiv (𝓡∂ 3) (𝓡 3) f x)) :
    ∃ φ : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) N ∞,
      Metric.closedBall 0 1 ⊆ φ.source ∧ ∀ x : ClosedCell 3, φ x.val = f x := by
  let v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨φ₀, h₀source, h₀eq⟩ := exists_partialDiffeomorph_of_closedCell_bijective f hf hinj hbij
  obtain ⟨d, _hw, hd⟩ := exists_collar_of_closedCell_bijective f hf hinj hbij
  let φ₁ := d.radialPartialDiffeomorph v
  have h₁eq (x : ClosedCell 3) (hx : x.val ∈ φ₁.source) : φ₁ x.val = f x := by
    obtain ⟨hne, ht⟩ := (d.mem_radialPartialDiffeomorph_source_iff v x.val).mp hx
    let z := sphereDirection v x.val
    have heq := d.radialPartialDiffeomorph_apply v z ‖x.val‖ (norm_pos_iff.mpr hne) ht
    rw [norm_smul_sphereDirection v hne] at heq
    change φ₁ x.val = d.toFun (z, ⟨1 - ‖x.val‖, ht⟩) at heq
    refine heq.trans ((hd (z, ⟨1 - ‖x.val‖, ht⟩) (sub_nonneg.mpr x.property)).trans ?_)
    apply congrArg f
    apply Subtype.ext
    dsimp only
    rw [sub_sub_cancel, norm_smul_sphereDirection v hne]
  let φ : Bool → PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) N ∞ :=
    fun b => if b then φ₁ else φ₀
  have heq (i : Bool) (x : ClosedCell 3) (hx : x.val ∈ (φ i).source) : φ i x.val = f x := by
    cases i with
    | false =>
      have hnorm : ‖x.val‖ < 1 := mem_ball_zero_iff.mp (h₀source ▸ hx)
      exact h₀eq x.val hnorm
    | true => exact h₁eq x hx
  have hcover : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ ⋃ i, (φ i).source := by
    intro x hx
    have hnorm := mem_closedBall_zero_iff.mp hx
    by_cases hlt : ‖x‖ < 1
    · exact mem_iUnion.mpr ⟨false, h₀source ▸ mem_ball_zero_iff.mpr hlt⟩
    · have hsphere : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
        mem_sphere_zero_iff_norm.mpr (le_antisymm hnorm (le_of_not_gt hlt))
      exact mem_iUnion.mpr ⟨true, d.sphere_subset_radialPartialDiffeomorph_source v hsphere⟩
  have hover (i j : Bool) : EqOn (φ i) (φ j) ((φ i).source ∩ (φ j).source) := by
    intro x hx
    by_cases hij : i = j
    · rw [hij]
    have hlt : ‖x‖ < 1 := by
      cases i <;> cases j
      · exact (hij rfl).elim
      · exact mem_ball_zero_iff.mp (h₀source ▸ hx.1)
      · exact mem_ball_zero_iff.mp (h₀source ▸ hx.2)
      · exact (hij rfl).elim
    exact (heq i ⟨x, hlt.le⟩ hx.1).trans (heq j ⟨x, hlt.le⟩ hx.2).symm
  have himage (i j : Bool) :
      φ i '' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∩ (φ i).source) ∩
        φ j '' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∩ (φ j).source) ⊆
        φ i '' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∩ (φ i).source ∩
          (φ j).source) := by
    rintro y ⟨⟨x, hx, rfl⟩, ⟨z, hz, hzx⟩⟩
    have hfx : f ⟨x, mem_closedBall_zero_iff.mp hx.1⟩ =
        f ⟨z, mem_closedBall_zero_iff.mp hz.1⟩ :=
      (heq i ⟨x, mem_closedBall_zero_iff.mp hx.1⟩ hx.2).symm.trans
        (hzx.symm.trans (heq j ⟨z, mem_closedBall_zero_iff.mp hz.1⟩ hz.2))
    have hxz : x = z := congrArg Subtype.val (hinj hfx)
    exact ⟨x, ⟨hx, hxz ▸ hz.2⟩, rfl⟩
  obtain ⟨ψ, hs, hψ⟩ := PartialDiffeomorph.exists_gluing_of_isCompact φ
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    ⟨0, Metric.mem_closedBall_self zero_le_one⟩
    (fun i => (φ i).open_source) (fun _ => subset_rfl) hcover hover himage
  refine ⟨ψ, hs, ?_⟩
  intro x
  have hx : x.val ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    mem_closedBall_zero_iff.mpr x.property
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  exact (hψ i ⟨hs hx, hi⟩).trans (heq i x hi)

end Boundaryless

/-! ## Cells in an open set of interior points; the two-cell three-sphere -/

section Interior

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
/-- An open set of interior points is a manifold without boundary. -/
theorem boundarylessManifold_of_forall_isInteriorPoint (U : TopologicalSpace.Opens M)
    (hU : ∀ y ∈ U, I.IsInteriorPoint y) : BoundarylessManifold I U :=
  ⟨fun x => I.isInteriorPoint_iff_isInteriorPoint_val.mpr (hU x.1 x.2)⟩

omit [IsManifold I ∞ M] in
/-- A full-rank cell into an open set, read in the open set. -/
theorem cell_restrict_properties (U : TopologicalSpace.Opens M) (f : ClosedCell 3 → U)
    (hf : ContMDiff (𝓡∂ 3) I ∞ (fun x => (f x : M)))
    (hfb : ∀ x, Bijective (mfderiv (𝓡∂ 3) I (fun x => (f x : M)) x)) :
    ContMDiff (𝓡∂ 3) I ∞ f ∧ ∀ x, Bijective (mfderiv (𝓡∂ 3) I f x) := by
  refine ⟨(ContMDiff.subtypeVal_comp_iff U f).mp hf, fun x => ?_⟩
  rw [← DifferentialGeometry.Topology.mfderiv_subtypeVal_comp U f x]
  exact hfb x

variable [T2Space M]

/-- **Two cells make a three-sphere.** An open set of interior points that is the union of the
images of two injective full-rank closed cells is diffeomorphic to the round `S³`. -/
theorem nonempty_sphereDiffeomorph_of_closedCell_cover (U : TopologicalSpace.Opens M)
    (hU : ∀ y ∈ U, I.IsInteriorPoint y) (f g : ClosedCell 3 → M)
    (hf : ContMDiff (𝓡∂ 3) I ∞ f) (hg : ContMDiff (𝓡∂ 3) I ∞ g) (hfi : Injective f)
    (hgi : Injective g) (hfb : ∀ x, Bijective (mfderiv (𝓡∂ 3) I f x))
    (hgb : ∀ x, Bijective (mfderiv (𝓡∂ 3) I g x)) (hcov : range f ∪ range g = U) :
    Nonempty (U ≃ₘ⟮I, 𝓡 3⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  have hUb : BoundarylessManifold I U := boundarylessManifold_of_forall_isInteriorPoint U hU
  have hfU : ∀ x, f x ∈ U := fun x => by
    change f x ∈ (U : Set M)
    rw [← hcov]
    exact Or.inl ⟨x, rfl⟩
  have hgU : ∀ x, g x ∈ U := fun x => by
    change g x ∈ (U : Set M)
    rw [← hcov]
    exact Or.inr ⟨x, rfl⟩
  let f' : ClosedCell 3 → U := fun x => ⟨f x, hfU x⟩
  let g' : ClosedCell 3 → U := fun x => ⟨g x, hgU x⟩
  obtain ⟨hf', hfb'⟩ := cell_restrict_properties U f' hf hfb
  obtain ⟨hg', hgb'⟩ := cell_restrict_properties U g' hg hgb
  let := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  have := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let D := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  have hDb : ∀ y : U, Bijective (mfderiv I (𝓡 3) D y) := fun y =>
    (D.mfderivToContinuousLinearEquiv (by simp) y).bijective
  have hcell : ∀ c : ClosedCell 3 → U, ContMDiff (𝓡∂ 3) I ∞ c →
      (∀ x, Bijective (mfderiv (𝓡∂ 3) I c x)) →
      ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (D ∘ c) ∧ ∀ x, Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (D ∘ c) x) := by
    intro c hc hcb
    refine ⟨D.contMDiff.comp hc, fun x => ?_⟩
    rw [mfderiv_comp x (D.contMDiff.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
    exact (hDb (c x)).comp (hcb x)
  obtain ⟨hA, hAb⟩ := hcell f' hf' hfb'
  obtain ⟨hB, hBb⟩ := hcell g' hg' hgb'
  have hAi : Injective (D ∘ f') := fun x y h => hfi (congrArg Subtype.val h)
  have hBi : Injective (D ∘ g') := fun x y h => hgi (congrArg Subtype.val h)
  obtain ⟨A, hAs, hAeq⟩ := exists_ballChart_of_closedCell_bijective (D ∘ f') hA hAi hAb
  obtain ⟨B, hBs, hBeq⟩ := exists_ballChart_of_closedCell_bijective (D ∘ g') hB hBi hBb
  have hcover : B '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∪
      A '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 = univ := by
    refine eq_univ_of_forall fun y => ?_
    have hy : (y : M) ∈ range f ∪ range g := by rw [hcov]; exact y.2
    rcases hy with ⟨x, hx⟩ | ⟨x, hx⟩
    · refine Or.inr ⟨x.val, mem_closedBall_zero_iff.mpr x.2, ?_⟩
      rw [hAeq x]
      exact Subtype.ext hx
    · refine Or.inl ⟨x.val, mem_closedBall_zero_iff.mpr x.2, ?_⟩
      rw [hBeq x]
      exact Subtype.ext hx
  obtain ⟨e, -⟩ := exists_sphere_diffeomorph_of_ball_chart_cover A B hAs hBs hcover
  exact ⟨D.trans e⟩

end Interior

end GC.GraphManifold.Assembly
