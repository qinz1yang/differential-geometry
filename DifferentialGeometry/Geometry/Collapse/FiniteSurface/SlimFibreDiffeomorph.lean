import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimSurfaceFactorApplications
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreProjection
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.BijectiveDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.SmoothDiffeomorph

/-!
# LFR20 item 2: the zero fibre is SMOOTHLY the factor, hence `S²` or `T²`

Blueprint LFR20 (master207A:26358), item 2: "Its connected fiber is smoothly `S²` or `T²`"; proof
step 4 (A:26477–26490): "the whole fiber is the `C^K` graph over `Z` … LFR04 upgrades its `C^K`
diffeomorphism with the compatible smooth `Z` to a smooth diffeomorphism, since `K ≥ 5`". Lane
LFR20-CMP, packet 3 (review 43, row LFR20 (iii)).

`slimSurfaceFactor_zeroFibre_diffeomorph` (deterministic, no limit): for a slim chart `c`, ANY
LC81 product model `P : SlimProductModel c K` (`K ≥ 5`) and ANY surface factor
`Q : SlimSurfaceFactor P`, the entire zero fibre `{x : slab // η x = 0}` of `η` on the slab
`{x ∈ B(p, L) | |η x| < 905·10³Δ}`, with the regular-fibre smooth structure used by
`SlimChart.trivial`, is smoothly diffeomorphic to the surface `Q.S` of the SAME model, and hence to
the round `S²` or to `AddCircle 1 × AddCircle 1` (LFR17 on `Q`).

Route. The map `g : y ↦ ψ⁻¹((e (j⁻¹ y))_W)` (projection of the actual fibre to the factor through
the SAME `j` and the SAME splitting) is `C^K`; it is bijective — every fibre point is `j` of a
cylinder point (`P.fibres`), `η ∘ j` is strictly increasing along the coordinate lines (LFR20.1 and
`strictMonoOn_comp_splitting_line`) and changes sign on `[-b, b]` (value clause) — and its
differential is injective: the projection kills exactly the vertical line `ℝ V`
(`mfderiv_vertical_eq_zero_of_const_on_lines` and the inverse product map) while
`d(η ∘ j)(V) > 3/4` and `η` is constant on the fibre. By the finite-order inverse function theorem
it is a `C^K` diffeomorphism (`exists_diffeomorph_of_bijective_mfderiv`), and LFR04
(`nonempty_diffeomorph_of_diffeomorph`) makes it smooth.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function Metric WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Manifold.SmoothApproximation
open DifferentialGeometry.Coordinates GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

attribute [local instance] SlimSurfaceFactor.instMetricS SlimSurfaceFactor.instChartedS
  SlimSurfaceFactor.instManifoldS SlimSurfaceFactor.instBundleS SlimSurfaceFactor.instRiemannianS

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "P2" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance nezero_finrank_euclidean_three_fibreDiffeo_LFR20CMP :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

variable {M : Type*} [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]

/-- **LFR20 item 2, smooth type.** See the module docstring. -/
theorem slimSurfaceFactor_zeroFibre_diffeomorph {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
    {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
    {c : SlimChart g hEnorm Δ σ α} {K : ℕ} (hK : 5 ≤ K) (hΔ : 1 ≤ Δ) (P : SlimProductModel c K)
    (Q : SlimSurfaceFactor P) :
    let f := realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
      c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
    let z₀ : lineBallOpens (905 * 10 ^ 3 * Δ) := ⟨0, zero_mem_lineBallOpens (by positivity)⟩
    let _ := regularFiberChartedSpace f z₀
      (contMDiff_realSlabMap isOpen_ball
        (c.contMDiffOn_coord.mono (ball_subset_closedBall.trans c.closedBall_subset_domain)) _)
      (fun x _ ↦ surjective_mfderiv_realSlabMap isOpen_ball
        (c.contMDiffOn_coord.mono (ball_subset_closedBall.trans c.closedBall_subset_domain))
        c.regular x)
    Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Q.S) ∧
    (Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
      Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
        (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  intro f z₀ instF
  have hΔ0 : 0 < Δ := by linarith
  have hcoordU : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ c.coord (ball p (10 ^ 6 * Δ)) :=
    c.contMDiffOn_coord.mono (ball_subset_closedBall.trans c.closedBall_subset_domain)
  have hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ f := contMDiff_realSlabMap isOpen_ball hcoordU _
  have hreg : ∀ x, f x = z₀ → Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) f x) :=
    fun x _ ↦ surjective_mfderiv_realSlabMap isOpen_ball hcoordU c.regular x
  let F := {x // f x = z₀}
  have hFman : IsManifold 𝓘(ℝ, P2) ∞ F := regularFiberIsManifold f z₀ hf hreg
  have hK0 : (K : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hK1 : (1 : ℕ∞ω) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hKinf : (K : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  -- the inclusion of the fibre
  let ι : F → M := fun y => (((y : realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
    c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ))) : M)
  have hι : ContMDiff 𝓘(ℝ, P2) 𝓘(ℝ, E3) ∞ ι :=
    contMDiff_subtype_val.comp (contMDiff_regularFiberInclusion f z₀ hf hreg)
  have hιmem : ∀ y : F, ι y ∈ ball p (10 ^ 6 * Δ) ∧ c.coord (ι y) = 0 := by
    intro y
    refine ⟨(mem_realSlabOpens_iff.mp y.1.2).1, ?_⟩
    have h := congrArg Subtype.val y.2
    rw [realSlabMap_coe] at h
    exact h
  have hιtarget : ∀ y : F, ι y ∈ P.j.target := fun y =>
    (P.exists_cylinder_of_coord_eq_zero hΔ0 (hιmem y).1 (hιmem y).2).choose_spec.2.2.2.1
  -- the projection of the fibre to the factor
  let G : F → Q.S := fun y => Q.ψ.symm (P.e (P.j.symm (ι y))).snd
  have hG : ContMDiff 𝓘(ℝ, P2) (𝓡 2) K G := by
    intro y
    have h1 : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) K P.j.symm (ι y) :=
      P.j.symm.contMDiffOn.contMDiffAt (P.j.symm.open_source.mem_nhds (hιtarget y))
    exact (Q.contMDiff_proj _).comp y (h1.comp y ((hι y).of_le hKinf))
  have hGinj : Injective G := fun y₁ y₂ h => Subtype.ext (Subtype.ext
    (Q.eq_of_proj_eq (by omega) hΔ0 (hιmem y₁).1 (hιmem y₁).2 (hιmem y₂).1 (hιmem y₂).2 h))
  have hGsurj : Surjective G := by
    intro s
    obtain ⟨m, hm, h0, hs⟩ := Q.exists_proj_eq (by omega) hΔ0 s
    have hmU : m ∈ realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
        c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) :=
      mem_realSlabOpens_iff.mpr ⟨hm, by rw [h0, abs_zero]; positivity⟩
    exact ⟨⟨⟨m, hmU⟩, Subtype.ext (by rw [realSlabMap_coe]; exact h0)⟩, hs⟩
  -- the differential of `G` is bijective
  have hDG : ∀ y : F, Bijective (mfderiv 𝓘(ℝ, P2) (𝓡 2) G y) := by
    intro y
    have hιd : MDifferentiableAt 𝓘(ℝ, P2) 𝓘(ℝ, E3) ι y := (hι y).mdifferentiableAt (by simp)
    have hjsd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j.symm (ι y) :=
      P.j.symm.mdifferentiableAt hK0 (hιtarget y)
    have hprd : MDifferentiableAt 𝓘(ℝ, E3) (𝓡 2) (fun x : P.N => Q.ψ.symm (P.e x).snd)
        (P.j.symm (ι y)) := (Q.contMDiff_proj _).mdifferentiableAt hK0
    have hGd : ∀ u, mfderiv 𝓘(ℝ, P2) (𝓡 2) G y u =
        mfderiv 𝓘(ℝ, E3) (𝓡 2) (fun x : P.N => Q.ψ.symm (P.e x).snd) (P.j.symm (ι y))
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j.symm (ι y) (mfderiv 𝓘(ℝ, P2) 𝓘(ℝ, E3) ι y u)) := by
      intro u
      have h1 := mfderiv_comp y hjsd hιd
      have h2 := mfderiv_comp y hprd (hjsd.comp y hιd)
      have h3 : G = (fun x : P.N => Q.ψ.symm (P.e x).snd) ∘ (P.j.symm ∘ ι) := rfl
      rw [h3, h2, h1]
      rfl
    have hιinj : Injective (mfderiv 𝓘(ℝ, P2) 𝓘(ℝ, E3) ι y) := by
      have hv1 : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3)
          (Subtype.val : realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
            c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) → M) (y : _) :=
        (contMDiff_subtype_val (n := ∞) _).mdifferentiableAt (by simp)
      have hv2 : MDifferentiableAt 𝓘(ℝ, P2) 𝓘(ℝ, E3) (Subtype.val : F → _) y :=
        ((contMDiff_regularFiberInclusion f z₀ hf hreg) y).mdifferentiableAt (by simp)
      have h := mfderiv_comp y hv1 hv2
      have hι' : ι = Subtype.val ∘ (Subtype.val : F → _) := rfl
      intro u v huv
      have huv' := huv
      rw [hι', h] at huv'
      simp only [ContinuousLinearMap.comp_apply, DifferentialGeometry.mfderiv_subtype_val_apply]
        at huv'
      exact mfderiv_regularFiberInclusion_injective f z₀ hf hreg y huv'
    have hηι : ∀ u, mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) c.coord (ι y) (mfderiv 𝓘(ℝ, P2) 𝓘(ℝ, E3) ι y u) =
        0 := by
      intro u
      have h := mfderiv_comp y (c.mdifferentiableAt_coord_of_mem_ball (hιmem y).1) hιd
      have hconst : c.coord ∘ ι = fun _ => (0 : ℝ) := funext fun y' => (hιmem y').2
      rw [hconst, mfderiv_const] at h
      exact (congrArg (fun L => L u) h).symm
    have hker : ∀ u, mfderiv 𝓘(ℝ, P2) (𝓡 2) G y u = 0 → u = 0 := by
      intro u hu
      rw [hGd] at hu
      have ha := Q.eq_zero_of_mfderiv_coord_proj (by omega) hΔ0 (hιmem y).1 (hιmem y).2 _
        (hηι u) hu
      exact hιinj (ha.trans (map_zero _).symm)
    have hinj : Injective (mfderiv 𝓘(ℝ, P2) (𝓡 2) G y) := by
      rw [← ContinuousLinearMap.coe_coe, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      exact hker
    refine ⟨hinj, ?_⟩
    have hfin : Module.finrank ℝ (TangentSpace 𝓘(ℝ, P2) y) =
        Module.finrank ℝ (TangentSpace (𝓡 2) (G y)) := finrank_splittingSurfaceModel_eq
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
      (f := (mfderiv 𝓘(ℝ, P2) (𝓡 2) G y).toLinearMap)).mp hinj
  -- conclusion
  have hFcpt : CompactSpace F :=
    isCompact_iff_compactSpace.mp (c.isProperMap.isCompact_preimage isCompact_singleton)
  have _ := Q.compactSpace
  have _ := Q.connectedSpace
  have hFK : IsManifold 𝓘(ℝ, P2) (K : ℕ∞ω) F := IsManifold.of_le hKinf
  have hSK : IsManifold (𝓡 2) (K : ℕ∞ω) Q.S := IsManifold.of_le hKinf
  obtain ⟨ΦK, -⟩ := exists_diffeomorph_of_bijective_mfderiv hK1
    (show (K : ℕ∞ω) ≠ ∞ from by exact_mod_cast (WithTop.natCast_ne_top K)) hG
    ⟨hGinj, hGsurj⟩ hDG
  obtain ⟨Φs⟩ := nonempty_diffeomorph_of_diffeomorph K (by omega) ΦK
  refine ⟨⟨Φs⟩, ?_⟩
  rcases Q.sphere_or_flat_torus (by omega) with ⟨⟨Ψs⟩⟩ | ⟨⟨Ψt⟩, -⟩
  · exact Or.inl ⟨Φs.trans Ψs⟩
  · exact Or.inr ⟨Φs.trans Ψt⟩

end DifferentialGeometry.Geometry.Collapse
