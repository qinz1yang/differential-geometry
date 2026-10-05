import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimSurfaceFactor
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SplittingLineVelocity
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreGraphApplications

/-!
# The projection of the slim zero level to the surface factor of the SAME model

Lane LFR20-CMP, packet 3 (smooth fibre type), the pointwise part. For a slim chart `c`
(coordinate `η`), an LC81 product model `P` and a surface factor `Q : SlimSurfaceFactor P`, put
`pr x = ψ⁻¹((e x)_W)` (`N → S`) and consider the source zero level
`Z = {m ∈ B(p, L) | η m = 0}` (`L = 10⁶Δ`) and the map `m ↦ pr (j⁻¹ m)`:

* `SlimProductModel.exists_cylinder_of_coord_eq_zero`: every `m ∈ Z` is `j x` for a cylinder point
  `x` (`|t x| < 0.93L`), with `m ∈ j.target` and `j⁻¹ m = x` (`P.fibres`);
* `SlimProductModel.strictMonoOn_coord_line`: `η ∘ j` is strictly increasing along every coordinate
  line on `[-19L/20, 19L/20]` ((LFR20.1) and `strictMonoOn_comp_splitting_line`);
* `SlimSurfaceFactor.eq_of_proj_eq` / `SlimSurfaceFactor.exists_proj_eq`: the map `Z → S` is
  injective and onto (value clause and the intermediate value theorem);
* `eq_zero_of_vertical` (linear algebra), `SlimSurfaceFactor.eq_zero_of_mfderiv_fst_snd`,
  `SlimSurfaceFactor.mfderiv_proj_vertical`, `SlimProductModel.mfderiv_fst_vertical`,
  `SlimProductModel.mfderiv_coord_vertical_ne_zero`, and the core
  `SlimSurfaceFactor.eq_zero_of_mfderiv_coord_proj`: a tangent vector `a` at `m ∈ Z` with
  `dη(a) = 0` and `d(pr ∘ j⁻¹)(a) = 0` vanishes.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function Metric WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.MetricGeometry

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

local instance nezero_finrank_euclidean_three_fibreProj_LFR20CMP :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩


/-- `mvfderiv` of a real function, evaluated, is `mfderiv` evaluated. -/
theorem mvfderiv_apply_eq_mfderiv_apply_E3 {X : Type*} [TopologicalSpace X]
    [ChartedSpace E3 X] {f : X → ℝ} {x : X} {w : TangentSpace 𝓘(ℝ, E3) x} :
    mvfderiv 𝓘(ℝ, E3) f x w = mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) f x w := by
  rw [mvfderiv]
  rfl

/-- **Linear algebra of the vertical direction.** If `dι` is injective, `dη (dι u) = 0`,
`dj ∘ djs = id`, `(dt, dpr)` is injective, `dpr v = 0`, `dt v = 1`, `dη (dj v) ≠ 0` and
`dpr (djs (dι u)) = 0`, then `u = 0`. -/
theorem eq_zero_of_vertical {Ty Tm Tx TS : Type*} [AddCommGroup Ty] [Module ℝ Ty]
    [AddCommGroup Tm] [Module ℝ Tm] [AddCommGroup Tx] [Module ℝ Tx] [AddCommGroup TS]
    [Module ℝ TS] (dι : Ty →ₗ[ℝ] Tm) (dη : Tm →ₗ[ℝ] ℝ) (djs : Tm →ₗ[ℝ] Tx) (dj : Tx →ₗ[ℝ] Tm)
    (dt : Tx →ₗ[ℝ] ℝ) (dpr : Tx →ₗ[ℝ] TS) (v : Tx) (hι : Injective dι) (u : Ty)
    (hηι : dη (dι u) = 0) (hjjs : ∀ a, dj (djs a) = a)
    (hprod : ∀ b, dt b = 0 → dpr b = 0 → b = 0) (hprv : dpr v = 0) (htv : dt v = 1)
    (hηv : dη (dj v) ≠ 0) (hu : dpr (djs (dι u)) = 0) : u = 0 := by
  set b := djs (dι u) with hb
  have hb' : b = dt b • v := by
    have h0 := hprod (b - dt b • v) (by rw [map_sub, map_smul, htv, smul_eq_mul, mul_one, sub_self])
      (by rw [map_sub, map_smul, hprv, smul_zero, hu, sub_zero])
    exact sub_eq_zero.mp h0
  have hη0 : dη (dj b) = 0 := by rw [hb, hjjs]; exact hηι
  rw [hb', map_smul, map_smul, smul_eq_mul] at hη0
  have hdt : dt b = 0 := (mul_eq_zero.mp hη0).resolve_right hηv
  have hb0 : b = 0 := by rw [hb', hdt, zero_smul]
  have hιu : dι u = 0 := by rw [← hjjs (dι u), ← hb, hb0, map_zero]
  exact hι (hιu.trans (map_zero dι).symm)

variable {M : Type*} [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
  {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
  {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
  {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
  {c : SlimChart g hEnorm Δ σ α} {K : ℕ}

/-- The slim coordinate is differentiable on `B(p, L)`. -/
theorem SlimChart.mdifferentiableAt_coord_of_mem_ball (c : SlimChart g hEnorm Δ σ α) {m : M}
    (hm : m ∈ ball p (10 ^ 6 * Δ)) : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) c.coord m :=
  (c.contMDiffOn_coord.contMDiffAt (c.isOpen_domain.mem_nhds
    (c.closedBall_subset_domain (ball_subset_closedBall hm)))).mdifferentiableAt (by simp)

namespace SlimProductModel

variable (P : SlimProductModel c K)

theorem fst_apply_symm_toLp (s : ℝ) (w : P.W) : (P.e (P.e.symm (toLp 2 (s, w)))).fst = s := by
  rw [P.e.apply_symm_apply]; rfl

theorem snd_apply_symm_toLp (s : ℝ) (w : P.W) : (P.e (P.e.symm (toLp 2 (s, w)))).snd = w := by
  rw [P.e.apply_symm_apply]; rfl

/-- Every point of the source zero level in `B(p, L)` is `j` of a cylinder point. -/
theorem exists_cylinder_of_coord_eq_zero (hΔ : 0 < Δ) {m : M} (hm : m ∈ ball p (10 ^ 6 * Δ))
    (h0 : c.coord m = 0) :
    ∃ x : P.N, |(P.e x).fst| < 93 / 100 * (10 ^ 6 * Δ) ∧ x ∈ P.j.source ∧ P.j x = m ∧
      m ∈ P.j.target ∧ P.j.symm m = x := by
  obtain ⟨x, hx, rfl⟩ := P.fibres m hm (by rw [h0, abs_zero]; positivity)
  have hxs : x ∈ P.j.source := P.cylinder_subset (show |(P.e x).fst| ≤ _ by linarith)
  exact ⟨x, hx, hxs, rfl, P.j.map_source hxs, P.j.left_inv hxs⟩

/-- `η ∘ j` is differentiable on the cylinder. -/
theorem mdifferentiableAt_coord_comp (hK : 1 ≤ K) {x : P.N}
    (hx : |(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ)) :
    MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => c.coord (P.j y)) x :=
  (c.mdifferentiableAt_coord_of_mem_ball (P.cylinder x hx).1).comp x
    (P.j.mdifferentiableAt (by exact_mod_cast (show K ≠ 0 by omega)) (P.cylinder_subset hx))

/-- **(LFR20.1) along the coordinate lines:** `η ∘ j` is strictly increasing. -/
theorem strictMonoOn_coord_line (hK : 4 ≤ K) (hΔ : 0 < Δ) (w : P.W) :
    StrictMonoOn (fun s => c.coord (P.j (P.e.symm (toLp 2 (s, w)))))
      (Icc (-(95 / 100 * (10 ^ 6 * Δ))) (95 / 100 * (10 ^ 6 * Δ))) := by
  have hr : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by exact_mod_cast (show 2 ≤ K - 2 by omega)
  have hℓ : (0 : ℝ) < 2 * (10 ^ 6 * Δ) := by positivity
  refine strictMonoOn_comp_splitting_line P.G hr P.enorm P.e hℓ P.V P.vertical
    (f := fun y => c.coord (P.j y)) w (fun s hs => P.mdifferentiableAt_coord_comp (by omega) ?_)
    (fun s hs => ?_)
  · rw [fst_apply_symm_toLp]; exact abs_le.mpr hs
  · have hx : |(P.e (P.e.symm (toLp 2 (s, w)))).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) := by
      rw [fst_apply_symm_toLp]; exact abs_le.mpr hs
    exact lt_trans (show (0 : ℝ) < 3 / 4 by norm_num) (P.cylinder _ hx).2.2.1

/-- `dt(V) = 1`. -/
theorem mfderiv_fst_vertical (x : P.N) :
    mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun x => (P.e x).fst) x (P.V x) = (1 : ℝ) := by
  rw [← mvfderiv_apply_eq_mfderiv_apply_E3]
  exact P.dt_vertical x

/-- (LFR20.1) as a differential: `dη (dj V) ≠ 0` on the cylinder. -/
theorem mfderiv_coord_vertical_ne_zero (hK : 1 ≤ K) {x : P.N}
    (hx : |(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ)) :
    mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) c.coord (P.j x)
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j x (P.V x)) ≠ (0 : ℝ) := by
  have hpos : (3 : ℝ) / 4 < mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z => c.coord (P.j z)) x (P.V x) := by
    rw [← mvfderiv_apply_eq_mfderiv_apply_E3]
    exact (P.cylinder x hx).2.2.1
  have h := mfderiv_comp x (c.mdifferentiableAt_coord_of_mem_ball (P.cylinder x hx).1)
    (P.j.mdifferentiableAt (by exact_mod_cast (show K ≠ 0 by omega)) (P.cylinder_subset hx))
  have h3 : (fun z => c.coord (P.j z)) = c.coord ∘ P.j := rfl
  rw [h3, h] at hpos
  exact (lt_trans (show (0 : ℝ) < 3 / 4 by norm_num) hpos).ne'

/-- `dj ∘ dj⁻¹ = id` on the target. -/
theorem mfderiv_comp_symm_apply (hK : 1 ≤ K) {m : M} (hm : m ∈ P.j.target)
    (a : TangentSpace 𝓘(ℝ, E3) m) :
    mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j (P.j.symm m) (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j.symm m a) = a := by
  have hK0 : (K : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have h := mfderiv_comp m (P.j.mdifferentiableAt hK0 (P.j.map_target hm))
    (P.j.symm.mdifferentiableAt hK0 hm)
  have hev : (P.j ∘ P.j.symm) =ᶠ[𝓝 m] id :=
    Filter.eventually_of_mem (P.j.open_target.mem_nhds hm) fun z hz => P.j.right_inv hz
  have h2 : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (P.j ∘ P.j.symm) m = mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) id m :=
    hev.mfderiv_eq
  have h3 := h.symm.trans (h2.trans mfderiv_id)
  exact congrArg (fun L => L a) h3

end SlimProductModel

namespace SlimSurfaceFactor

variable {P : SlimProductModel c K} (Q : SlimSurfaceFactor P)

/-- The projection `N → S` along the splitting is `C^K`. -/
theorem contMDiff_proj : ContMDiff 𝓘(ℝ, E3) (𝓡 2) K (fun x : P.N => Q.ψ.symm (P.e x).snd) :=
  contMDiff_snd.comp Q.product_symm_contMDiff

/-- **The projection is injective on the zero level.** -/
theorem eq_of_proj_eq (hK : 4 ≤ K) (hΔ : 0 < Δ) {m₁ m₂ : M} (hm₁ : m₁ ∈ ball p (10 ^ 6 * Δ))
    (h₁ : c.coord m₁ = 0) (hm₂ : m₂ ∈ ball p (10 ^ 6 * Δ)) (h₂ : c.coord m₂ = 0)
    (h : Q.ψ.symm (P.e (P.j.symm m₁)).snd = Q.ψ.symm (P.e (P.j.symm m₂)).snd) : m₁ = m₂ := by
  obtain ⟨x₁, hx₁, -, rfl, -, hs₁⟩ := P.exists_cylinder_of_coord_eq_zero hΔ hm₁ h₁
  obtain ⟨x₂, hx₂, -, rfl, -, hs₂⟩ := P.exists_cylinder_of_coord_eq_zero hΔ hm₂ h₂
  rw [hs₁, hs₂] at h
  have hsnd : (P.e x₁).snd = (P.e x₂).snd := Q.ψ.symm.injective h
  have hx₁' : P.e.symm (toLp 2 ((P.e x₁).fst, (P.e x₁).snd)) = x₁ := P.e.symm_apply_apply x₁
  have hx₂' : P.e.symm (toLp 2 ((P.e x₂).fst, (P.e x₁).snd)) = x₂ := by
    rw [hsnd]; exact P.e.symm_apply_apply x₂
  have hm1 : (P.e x₁).fst ∈ Icc (-(95 / 100 * (10 ^ 6 * Δ))) (95 / 100 * (10 ^ 6 * Δ)) :=
    abs_le.mp (by linarith)
  have hm2 : (P.e x₂).fst ∈ Icc (-(95 / 100 * (10 ^ 6 * Δ))) (95 / 100 * (10 ^ 6 * Δ)) :=
    abs_le.mp (by linarith)
  have hfst : (P.e x₁).fst = (P.e x₂).fst := by
    refine (P.strictMonoOn_coord_line hK hΔ (P.e x₁).snd).injOn hm1 hm2 ?_
    rw [hx₁', hx₂', h₁, h₂]
  rw [← hx₁', ← hx₂', hfst]

/-- **The projection maps the zero level onto the factor.** -/
theorem exists_proj_eq (hK : 1 ≤ K) (hΔ : 0 < Δ) (s : Q.S) :
    ∃ m ∈ ball p (10 ^ 6 * Δ), c.coord m = 0 ∧ Q.ψ.symm (P.e (P.j.symm m)).snd = s := by
  set b : ℝ := 95 / 100 * (10 ^ 6 * Δ) with hb
  have hb0 : 0 < b := by positivity
  let w := Q.ψ s
  let h : ℝ → ℝ := fun t => c.coord (P.j (P.e.symm (toLp 2 (t, w))))
  have hcyl' : ∀ t ∈ Icc (-b) b, |(P.e (P.e.symm (toLp 2 (t, w)))).fst| ≤ b := by
    intro t ht; rw [SlimProductModel.fst_apply_symm_toLp]; exact abs_le.mpr ht
  have hcont : ContinuousOn h (Icc (-b) b) := by
    intro t ht
    have hline : Continuous fun t : ℝ => P.e.symm (toLp 2 (t, w)) :=
      P.e.symm.continuous.comp ((WithLp.prod_continuous_toLp 2 ℝ P.W).comp
        (continuous_id.prodMk continuous_const))
    exact (ContinuousAt.comp (f := fun t : ℝ => P.e.symm (toLp 2 (t, w)))
      (P.mdifferentiableAt_coord_comp hK (hcyl' t ht)).continuousAt
      hline.continuousAt).continuousWithinAt
  have hval : ∀ t ∈ Icc (-b) b, |h t - t| < 2 * (Δ / 100) := by
    intro t ht
    have h1 := (P.cylinder _ (hcyl' t ht)).2.1
    rw [SlimProductModel.fst_apply_symm_toLp] at h1
    exact h1
  have hlo : h (-b) < 0 := by
    have h1 := (abs_lt.mp (hval (-b) ⟨le_rfl, by linarith⟩)).2
    linarith
  have hhi : 0 < h b := by
    have h1 := (abs_lt.mp (hval b ⟨by linarith, le_rfl⟩)).1
    linarith
  obtain ⟨t₀, ht₀, hzero⟩ :=
    intermediate_value_Icc (show -b ≤ b by linarith) hcont ⟨hlo.le, hhi.le⟩
  refine ⟨P.j (P.e.symm (toLp 2 (t₀, w))), (P.cylinder _ (hcyl' t₀ ht₀)).1, hzero, ?_⟩
  have hl : P.j.symm (P.j (P.e.symm (toLp 2 (t₀, w)))) = P.e.symm (toLp 2 (t₀, w)) :=
    P.j.left_inv (P.cylinder_subset (hcyl' t₀ ht₀))
  rw [hl, SlimProductModel.snd_apply_symm_toLp]
  exact Q.ψ.symm_apply_apply s

/-- **The product differential is injective:** `dt b = 0` and `d pr b = 0` force `b = 0`. -/
theorem eq_zero_of_mfderiv_fst_snd (hK : 1 ≤ K) (x : P.N) (b : TangentSpace 𝓘(ℝ, E3) x)
    (hb1 : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun x => (P.e x).fst) x b = 0)
    (hb2 : mfderiv 𝓘(ℝ, E3) (𝓡 2) (fun x : P.N => Q.ψ.symm (P.e x).snd) x b = 0) : b = 0 := by
  have hK0 : (K : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  let Pq : P.N → ℝ × Q.S := fun x => ((P.e x).fst, Q.ψ.symm (P.e x).snd)
  let Ψ' : ℝ × Q.S → P.N := fun q => P.e.symm (toLp 2 (q.1, Q.ψ q.2))
  have hid : Ψ' ∘ Pq = id := by
    funext x
    change P.e.symm (toLp 2 ((P.e x).fst, Q.ψ (Q.ψ.symm (P.e x).snd))) = x
    rw [Q.ψ.apply_symm_apply]
    exact P.e.symm_apply_apply x
  have hPqd : MDifferentiableAt 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) Pq x :=
    (Q.product_symm_contMDiff x).mdifferentiableAt hK0
  have htd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun x => (P.e x).fst) x :=
    (contMDiff_fst.comp Q.product_symm_contMDiff x).mdifferentiableAt hK0
  have hprd : MDifferentiableAt 𝓘(ℝ, E3) (𝓡 2) (fun x : P.N => Q.ψ.symm (P.e x).snd) x :=
    (Q.contMDiff_proj x).mdifferentiableAt hK0
  have hΨd : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Ψ' (Pq x) :=
    (Q.product_contMDiff _).mdifferentiableAt hK0
  have hc := mfderiv_comp x hΨd hPqd
  rw [hid, mfderiv_id] at hc
  have hPqb : mfderiv 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) Pq x b = 0 := by
    have h := mfderiv_prodMk htd hprd
    change mfderiv 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2))
      (fun x => ((P.e x).fst, Q.ψ.symm (P.e x).snd)) x b = 0
    rw [h]
    exact Prod.ext hb1 hb2
  have h := congrArg (fun L => L b) hc
  change b = mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Ψ' (Pq x)
    (mfderiv 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) Pq x b) at h
  rw [hPqb, map_zero] at h
  exact h

/-- **The projection kills the vertical field.** -/
theorem mfderiv_proj_vertical (hK : 4 ≤ K) (hΔ : 0 < Δ) (x : P.N) :
    mfderiv 𝓘(ℝ, E3) (𝓡 2) (fun x : P.N => Q.ψ.symm (P.e x).snd) x (P.V x) = 0 := by
  have hr : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by exact_mod_cast (show 2 ≤ K - 2 by omega)
  have hℓ : (0 : ℝ) < 2 * (10 ^ 6 * Δ) := by positivity
  exact mfderiv_vertical_eq_zero_of_const_on_lines P.G hr P.enorm P.e hℓ P.V P.vertical
    ((Q.contMDiff_proj x).mdifferentiableAt (by exact_mod_cast (show K ≠ 0 by omega)))
    fun s => congrArg Q.ψ.symm (SlimProductModel.snd_apply_symm_toLp P s (P.e x).snd)

/-- **The core of the differential:** at a point `m` of the zero level, a tangent vector `a` with
`dη(a) = 0` and `d(pr ∘ j⁻¹)(a) = 0` vanishes. -/
theorem eq_zero_of_mfderiv_coord_proj (hK : 4 ≤ K) (hΔ : 0 < Δ) {m : M}
    (hm : m ∈ ball p (10 ^ 6 * Δ)) (h0 : c.coord m = 0) (a : TangentSpace 𝓘(ℝ, E3) m)
    (ha : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) c.coord m a = 0)
    (hb : mfderiv 𝓘(ℝ, E3) (𝓡 2) (fun x : P.N => Q.ψ.symm (P.e x).snd) (P.j.symm m)
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j.symm m a) = 0) : a = 0 := by
  obtain ⟨x, hx, -, hjx, hmt, hjs⟩ := P.exists_cylinder_of_coord_eq_zero hΔ hm h0
  have hxb : |(P.e (P.j.symm m)).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) := by rw [hjs]; linarith
  have hηv0 := P.mfderiv_coord_vertical_ne_zero (by omega) hxb
  have hkey : ∀ m' : M, m' = m → mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) c.coord m'
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j (P.j.symm m) (P.V (P.j.symm m))) ≠ (0 : ℝ) →
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) c.coord m
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j (P.j.symm m) (P.V (P.j.symm m))) ≠ (0 : ℝ) := by
    intro m' hm' h
    rw [hm'] at h
    exact h
  have hηv := hkey _ (P.j.right_inv hmt) hηv0
  exact eq_zero_of_vertical LinearMap.id
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) c.coord m).toLinearMap
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j.symm m).toLinearMap
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j (P.j.symm m)).toLinearMap
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun x => (P.e x).fst) (P.j.symm m)).toLinearMap
    (mfderiv 𝓘(ℝ, E3) (𝓡 2) (fun x : P.N => Q.ψ.symm (P.e x).snd) (P.j.symm m)).toLinearMap
    (P.V (P.j.symm m)) injective_id a ha (P.mfderiv_comp_symm_apply (by omega) hmt)
    (Q.eq_zero_of_mfderiv_fst_snd (by omega) _) (Q.mfderiv_proj_vertical hK hΔ _)
    (P.mfderiv_fst_vertical _) hηv hb

end SlimSurfaceFactor

end DifferentialGeometry.Geometry.Collapse
