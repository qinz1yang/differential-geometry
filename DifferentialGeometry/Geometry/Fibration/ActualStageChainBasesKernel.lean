import DifferentialGeometry.Geometry.Fibration.ActualStageChainSmoothBasesFibres

/-!
# GAF02 BASES, the kernel identification `ker D(π_st E)(p) = ker D f_st(p)` on `D_st`

Blueprint `master207B.tex`, GAF02 (B:5797–5870): the later maps "preserve fibers [...] and
kernels on CGP08's specified threshold-6 carriers". This is the last open item of the BASES
object after `Gaf02Bases` (lane C14-BASESc, state file `state-C14-BASES.md`, section OPEN).
Lane S-BASES-KER (successor of C14-BASESc), group G9.

Route (no rank count): at `p ∈ D_st = B⁶_st ∩ f_st⁻¹(V_st⁰)` the native value lies in a marked
patch `V_i⁰`; near `p`, the plateau (OPEN, `isOpen_gafStagePlateau_BAS`) keeps `f_st q` in the
native zero set (`plat_mem_zeroSet_BAS`) and the marked condition is open, so `f_st q ∈ V_i⁰` and
`f_st = φ_i ∘ κ_i ∘ f_st` near `p` (BASES' chart inverse `φ_i`, `InvOn`). Retention
`κ_i ∘ Θ_st = κ_i` makes `λ = φ_i ∘ κ_i` a LOCAL LEFT INVERSE of `Θ_st` along `f_st`:
`λ ∘ Θ_st ∘ f_st = f_st` near `p`, and `π_st E = Θ_st ∘ f_st` (`final_factor_BAS`) with `Θ_st`
smooth at the stage images (`contDiffAt_theta_BAS`). The chain rule gives
`D f = Dλ ∘ DΘ ∘ D f`, hence both kernel inclusions.

* `ker_mfderiv_comp_eq_of_left_inverse_BAS` (generic: manifold chain rule for a local left
  inverse);
* `ker_mfderiv_final_of_patch_BAS` (generic: one marked patch with retention, chart inverse and
  openness of the plateau data);
* `Gaf02Bases.ker_final_circle_BAS`, `…edge_BAS`, `…slim_BAS` (per stage);
* **`Gaf02Bases.ker_final_eq_BAS`**: for `p ∈ D_st` (every stage) the kernels of the derivatives
  of `π_st E` and of `f_st` at `p` are EQUAL;
* `Gaf02Bases.ker_final_eq_domain5_BAS` (the same on FC33's `U_st ⊆ D_st`);
* `Gaf02Chain.ker_final_eq_BAS` (kernel form on `(C, R)`: the producer's object).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **Kernels under a local left inverse (manifold form).** If `lam ∘ Θ ∘ f = f` near `p` with
`f` manifold-differentiable at `p`, `Θ` differentiable at `f p` and `lam` at `Θ (f p)`, then
`ker D(Θ ∘ f)(p) = ker Df(p)`. -/
theorem ker_mfderiv_comp_eq_of_left_inverse_BAS {E H' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H' M] {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : M → F} {Θ : F → G}
    {lam : G → F} {p : M} (hf : MDifferentiableAt I 𝓘(ℝ, F) f p)
    (hΘ : DifferentiableAt ℝ Θ (f p)) (hlam : DifferentiableAt ℝ lam (Θ (f p)))
    (hleft : (fun y => lam (Θ (f y))) =ᶠ[𝓝 p] f) :
    LinearMap.ker (mfderiv I 𝓘(ℝ, G) (Θ ∘ f) p).toLinearMap =
      LinearMap.ker (mfderiv I 𝓘(ℝ, F) f p).toLinearMap := by
  have h1 : mfderiv I 𝓘(ℝ, G) (Θ ∘ f) p =
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) Θ (f p)).comp (mfderiv I 𝓘(ℝ, F) f p) :=
    mfderiv_comp p hΘ.mdifferentiableAt hf
  have h2 : mfderiv I 𝓘(ℝ, F) (lam ∘ (Θ ∘ f)) p =
      (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, F) lam (Θ (f p))).comp (mfderiv I 𝓘(ℝ, G) (Θ ∘ f) p) :=
    mfderiv_comp p hlam.mdifferentiableAt (hΘ.mdifferentiableAt.comp p hf)
  have h3 : mfderiv I 𝓘(ℝ, F) (lam ∘ (Θ ∘ f)) p = mfderiv I 𝓘(ℝ, F) f p :=
    hleft.mfderiv_eq
  ext v
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    have h4 := congrArg (fun T => T v) (h2.symm.trans h3)
    simp only [ContinuousLinearMap.comp_apply] at h4
    exact h4.symm.trans (by rw [h, map_zero]; rfl)
  · intro h
    rw [h1, ContinuousLinearMap.comp_apply, h, map_zero]

/-- **The kernel identification for one marked patch.** Let `f` be continuous and
manifold-differentiable at `p`, with `f p` in the marked patch `V⁰ = Z ∩ {v > .9R, ‖u‖ < 5.5ℓR}`
of the coordinate `κ = R⁻¹u`, `f q ∈ Z` near `p`, `Θ` retaining `u` and differentiable at `f p`,
and `φ` a smooth inverse of `κ` on `V⁰` over the ball `B(0, 5.5ℓ)`. Then `ker D(Θ ∘ f)(p) =
ker Df(p)`. -/
theorem ker_mfderiv_final_of_patch_BAS {E H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H' M] {H E' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (Z : Set H) (u : H →L[ℝ] E') (vm : H →L[ℝ] ℝ)
    (R ℓ : ℝ) (Θ : H → H) (φ : E' → H) {f : M → H} {p : M} (hfc : Continuous f)
    (hfd : MDifferentiableAt I 𝓘(ℝ, H) f p) (hΘ : DifferentiableAt ℝ Θ (f p))
    (hret : ∀ w, u (Θ w) = u w) (hφ : ContDiffOn ℝ ∞ φ (ball (0 : E') (11 / 2 * ℓ)))
    (hinv : InvOn φ (R⁻¹ • u) (markedPatch_BPRE Z u vm R ℓ) (ball (0 : E') (11 / 2 * ℓ)))
    (hmaps : MapsTo (R⁻¹ • u) (markedPatch_BPRE Z u vm R ℓ) (ball (0 : E') (11 / 2 * ℓ)))
    (hp : f p ∈ markedPatch_BPRE Z u vm R ℓ) (hZ : ∀ᶠ q in 𝓝 p, f q ∈ Z) :
    LinearMap.ker (mfderiv I 𝓘(ℝ, H) (Θ ∘ f) p).toLinearMap =
      LinearMap.ker (mfderiv I 𝓘(ℝ, H) f p).toLinearMap := by
  have hκ : ∀ w, (R⁻¹ • u) (Θ w) = (R⁻¹ • u) w := fun w => by
    rw [smul_apply, smul_apply, hret]
  refine ker_mfderiv_comp_eq_of_left_inverse_BAS (lam := φ ∘ (R⁻¹ • u)) hfd hΘ ?_ ?_
  · have hb : (R⁻¹ • u) (Θ (f p)) ∈ ball (0 : E') (11 / 2 * ℓ) := by
      rw [hκ]
      exact hmaps hp
    exact ((hφ.contDiffAt (isOpen_ball.mem_nhds hb)).differentiableAt (by simp)).comp _
      (R⁻¹ • u).differentiableAt
  · have hmark : ∀ᶠ q in 𝓝 p, f q ∈ markedCondition_BPRE u vm R ℓ :=
      hfc.continuousAt.eventually_mem ((isOpen_markedCondition_BPRE u vm R ℓ).mem_nhds hp.2)
    filter_upwards [hZ, hmark] with q hqZ hqm
    have hq : f q ∈ markedPatch_BPRE Z u vm R ℓ := ⟨hqZ, hqm.1, hqm.2⟩
    change φ ((R⁻¹ • u) (Θ (f q))) = f q
    rw [hκ]
    exact hinv.1 hq

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- `π_st E = Θ_st ∘ f_st` as functions. -/
theorem final_eq_comp_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) (st : Fin 3) :
    (fun p => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E p)) =
      C.Θ_BAS st ∘ C.stageMap_BAS st :=
  funext (C.final_factor_BAS st)

/-- The native zero set is seen from the open plateau: `f_st q ∈ Z_st` for all `q` near a
plateau point. -/
theorem eventually_mem_zeroSet_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (st : Fin 3) {p : X} (hp : p ∈ gafStagePlateau_BAS P.toLocalChartPackets st) :
    ∀ᶠ q in 𝓝 p, C.stageMap_BAS st q ∈ (C.slot st).zeroSet :=
  Filter.eventually_of_mem ((isOpen_gafStagePlateau_BAS P.toLocalChartPackets st).mem_nhds hp)
    fun _ hq => C.plat_mem_zeroSet_BAS hq

/-- FC33's `U_st` lies in the restricted carrier `D_st`. -/
theorem domain5_subset_carrier_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (st : Fin 3) :
    gafStageDomain5_BAS P.toLocalChartPackets st ⊆ C.carrier_BAS st := fun _ hp =>
  ⟨gafStageDomain5_subset_plateau_BAS P.toLocalChartPackets (zero_le_one.trans C.std.2.1) st hp,
    C.stageMap_mem_markedBase_R74 st hp⟩

end Gaf02Chain

namespace Gaf02Bases

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw} {R : Gaf02RoughData C}

/-- **Kernel identification, circle stage**: at a plateau point whose native value lies in the
circle patch `V_j⁰`. -/
theorem ker_final_circle_BAS (B : Gaf02Bases C R)
    (j : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hp : p ∈ gafStagePlateau_BAS P.toLocalChartPackets 0)
    (hpj : C.stageMap_BAS 0 p ∈ C.circlePatch_BAS j) :
    LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (fun q =>
        (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E q)) p).toLinearMap =
      LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
        (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (C.stageMap_BAS 0) p).toLinearMap := by
  rw [C.final_eq_comp_BAS 0]
  exact ker_mfderiv_final_of_patch_BAS (C.slot 0).zeroSet (gafCircleVector P.toLocalChartPackets j)
    (gafCircleMarker P.toLocalChartPackets j) (ρ j.1) 1 (C.Θ_BAS 0) (B.circle.chart j)
    (C.stageMap_contMDiff_BAS 0).continuous
    ((C.stageMap_contMDiff_BAS 0).mdifferentiableAt (by simp))
    ((C.contDiffAt_theta_BAS 0 p).differentiableAt (by simp))
    (fun w => (C.theta_retains_circle_BAS j w).1) (B.circle.spec.patch j).2.1
    (B.circle.spec.patch j).2.2.1 (B.circle.spec.patch j).1.mapsTo hpj
    (C.eventually_mem_zeroSet_BAS 0 hp)

/-- **Kernel identification, edge stage** (axis coordinate): at a plateau point whose native value
lies in the edge patch `V_j⁰`. -/
theorem ker_final_edge_BAS (B : Gaf02Bases C R) (j : P.edge.finite_centres.toFinset) {p : X}
    (hp : p ∈ gafStagePlateau_BAS P.toLocalChartPackets 1)
    (hpj : C.stageMap_BAS 1 p ∈ C.edgePatch_BAS j) :
    LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (fun q =>
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.E q)) p).toLinearMap =
      LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
        (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (C.stageMap_BAS 1) p).toLinearMap := by
  rw [C.final_eq_comp_BAS 1]
  exact ker_mfderiv_final_of_patch_BAS (C.slot 1).zeroSet
    (axisCoordCLM_BAS.comp (gafEdgeVector P.toLocalChartFamily P.zero j))
    (gafEdgeMarker P.toLocalChartFamily P.zero j) (ρ j.1) Δ (C.Θ_BAS 1) (B.edge.chart j)
    (C.stageMap_contMDiff_BAS 1).continuous
    ((C.stageMap_contMDiff_BAS 1).mdifferentiableAt (by simp))
    ((C.contDiffAt_theta_BAS 1 p).differentiableAt (by simp))
    (fun w => (C.theta_retains_edgeAxis_BAS j w).1) (B.edge.spec.patch j).2.1
    (B.edge.spec.patch j).2.2.1 (B.edge.spec.patch j).1.mapsTo hpj
    (C.eventually_mem_zeroSet_BAS 1 hp)

/-- **Kernel identification, slim stage** (`Θ₃ = id`): at a plateau point whose native value lies
in the slim patch `V_j⁰`. -/
theorem ker_final_slim_BAS (B : Gaf02Bases C R) (j : P.slim.finite_centres.toFinset) {p : X}
    (hp : p ∈ gafStagePlateau_BAS P.toLocalChartPackets 2)
    (hpj : C.stageMap_BAS 2 p ∈ C.slimPatch_BAS j) :
    LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (fun q =>
        (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E q)) p).toLinearMap =
      LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
        (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (C.stageMap_BAS 2) p).toLinearMap := by
  rw [C.final_eq_comp_BAS 2]
  exact ker_mfderiv_final_of_patch_BAS (C.slot 2).zeroSet
    (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero j))
    (gafSlimMarker P.toLocalChartFamily P.zero j) (ρ j.1) (10 ^ 5 * Δ) (C.Θ_BAS 2) (B.slim.chart j)
    (C.stageMap_contMDiff_BAS 2).continuous
    ((C.stageMap_contMDiff_BAS 2).mdifferentiableAt (by simp))
    ((C.contDiffAt_theta_BAS 2 p).differentiableAt (by simp))
    (fun w => by rw [C.theta_two_eq_id_BAS]; rfl) (B.slim.spec.patch j).2.1
    (B.slim.spec.patch j).2.2.1 (B.slim.spec.patch j).1.mapsTo hpj
    (C.eventually_mem_zeroSet_BAS 2 hp)

/-- **Kernel identification on the threshold-6 carriers** (GAF02, BASES: the later maps preserve
kernels on `D_st`): for `p ∈ D_st = B⁶_st ∩ f_st⁻¹(V_st⁰)` (every stage), `ker D(π_st E)(p) =
ker D f_st(p)`. -/
theorem ker_final_eq_BAS (B : Gaf02Bases C R) (st : Fin 3) {p : X}
    (hp : p ∈ C.carrier_BAS st) :
    LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (fun q =>
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E q)) p).toLinearMap =
      LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
        (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (C.stageMap_BAS st) p).toLinearMap := by
  rcases (by decide : ∀ s : Fin 3, s = 0 ∨ s = 1 ∨ s = 2) st with rfl | rfl | rfl
  · have hm : C.stageMap_BAS 0 p ∈ ⋃ j, C.circlePatch_BAS j := hp.2
    exact (mem_iUnion.mp hm).elim fun j hj => B.ker_final_circle_BAS j hp.1 hj
  · have hm : C.stageMap_BAS 1 p ∈ ⋃ j, C.edgePatch_BAS j := hp.2
    exact (mem_iUnion.mp hm).elim fun j hj => B.ker_final_edge_BAS j hp.1 hj
  · have hm : C.stageMap_BAS 2 p ∈ ⋃ j, C.slimPatch_BAS j := hp.2
    exact (mem_iUnion.mp hm).elim fun j hj => B.ker_final_slim_BAS j hp.1 hj

/-- Pointwise form of `ker_final_eq_BAS`: on `D_st`, a tangent vector is killed by `D(π_st E)(p)`
iff it is killed by `D f_st(p)`. -/
theorem mfderiv_final_eq_zero_iff_BAS (B : Gaf02Bases C R) {st : Fin 3} {p : X}
    (hp : p ∈ C.carrier_BAS st) {v : TangentSpace 𝓘(ℝ, E3) p} :
    mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (fun q => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E q)) p v = 0 ↔
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
        (C.stageMap_BAS st) p v = 0 := by
  have h := congrArg (fun K => v ∈ K) (B.ker_final_eq_BAS st hp)
  simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, eq_iff_iff] using h

/-- **Kernel identification on FC33's exact threshold-5 domain** `U_st ⊆ D_st`. -/
theorem ker_final_eq_domain5_BAS (B : Gaf02Bases C R) (st : Fin 3) {p : X}
    (hp : p ∈ gafStageDomain5_BAS P.toLocalChartPackets st) :
    LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (fun q =>
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E q)) p).toLinearMap =
      LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
        (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (C.stageMap_BAS st) p).toLinearMap :=
  B.ker_final_eq_BAS st (C.domain5_subset_carrier_BAS st hp)

end Gaf02Bases

namespace Gaf02Chain

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **Kernel form on `(C, R)`**: the kernel identification for the producer's bases object
(no hypotheses besides `(C, R)`). -/
theorem ker_final_eq_BAS (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw)
    (R : Gaf02RoughData C) (st : Fin 3) {p : X} (hp : p ∈ C.carrier_BAS st) :
    LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (fun q =>
        (gafStageQ P.toLocalChartFamily P.zero st).starProjection (C.E q)) p).toLinearMap =
      LinearMap.ker (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace
        (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) (C.stageMap_BAS st) p).toLinearMap :=
  (C.gaf02Bases_BAS R).ker_final_eq_BAS st hp

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
