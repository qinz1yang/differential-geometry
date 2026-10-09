import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimSurfaceFactorProducer
import DifferentialGeometry.Topology.Manifold.SmoothOrientationPullbackOne
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# An oriented source orients every slim product model (review 70, D70-3, route β)

Lane C14-SLIM-STD, group 2. External review 70 §3.3 (β), lead decision D70-3: the model `P.N` of an
LC81 slim product model `P : SlimProductModel c K` carries an orientation as soon as the ambient
manifold `M` does. Only the EXISTENCE of an orientation of `P.N` is concluded; nothing is claimed
about its compatibility with `P.j` (and nothing of that kind is assumed).

Route (no orientation of `P.N` is an input anywhere):
* LFR11's product map `Ψ = splittingProductDiffeomorph P.G _ P.enorm P.e : ℝ × Z ≅ P.N`
  (`Z = {t = 0}`, class `C^K`, `Ψ (u, z) = e⁻¹(u, (e z)_W)`; `exactSplitting_regularity`, no
  orientation input);
* the compression `σ(t) = (L/5)·arctan t` of the line (`L = 10⁶Δ`): `|σ| < 2L/5`, `σ' > 0`;
* `C = Ψ ∘ (σ × id) ∘ Ψ⁻¹ : P.N → P.N` lands in the central cylinder `{|t| ≤ .95L} ⊆ P.j.source`
  (`P.cylinder_subset`), so `φ = P.j ∘ C : P.N → M` is a `C¹` map with bijective differential
  everywhere (a global finite-order local diffeomorphism);
* the orientation of `M` pulls back along `φ` (`nonempty_manifoldOrientation_pullback_one_SSTD`).

* `SlimProductModel.exists_localDiffeomorph_to_source_SSTD`: the map `φ` (`C¹`, bijective
  differential, values in `P.j '' {|t| ≤ .95L}`).
* `SlimProductModel.nonempty_orientation_of_oriented_source_SSTD` (D70-3 β, the review's statement).
* consumer `SlimProductModel.nonempty_slimSurfaceFactor_of_oriented_source_SSTD`: with LFR20-CMP's
  producer `nonempty_slimSurfaceFactor`, every slim product model over an oriented manifold has a
  surface factor.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting DifferentialGeometry.Manifold
  DifferentialGeometry.Topology.Manifold GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The model of the zero factor `Z` of the exact splitting. -/
local notation "𝓘P2" => 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ)

/-- The model of `ℝ × Z`. -/
local notation "𝓘P" =>
  ModelWithCorners.prod 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ)

local instance nezero_finrank_euclideanThree_modelOrientation_SSTD :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- The compression of the line used by route β: `t ↦ c · arctan t`. -/
theorem hasDerivAt_mul_arctan_SSTD (c t : ℝ) :
    HasDerivAt (fun s : ℝ => c * Real.arctan s) (c * (1 / (1 + t ^ 2))) t :=
  (Real.hasDerivAt_arctan t).const_mul c

theorem abs_mul_arctan_lt_SSTD {c : ℝ} (hc : 0 < c) (t : ℝ) : |c * Real.arctan t| < 2 * c := by
  have h1 := Real.arctan_lt_pi_div_two t
  have h2 := Real.neg_pi_div_two_lt_arctan t
  have h4 := Real.pi_le_four
  rw [abs_mul, abs_of_pos hc]
  have : |Real.arctan t| < 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  nlinarith

/-- The differential of `t ↦ c · arctan t` (`c ≠ 0`) is bijective. -/
theorem bijective_mfderiv_mul_arctan_SSTD {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    Bijective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => c * Real.arctan s) t) := by
  have hd : c * (1 / (1 + t ^ 2)) ≠ 0 := mul_ne_zero hc (by positivity)
  have hF : (fderiv ℝ (fun s : ℝ => c * Real.arctan s) t : ℝ → ℝ) =
      fun v => v * (c * (1 / (1 + t ^ 2))) := by
    rw [(hasDerivAt_mul_arctan_SSTD c t).hasFDerivAt.fderiv]
    funext v
    simp
  rw [mfderiv_eq_fderiv]
  change Bijective (fderiv ℝ (fun s : ℝ => c * Real.arctan s) t : ℝ → ℝ)
  rw [hF]
  exact ⟨fun v w h => mul_right_cancel₀ hd h, fun w => ⟨w / _, div_mul_cancel₀ w hd⟩⟩

variable {M : Type*} [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]

/-- **Route β, the map**: for `K ≥ 4` and `Δ > 0` there is a `C¹` map `φ : P.N → M` with bijective
differential at every point, with values in `P.j '' {|t| ≤ .95L}` (`φ = P.j ∘ C`, `C` the
compression of the line factor through LFR11's product map). -/
theorem SlimProductModel.exists_localDiffeomorph_to_source_SSTD
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
    {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
    {c : SlimChart g hEnorm Δ σ α} {K : ℕ} (hK : 4 ≤ K) (hΔ : 0 < Δ)
    (P : SlimProductModel c K) :
    ∃ φ : P.N → M, ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) 1 φ ∧
      (∀ x, Bijective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) φ x)) ∧
      ∀ x, ∃ y, |(P.e y).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∧ φ x = P.j y := by
  have hk : (2 : ℕ∞) ≤ ((K - 2 : ℕ) : ℕ∞) := by exact_mod_cast (show 2 ≤ K - 2 by omega)
  let _ := splittingFactorChartedSpace P.G hk P.enorm P.e
  let _ := splittingFactor_isManifold_one P.G hk P.enorm P.e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hΨapp, -, -, -⟩ :=
    exactSplitting_regularity P.G hk P.enorm P.e
  let Ψ := splittingProductDiffeomorph P.G hk P.enorm P.e
  have hL : 0 < 10 ^ 6 * Δ / 5 := by positivity
  let s : ℝ → ℝ := fun t => 10 ^ 6 * Δ / 5 * Real.arctan t
  let S : ℝ × {x : P.N // (P.e x).fst = 0} → ℝ × {x : P.N // (P.e x).fst = 0} := Prod.map s id
  let C : P.N → P.N := fun x => Ψ (S (Ψ.symm x))
  have hfst : ∀ x, (P.e (C x)).fst = s (Ψ.symm x).1 := by
    intro x
    change (P.e (Ψ (S (Ψ.symm x)))).fst = _
    rw [hΨapp, IsometryEquiv.apply_symm_apply]
    rfl
  have hcyl : ∀ x, |(P.e (C x)).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) := by
    intro x
    rw [hfst]
    have := abs_mul_arctan_lt_SSTD hL (Ψ.symm x).1
    have h0 : 0 < 10 ^ 6 * Δ := by positivity
    change |10 ^ 6 * Δ / 5 * Real.arctan (Ψ.symm x).1| ≤ _
    linarith
  have hsrc : ∀ x, C x ∈ P.j.source := fun x => P.cylinder_subset (hcyl x)
  have hn1 : (1 : ℕ∞ω) ≤ (((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2 := by
    rw [withTop_natCast_add_two]
    exact_mod_cast (show 1 ≤ K - 2 + 2 by omega)
  have hK1 : (1 : ℕ∞ω) ≤ (K : ℕ∞ω) := by exact_mod_cast (show 1 ≤ K by omega)
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 s :=
    (contDiff_const.mul Real.contDiff_arctan).contMDiff
  have hS : ContMDiff 𝓘P 𝓘P 1 S :=
    hs.prodMap contMDiff_id
  have hC : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) 1 C :=
    (Ψ.contMDiff.of_le hn1).comp (hS.comp (Ψ.symm.contMDiff.of_le hn1))
  let φ : P.N → M := fun x => P.j (C x)
  have hφ : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) 1 φ := fun x =>
    ((P.j.contMDiffOn.of_le hK1).contMDiffAt (P.j.open_source.mem_nhds (hsrc x))).comp x (hC x)
  refine ⟨φ, hφ, fun x => ?_, fun x => ⟨C x, hcyl x, rfl⟩⟩
  -- the differential
  have hΨd : MDifferentiableAt 𝓘P 𝓘(ℝ, E3) Ψ (S (Ψ.symm x)) :=
    (Ψ.contMDiff.of_le hn1).contMDiffAt.mdifferentiableAt one_ne_zero
  have hΨsd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘P Ψ.symm x :=
    (Ψ.symm.contMDiff.of_le hn1).contMDiffAt.mdifferentiableAt one_ne_zero
  have hjd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j (C x) :=
    P.j.mdifferentiableAt (by exact_mod_cast (show K ≠ 0 by omega)) (hsrc x)
  have hsd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) s (Ψ.symm x).1
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) s (Ψ.symm x).1) :=
    ((hs _).mdifferentiableAt one_ne_zero).hasMFDerivAt
  have hSD : HasMFDerivAt 𝓘P 𝓘P S (Ψ.symm x)
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) s (Ψ.symm x).1).prodMap (mfderiv 𝓘P2 𝓘P2 id (Ψ.symm x).2)) :=
    hsd.prodMap (hasMFDerivAt_id _)
  have hD : HasMFDerivAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) φ x
      ((mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j (C x)).comp ((mfderiv 𝓘P 𝓘(ℝ, E3) Ψ (S (Ψ.symm x))).comp
        (((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) s (Ψ.symm x).1).prodMap
          (mfderiv 𝓘P2 𝓘P2 id (Ψ.symm x).2)).comp (mfderiv 𝓘(ℝ, E3) 𝓘P Ψ.symm x)))) :=
    hjd.hasMFDerivAt.comp x (hΨd.hasMFDerivAt.comp x (hSD.comp x hΨsd.hasMFDerivAt))
  have hb1 : Bijective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) P.j (C x)) :=
    ((P.j.isLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (K : ℕ∞ω) (hsrc x)).mfderivToContinuousLinearEquiv
      (by exact_mod_cast (show K ≠ 0 by omega))).bijective
  have hb2 : Bijective (mfderiv 𝓘P 𝓘(ℝ, E3) Ψ (S (Ψ.symm x))) :=
    (Ψ.mfderivToContinuousLinearEquiv (by simp) (S (Ψ.symm x))).bijective
  have hb4 : Bijective (mfderiv 𝓘(ℝ, E3) 𝓘P Ψ.symm x) :=
    (Ψ.symm.mfderivToContinuousLinearEquiv (by simp) x).bijective
  have hid : Bijective (mfderiv 𝓘P2 𝓘P2 id (Ψ.symm x).2) :=
    ((Diffeomorph.refl 𝓘P2 {x : P.N // (P.e x).fst = 0} 1).mfderivToContinuousLinearEquiv
      one_ne_zero (Ψ.symm x).2).bijective
  have hb3 : Bijective ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) s (Ψ.symm x).1).prodMap
      (mfderiv 𝓘P2 𝓘P2 id (Ψ.symm x).2)) := by
    rw [ContinuousLinearMap.coe_prodMap']
    exact (bijective_mfderiv_mul_arctan_SSTD hL.ne' _).prodMap hid
  rw [hD.mfderiv]
  exact hb1.comp (hb2.comp (hb3.comp hb4))

/-- **D70-3, route β: an oriented source orients the slim product model.** For `K ≥ 5`, `Δ ≥ 1`,
every LC81 slim product model `P : SlimProductModel c K` over an oriented `M` has an orientation of
its model `P.N` (existence only; no compatibility with `P.j` is claimed or assumed). -/
theorem SlimProductModel.nonempty_orientation_of_oriented_source_SSTD
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
    {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
    {c : SlimChart g hEnorm Δ σ α} {K : ℕ} (hK : 5 ≤ K) (hΔ : 1 ≤ Δ)
    (P : SlimProductModel c K) (oM : DifferentialGeometry.ManifoldOrientation (𝓡 3) M 3) :
    Nonempty (DifferentialGeometry.ManifoldOrientation (𝓡 3) P.N 3) := by
  obtain ⟨φ, hφ, hbij, -⟩ := P.exists_localDiffeomorph_to_source_SSTD (by omega)
    (lt_of_lt_of_le zero_lt_one hΔ)
  exact nonempty_manifoldOrientation_pullback_one_SSTD 𝓘(ℝ, E3) 𝓘(ℝ, E3) φ hφ hbij oM
    (finrank_euclideanSpace_fin)

/-- **Consumer: the surface factor of a slim product model over an oriented manifold** (route β
followed by LFR20-CMP's `nonempty_slimSurfaceFactor`). -/
theorem SlimProductModel.nonempty_slimSurfaceFactor_of_oriented_source_SSTD
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
    {hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g} {Δ σ : ℝ}
    {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
    {c : SlimChart g hEnorm Δ σ α} {K : ℕ} (hK : 5 ≤ K) (hΔ : 1 ≤ Δ)
    (P : SlimProductModel c K) (oM : DifferentialGeometry.ManifoldOrientation (𝓡 3) M 3) :
    Nonempty (SlimSurfaceFactor P) := by
  obtain ⟨oN⟩ := P.nonempty_orientation_of_oriented_source_SSTD hK hΔ oM
  exact nonempty_slimSurfaceFactor (by omega) P oN

end DifferentialGeometry.Geometry.Collapse
