import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.AxisMinimizingDirectionsApplications
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.CarrierRescale

/-!
# LFR28 B7: the model gradient clause `hGgrad` of (LFR28.4)

Blueprint 207A, LFR28 (A:27223), proof step 2: "The model smoothing has its own `10⁻⁸` error against
those same radial directions." On the product model `N = ℝ × S` (isometric product chart
`Θ : ℝ × S → N`, `e (Θ (t, s)) = (t, ψ s)`, `Θ^*G = dt² + κ`) the model height is
`G_N = Δ · F ∘ (Θ⁻¹ ·).2` for a smoothing `F` of the distance to `s₀` on the rescaled carrier.

* `mfderiv_diffeomorph_apply_mfderiv_symm`: `dΘ_{Θ⁻¹ x} ∘ dΘ⁻¹_x = id` (any order `≠ 0`).
* `mvfderiv_snd_comp_symm_mfderiv`: `dG_N(dΘ_p(a, w)) = Δ dF(w)`.
* `edgeModel_gradient_clause_of_product` (**B7 kernel**): if `|Δ dF(w) + κ(u, w)| ≤ ε|w|_κ` for every
  `κ`-minimizing direction `u` from `s` to `s₀` at the radii `5/2 Δ ≤ d(s, s₀) ≤ 13/2 Δ`, then
  `|dG_N(X) + G(v, X)| ≤ ε|X|_G` for every `G`-minimizing direction `v` from `x` to the axis
  `e⁻¹{snd = ψ s₀}` at the same radii (R1, `inner_mfderiv_axisMinimizingDirection`).
* `gradient_clause_of_rescaled` (R2 bridge): the gradient clause of LFR24 on the rescaled carrier
  `(S, Δ⁻¹ d, κΔ = Δ⁻² κ)` gives the unscaled clause above.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter Metric Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- `dΘ_{Θ⁻¹ x} (dΘ⁻¹_x X) = X` for a diffeomorphism of any positive order. -/
theorem mfderiv_diffeomorph_apply_mfderiv_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] {m : WithTop ℕ∞} (hm : m ≠ 0)
    (Θ : Diffeomorph I I' M M' m) (x : M') (X : TangentSpace I' x) :
    mfderiv I I' Θ (Θ.symm x) (mfderiv I' I Θ.symm x X) = X := by
  have hΘs : MDifferentiableAt I' I Θ.symm x := Θ.symm.mdifferentiable hm x
  have hΘ : MDifferentiableAt I I' Θ (Θ.symm x) := Θ.mdifferentiable hm (Θ.symm x)
  have hcomp : (Θ : M → M') ∘ (Θ.symm : M' → M) = id := funext Θ.apply_symm_apply
  have hchain := mfderiv_comp x hΘ hΘs
  rw [hcomp, mfderiv_id] at hchain
  have happ := congrArg (fun A : TangentSpace I' x →L[ℝ] TangentSpace I' x => A X) hchain.symm
  exact happ

variable {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N]

/-- The derivative of the model height `G_N = Δ · F ∘ (Θ⁻¹ ·).2` along `dΘ`. -/
theorem mvfderiv_snd_comp_symm_mfderiv {m : WithTop ℕ∞} (hm : m ≠ 0)
    (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N m) {F : S → ℝ} (Δ : ℝ)
    (p : ℝ × S) (hF : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) F p.2) (Y : ℝ × E2) :
    mvfderiv 𝓘(ℝ, E3) (fun y => Δ * F (Θ.symm y).2) (Θ p)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p Y) =
      Δ * mvfderiv (𝓡 2) F p.2 Y.2 := by
  set g : ℝ × S → ℝ := fun q => Δ * F q.2 with hgdef
  have hg : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) g p
      (Δ • (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) F p.2).comp (ContinuousLinearMap.snd ℝ ℝ E2)) :=
    (hF.hasMFDerivAt.comp p (hasMFDerivAt_snd p)).const_smul Δ
  have hsp : Θ.symm (Θ p) = p := Θ.symm_apply_apply p
  have hgd : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) g (Θ.symm (Θ p)) := by
    rw [hsp]
    exact hg.mdifferentiableAt
  have hGN : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (g ∘ Θ.symm) (Θ p) :=
    hgd.comp (Θ p) (Θ.symm.mdifferentiable hm (Θ p))
  have hcomp : (g ∘ Θ.symm) ∘ Θ = g := funext fun q => by
    simp only [comp_apply, Θ.symm_apply_apply]
  have hchain := mfderiv_comp p hGN (Θ.mdifferentiable hm p)
  rw [hcomp, hg.mfderiv] at hchain
  have happ := congrArg (fun A : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p →L[ℝ] ℝ => A Y) hchain
  exact happ.symm

/-- **LFR28 B7 (kernel).** On an isometric product chart, the model height `Δ · F ∘ (Θ⁻¹ ·).2`
satisfies the gradient clause `hGgrad` of `(LFR28.4)` against the minimizing directions to the
axis, with the error of `F`'s own clause against the minimizing directions to `s₀`. -/
theorem edgeModel_gradient_clause_of_product {N W S : Type} [MetricSpace N]
    [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [CompleteSpace N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [MetricSpace W]
    [MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S] [CompleteSpace S]
    [RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) S]
    {r r' : ℕ∞}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((r : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _)) (hr : 2 ≤ r)
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (κ : ContMDiffRiemannianMetric (𝓡 2) ((r' : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : S → Type _)) (hr' : 2 ≤ r')
    (hκnorm : ∀ (x : S) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w)))
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) (ψ : S ≃ᵢ W) {m : WithTop ℕ∞} (hm : 2 ≤ m)
    (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N m)
    (he : ∀ p : ℝ × S, e (Θ p) = WithLp.toLp 2 (p.1, ψ p.2))
    (hpull : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
      G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2)
    (s₀ : S) {F : S → ℝ} {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 ≤ ε)
    (hF : ∀ s : S, 5 / 2 * Δ ≤ dist s s₀ → dist s s₀ ≤ 13 / 2 * Δ →
      MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) F s ∧
        ∀ u ∈ κ.finiteMinimizingDirectionsTo ({s₀} : Set S) s, ∀ w : TangentSpace (𝓡 2) s,
          |Δ * mvfderiv (𝓡 2) F s w + κ.inner s u w| ≤ ε * Real.sqrt (κ.inner s w w)) :
    ∀ x : N, 5 / 2 * Δ ≤ dist (e x).snd (ψ s₀) → dist (e x).snd (ψ s₀) ≤ 13 / 2 * Δ →
      ∀ v ∈ G.finiteMinimizingDirectionsTo (e ⁻¹' {z | z.snd = ψ s₀}) x,
        ∀ X : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3) (fun y => Δ * F (Θ.symm y).2) x X + G.inner x v X| ≤
            ε * Real.sqrt (G.inner x X X) := by
  intro x hx1 hx2 v hv X
  obtain ⟨p, rfl⟩ : ∃ p, Θ p = x := ⟨Θ.symm x, Θ.apply_symm_apply x⟩
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hm
    exact absurd hm (by decide)
  have hsnd : (e (Θ p)).snd = ψ p.2 := by rw [he p]; rfl
  have hdist : dist (e (Θ p)).snd (ψ s₀) = dist p.2 s₀ := by rw [hsnd, ψ.dist_eq]
  rw [hdist] at hx1 hx2
  have hs : p.2 ≠ s₀ := by
    intro h
    rw [h, dist_self] at hx1
    linarith
  obtain ⟨hFd, hFg⟩ := hF p.2 hx1 hx2
  have hΘ2 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) 2 Θ := Θ.contMDiff.of_le hm
  have hpp : Θ (p.1, p.2) = Θ p := rfl
  rw [← hpp] at hv
  obtain ⟨u, hu, hinner⟩ := inner_mfderiv_axisMinimizingDirection G hr hGnorm κ hr' hκnorm e ψ
    Θ Θ.symm Θ.symm_apply_apply Θ.apply_symm_apply hΘ2 he hpull s₀ p.1 p.2 hs v hv
  -- the model coordinates of `X`
  set Y : ℝ × E2 := mfderiv 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) Θ.symm (Θ p) X with hYdef
  have hXY : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p Y = X := by
    have h := mfderiv_diffeomorph_apply_mfderiv_symm hm0 Θ (Θ p) X
    rw [Θ.symm_apply_apply] at h
    exact h
  have hd : mvfderiv 𝓘(ℝ, E3) (fun y => Δ * F (Θ.symm y).2) (Θ p) X =
      Δ * mvfderiv (𝓡 2) F p.2 Y.2 := by
    rw [← mvfderiv_snd_comp_symm_mfderiv hm0 Θ Δ p hFd Y, hXY]
  have hi : G.inner (Θ p) v X = κ.inner p.2 u Y.2 := by
    rw [G.symm, ← hXY]
    exact (hinner Y.1 Y.2).trans (κ.symm _ _ _)
  have hn : κ.inner p.2 Y.2 Y.2 ≤ G.inner (Θ p) X X := by
    rw [← hXY, hpull p Y Y]
    nlinarith [mul_self_nonneg Y.1]
  rw [hd, hi]
  exact (hFg u hu Y.2).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hn) hε)

/-- **LFR28 B7 (R2 bridge).** The gradient clause on the rescaled carrier `(S, Δ⁻¹ d, κΔ)` with
`κΔ = Δ⁻² κ` and R2's direction transfer gives the unscaled clause of
`edgeModel_gradient_clause_of_product`. -/
theorem gradient_clause_of_rescaled {S : Type} [mS : MetricSpace S] [ChartedSpace E2 S]
    [IsManifold (𝓡 2) ∞ S] {n : ℕ∞ω}
    (κ κΔ : ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : S → Type _))
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hκΔ : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), κΔ.inner x v w = Δ⁻¹ ^ 2 * κ.inner x v w)
    (htrans : ∀ (Y : Set S) (s : S) (u : TangentSpace (𝓡 2) s),
      u ∈ κ.finiteMinimizingDirectionsTo Y s →
        letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
        Δ • u ∈ κΔ.finiteMinimizingDirectionsTo Y s)
    (s₀ s : S) {F : S → ℝ} {ε : ℝ}
    (hgrad : letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
      ∀ u ∈ κΔ.finiteMinimizingDirectionsTo ({s₀} : Set S) s, ∀ w : TangentSpace (𝓡 2) s,
        |mvfderiv (𝓡 2) F s w + κΔ.inner s u w| ≤ ε * Real.sqrt (κΔ.inner s w w)) :
    ∀ u ∈ κ.finiteMinimizingDirectionsTo ({s₀} : Set S) s, ∀ w : TangentSpace (𝓡 2) s,
      |Δ * mvfderiv (𝓡 2) F s w + κ.inner s u w| ≤ ε * Real.sqrt (κ.inner s w w) := by
  intro u hu w
  have h := hgrad (Δ • u) (htrans {s₀} s u hu) w
  have hΔ0 : Δ ≠ 0 := hΔ.ne'
  have h1 : κΔ.inner s (Δ • u) w = Δ⁻¹ * κ.inner s u w := by
    rw [hκΔ, map_smul, smul_apply, smul_eq_mul]
    field_simp
  have h2 : Real.sqrt (κΔ.inner s w w) = Δ⁻¹ * Real.sqrt (κ.inner s w w) := by
    rw [hκΔ, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [h1, h2] at h
  have h3 : Δ * mvfderiv (𝓡 2) F s w + κ.inner s u w =
      Δ * (mvfderiv (𝓡 2) F s w + Δ⁻¹ * κ.inner s u w) := by
    field_simp
  rw [h3, abs_mul, abs_of_pos hΔ]
  calc Δ * |mvfderiv (𝓡 2) F s w + Δ⁻¹ * κ.inner s u w|
      ≤ Δ * (ε * (Δ⁻¹ * Real.sqrt (κ.inner s w w))) :=
        mul_le_mul_of_nonneg_left h hΔ.le
    _ = ε * Real.sqrt (κ.inner s w w) := by field_simp

end DifferentialGeometry.Geometry.Collapse
