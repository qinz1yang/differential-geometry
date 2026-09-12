import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Loops
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


structure SmoothImmersion where
  map : AddCircle (1 : ℝ) → M
  smooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x : ℝ => map (x : AddCircle (1 : ℝ)))
  immersed : ∀ x : ℝ,
    mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => map (y : AddCircle (1 : ℝ))) x (1 : ℝ) ≠ 0

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem CurveMap.smooth_slice (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) {t : ℝ} (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x => c.lift x t) := by
  have hp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun x : ℝ => (x, t)) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  exact contMDiffOn_univ.mp (hc.comp hp.contMDiffOn (fun _ _ => ⟨mem_univ _, ht⟩))

def SmoothImmersion.slice (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) : SmoothImmersion (I := I) (M := M) where
  map := fun z => c z t
  smooth := c.smooth_slice hc ht
  immersed := fun x => hi x t ht

def SmoothCircleMap (f : AddCircle (1 : ℝ) → AddCircle (1 : ℝ)) : Prop :=
  ∀ x : ℝ, ∃ localLift : ℝ → ℝ, ContDiffAt ℝ ∞ localLift x ∧
    ∀ᶠ y in 𝓝 x, (localLift y : AddCircle (1 : ℝ)) = f (y : AddCircle (1 : ℝ))

structure CircleReparametrization (J : Set ℝ) where
  map : ℝ → (AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
  smooth : ∀ x t, t ∈ J → ∃ localLift : ℝ × ℝ → ℝ,
    ContDiffWithinAt ℝ ∞ localLift (univ ×ˢ J) (x, t) ∧
      ∀ᶠ p in 𝓝[univ ×ˢ J] (x, t),
        (localLift p : AddCircle (1 : ℝ)) = map p.2 (p.1 : AddCircle (1 : ℝ))
  smooth_inverse : ∀ x t, t ∈ J → ∃ localLift : ℝ × ℝ → ℝ,
    ContDiffWithinAt ℝ ∞ localLift (univ ×ˢ J) (x, t) ∧
      ∀ᶠ p in 𝓝[univ ×ˢ J] (x, t),
        (localLift p : AddCircle (1 : ℝ)) = (map p.2).symm (p.1 : AddCircle (1 : ℝ))

omit [CompleteSpace E] in
theorem parabolic_gauge_velocity [I.Boundaryless] (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) {J : Set ℝ} (hc : c.SmoothOn (I := I) J)
    (hi : c.ImmersedOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    0 < (c.speed g x t) ^ (-2 : ℤ) ∧
    (c.speed g x t) ^ (-2 : ℤ) • c.Dx g c.X x t = c.curvatureVector g x t +
      (deriv (fun y => c.speed g y t) x / c.speed g x t ^ 3) • c.X x t := by
  classical
  have hspos : 0 < c.speed g x t := c.speed_pos g hi x t ht
  have hne : c.speed g x t ≠ 0 := ne_of_gt hspos
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun y : ℝ => c.lift y t) x :=
    (c.smooth_slice hc ht).contMDiffAt
  have hγ2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y : ℝ => c.lift y t) x := by
    refine hγ.of_le (m := 2) ?_
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hrep : DifferentiableAt ℝ
      (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.chartRepAt
        (I := I) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x) x := by
    simpa only [CurveMap.X] using
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.differentiableAt_chartRepAt_curveVelocity
        (I := I) hγ2
  have hpair : HasDerivAt (fun s : ℝ => (g t).inner (c.lift s t) (c.X s t) (c.X s t))
      ((g t).inner (c.lift x t)
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x) (c.X x t) +
        (g t).inner (c.lift x t) (c.X x t)
          (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
            (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x)) x :=
    DifferentialGeometry.Geometry.Riemannian.Variation.inner_deriv_at (I := I) (n := ∞)
      (by simp) (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t)
      (fun s : ℝ => c.X s t) x hγ hrep hrep
  have hF : HasDerivAt (fun s : ℝ => (g t).inner (c.lift s t) (c.X s t) (c.X s t))
      (2 * (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) x := by
    have hval : (g t).inner (c.lift x t)
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x) (c.X x t) +
      (g t).inner (c.lift x t) (c.X x t)
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x) =
        2 * (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) := by
      rw [show c.Dx g c.X x t =
        DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x from rfl]
      rw [← (g t).symm (c.lift x t) (c.X x t)
        (DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
          (g t) (fun y : ℝ => c.lift y t) (fun s : ℝ => c.X s t) x)]
      ring
    exact hval ▸ hpair
  have hneF : (g t).inner (c.lift x t) (c.X x t) (c.X x t) ≠ 0 := by
    intro h0
    exact hne (by simp [CurveMap.speed, h0])
  have hspeed : HasDerivAt (fun y : ℝ => c.speed g y t)
      ((2 * (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) /
        (2 * c.speed g x t)) x := by
    have := hF.sqrt hneF
    simpa only [CurveMap.speed] using this
  have hspd : deriv (fun y : ℝ => c.speed g y t) x =
      (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) / c.speed g x t := by
    rw [hspeed.deriv]
    field_simp
  have hinv : HasDerivAt (fun y : ℝ => (c.speed g y t)⁻¹)
      (-(2 * ((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) /
          (2 * c.speed g x t)) / c.speed g x t ^ 2) x :=
    hspeed.inv hne
  have hsmul := DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong_smulFun
    (g t) (fun y : ℝ => c.lift y t) (fun y : ℝ => (c.speed g y t)⁻¹)
    (fun s : ℝ => c.X s t) x hinv.differentiableAt hrep
  refine ⟨zpow_pos hspos _, ?_⟩
  rw [show c.curvatureVector g x t = (c.speed g x t)⁻¹ •
      DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong
        (g t) (fun y : ℝ => c.lift y t)
        (fun s : ℝ => (c.speed g s t)⁻¹ • c.X s t) x from rfl]
  rw [hsmul, hinv.deriv, hspd]
  have hz : c.speed g x t ^ (-2 : ℤ) = (c.speed g x t)⁻¹ * (c.speed g x t)⁻¹ := by
    rw [zpow_neg, zpow_ofNat, pow_two, mul_inv]
  have hcoef : (c.speed g x t)⁻¹ *
        (-(2 * ((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) /
            (2 * c.speed g x t)) / c.speed g x t ^ 2) +
      ((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) /
        c.speed g x t / c.speed g x t ^ 3) = 0 := by
    field_simp
    ring
  have hdi : (c.speed g x t)⁻¹ *
        (-(2 * ((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) /
            (2 * c.speed g x t)) / c.speed g x t ^ 2) =
      -((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) /
        c.speed g x t / c.speed g x t ^ 3) := by
    linarith [hcoef]
  rw [hz, smul_add, smul_smul, smul_smul, hdi, neg_smul]
  abel

@[instance_reducible] def smoothImmersionTopology {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    TopologicalSpace (SmoothImmersion (I := I) (M := M)) :=
  TopologicalSpace.generateFrom {U | ∃ c : SmoothImmersion (I := I) (M := M),
    ∃ m : ℕ, ∃ ε : ℝ, 0 < ε ∧ U = {d | ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv m (fun y : ℝ => e.map (d.map (y : AddCircle (1 : ℝ)))) x -
        iteratedDeriv m (fun y : ℝ => e.map (c.map (y : AddCircle (1 : ℝ)))) x‖ < ε}}

@[instance_reducible] def smoothCylinderTopology {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (J : Set ℝ) : TopologicalSpace (CurveMap M) :=
  TopologicalSpace.generateFrom {U | ∃ c : CurveMap M, ∃ m : ℕ, ∃ ε : ℝ,
    0 < ε ∧ U = {d | ∃ ρ : ℝ, ρ < ε ∧ ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ J,
      ‖iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (d.lift q.1 q.2))
        (univ ×ˢ J) p -
      iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (c.lift q.1 q.2))
        (univ ×ˢ J) p‖ ≤ ρ}}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem smoothCylinderJets_eq_of_eqOn {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {c d : CurveMap M} {J : Set ℝ} (h : ∀ z t, t ∈ J → c z t = d z t)
    (m : ℕ) (p : ℝ × ℝ) (hp : p ∈ univ ×ˢ J) :
    iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (c.lift q.1 q.2)) (univ ×ˢ J) p =
      iteratedFDerivWithin ℝ m (fun q : ℝ × ℝ => e.map (d.lift q.1 q.2)) (univ ×ˢ J) p := by
  apply iteratedFDerivWithin_congr _ hp m
  intro q hq
  exact congrArg e.map (h (q.1 : AddCircle (1 : ℝ)) q.2 hq.2)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem smoothCylinderTopology_induced_eq_of_eqOn {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} {J : Set ℝ} (f g : P → CurveMap M)
    (h : ∀ p z t, t ∈ J → f p z t = g p z t) :
    TopologicalSpace.induced f (smoothCylinderTopology e J) =
      TopologicalSpace.induced g (smoothCylinderTopology e J) := by
  unfold smoothCylinderTopology
  rw [induced_generateFrom_eq, induced_generateFrom_eq]
  congr 1
  apply Set.image_congr
  intro V hV
  obtain ⟨c, m, ε, hε, rfl⟩ := hV
  ext p
  change (∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J, _ ≤ ρ) ↔
    (∃ ρ : ℝ, ρ < ε ∧ ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ J, _ ≤ ρ)
  constructor
  · rintro ⟨ρ, hρ, hbound⟩
    refine ⟨ρ, hρ, ?_⟩
    intro q hq
    simpa only [smoothCylinderJets_eq_of_eqOn e (h p) m q ⟨mem_univ _, hq.2⟩] using
      hbound q hq
  · rintro ⟨ρ, hρ, hbound⟩
    refine ⟨ρ, hρ, ?_⟩
    intro q hq
    simpa only [smoothCylinderJets_eq_of_eqOn e (h p) m q ⟨mem_univ _, hq.2⟩] using
      hbound q hq


theorem smoothImmersionTopology_independent {N N' : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (e' : Width.SmoothLoopEmbedding (I := I) (Q := M) N') :
    smoothImmersionTopology e = smoothImmersionTopology e' := by
  sorry

theorem smoothCylinderTopology_independent {N N' : ℕ} {s u : ℝ} (hsu : s < u)
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (e' : Width.SmoothLoopEmbedding (I := I) (Q := M) N') :
    TopologicalSpace.induced
      (fun c : {c : CurveMap M // c.SmoothOn (I := I) (Icc s u)} => c.1)
      (smoothCylinderTopology e (Icc s u)) =
    TopologicalSpace.induced
      (fun c : {c : CurveMap M // c.SmoothOn (I := I) (Icc s u)} => c.1)
      (smoothCylinderTopology e' (Icc s u)) := by
  sorry

theorem smooth_immersion_regular_family {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P]
    (initial : P → SmoothImmersion (I := I) (M := M))
    (hinit : @Continuous P _ inferInstance (smoothImmersionTopology e) initial) :
    ∃ loops : C(P, Width.RegularLoop I M), ∀ p z, loops p z = (initial p).map z := by
  sorry

variable [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M] [nonemptyM : Nonempty M]
  [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary
variable {D : RealTimeInterval} {a b : ℝ}

theorem rfs_csf_gauge (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {s u : ℝ} (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (φ : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ))
    (hφ : SmoothCircleMap φ) (hφinv : SmoothCircleMap φ.symm) :
    CurveMap.IsSolutionOn (I := I) (fun z t => c (φ z) t) B.family.metric (Icc s u) := by
  sorry

theorem geometric_solution_reparametrize
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {s u : ℝ} (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (α : ℝ → ℝ → ℝ)
    (hc : c.IsGeometricSolutionOn B.family.metric (Icc s u) α) :
    ∃ τ > 0, s + τ ≤ u ∧ ∃ φ : CircleReparametrization (Icc s (s + τ)),
      (∀ z, φ.map s z = z) ∧
      CurveMap.IsSolutionOn (I := I) (fun z t => c (φ.map t z) t) B.family.metric (Icc s (s + τ)) := by
  sorry

theorem rfs_csf_local_input (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ico a b) (c₀ : SmoothImmersion (I := I) (M := M)) :
    ∃ τ > 0, t₀ + τ ≤ b ∧ ∃ c : CurveMap M,
      c.IsSolutionOn B.family.metric (Icc t₀ (t₀ + τ)) ∧
      ∀ z, c z t₀ = c₀.map z := by
  sorry

theorem local_solution_unique (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {t₀ t₁ t₂ : ℝ} (ht₀ : a ≤ t₀) (h₁ : t₀ < t₁) (h₂ : t₀ < t₂)
    (hb₁ : t₁ ≤ b) (hb₂ : t₂ ≤ b) (c₁ c₂ : CurveMap M)
    (hc₁ : c₁.IsSolutionOn B.family.metric (Icc t₀ t₁))
    (hc₂ : c₂.IsSolutionOn B.family.metric (Icc t₀ t₂))
    (hinit : ∀ z, c₁ z t₀ = c₂ z t₀) :
    ∀ z t, t ∈ Icc t₀ (min t₁ t₂) → c₁ z t = c₂ z t := by
  sorry

theorem local_solution_starting_time_uniform
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (t₀ : {t : ℝ // t ∈ Ico a b}) (c₀ : SmoothImmersion (I := I) (M := M)) :
    letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
    ∃ τ > 0, ∃ U : Set ({t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ (t₀, c₀) ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc 0 τ)) solutions) ∧
        ∀ p : U, (p.1.1 : ℝ) + τ ≤ b ∧
          (solutions p).IsSolutionOn
            (fun v => B.family.metric ((p.1.1 : ℝ) + v)) (Icc 0 τ) ∧
          ∀ z, solutions p z 0 = p.1.2.map z := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
