import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.RegularCollisionContactR3B
import DifferentialGeometry.Analysis.Complex.WeakHolomorphic.Continuous
import DifferentialGeometry.Analysis.Elliptic.Planar.SmoothNodalArcs

/-!
# O-MY-R3B port 3/4：去 minimizer 的 `RegularCollisionNodalArcs`

W8 `Plateau/Embeddedness/RegularCollisionNodalArcs.lean` 的 port：`hu : IsMorreyDisk g γ u` →
`hsmI`、`hconfI`、`hharmI`，结论与证明逐字不变（两行超宽的 rcases pattern 折行）；
改名 `morrey_regular_collision_zero_germ_or_smooth_nodal_arcs` →
`confHarm_zero_germ_or_smooth_nodal_arcs_R3B`。
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold Bundle MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold Interval ComplexConjugate

/-- The same actual nontransverse Morrey collision supplies an analytic inverse-
gauge section and either a zero germ or a complete finite smooth radial nodal
cover for its original isothermal graph difference. Every original witness and
its metric, PDE, contact, zero-set transport and weak equation are retained.
The finite angle index may duplicate an endpoint ray; no simultaneous sheet
cellularity or global embedding conclusion is asserted. -/
theorem CuspIncompressibility.ConsumerAudit.confHarm_zero_germ_or_smooth_nodal_arcs_R3B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {u : C(closedDisk, M)} (hsmI : DiskSmoothInterior (E := E) u)
    (hconfI : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension u) z)
    (hharmI : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension u) z = 0)
    (hd3 : Module.finrank ℝ E = 3)
    {a b : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hb : b ∈ ball (0 : ℂ) 1)
    (hab : a ≠ b) (hvalue : diskExtension u a = diskExtension u b)
    (hDa : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a))
    (hDb : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) b))
    (hnot : ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) b)))) :
    let U : ℂ → M := diskExtension u
    let p := U a
    let s := ball (0 : ℂ) 1 ∩ U ⁻¹' (chartAt E p).source
    let ξ : Fin (Module.finrank ℝ E) → ℂ := fun i => chartComplexGradient p U i a
    let Q := chartGramBilin g p p
    let proj := chartLeadingPlaneProjection g p p ξ
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => proj (X z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * ξ i).re)
    ∃ (N : E) (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ),
      Q N N = 1 ∧ proj N = 0 ∧
      (∀ v : E, v = lift (proj v) + (Q N v) • N) ∧
      a ∈ e₁.source ∧ b ∈ e₂.source ∧
      e₁.source ⊆ s ∧ e₂.source ⊆ s ∧ Disjoint e₁.source e₂.source ∧
      (e₁ : ℂ → ℂ) = F ∧ (e₂ : ℂ → ℂ) = F ∧
      IsOpen O ∧ F a ∈ O ∧ O ⊆ e₁.target ∩ e₂.target ∧
      let h₁ : ℂ → ℝ := fun y => Q N (X (e₁.symm y) - X a)
      let h₂ : ℂ → ℝ := fun y => Q N (X (e₂.symm y) - X a)
      let w : ℂ → ℝ := fun y => h₁ y - h₂ y
      w (F a) = 0 ∧ fderiv ℝ w (F a) = 0 ∧
      (∀ y ∈ O,
        X (e₁.symm y) = X a + lift (y - F a) + h₁ y • N ∧
        X (e₂.symm y) = X a + lift (y - F a) + h₂ y • N) ∧
      ∃ (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
        (beta : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ)
        (e : OpenPartialHomeomorph ℂ ℂ) (lam : ℂ → ℝ),
        (∀ y ∈ O, (A y).PosDef ∧ Analysis.planarScalarOperator A beta c w y = 0) ∧
        F a ∈ e.source ∧ e.source ⊆ O ∧ e (F a) = 0 ∧
        ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
        ContDiffOn ℝ ∞ lam e.source ∧ (∀ y ∈ e.source, 0 < lam y) ∧
        let v : ℂ → ℝ := fun y => w (e.symm y)
        let drift : ℂ → ℂ := fun y => (lam (e.symm y))⁻¹ •
          Analysis.planarCoordinateDrift A beta e (e.symm y)
        let potential : ℂ → ℝ := fun y => c (e.symm y) / lam (e.symm y)
        v 0 = 0 ∧ fderiv ℝ v 0 = 0 ∧
        ContDiffOn ℝ ∞ v e.target ∧ ContDiffOn ℝ ∞ drift e.target ∧
        ContDiffOn ℝ ∞ potential e.target ∧
        (∀ y ∈ e.target,
          Laplacian.laplacian v y + fderiv ℝ v y (drift y) + potential y * v y = 0) ∧
        (∀ y ∈ e.source, v (e y) = w y) ∧
        e.target ∩ v ⁻¹' ({0} : Set ℝ) = e '' (e.source ∩ w ⁻¹' ({0} : Set ℝ)) ∧
        let Z : ℂ → ℂ × ℂ := Analysis.planarGradientSection v
        Z 0 = 0 ∧
        ContDiffOn ℝ ∞ Z e.target ∧
        ContDiffOn ℝ ∞ (fun y => Analysis.planarGradientLinearCoefficient
          (drift y) (potential y)) e.target ∧
        ContDiffOn ℝ ∞ (fun y => Analysis.planarGradientConjugateCoefficient
          (drift y)) e.target ∧
        (∀ y ∈ e.target,
          (1 / 2 : ℂ) • (fderiv ℝ Z y 1 + Complex.I • fderiv ℝ Z y Complex.I) =
            Analysis.planarGradientLinearCoefficient (drift y) (potential y) (Z y) +
              Analysis.planarGradientConjugateCoefficient (drift y)
                (conj (Z y).1, conj (Z y).2)) ∧
        (∀ y ∈ e.target, Z y = 0 ↔ v y = 0 ∧ fderiv ℝ v y = 0) ∧
        ∃ (T : Set ℂ) (C : ℝ), IsOpen T ∧ 0 ∈ T ∧ T ⊆ e.target ∧ 0 < C ∧
          (∀ y ∈ T, ‖(1 / 2 : ℂ) • (fderiv ℝ Z y 1 +
            Complex.I • fderiv ℝ Z y Complex.I)‖ ≤ C * ‖Z y‖) ∧
          ∃ R : ℝ, 0 < R ∧ closedBall (0 : ℂ) R ⊆ T ∧ 4 * R * C < 1 / 2 ∧
            ∃ K : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ),
              Measurable K ∧
              (∀ y ∈ T, K y (Z y) = (1 / 2 : ℂ) •
                (fderiv ℝ Z y 1 + Complex.I • fderiv ℝ Z y Complex.I)) ∧
              (∀ y, ‖K y‖ ≤ C) ∧ (∀ y ∉ T, K y = 0) ∧
              ∃ P : C(closedBall (0 : ℂ) R, (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)),
                ‖P - 1‖ ≤ (4 * R * C) / (1 - 4 * R * C) ∧
                (∀ z : closedBall (0 : ℂ) R, IsUnit (P z)) ∧
                (let P₀ : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := fun z =>
                  1 + Analysis.diskCauchyIntegral
                    (fun w : closedBall (0 : ℂ) R => K w * P w) z
                 Ring.inverse (P₀ 0) (Z 0) = 0 ∧
                 (∀ z : closedBall (0 : ℂ) R, P₀ z = P z) ∧
                 (∀ z ∈ closedBall (0 : ℂ) R, IsUnit (P₀ z)) ∧
                 (∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
                   tsupport φ ⊆ ball (0 : ℂ) R →
                   Integrable (fun z : ℂ =>
                     (((fderiv ℝ φ z (1 : ℂ) : ℂ) +
                       Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • P₀ z) ∧
                   (∫ z : ℂ,
                     (((fderiv ℝ φ z (1 : ℂ) : ℂ) +
                       Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • P₀ z) =
                     -(∫ w : closedBall (0 : ℂ) R,
                       (φ (w : ℂ) : ℂ) • (K w * P w)
                         ∂(volume.comap ((↑) : closedBall (0 : ℂ) R → ℂ)))) ∧
                 ContinuousOn (fun z => Ring.inverse (P₀ z) (Z z)) (ball (0 : ℂ) (R / 2)) ∧
                 (∀ (φ : ℂ → ℂ), ContDiff ℝ 1 φ → HasCompactSupport φ →
                   tsupport φ ⊆ ball (0 : ℂ) (R / 2) →
                   (∫ z, Analysis.complexDbar φ z • Ring.inverse (P₀ z) (Z z)) = 0) ∧
                 AnalyticOnNhd ℂ (fun z => Ring.inverse (P₀ z) (Z z))
                   (ball (0 : ℂ) (R / 2)) ∧
                 ((∀ᶠ z in 𝓝 (0 : ℂ), v z = 0) ∨
                   ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) (R / 2) ∧
                     (∀ z ∈ ball (0 : ℂ) ρ, z ≠ 0 → fderiv ℝ v z ≠ 0) ∧
                     ∃ S : Set ℝ, S.Finite ∧ ∃ Γ : S → ℝ → ℂ,
                       (∀ s, Γ s 0 = 0 ∧ ContDiffOn ℝ ∞ (Γ s) (Ioo (-ρ) ρ) ∧
                         HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
                         Set.InjOn (Γ s) (Ico 0 ρ) ∧
                         ∀ r ∈ Ioo (-ρ) ρ, ‖Γ s r‖ = |r| ∧ v (Γ s r) = 0) ∧
                       ∀ z ∈ ball (0 : ℂ) ρ,
                         v z = 0 ↔ z = 0 ∨ ∃ s : S, ∃ r ∈ Ioo 0 ρ, z = Γ s r)) := by
  classical
  intro U p s ξ Q proj X F lift
  with_reducible
    obtain ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
      hdisj, he₁, he₂, hOo, haO, hOsub, hw0, hDw0, hrecon, A, beta, c, e, lam,
      hpdeOriginal, hep, heO, he0, he, hei, hlam, hlampos,
      hv0, hDv0, hv, hB, hq, hpde, hmap, hzeros, hZ0, hZ, hlinear, hconjugate, hsystem, hzero,
      T, C, hTo, h0T, hTe, hC, hbound, R, hR, hRT, hk,
      K, hKmeas, hKeq, hKbound, hKzero, P, hnear, hunit, hH0, hrep, hPunit, hweak, hcontinuous,
      hintegral⟩ :=
      CuspIncompressibility.ConsumerAudit.confHarm_weak_inverse_gauge_with_contact_R3B
        hsmI hconfI hharmI hd3 ha hb hab hvalue hDa hDb hnot
  let v : ℂ → ℝ := fun y => Q N (X (e₁.symm (e.symm y)) - X a) -
    Q N (X (e₂.symm (e.symm y)) - X a)
  let Z : ℂ → ℂ × ℂ := Analysis.planarGradientSection v
  let P₀ : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := fun z =>
    1 + Analysis.diskCauchyIntegral (fun w : closedBall (0 : ℂ) R => K w * P w) z
  have hanalytic : AnalyticOnNhd ℂ (fun z => Ring.inverse (P₀ z) (Z z))
      (ball (0 : ℂ) (R / 2)) := by
    apply Analysis.analyticOnNhd_of_continuousOn_of_integral_realTestDbar_smul_eq_zero
      isOpen_ball hcontinuous
    intro φ hφ hc hs
    have hφc : ContDiff ℝ 1 (fun z => (φ z : ℂ)) :=
      (Complex.ofRealCLM.contDiff.comp hφ).of_le (by simp)
    have hh := hintegral (fun z => (φ z : ℂ)) hφc
      (hc.comp_left Complex.ofReal_zero)
      ((tsupport_comp_subset Complex.ofReal_zero φ).trans hs)
    have heq (z : ℂ) := Analysis.complexDbar_ofReal
      (hφ.differentiable (by simp) z)
    simpa only [heq] using hh
  have hsmall : ball (0 : ℂ) (R / 2) ⊆ closedBall (0 : ℂ) R :=
    (ball_subset_ball (half_le_self hR.le)).trans ball_subset_closedBall
  have hP₀ : ContinuousOn P₀ (closedBall (0 : ℂ) R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact P.continuous.congr fun z => (hrep z).symm
  have hvsmall : ContDiffOn ℝ ∞ v (ball (0 : ℂ) (R / 2)) :=
    hv.mono ((hsmall.trans hRT).trans hTe)
  refine ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
    hdisj, he₁, he₂, hOo, haO, hOsub, hw0, hDw0, hrecon, A, beta, c, e, lam,
    hpdeOriginal, hep, heO, he0, he, hei, hlam, hlampos,
    hv0, hDv0, hv, hB, hq, hpde, hmap, hzeros, hZ0, hZ, hlinear, hconjugate, hsystem, hzero,
    T, C, hTo, h0T, hTe, hC, hbound, R, hR, hRT, hk, K, hKmeas, hKeq,
    hKbound, hKzero, P, hnear, hunit, hH0, hrep, hPunit, hweak, hcontinuous, hintegral,
    hanalytic, ?_⟩
  by_cases hgerm : ∀ᶠ z in 𝓝 (0 : ℂ), v z = 0
  · exact Or.inl hgerm
  · apply Or.inr
    simpa only [sub_zero] using
      Analysis.exists_finite_smooth_nodal_arcs_of_analytic_inverse_gauge
        isOpen_ball (mem_ball_self (half_pos hR)) hvsmall (hP₀.mono hsmall)
        (hPunit 0 (mem_closedBall_self hR.le))
        (hanalytic 0 (mem_ball_self (half_pos hR))) hgerm hv0 hDv0
