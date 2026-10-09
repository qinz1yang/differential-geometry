import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.TangentGraphDifferenceR3B
import DifferentialGeometry.Geometry.HarmonicMap.TangentGraphContact
import DifferentialGeometry.Analysis.Elliptic.Planar.IsothermalPrincipal
import DifferentialGeometry.Analysis.Elliptic.Planar.FirstOrderReduction
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.BoundedCoefficient
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.BoundedGauge
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.WeakGaugeApproximation

/-!
# O-MY-R3B port 2/4：去 minimizer 的 `RegularCollisionContact`

W8 `Plateau/Embeddedness/RegularCollisionContact.lean` 的 port：`hu : IsMorreyDisk g γ u` →
`hsmI`、`hconfI`、`hharmI`（只用到这三个 field），其余结论与证明逐字不变；
改名 `morrey_regular_collision_X` → `confHarm_X_R3B`。四个原 source body 的分段保留。
-/

-- O-MY-R3B port (orig. ActualMorreyIsothermalContact): IsMorreyDisk -> 3 fields

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold Interval

/-- The same original Morrey graph-height difference admits a local full scalar
Laplacian equation. This changes only scalar graph coordinates and retains both
lower-order terms and the exact zero-set image equation. -/
theorem CuspIncompressibility.ConsumerAudit.confHarm_isothermal_height_difference_with_contact_R3B
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
        e.target ∩ v ⁻¹' ({0} : Set ℝ) = e '' (e.source ∩ w ⁻¹' ({0} : Set ℝ)) := by
  classical
  intro U p s ξ Q proj X F lift
  with_reducible
    obtain ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
      hdisj, he₁, he₂, hei₁, hei₂, hOo, haO, hOsub, hh₁, hh₂, hw, hrecon,
      A, beta, c, hA, hbeta, hc, hpde⟩ :=
      CuspIncompressibility.ConsumerAudit.confHarm_elliptic_height_difference_R3B
        hsmI hconfI hharmI hd3 ha hb hab hvalue hDa hDb hnot
  let h₁ : ℂ → ℝ := fun y => Q N (X (e₁.symm y) - X a)
  let h₂ : ℂ → ℝ := fun y => Q N (X (e₂.symm y) - X a)
  let w : ℂ → ℝ := fun y => h₁ y - h₂ y
  have hEq : ∀ y ∈ O, Analysis.planarScalarOperator A beta c w y = 0 :=
    fun y hy => (hpde y hy).2
  have hs : IsOpen s := hsmI.continuousOn.isOpen_inter_preimage
    isOpen_ball (chartAt E p).open_source
  have hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s :=
    hsmI.mono inter_subset_left
  have hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source := by
    intro z hz
    change z ∈ ball (0 : ℂ) 1 ∩ U ⁻¹' (chartAt E p).source at hz
    exact hz.2
  have hcontact : w (F a) = 0 ∧ fderiv ℝ w (F a) = 0 := by
    with_reducible
      exact chart_height_difference_value_fderiv_zero_of_nontransverse_collision
        hs hU hchart proj (Q N) N lift hsplit e₁ e₂ he₁s he₂s hdisj
        he₁ he₂ hei₁ hei₂ hae₁ hbe₂ hvalue hnot (X a)
  obtain ⟨e, lam, hep, heO, he0, he, hei, hlam, hlampos,
    hv, hB, hq, hpdeIso, hmap, hzeros⟩ :=
    Analysis.exists_local_isothermal_scalar_equation hOo A beta c w
      hA hbeta hc hw (fun y hy => (hpde y hy).1) hEq haO
  let v : ℂ → ℝ := fun y => w (e.symm y)
  have h0target : (0 : ℂ) ∈ e.target := he0 ▸ e.map_source hep
  have hinv : e.symm 0 = F a := by
    rw [← he0]
    exact e.left_inv hep
  have hv0 : v 0 = 0 := by
    change w (e.symm 0) = 0
    rw [hinv]
    exact hcontact.1
  have hwdiff : DifferentiableAt ℝ w (e.symm 0) := by
    rw [hinv]
    exact (hw.contDiffAt (hOo.mem_nhds haO)).differentiableAt (by simp)
  have heidiff : DifferentiableAt ℝ e.symm 0 :=
    (hei.contDiffAt (e.open_target.mem_nhds h0target)).differentiableAt (by simp)
  have hDv0 : fderiv ℝ v 0 = 0 := by
    change fderiv ℝ (w ∘ e.symm) 0 = 0
    rw [fderiv_comp 0 hwdiff heidiff, hinv, hcontact.2,
      ContinuousLinearMap.zero_comp]
  exact ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
    hdisj, he₁, he₂, hOo, haO, hOsub, hcontact.1, hcontact.2, hrecon, A, beta, c, e, lam,
    fun y hy => ⟨(hpde y hy).1, hEq y hy⟩, hep, heO, he0, he, hei, hlam, hlampos,
    hv0, hDv0, hv, hB, hq, hpdeIso, hmap, hzeros⟩

end -- original module scope boundary

-- O-MY-R3B port (orig. ActualMorreyAugmentedContact): IsMorreyDisk -> 3 fields

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold Interval ComplexConjugate

/-- The literal isothermal height difference of the original Morrey disk supplies
an augmented first-order equation and a local differential inequality at contact.
This preserves the original scalar equation, coordinates, and zero-set transport. -/
theorem CuspIncompressibility.ConsumerAudit.confHarm_augmented_height_difference_with_contact_R3B
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
          ∀ y ∈ T, ‖(1 / 2 : ℂ) • (fderiv ℝ Z y 1 +
            Complex.I • fderiv ℝ Z y Complex.I)‖ ≤ C * ‖Z y‖ := by
  classical
  intro U p s ξ Q proj X F lift
  with_reducible
    obtain ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
      hdisj, he₁, he₂, hOo, haO, hOsub, hw0, hDw0, hrecon, A, beta, c, e, lam,
      hpdeOriginal, hep, heO, he0, he, hei, hlam, hlampos,
      hv0, hDv0, hv, hB, hq, hpde, hmap, hzeros⟩ :=
      CuspIncompressibility.ConsumerAudit.confHarm_isothermal_height_difference_with_contact_R3B
        hsmI hconfI hharmI hd3 ha hb hab hvalue hDa hDb hnot
  let h₁ : ℂ → ℝ := fun y => Q N (X (e₁.symm y) - X a)
  let h₂ : ℂ → ℝ := fun y => Q N (X (e₂.symm y) - X a)
  let w : ℂ → ℝ := fun y => h₁ y - h₂ y
  let v : ℂ → ℝ := fun y => w (e.symm y)
  let drift : ℂ → ℂ := fun y => (lam (e.symm y))⁻¹ •
    Analysis.planarCoordinateDrift A beta e (e.symm y)
  let potential : ℂ → ℝ := fun y => c (e.symm y) / lam (e.symm y)
  have hzero : (0 : ℂ) ∈ e.target := by
    rw [← he0]
    exact e.map_source hep
  have hZ := Analysis.contDiffOn_planarGradientSection e.open_target hv
  have hZ0 : Analysis.planarGradientSection v 0 = 0 :=
    (Analysis.planarGradientSection_eq_zero_iff v 0).mpr ⟨hv0, hDv0⟩
  have hcoeff := Analysis.contDiffOn_planarGradientCoefficients hB hq
  obtain ⟨T, C, hTo, h0T, hTe, hC, hbound⟩ :=
    Analysis.exists_local_planarGradientSection_dbar_bound e.open_target hv hB hq hpde hzero
  refine ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
    hdisj, he₁, he₂, hOo, haO, hOsub, hw0, hDw0, hrecon, A, beta, c, e, lam,
    hpdeOriginal, hep, heO, he0, he, hei, hlam, hlampos,
    hv0, hDv0, hv, hB, hq, hpde, hmap, hzeros, hZ0, hZ, hcoeff.1, hcoeff.2, ?_, ?_,
    T, C, hTo, h0T, hTe, hC, hbound⟩
  · intro y hy
    exact Analysis.planarGradientSection_dbar_eq (drift y) (potential y)
      ((hv.contDiffAt (e.open_target.mem_nhds hy)).of_le (by simp)) (hpde y hy)
  · intro y _
    exact Analysis.planarGradientSection_eq_zero_iff v y

end -- original module scope boundary

-- O-MY-R3B port (orig. ActualMorreyBoundedGaugeContact): IsMorreyDisk -> 3 fields

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold Bundle MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold Interval ComplexConjugate

private theorem small_ball_pair_coefficient_data
    {T : Set ℂ} {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hrT : closedBall (0 : ℂ) r ⊆ T)
    (K : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (hK : Measurable K)
    (hbound : ∀ z, ‖K z‖ ≤ C) :
    ∃ R : ℝ, 0 < R ∧ closedBall (0 : ℂ) R ⊆ T ∧ 4 * R * C < 1 / 2 ∧
      AEStronglyMeasurable (fun z : closedBall (0 : ℂ) R => K z)
        (volume.comap ((↑) : closedBall (0 : ℂ) R → ℂ)) ∧
      ∀ᵐ z : closedBall (0 : ℂ) R
        ∂(volume.comap ((↑) : closedBall (0 : ℂ) R → ℂ)), ‖K z‖ ≤ C := by
  let R : ℝ := min r (1 / (16 * (C + 1)))
  have hR : 0 < R := lt_min hr (by positivity)
  have hRr : R ≤ r := min_le_left _ _
  have hsmall : R * (16 * (C + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 16 * (C + 1))).mp (min_le_right _ _)
  refine ⟨R, hR, (closedBall_subset_closedBall hRr).trans hrT, ?_, ?_, ?_⟩
  · nlinarith
  · exact (hK.comp measurable_subtype_coe).aestronglyMeasurable
  · exact Eventually.of_forall fun z => hbound z


/-- The same augmented Morrey section supplies the actual bounded measurable
gauge data on a smaller disk. The constructed unit gauge uses that same coefficient
and satisfies its literal weak equation; no gauge differentiability is assumed. -/
theorem CuspIncompressibility.ConsumerAudit.confHarm_bounded_gauge_with_contact_R3B
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
                 ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
                   tsupport φ ⊆ ball (0 : ℂ) R →
                   Integrable (fun z : ℂ =>
                     (((fderiv ℝ φ z (1 : ℂ) : ℂ) +
                       Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • P₀ z) ∧
                   (∫ z : ℂ,
                     (((fderiv ℝ φ z (1 : ℂ) : ℂ) +
                       Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • P₀ z) =
                     -(∫ w : closedBall (0 : ℂ) R,
                       (φ (w : ℂ) : ℂ) • (K w * P w)
                         ∂(volume.comap ((↑) : closedBall (0 : ℂ) R → ℂ)))) := by
  classical
  intro U p s ξ Q proj X F lift
  with_reducible
    obtain ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
      hdisj, he₁, he₂, hOo, haO, hOsub, hw0, hDw0, hrecon, A, beta, c, e, lam,
      hpdeOriginal, hep, heO, he0, he, hei, hlam, hlampos,
      hv0, hDv0, hv, hB, hq, hpde, hmap, hzeros, hZ0, hZ, hlinear, hconjugate, hsystem, hzero,
      T, C, hTo, h0T, hTe, hC, hbound⟩ :=
      CuspIncompressibility.ConsumerAudit.confHarm_augmented_height_difference_with_contact_R3B
        hsmI hconfI hharmI hd3 ha hb hab hvalue hDa hDb hnot
  obtain ⟨K, hKmeas, hKeq, hKbound, hKzero⟩ :=
    Analysis.exists_measurable_pair_dbar_coefficient hTo
      ((hZ.mono hTe).of_le (by simp)) hC.le hbound
  obtain ⟨r, hr, hrT⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hTo.mem_nhds h0T)
  obtain ⟨R, hR, hRT, hk, hKR, hKB⟩ :=
    small_ball_pair_coefficient_data hr hC.le hrT K hKmeas hKbound
  obtain ⟨P, _, hnear, hunit, hweak⟩ :=
    DiskRegularity.ConsumerAudit.bounded_measurable_unit_gauge_with_weak_equation
      0 R hR (fun z : closedBall (0 : ℂ) R => K z) hKR C hC.le hKB hk
  let v : ℂ → ℝ := fun y => Q N (X (e₁.symm (e.symm y)) - X a) -
    Q N (X (e₂.symm (e.symm y)) - X a)
  let Z : ℂ → ℂ × ℂ := Analysis.planarGradientSection v
  let P₀ : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := fun z =>
    1 + Analysis.diskCauchyIntegral (fun w : closedBall (0 : ℂ) R => K w * P w) z
  have hH0 : Ring.inverse (P₀ 0) (Z 0) = 0 := by
    rw [show Z 0 = 0 from hZ0]
    exact map_zero _
  exact ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
    hdisj, he₁, he₂, hOo, haO, hOsub, hw0, hDw0, hrecon, A, beta, c, e, lam,
    hpdeOriginal, hep, heO, he0, he, hei, hlam, hlampos,
    hv0, hDv0, hv, hB, hq, hpde, hmap, hzeros, hZ0, hZ, hlinear, hconjugate, hsystem, hzero,
    T, C, hTo, h0T, hTe, hC, hbound, R, hR, hRT, hk, K, hKmeas, hKeq,
    hKbound, hKzero, P, hnear, hunit, hH0, hweak⟩

end -- original module scope boundary

-- O-MY-R3B port (orig. ActualMorreyWeakInverseGaugeContact): IsMorreyDisk -> 3 fields

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold Bundle MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold Interval ComplexConjugate

/-- The same actual Morrey graph section and same bounded integral gauge satisfy
weak inverse-gauge cancellation. Every original graph, metric, scalar PDE and
zero-set conclusion is retained in the same existential tuple. -/
theorem CuspIncompressibility.ConsumerAudit.confHarm_weak_inverse_gauge_with_contact_R3B
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
                 ∀ (φ : ℂ → ℂ), ContDiff ℝ 1 φ → HasCompactSupport φ →
                   tsupport φ ⊆ ball (0 : ℂ) (R / 2) →
                   (∫ z, Analysis.complexDbar φ z • Ring.inverse (P₀ z) (Z z)) = 0) := by
  classical
  intro U p s ξ Q proj X F lift
  with_reducible
    obtain ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
      hdisj, he₁, he₂, hOo, haO, hOsub, hw0, hDw0, hrecon, A, beta, c, e, lam,
      hpdeOriginal, hep, heO, he0, he, hei, hlam, hlampos,
      hv0, hDv0, hv, hB, hq, hpde, hmap, hzeros, hZ0, hZ, hlinear, hconjugate, hsystem, hzero,
      T, C, hTo, h0T, hTe, hC, hbound, R, hR, hRT, hk,
      K, hKmeas, hKeq, hKbound, hKzero, P, hnear, hunit, hH0, hrep, hPunit, hweak⟩ :=
      CuspIncompressibility.ConsumerAudit.confHarm_bounded_gauge_with_contact_R3B
        hsmI hconfI hharmI hd3 ha hb hab hvalue hDa hDb hnot
  let v : ℂ → ℝ := fun y => Q N (X (e₁.symm (e.symm y)) - X a) -
    Q N (X (e₂.symm (e.symm y)) - X a)
  let Z : ℂ → ℂ × ℂ := Analysis.planarGradientSection v
  let P₀ : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := fun z =>
    1 + Analysis.diskCauchyIntegral (fun w : closedBall (0 : ℂ) R => K w * P w) z
  let δ := (4 * R * C) / (1 - 4 * R * C)
  have hd : 0 < 1 - 4 * R * C := by linarith
  have hδ0 : 0 ≤ δ := div_nonneg (by positivity) hd.le
  have hδ : δ < 1 := (div_lt_one hd).mpr (by linarith)
  have hnear₀ : ∀ z ∈ closedBall (0 : ℂ) R, ‖P₀ z - 1‖ ≤ δ := by
    intro z hz
    have hrepz : P₀ z = P ⟨z, hz⟩ := hrep ⟨z, hz⟩
    rw [hrepz]
    exact ((P - 1).norm_coe_le_norm ⟨z, hz⟩).trans hnear
  have hZe : ContDiffOn ℝ ∞ Z e.target := hZ
  have hZsmall : ContDiffOn ℝ 1 Z (ball (0 : ℂ) R) :=
    (hZe.of_le (by simp)).mono ((ball_subset_closedBall.trans hRT).trans hTe)
  obtain ⟨hcontinuous, hintegral⟩ := Analysis.disk_gauge_inverse_section_weak_equation
    0 R hR P P₀ K hrep hKmeas.aestronglyMeasurable hδ0 hδ hC.le hnear₀ hKbound
    (fun φ hφ hc hs => (hweak φ hφ hc hs).2) Z hZsmall
    (fun z hz => (hKeq z (hRT (ball_subset_closedBall hz))).symm)
  exact ⟨N, e₁, e₂, O, hNN, hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
    hdisj, he₁, he₂, hOo, haO, hOsub, hw0, hDw0, hrecon, A, beta, c, e, lam,
    hpdeOriginal, hep, heO, he0, he, hei, hlam, hlampos,
    hv0, hDv0, hv, hB, hq, hpde, hmap, hzeros, hZ0, hZ, hlinear, hconjugate, hsystem, hzero,
    T, C, hTo, h0T, hTe, hC, hbound, R, hR, hRT, hk, K, hKmeas, hKeq,
    hKbound, hKzero, P, hnear, hunit, hH0, hrep, hPunit, hweak, hcontinuous, hintegral⟩

end -- original module scope boundary

