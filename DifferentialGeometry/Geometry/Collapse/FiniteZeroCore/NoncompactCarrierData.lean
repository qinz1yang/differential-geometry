import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowMap
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulCarrierFlow
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.BundleDiscCore

/-!
# LFR49, noncompact branch, model side: the carrier data from LFR46 (tube form) and LFR47

Frozen blueprint master207A, LFR49 (A:29096): "If it is noncompact, apply LFR45–LFR47, choosing the
point-outward field before its flow map. The zero carrier now has metric order `K-5 ≥ 5`, its actual
soul-flow and normal bundle are smooth, and all distances and the supplied cone remain unchanged."

`lfr49_noncompact_carrier_data` writes this step against the RESTATED LFR46
(`exists_finite_normalFlowMap_tube`, lane CMS3-FLOW2; the originally frozen form is false). From the
same hypotheses (LFR45's tube `(ε, ψ)`, the base map `b` with its inverse contract, the normal
parametrization `ι`), ONE choice of `X, ℓ, A₂, e` and the carrier generator `W` give:
* LFR46's `|X|² ≤ 4` and point margin `-1/4` against the finite minimizing directions to `p`
  beyond `A₂` (in the ORIGINAL structure of `M`);
* on LFR47's carrier `TransportedCarrier e`: `W` smooth, `d(id) W = X`, `g_c(W, W) ≤ 4` for the
  unchanged metric read in the carrier (`TransportedCarrier.metric`, every admissible order), and
  `du(W) = 1` beyond `ℓ` for the fibre radius `u = ‖(D⁻¹ ·).2‖` of the smooth carrier map
  `D = TransportedCarrier.diffeomorph e` (`exists_smooth_carrierFlow`);
* T5's core data for `u` (`bundle_disc_core_data`): continuous, proper, smooth where positive, and
  every open core `int {u ≤ T}` is the whole carrier.

These are the model inputs of `exists_scale_eventually_open_ball_bundle_type_finite` EXCEPT two
items that are not in this tree (state-LFR49.md): (a) the carrier re-charted over the model of the
sources together with smooth comparison maps from it (`C¹` chart convergence to the carrier
metric); (b) the point margin of `W` against the CARRIER metric's finite minimizing directions.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.FiniteSoul
open DifferentialGeometry.Topology (TransportedCarrier)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B] [CompactSpace B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
  [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- **LFR49 noncompact branch, model side (LFR46 tube form + LFR47 flow + T5).** Under the
hypotheses of the restated LFR46 (`3 ≤ r`), one choice of `X, ℓ, A₂, e` and of the smooth carrier
generator `W` has: `|X|² ≤ 4`, the point margin of `X` beyond `A₂`, the zero section onto `b`;
`W` smooth on `TransportedCarrier e` with `d(id) W = X`, `g_c(W, W) ≤ 4` at every admissible order,
`du(W) = 1` beyond `ℓ` for `u = ‖(D⁻¹ ·).2‖`, `D = TransportedCarrier.diffeomorph e`; and `u` is a
continuous proper core coordinate, smooth where positive, whose open cores are the whole carrier. -/
theorem lfr49_noncompact_carrier_data [NeZero (Module.finrank ℝ E)] {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty)
    (hout : ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0)
    {ε : ℝ} (hε : 0 < ε) (ψ : M → TangentBundle I M)
    (hψs : ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε})
    (hψ : ∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
      Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S)
    (hψexp : ∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
      ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd))
    (hdS : ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
      {x | 0 < infDist x S ∧ infDist x S < ε})
    (b : B → M) (hbinj : Injective b) (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x)
    (ι : TotalSpace F V → TangentBundle I M)
    (hι : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ι)
    (hιb : ∀ z, (ι z).proj = b z.proj)
    (hιlin : ∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ι ⟨s, w⟩).snd (A w))
    (hιnorm : ∀ z : TotalSpace F V, g.inner (ι z).proj (ι z).snd (ι z).snd = ‖z.2‖ ^ 2)
    (hιν : ∀ z, ι z ∈ normalSetFinite g S)
    (hιonto : ∀ v ∈ normalSetFinite g S, ∃ z, ι z = v) (p : M) :
    ∃ (X : (x : M) → TangentSpace I x) (ℓ A₂ : ℝ)
      (e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I⟯ M),
      0 < ℓ ∧ 0 < A₂ ∧ (∀ x, g.inner x (X x) (X x) ≤ 4) ∧
      (∀ q, A₂ ≤ dist p q → ∀ u ∈ g.finiteMinimizingDirectionsTo {p} q,
        g.inner q (X q) u ≤ -(1 / 4)) ∧
      (∀ s : B, e ⟨s, 0⟩ = b s) ∧
      ∃ W : (y : TransportedCarrier e.toHomeomorph) → TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y,
        ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)).tangent ∞
          (fun y => (⟨y, W y⟩ :
            TangentBundle (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TransportedCarrier e.toHomeomorph))) ∧
        (∀ y, mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I (TransportedCarrier.identity e) y (W y) =
          X y.point) ∧
        (∀ (m' : ℕ∞ω) (hmn : m' ≤ (r : ℕ∞ω) + 1) (hmr : m' + 1 ≤ ((r - 2 : ℕ∞) : ℕ∞ω))
          (y : TransportedCarrier e.toHomeomorph),
          (TransportedCarrier.metric e g hmn hmr).inner y (W y) (W y) ≤ 4) ∧
        (∀ y, ℓ < ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
            e.toHomeomorph).symm y).2‖ →
          mvfderiv (I := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
            (fun y' => ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
              e.toHomeomorph).symm y').2‖) y (W y) = 1) ∧
        Continuous (fun y => ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
            e.toHomeomorph).symm y).2‖) ∧
        (∀ T, IsCompact {y | ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
            e.toHomeomorph).symm y).2‖ ≤ T}) ∧
        ContMDiffOn (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
          (fun y => ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
            e.toHomeomorph).symm y).2‖)
          {y | 0 < ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
            e.toHomeomorph).symm y).2‖} ∧
        ∀ T : ℝ, 0 < T → ∃ Ψ : PartialDiffeomorph (𝓘(ℝ, EB).prod 𝓘(ℝ, F))
            (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TransportedCarrier e.toHomeomorph)
            (TransportedCarrier e.toHomeomorph) ∞,
          Ψ.source = interior {y | ‖((TransportedCarrier.diffeomorph
            (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F)) e.toHomeomorph).symm y).2‖ ≤ T} ∧
          Ψ.target = univ := by
  obtain ⟨X, φ, ℓ, A₂, δ, prof, hℓ, hA₂, hδ, -, -, -, hXB, -, hφ0, hφadd, hφX, hmargin, -, -,
      hprof, hprof0, -, -, hXS, e, he0, -, hray, hXray, -, -, -⟩ :=
    exists_finite_normalFlowMap_tube g hr hnorm hsec hSc hSne hout hε ψ hψs hψ hψexp hdS b hbinj
      hbS hbinv ι hι hιb hιlin hιnorm hιν hιonto p
  have hXS' : ∀ s : B, X (e ⟨s, 0⟩) = 0 := fun s => by
    rw [he0 s]
    exact hXS (b s) (hbS ▸ mem_range_self s)
  obtain ⟨-, W, -, -, hW, hWX, -, -, hdu⟩ :=
    exists_smooth_carrierFlow hr e X hδ prof hprof hprof0 hXS' hXray φ hφ0 hφadd hφX hℓ.le hray
  obtain ⟨hu, hucpt, -, huW, hcore⟩ :=
    bundle_disc_core_data (TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
      e.toHomeomorph)
  refine ⟨X, ℓ, A₂, e, hℓ, hA₂, hXB, hmargin, he0, W, hW, hWX, fun m' hmn hmr y => ?_, hdu, hu,
    hucpt, huW, hcore⟩
  rw [TransportedCarrier.metric_inner, hWX y]
  exact hXB y.point

end DifferentialGeometry.Geometry.Collapse
