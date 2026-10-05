import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.JointZeroPacket
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.NoncompactCarrierData

/-!
# Consumers of the LFR49 row tier and of the noncompact carrier data (lane LFR49, group G3)

* `lfr49_tier_eventually_cone_witness`: LC58's per-sequence `Good` for item (1). Every sequence with
  LFR14's eventual hypotheses has a subsequence and ONE scale `R ≥ T` at which, on a tail, the
  sources have actual pointed Kleiner–Lott `δ`-maps to ONE cone with AC82 radial data.
* `lfr49_noncompact_carrier_transverse_cores`: on LFR47's carrier, for every level `T > ℓ` the open
  core `int {u ≤ T}` is the whole carrier and the carrier generator `W` crosses the level set
  `{u = T}` with `du(W) = 1` (the transversality LC47 and T3 consume).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **LC58's per-sequence `Good` for item (1), from the row tier.** -/
theorem lfr49_tier_eventually_cone_witness
    (K : ℕ) (hK : 10 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) (A : ℝ → ℝ)
    {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
    [∀ i, IsManifold I3 ∞ (X i)] [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle I3 (X i))] [∀ i, CompleteSpace (X i)]
    [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ᶠ i in atTop, ENNReal.ofReal v ≤
      riemannianVolumeMeasure I3 (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ R : ℝ, T ≤ R ∧ ∃ hR : 0 < R,
      ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
        ∀ᶠ j in atTop, Nonempty (@KleinerLottApprox (X (k j)) C
          ((mX (k j)).rescale R⁻¹ (inv_pos.mpr hR)) mC (p (k j)) o δ) := by
  obtain ⟨k, hk, R, hTR, hR, N, mN, cN, hrest⟩ :=
    lfr49_finite_joint_zero_packet_compact_tier K hK hr hv A g hmetric p hvol hcurv hη hL hsec
      (ε := 1 / 2) (e := 1 / 80) hδ hδ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (T := T)
  obtain ⟨hMN, G, q, hprop, hconn, hRiem, hsecG, hGH, C, mC, o, hH, hcone, hev⟩ := hrest
  exact ⟨k, hk, R, hTR, hR, C, mC, o, hH, Filter.Eventually.mono hev fun j hj => hj.1⟩

section Carrier

open DifferentialGeometry.Geometry.FiniteSoul
open DifferentialGeometry.Topology (TransportedCarrier)
open Function

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

/-- **Transverse open cores on the carrier.** Under the restated LFR46's hypotheses, one choice
of `e` and of the carrier generator `W` has, for every level `T > ℓ`, the open core
`int {u ≤ T}` diffeomorphic to the whole carrier and `du(W) = 1` along `{u = T}`. -/
theorem lfr49_noncompact_carrier_transverse_cores [NeZero (Module.finrank ℝ E)] {r : ℕ∞}
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
    ∃ (ℓ : ℝ) (e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I⟯ M)
      (W : (y : TransportedCarrier e.toHomeomorph) → TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y),
      0 < ℓ ∧ ∀ T : ℝ, ℓ < T →
        (∃ Ψ : PartialDiffeomorph (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F))
            (TransportedCarrier e.toHomeomorph) (TransportedCarrier e.toHomeomorph) ∞,
          Ψ.source = interior {y | ‖((TransportedCarrier.diffeomorph
            (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F)) e.toHomeomorph).symm y).2‖ ≤ T} ∧
          Ψ.target = univ) ∧
        ∀ y, ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
            e.toHomeomorph).symm y).2‖ = T →
          mvfderiv (I := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
            (fun y' => ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
              e.toHomeomorph).symm y').2‖) y (W y) = 1 := by
  obtain ⟨-, ℓ, -, e, hℓ, -, -, -, -, W, -, -, -, hdu, -, -, -, hcore⟩ :=
    lfr49_noncompact_carrier_data g hr hnorm hsec hSc hSne hout hε ψ hψs hψ hψexp hdS b hbinj
      hbS hbinv ι hι hιb hιlin hιnorm hιν hιonto p
  exact ⟨ℓ, e, W, hℓ, fun T hT => ⟨hcore T (hℓ.trans hT), fun y hy => hdu y (hy ▸ hT)⟩⟩

end Carrier

end DifferentialGeometry.Geometry.Collapse
