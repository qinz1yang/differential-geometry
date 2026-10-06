import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingSpeed_CX5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyFinal_CX3

set_option autoImplicit false

/-! # Supply H2's isotopy and speed inputs from the proved H1 theorem

The endpoint equality and the isotopy-speed bound are derived from the actual
CX3 transfer isotopy. Equality on the closed parameter interval suffices to
identify its endpoint derivatives too, by uniqueness of one-sided derivatives.
-/

noncomputable section
open Set Filter Topology Bundle Metric
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners ℝ V HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]

variable (h : SmoothRiemannianMetric I M)

/-- The zeroth-order part of the actual CX3 small-field bound controls energy. -/
theorem CkSmall_tangent_sq_CX5 {A : CkAtlas_S15 I M}
    {X : ∀ p : M, TangentSpace I p} {k : ℕ} {η : ℝ}
    (hη : 0 < η) (hsmall : CkSmall_S15 h A X k η) {p : M} (hp : p ∈ A.cover) :
    h.inner p (X p) (X p) < η ^ 2 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  have hb := (hsmall i (extChartAt I (A.ctr i) p) (ball_subset_closedBall hi.2)).1
  rw [(extChartAt I (A.ctr i)).left_inv hi.1] at hb
  change Real.sqrt (h.inner p (X p) (X p)) < η at hb
  have hn := metric_inner_self_nonneg h p (X p)
  have hs := Real.sq_sqrt hn
  nlinarith [Real.sqrt_nonneg (h.inner p (X p) (X p))]

/-- Equality on the closed isotopy interval identifies energy at its endpoints
as well as in its interior. -/
theorem curve_energy_eqOn_CX5 {γ δ : ℝ → M} {μ : ℝ}
    (hμ : μ ∈ Icc (0 : ℝ) 1) (heq : EqOn γ δ (Icc (0 : ℝ) 1))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ μ)
    (hδ : MDifferentiableAt 𝓘(ℝ, ℝ) I δ μ) :
    h.inner (γ μ) (mfderiv 𝓘(ℝ, ℝ) I γ μ (timeVector_CX5 μ))
        (mfderiv 𝓘(ℝ, ℝ) I γ μ (timeVector_CX5 μ)) =
      h.inner (δ μ) (mfderiv 𝓘(ℝ, ℝ) I δ μ (timeVector_CX5 μ))
        (mfderiv 𝓘(ℝ, ℝ) I δ μ (timeVector_CX5 μ)) := by
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) 1) μ :=
    uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr ((uniqueDiffOn_Icc zero_lt_one) μ hμ)
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := I) heq hμ
  rw [mfderivWithin_eq_mfderiv hu hγ, mfderivWithin_eq_mfderiv hu hδ] at hd
  have hv : (mfderiv 𝓘(ℝ, ℝ) I γ μ (timeVector_CX5 μ) : V) =
      (mfderiv 𝓘(ℝ, ℝ) I δ μ (timeVector_CX5 μ) : V) :=
    congrArg (fun L => (L (timeVector_CX5 μ) : V)) hd
  exact congrArg₂ (fun (p : M) (v : V) => h.inner p v v) (heq hμ) hv

section Complete
variable [FiniteDimensional ℝ V] [I.Boundaryless]
  [NeZero (Module.finrank ℝ V)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle V (fun x : M ↦ TangentSpace I x)] [LocallyCompactSpace M]
variable (hEnorm : IsMetricNorm h)

/-- The ambient extension has the geodesic energy of its generating vector
field on the inner domain. -/
theorem isotopy_energy_CX5 (X : ∀ p : M, TangentSpace I p)
    (E : ℝ × M → M) (hE : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ E)
    {D : Set M} (heq : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p ∈ D,
      E (μ, p) = scaledExp_S15 h hEnorm X μ p)
    {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1) {p : M} (hp : p ∈ D) :
    h.inner (E (μ, p))
      (mfderiv 𝓘(ℝ, ℝ) I (fun r => E (r, p)) μ (timeVector_CX5 μ))
      (mfderiv 𝓘(ℝ, ℝ) I (fun r => E (r, p)) μ (timeVector_CX5 μ)) =
        h.inner p (X p) (X p) := by
  have hEc : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun r : ℝ => E (r, p)) :=
    hE.comp (contMDiff_id.prodMk contMDiff_const)
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (intrinsicGeodesic h hEnorm p (X p)) μ :=
    ((intrinsicGeodesic_contMDiffOn h hEnorm p (X p)).contMDiffAt univ_mem).mdifferentiableAt (by simp)
  have hsame : EqOn (fun r => E (r, p)) (intrinsicGeodesic h hEnorm p (X p))
      (Icc (0 : ℝ) 1) := fun r hr =>
    (heq r hr p hp).trans (scaledExp_eq_geodesic_S15 h hEnorm X r p)
  calc
    _ = h.inner (intrinsicGeodesic h hEnorm p (X p) μ)
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic h hEnorm p (X p)) μ (timeVector_CX5 μ))
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic h hEnorm p (X p)) μ (timeVector_CX5 μ)) :=
      curve_energy_eqOn_CX5 h hμ hsame (hEc.mdifferentiableAt (by simp)) hγ
    _ = h.inner p (X p) (X p) := by
      convert! intrinsicGeodesic_speedSq_eq h hEnorm p (X p) μ using 1

include hEnorm in
/-- A directly usable H2 isotopy from `transfer_isotopy_of_Ck_close_CX3`.
All time slices are injective (indeed they come from S15 global diffeomorphisms),
and their parameter speed is strictly less than the requested `η`. -/
theorem transfer_isotopy_for_smoothing_CX5 (A : CkAtlas_S15 I M)
    {D D1 D2 : Set M} (hD : IsCompact D) (hD1 : IsCompact D1) (hD2 : IsCompact D2)
    (hDD1 : D ⊆ D1) (hD12 : D1 ⊆ interior D2) (hD2A : D2 ⊆ A.cover)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ O : Set M, IsOpen O ∧ D2 ⊆ O ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧
        ∀ Φ : M → M, ContMDiffOn I I ∞ Φ O →
          (∀ p ∈ O, Manifold.riemannianEDist I p (Φ p) < ENNReal.ofReal ρ) →
          CkCloseInAtlas_CX3 A D2 k ε Φ →
          ∃ E : ℝ × M → M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ E ∧
            (∀ p, E (0, p) = p) ∧ (∀ p ∈ D, E (1, p) = Φ p) ∧
            (∀ μ : ℝ, Function.Injective (fun p => E (μ, p))) ∧
            ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p ∈ D,
              h.inner (E (μ, p))
                (mfderiv 𝓘(ℝ, ℝ) I (fun r => E (r, p)) μ (timeVector_CX5 μ))
                (mfderiv 𝓘(ℝ, ℝ) I (fun r => E (r, p)) μ (timeVector_CX5 μ)) < η ^ 2 := by
  obtain ⟨O, hO, hD2O, ρ, hρ, htransfer⟩ :=
    transfer_isotopy_of_Ck_close_CX3 h hEnorm A hD hD1 hD2 hDD1 hD12 hD2A k hk
  refine ⟨O, hO, hD2O, ρ, hρ, ?_⟩
  intro η hη
  obtain ⟨ε, hε, hfamily⟩ := htransfer η hη
  refine ⟨ε, hε, ?_⟩
  intro Φ hΦ hdist hclose
  obtain ⟨X, Ψ, C, _, hsmall, _, _, _, hΨ, hself, hcoc, _, heq, hend, _⟩ :=
    hfamily Φ hΦ hdist hclose
  let E : ℝ × M → M := fun q => Ψ 0 q.1 q.2
  have hE : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ E :=
    hΨ.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)
  refine ⟨E, hE, hself 0, hend, ?_, ?_⟩
  · intro μ
    exact (transferDiffeo_S15 Ψ hΨ hself hcoc 0 μ).injective
  · intro μ hμ p hp
    rw [isotopy_energy_CX5 h hEnorm X E hE heq hμ hp]
    exact CkSmall_tangent_sq_CX5 h hη hsmall
      (hD2A (interior_subset (hD12 (hDD1 hp))))

end Complete
end GC.LongTime.Ch12
