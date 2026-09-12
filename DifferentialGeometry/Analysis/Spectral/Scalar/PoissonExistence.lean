import DifferentialGeometry.Analysis.Elliptic.HarmonicRigidity
import DifferentialGeometry.Analysis.Spectral.Scalar.SpectralGap
import DifferentialGeometry.Analysis.Spectral.Scalar.PoissonSolvability
import DifferentialGeometry.Analysis.Elliptic.Regularity.Bochner.Polarised
import DifferentialGeometry.Analysis.Heat.Smoothing.Regularity.SmoothRepresentative
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.ChartH2kRegularity
import DifferentialGeometry.Analysis.Heat.Smoothing.Spectral.IteratedDomain
import DifferentialGeometry.Analysis.Sobolev.Hs.Inclusion

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators lp
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian.BochnerPolarised

private def toSmoothScalar (g : SmoothRiemannianMetric I M) (q : C^∞⟮I, M; ℝ⟯) :
    SmoothScalar g :=
  ⟨(fun x : M => q x), q.contMDiff⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
private theorem smoothScalar_coe_toContMDiffMap (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) :
    (⟨f.toFun, f.smooth⟩ : C^∞⟮I, M; ℝ⟯) = f.toContMDiffMap := rfl

def smoothRepresentativeOfLaplacianImage (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ (q : SmoothScalar g) (u_h : laplacianDomain (I := I) (M := M) g),
    laplacianOp (I := I) (M := M) g u_h = smoothToLp (I := I) (M := M) g q →
      ∃ f : SmoothScalar g,
        (∀ x : M, ΔG (I := I) g (⟨f.toFun, f.smooth⟩ : C^∞⟮I, M; ℝ⟯) x = q.toFun x) ∧
          H1ComplToLp (I := I) (M := M) g
              (smoothToH1Compl (I := I) (M := M) g f) =
            H1ComplToLp (I := I) (M := M) g (u_h : H1Compl (I := I) (M := M) g)

omit [NeZero (Module.finrank ℝ E)] in
private theorem inner_smoothToLp_eq_integral_mul
    (g : SmoothRiemannianMetric I M) (f h : SmoothScalar g) :
    ⟪smoothToLp (I := I) (M := M) g f, smoothToLp (I := I) (M := M) g h⟫_ℝ =
      ∫ x, f.toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) f.memLp_two,
    MemLp.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) h.memLp_two] with x hx₁ hx₂
  rw [smoothToLp_apply, smoothToLp_apply, hx₁, hx₂, Real.inner_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem integral_one_ne_zero [Nonempty M]
    (g : SmoothRiemannianMetric I M) :
    (∫ _x : M, (1 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≠ 0 := by
  have hvolpos : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have hfin : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hne : (riemannianVolumeMeasure (I := I) (M := M) g) Set.univ ≠ 0 :=
    isOpen_univ.measure_ne_zero _ Set.univ_nonempty
  have htop : (riemannianVolumeMeasure (I := I) (M := M) g) Set.univ ≠ ⊤ :=
    measure_ne_top _ _
  rw [integral_const, smul_eq_mul, mul_one]
  exact (ENNReal.toReal_pos hne htop).ne'

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] in
private theorem ΔG_const (g : SmoothRiemannianMetric I M) (c : ℝ) (x : M) :
    ΔG (I := I) g (⟨(fun _ : M => c), contMDiff_const⟩ : C^∞⟮I, M; ℝ⟯) x = 0 := by
  convert Δ_g_const (I := I) g c x using 1
  rfl

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] in
private theorem ΔG_sub_const (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (c : ℝ) (x : M) :
    ΔG (I := I) g (⟨(fun y : M => f y - c),
        hf.sub contMDiff_const⟩ : C^∞⟮I, M; ℝ⟯) x =
      ΔG (I := I) g (⟨f, hf⟩ : C^∞⟮I, M; ℝ⟯) x := by
  have h := Δ_g_sub (I := I) (M := M) g (f := f) (h := fun _ : M => c)
    hf contMDiff_const (hf.sub contMDiff_const) x
  have hc := ΔG_const (I := I) (M := M) g c x
  linarith [h, hc]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] in
private theorem ΔG_sub_eq (g : SmoothRiemannianMetric I M) {f₁ f₂ : M → ℝ}
    (h₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁) (h₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₂) (x : M) :
    ΔG (I := I) g (⟨(fun y : M => f₁ y - f₂ y),
        h₁.sub h₂⟩ : C^∞⟮I, M; ℝ⟯) x =
      ΔG (I := I) g (⟨f₁, h₁⟩ : C^∞⟮I, M; ℝ⟯) x -
        ΔG (I := I) g (⟨f₂, h₂⟩ : C^∞⟮I, M; ℝ⟯) x :=
  Δ_g_sub (I := I) (M := M) g (f := f₁) (h := f₂) h₁ h₂ (h₁.sub h₂) x

theorem exists_meanZero_smoothRepresentative
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (q : SmoothScalar g)
    (hq : (∫ x, q.toFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0)
    (hlift : smoothRepresentativeOfLaplacianImage (I := I) (M := M) g) :
    ∃ f : SmoothScalar g,
      (∫ x, f.toFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 ∧
        ∀ x : M, ΔG (I := I) g (⟨f.toFun, f.smooth⟩ : C^∞⟮I, M; ℝ⟯) x = q.toFun x := by
  classical
  have hvolpos : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have hfmc : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hfin : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have horth : ∀ i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val)),
      laplacianEigenvalueOf i.1.val = 0 →
      ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
        smoothToLp (I := I) (M := M) g q⟫_ℝ = 0 := by
    intro i hi
    let b := resolventEigenbasisSigma (I := I) (M := M) g i
    have hbridge : b = resolventHilbertEigenbasisSigma (I := I) (M := M) g i := rfl
    have hμ1 : i.1.val = 1 := by
      have hne : i.1.val ≠ 0 := i.1.val_ne_zero
      unfold laplacianEigenvalueOf at hi
      rw [div_eq_zero_iff] at hi
      rcases hi with h | h
      · linarith
      · exact absurd h hne
    have hmem : b ∈ resolventEigenspace (I := I) (M := M) g i.1.val := by
      rw [hbridge]
      simpa only [resolventHilbertEigenbasisSigma_apply] using
        resolventEigenbasisVec_mem (I := I) (M := M) g i
    have hRu : resolventL2 (I := I) (M := M) g b = b := by
      have h := (mem_resolventEigenspace_iff (I := I) (M := M) g i.1.val b).mp hmem
      rw [hμ1, one_smul] at h
      exact h
    let v : laplacianDomain (I := I) (M := M) g :=
      ⟨resolvent (I := I) (M := M) g b,
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨b, rfl⟩⟩
    have hv : (v : H1Compl (I := I) (M := M) g) = resolvent (I := I) (M := M) g b := rfl
    have hpre : laplacianDomain.preimage (I := I) (M := M) g v = b := by
      apply resolvent_injective (I := I) (M := M) g
      rw [resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g v, hv]
    have hlap : laplacianOp (I := I) (M := M) g v = 0 := by
      rw [laplacianOp_apply, hpre, hv, ← resolventL2_apply, hRu, sub_self]
    obtain ⟨f, hfΔ, hfcls⟩ := hlift (0 : SmoothScalar g) v (by rw [hlap, map_zero])
    have hfΔzero : ∀ x : M, ΔG (I := I) g (⟨f.toFun, f.smooth⟩ : C^∞⟮I, M; ℝ⟯) x = 0 := by
      intro x
      have := hfΔ x
      simpa using this
    obtain ⟨c, hc⟩ := exists_eq_const_of_laplacian_eq_zero (I := I) (M := M) g
      (⟨f.toFun, f.smooth⟩ : C^∞⟮I, M; ℝ⟯) hfΔzero
    have hfconst : f = (⟨(fun _ : M => c), contMDiff_const⟩ : SmoothScalar g) := by
      apply SmoothScalar.ext
      funext x
      exact hc x
    have hcls : smoothToLp (I := I) (M := M) g f = b := by
      rw [← H1ComplToLp_smoothToH1Compl (I := I) (M := M) g f]
      rw [hfcls, hv, ← resolventL2_apply, hRu]
    have hb : resolventHilbertEigenbasisSigma (I := I) (M := M) g i =
        smoothToLp (I := I) (M := M) g
          (⟨(fun _ : M => c), contMDiff_const⟩ : SmoothScalar g) := by
      rw [← hbridge, ← hcls, hfconst]
    rw [hb, inner_smoothToLp_eq_integral_mul]
    have hint : (∫ x, (fun _ : M => c) x * q.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = c * ∫ x, q.toFun x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      have hfun : (fun x : M => (fun _ : M => c) x * q.toFun x) =
          (fun x : M => c * q.toFun x) := rfl
      rw [hfun, integral_const_mul]
    rw [hint, hq, mul_zero]
  obtain ⟨c₀, hc₀, hgap⟩ := exists_pos_le_nonzeroLaplacianEigenvalueSet (I := I) (M := M) g
  obtain ⟨u_h, hlap_u⟩ := exists_laplacianDomain_laplacianOp_eq_of_inner_eigenbasis_eq_zero
    (I := I) (M := M) g hc₀ hgap (smoothToLp (I := I) (M := M) g q) horth
  obtain ⟨f₀, hf₀Δ, _⟩ := hlift q u_h hlap_u
  have hf₀int : Integrable (fun x : M => f₀.toFun x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f₀.smooth.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set c : ℝ := (∫ x, f₀.toFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) /
    (∫ _x : M, (1 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) with hcdef
  refine ⟨⟨fun x : M => f₀.toFun x - c, f₀.smooth.sub contMDiff_const⟩, ⟨?_, ?_⟩⟩
  · have hci : Integrable (fun _ : M => c) (riemannianVolumeMeasure (I := I) (M := M) g) :=
      integrable_const c
    rw [integral_sub hf₀int hci]
    have hone : (∫ _x : M, (fun _ : M => c) _x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        c * ∫ _x : M, (1 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      calc (∫ _x : M, (fun _ : M => c) _x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
          = ∫ _x : M, c * (1 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
            simp
        _ = c * ∫ _x : M, (1 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
            integral_const_mul _ _
    rw [hone, hcdef, div_mul_cancel₀ _ (integral_one_ne_zero (I := I) (M := M) g), sub_self]
  · intro x
    have hsub := ΔG_sub_const g f₀.smooth c x
    have hq' : ΔG (I := I) g (⟨f₀.toFun, f₀.smooth⟩ : C^∞⟮I, M; ℝ⟯) x = q.toFun x := hf₀Δ x
    rw [hsub, hq']

omit [NeZero (Module.finrank ℝ E)] in
theorem eq_of_laplacian_eq_of_integral_eq [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) {f₁ f₂ : C^∞⟮I, M; ℝ⟯}
    (hΔ : ∀ x : M, ΔG (I := I) g f₁ x = ΔG (I := I) g f₂ x)
    (hint : (∫ x, f₁ x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, f₂ x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :
    f₁ = f₂ := by
  classical
  have hvolpos : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have hfin : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set h : C^∞⟮I, M; ℝ⟯ := ⟨fun y : M => f₁ y - f₂ y,
    f₁.contMDiff.sub f₂.contMDiff⟩ with hh
  have hΔ' : ∀ x : M,
      ΔG (I := I) g (⟨(f₁ : M → ℝ), f₁.contMDiff⟩ : C^∞⟮I, M; ℝ⟯) x =
        ΔG (I := I) g (⟨(f₂ : M → ℝ), f₂.contMDiff⟩ : C^∞⟮I, M; ℝ⟯) x := hΔ
  have hΔzero : ∀ x : M, ΔG (I := I) g h x = 0 := by
    intro x
    have hsub := ΔG_sub_eq g f₁.contMDiff f₂.contMDiff x
    rw [← hh] at hsub
    rw [hsub, hΔ' x, sub_self]
  obtain ⟨c, hc⟩ := exists_eq_const_of_laplacian_eq_zero (I := I) (M := M) g h hΔzero
  have hf₁int : Integrable (fun x : M => f₁ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f₁.contMDiff.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf₂int : Integrable (fun x : M => f₂ x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    f₂.contMDiff.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsub_int : (∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 := by
    have hfun : (fun x : M => h x) = (fun y : M => f₁ y - f₂ y) := by
      rw [hh]; rfl
    rw [hfun, integral_sub hf₁int hf₂int, hint, sub_self]
  have hcint : (∫ x, h x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      c * ∫ _x : M, (1 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hfun : (fun x : M => h x) = fun _ : M => c := by
      funext x
      exact hc x
    rw [hfun]
    calc (∫ _x : M, (fun _ : M => c) _x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g))
        = ∫ _x : M, c * (1 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by simp
      _ = c * ∫ _x : M, (1 : ℝ) ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
          integral_const_mul _ _
  have hczero : c = 0 := by
    have hone := integral_one_ne_zero (I := I) (M := M) g
    have hprod : c * (∫ _x : M, (1 : ℝ)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 := hcint.symm.trans hsub_int
    rcases mul_eq_zero.mp hprod with h' | h'
    · exact h'
    · exact absurd h' hone
  apply Subtype.ext
  funext x
  have hx : f₁ x - f₂ x = 0 := by
    have hthis := hc x
    rw [hczero, hh] at hthis
    simpa using hthis
  exact sub_eq_zero.mp hx

theorem existsUnique_meanZero_smooth_poisson_of_smoothRepresentativeOfLaplacianImage
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (q : C^∞⟮I, M; ℝ⟯)
    (hq : (∫ x, q x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0)
    (hlift : smoothRepresentativeOfLaplacianImage (I := I) (M := M) g) :
    ∃! f : C^∞⟮I, M; ℝ⟯,
      (∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 ∧
        ∀ x : M, ΔG (I := I) g f x = q x := by
  obtain ⟨f, hfint, hfΔ⟩ := exists_meanZero_smoothRepresentative (I := I) (M := M) g
    (toSmoothScalar (I := I) (M := M) g q) (by simpa [toSmoothScalar] using hq) hlift
  refine ⟨f.toContMDiffMap, ⟨?_, ?_⟩, ?_⟩
  · simpa [SmoothScalar.coe_toContMDiffMap] using hfint
  · intro x
    simpa [toSmoothScalar, smoothScalar_coe_toContMDiffMap] using hfΔ x
  · intro y hy
    refine eq_of_laplacian_eq_of_integral_eq (I := I) (M := M) g ?_ ?_
    · intro x
      exact (hy.2 x).trans (by simpa [toSmoothScalar, smoothScalar_coe_toContMDiffMap] using (hfΔ x).symm)
    · rw [hy.1]
      simpa [SmoothScalar.coe_toContMDiffMap] using hfint.symm

section LaplacianImageSmoothRepresentative

open DifferentialGeometry.Analysis.Laplacian.Spectral
open DifferentialGeometry.Analysis.Sobolev.Hs

private theorem inner_oneSubLapClassical_eq (g : SmoothRiemannianMetric I M) (u : SmoothScalar g)
    (i : EigenIdx (I := I) (M := M) g) :
    ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
        smoothToLp (I := I) (M := M) g u.oneSubLapClassical⟫_ℝ =
      (1 + EigenIdx.lambda (I := I) (M := M) i) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          smoothToLp (I := I) (M := M) g u⟫_ℝ := by
  have h := laplacianOp_inner_eigenbasis (I := I) (M := M) g
    ⟨smoothToH1Compl (I := I) (M := M) g u,
      smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u⟩ i
  rw [laplacianOp_smoothToH1Compl (I := I) (M := M) u,
    H1ComplToLp_smoothToH1Compl] at h
  rw [inner_sub_right] at h
  linarith

private theorem inner_oneSubLapClassical_iterate (g : SmoothRiemannianMetric I M) (m : ℕ)
    (u : SmoothScalar g) (i : EigenIdx (I := I) (M := M) g) :
    ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
        smoothToLp (I := I) (M := M) g
          ((SmoothScalar.oneSubLapClassical (g := g))^[m] u)⟫_ℝ =
      (1 + EigenIdx.lambda (I := I) (M := M) i) ^ m *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          smoothToLp (I := I) (M := M) g u⟫_ℝ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      rw [inner_oneSubLapClassical_eq]
      rw [ih, pow_succ]
      ring


private theorem summable_even_weighted_coeff_of_smooth (g : SmoothRiemannianMetric I M) (m : ℕ)
    (u : SmoothScalar g) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (1 + EigenIdx.lambda (I := I) (M := M) i) ^ (2 * m) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          smoothToLp (I := I) (M := M) g u⟫_ℝ ^ 2) := by
  have h0 := DifferentialGeometry.Analysis.HeatEquation.summable_basis_coeff_sq (I := I) (M := M) g
    (smoothToLp (I := I) (M := M) g
      ((SmoothScalar.oneSubLapClassical (g := g))^[m] u))
  refine Summable.congr h0 (fun i => ?_)
  rw [inner_oneSubLapClassical_iterate, mul_pow, ← pow_mul, Nat.mul_comm m 2]

private theorem summable_weighted_coeff_of_smooth (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (u : SmoothScalar g) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      scalarSobolevWeight (I := I) (M := M) i σ *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          smoothToLp (I := I) (M := M) g u⟫_ℝ ^ 2) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (σ / 2)
  have hσm : σ ≤ ((2 * m : ℕ) : ℝ) := by
    push_cast
    linarith
  let T : ScalarHs (I := I) (M := M) g ((2 * m : ℕ) : ℝ) :=
    { coeff := fun i => ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
        smoothToLp (I := I) (M := M) g u⟫_ℝ
      weighted_summable := by
        refine Summable.congr
          (summable_even_weighted_coeff_of_smooth (I := I) (M := M) g m u) (fun i => ?_)
        simp only [scalarSobolevWeight, Real.rpow_natCast] }
  exact ScalarHs.weighted_summable_of_le (I := I) (M := M) hσm T

private theorem summable_coeff_of_laplacianOp_eq_smooth (g : SmoothRiemannianMetric I M)
    {u_h : laplacianDomain (I := I) (M := M) g} {q : SmoothScalar g}
    (h : laplacianOp (I := I) (M := M) g u_h = smoothToLp (I := I) (M := M) g q)
    (k : ℕ) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (1 + EigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          H1ComplToLp (I := I) (M := M) g
            (u_h : H1Compl (I := I) (M := M) g)⟫_ℝ ^ 2) := by
  obtain ⟨c₀, hc₀pos, hgap⟩ :=
    exists_pos_le_nonzeroLaplacianEigenvalueSet (I := I) (M := M) g
  have hcoeff : ∀ i : EigenIdx (I := I) (M := M) g,
      ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          smoothToLp (I := I) (M := M) g q⟫_ℝ =
        -EigenIdx.lambda (I := I) (M := M) i *
          ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
            H1ComplToLp (I := I) (M := M) g
              (u_h : H1Compl (I := I) (M := M) g)⟫_ℝ := by
    intro i
    have h2 := laplacianOp_inner_eigenbasis (I := I) (M := M) g u_h i
    rw [h] at h2
    exact h2
  have hsum_q : Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (1 + EigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          smoothToLp (I := I) (M := M) g q⟫_ℝ ^ 2) :=
    Summable.congr (summable_weighted_coeff_of_smooth (I := I) (M := M) g
      ((2 * k : ℕ) : ℝ) q)
      (fun i => by simp only [scalarSobolevWeight, Real.rpow_natCast])
  have hsum_u : Summable (fun i : EigenIdx (I := I) (M := M) g =>
      ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
        H1ComplToLp (I := I) (M := M) g
          (u_h : H1Compl (I := I) (M := M) g)⟫_ℝ ^ 2) :=
    DifferentialGeometry.Analysis.HeatEquation.summable_basis_coeff_sq (I := I) (M := M) g _
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    ((hsum_q.mul_left (c₀⁻¹ ^ 2)).add hsum_u)
  · exact mul_nonneg
      (pow_nonneg (by linarith [EigenIdx.lambda_nonneg (I := I) (M := M) i]) _)
      (sq_nonneg _)
  · rcases eq_or_ne (EigenIdx.lambda (I := I) (M := M) i) 0 with h0 | h0
    · rw [h0]
      simp only [add_zero, one_pow, one_mul]
      exact le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · have hgap_i : c₀ ≤ EigenIdx.lambda (I := I) (M := M) i :=
        hgap _ (mem_nonzeroLaplacianEigenvalueSet_of_laplacianEigenvalueOf_ne_zero
          (I := I) (M := M) i.1 h0)
      have hA2 : c₀ ^ 2 ≤ EigenIdx.lambda (I := I) (M := M) i ^ 2 := by nlinarith
      have hb : ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
            H1ComplToLp (I := I) (M := M) g
              (u_h : H1Compl (I := I) (M := M) g)⟫_ℝ =
          -(⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
            smoothToLp (I := I) (M := M) g q⟫_ℝ) /
            EigenIdx.lambda (I := I) (M := M) i := by
        rw [hcoeff i]
        field_simp
      have hstep : (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
            smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2 /
              EigenIdx.lambda (I := I) (M := M) i ^ 2 ≤
          c₀⁻¹ ^ 2 * (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
            smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2 := by
        have h1 : (EigenIdx.lambda (I := I) (M := M) i ^ 2)⁻¹ ≤ (c₀ ^ 2)⁻¹ := by
          rw [← one_div, ← one_div]
          exact one_div_le_one_div_of_le (by positivity) hA2
        have h2 : (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
              smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2 *
                (EigenIdx.lambda (I := I) (M := M) i ^ 2)⁻¹ ≤
            (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
              smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2 * (c₀ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        rw [div_eq_mul_inv]
        calc (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
              smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2 *
                (EigenIdx.lambda (I := I) (M := M) i ^ 2)⁻¹
            ≤ (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
              smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2 * (c₀ ^ 2)⁻¹ := h2
          _ = c₀⁻¹ ^ 2 * (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
              smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2 := by
              rw [inv_pow]; ring
      rw [hb, neg_div, neg_sq, div_pow]
      calc (1 + EigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) *
            ((⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
              smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2 /
              EigenIdx.lambda (I := I) (M := M) i ^ 2)
          ≤ (1 + EigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) *
              (c₀⁻¹ ^ 2 * (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
                smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hstep
              (pow_nonneg (by linarith [EigenIdx.lambda_nonneg (I := I) (M := M) i]) _)
        _ = c₀⁻¹ ^ 2 * ((1 + EigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) *
              (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
                smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2) := by ring
        _ ≤ c₀⁻¹ ^ 2 * ((1 + EigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) *
              (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
                smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2) +
              (⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
                smoothToLp (I := I) (M := M) g q⟫_ℝ) ^ 2 /
              EigenIdx.lambda (I := I) (M := M) i ^ 2 :=
            le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem mem_laplacianDomainPow_of_laplacianOp_eq_smooth (g : SmoothRiemannianMetric I M)
    {u_h : laplacianDomain (I := I) (M := M) g} {q : SmoothScalar g}
    (h : laplacianOp (I := I) (M := M) g u_h = smoothToLp (I := I) (M := M) g q) :
    ∀ k : ℕ, (u_h : H1Compl (I := I) (M := M) g) ∈
      laplacianDomainPow (I := I) (M := M) g k := by
  intro k
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · rw [hk0, laplacianDomainPow_zero]
    exact Submodule.mem_top
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [hj]
    obtain ⟨u_h', hu_h'_mem, hu_h'_eq⟩ :=
      DifferentialGeometry.Analysis.HeatEquation.exists_laplacianDomainPow_succ_lift_of_weighted_coeff_summable
        (I := I) (M := M) g
        (H1ComplToLp (I := I) (M := M) g (u_h : H1Compl (I := I) (M := M) g)) j
        (summable_coeff_of_laplacianOp_eq_smooth (I := I) (M := M) g h (j + 1))
    have h_eq : u_h' = (u_h : H1Compl (I := I) (M := M) g) :=
      H1ComplToLp_injective_on_laplacianDomain (I := I) (M := M) g
        (u := ⟨u_h', laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g j hu_h'_mem⟩)
        (v := u_h) hu_h'_eq
    rwa [h_eq] at hu_h'_mem

theorem smoothRepresentativeOfLaplacianImage_holds (g : SmoothRiemannianMetric I M) :
    smoothRepresentativeOfLaplacianImage (I := I) (M := M) g := by
  intro q u_h h
  have hmem := mem_laplacianDomainPow_of_laplacianOp_eq_smooth (I := I) (M := M) g h
  have hreg : ∀ k : ℕ, DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g (u_h : H1Compl (I := I) (M := M) g) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    fun k => DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.memWkpChart_two_k_of_laplacianDomainPow
      (I := I) (M := M) g k (hmem k)
  obtain ⟨f_fun, hf_smooth, hf_ae⟩ :=
    DifferentialGeometry.Analysis.HeatEquation.smooth_representative_of_memWkpChart_forall
      (I := I) (M := M) g _ hreg
  let f : SmoothScalar (I := I) g := ⟨f_fun, hf_smooth⟩
  have hclass : H1ComplToLp (I := I) (M := M) g (smoothToH1Compl (I := I) (M := M) g f) =
      H1ComplToLp (I := I) (M := M) g (u_h : H1Compl (I := I) (M := M) g) := by
    rw [H1ComplToLp_smoothToH1Compl]
    apply Lp.ext
    exact (MemLp.coeFn_toLp f.memLp_two).trans hf_ae.symm
  refine ⟨f, ?_, hclass⟩
  have hsub : (⟨smoothToH1Compl (I := I) (M := M) g f,
      smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) f⟩ :
        laplacianDomain (I := I) (M := M) g) = u_h :=
    Subtype.ext (H1ComplToLp_injective_on_laplacianDomain (I := I) (M := M) g hclass)
  have hfq : f.laplacian = q :=
    smoothToLp_injective (I := I) (M := M) g (by
      rw [← laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian (I := I) (M := M) f, hsub, h])
  intro x
  rw [← SmoothScalar.laplacian_toFun]
  exact congrFun (congrArg SmoothScalar.toFun hfq) x

theorem existsUnique_meanZero_smooth_poisson [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (q : C^∞⟮I, M; ℝ⟯)
    (hq : (∫ x, q x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0) :
    ∃! f : C^∞⟮I, M; ℝ⟯,
      (∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 ∧
        ∀ x : M, ΔG (I := I) g f x = q x :=
  existsUnique_meanZero_smooth_poisson_of_smoothRepresentativeOfLaplacianImage
    (I := I) (M := M) g q hq (smoothRepresentativeOfLaplacianImage_holds (I := I) (M := M) g)

end LaplacianImageSmoothRepresentative

end Laplacian
end Analysis
end DifferentialGeometry

end
