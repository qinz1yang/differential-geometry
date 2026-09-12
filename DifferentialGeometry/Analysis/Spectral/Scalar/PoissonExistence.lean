import DifferentialGeometry.Analysis.Elliptic.HarmonicRigidity
import DifferentialGeometry.Analysis.Spectral.Scalar.SpectralGap
import DifferentialGeometry.Analysis.Spectral.Scalar.PoissonSolvability
import DifferentialGeometry.Analysis.Elliptic.Regularity.Bochner.Polarised

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

end Laplacian
end Analysis
end DifferentialGeometry

end
