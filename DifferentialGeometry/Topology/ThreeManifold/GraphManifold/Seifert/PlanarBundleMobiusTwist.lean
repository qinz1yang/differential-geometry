import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarBundleMobiusPullback
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport

/-!
# Circle bundles over a Möbius base

Chapter 6, lane MD5, tier T4 of the P1 Morse-decomposition plan, third file (after
`SF/PlanarBundleMobiusCover.lean` and `SF/PlanarBundleMobiusPullback.lean`; the chart itself is
assembled in `SF/PlanarBundleMobius.lean`).
The pulled-back fibration over the annulus is a product by T1 (`exists_pullProduct`). The annulus
is oriented by pulling back the constant orientation of `ℂ` (`annOrientation`); the deck involution
reverses it (`annDeckDiffeo_reverses`: at `7/4` the derivative of `deck` is complex conjugation,
`fderiv_deck_seven_quarters`). The deck of the fibre product (`deckP`, `deckT`) preserves the
pulled-back orientation of the total space (`orientation_map_deckP`), so for a positive fibre
coordinate `τ` the twisted coordinate `twistCoord τ = (deck × conj) ∘ τ ∘ deck` is again positive
(`twistCoord_isPositive`). The half annuli `rightOpen`, `leftOpen` overlap in a contractible
sector (`sectorHomeomorph` onto a convex box, `isSimplyConnected_sector`), the cutoff
`seamCutoff` is a function of `re w / ‖w‖`, and `exists_upperCoord` glues `τ` with its twist
once (`FibreCoordinate.glue`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

namespace MobiusCover

theorem tangentChartEquiv_plane (p x : ℂ)
    (hx : x ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p).baseSet) :
    tangentChartEquiv 𝓘(ℝ, ℂ) ℂ p x hx = LinearEquiv.refl ℝ ℂ := by
  apply LinearEquiv.ext
  intro v
  have h1 := Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ
    (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p) hx v
  rw [TangentBundle.continuousLinearMapAt_model_space] at h1
  exact h1.symm

def planeConst : ManifoldOrientation 𝓘(ℝ, ℂ) ℂ 2 where
  dimension_eq := Complex.finrank_real_complex
  orientation _ := Complex.orientation
  locally_constant p x hx := by
    have hb : ∀ y : ℂ, y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) p).baseSet := fun y => by
      simp
    refine ⟨univ, isOpen_univ, mem_univ x, fun y _ => hb y, fun y _ => ?_⟩
    rw [tangentChartEquiv_plane, tangentChartEquiv_plane]
    rfl

theorem bijective_mfderiv_annEmb (x : annulusSurface.{u}.Carrier) :
    Function.Bijective (mfderiv (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℂ)
      annEmb x) := by
  have hinj : Function.Injective (mfderiv (SurfaceModel.model annulusSurface.{u}.kind)
      𝓘(ℝ, ℂ) annEmb x) :=
    isSmoothEmbedding_annEmb.isImmersion.mfderiv_injective (by simp) x
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank ℝ (TangentSpace (SurfaceModel.model annulusSurface.{u}.kind) x) =
      Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℂ) (annEmb x)) := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = Module.finrank ℝ ℂ
    rw [finrank_euclideanSpace_fin, Complex.finrank_real_complex]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

def annOrientation : ManifoldOrientation (SurfaceModel.model annulusSurface.{u}.kind)
    annulusSurface.{u}.Carrier 2 :=
  Manifold.manifoldOrientationPullback (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℂ)
    (finrank_euclideanSpace_fin) annEmb isSmoothEmbedding_annEmb.isImmersion.contMDiff
    bijective_mfderiv_annEmb planeConst

def annDiff (x : annulusSurface.{u}.Carrier) : EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] ℂ :=
  (Manifold.differentialEquivOfBijective (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℂ)
    annEmb bijective_mfderiv_annEmb x).toLinearEquiv

theorem annDiff_apply (x : annulusSurface.{u}.Carrier)
    (v : TangentSpace (SurfaceModel.model annulusSurface.{u}.kind) x) :
    annDiff x v = mfderiv (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℂ) annEmb x v := rfl

theorem orientation_map_annOrientation (x : annulusSurface.{u}.Carrier) :
    Orientation.map (Fin 2) (annDiff x) (annOrientation.orientation x) = Complex.orientation :=
  Manifold.orientation_map_manifoldOrientationPullback _ _ _ _ _ _ _ x

theorem seven_quarters_mem : (7 / 4 : ℂ) ∈ annulus := by
  rw [annulus, mem_ofPred_eq, show (7 / 4 : ℂ) = ((7 / 4 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  constructor <;> norm_num

theorem deck_real {t : ℝ} (ht : |t| < 7 / 4) :
    deck ((7 / 4 + t : ℝ) : ℂ) = ((t - 7 / 4 : ℝ) : ℂ) := by
  have hpos : 0 < 7 / 4 + t := by linarith [neg_abs_le t]
  rw [deck, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, Complex.real_smul,
    ← Complex.ofReal_mul, ← Complex.ofReal_neg]
  congr 1
  rw [div_mul_cancel₀ _ hpos.ne']
  ring

theorem deck_circle (t : ℝ) :
    deck ((7 / 4 : ℂ) * Complex.exp (t * Complex.I)) =
      -((7 / 4 : ℂ) * Complex.exp (t * Complex.I)) := by
  have hn : ‖(7 / 4 : ℂ) * Complex.exp (t * Complex.I)‖ = 7 / 4 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      show (7 / 4 : ℂ) = ((7 / 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by norm_num)]
  rw [deck, hn]
  norm_num

theorem fderiv_deck_seven_quarters :
    fderiv ℝ deck (7 / 4 : ℂ) = (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
  have hd : DifferentiableAt ℝ deck (7 / 4 : ℂ) :=
    (contDiffAt_deck (ne_zero_of_mem_annulus seven_quarters_mem)).differentiableAt (by simp)
  set L := fderiv ℝ deck (7 / 4 : ℂ)
  have h1 : L 1 = 1 := by
    have hc : HasDerivAt (fun t : ℝ => ((7 / 4 + t : ℝ) : ℂ)) 1 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_add (7 / 4 : ℝ)).ofReal_comp
      simpa using this
    have h0 : ((7 / 4 + (0 : ℝ) : ℝ) : ℂ) = 7 / 4 := by push_cast; ring
    have hA : HasDerivAt (fun t : ℝ => deck ((7 / 4 + t : ℝ) : ℂ)) (L 1) 0 := by
      have h' : HasFDerivAt deck L (((7 / 4 + (0 : ℝ) : ℝ) : ℂ)) := by
        rw [h0]
        exact hd.hasFDerivAt
      exact HasFDerivAt.comp_hasDerivAt (l := deck)
        (f := fun t : ℝ => ((7 / 4 + t : ℝ) : ℂ)) (0 : ℝ) h' hc
    have hB : HasDerivAt (fun t : ℝ => ((t - 7 / 4 : ℝ) : ℂ)) 1 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).sub_const (7 / 4 : ℝ)).ofReal_comp
      simpa using this
    have hev : (fun t : ℝ => deck ((7 / 4 + t : ℝ) : ℂ)) =ᶠ[𝓝 0]
        fun t : ℝ => ((t - 7 / 4 : ℝ) : ℂ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 7 / 4 by norm_num)]
        with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact deck_real ht
    exact hA.unique (hB.congr_of_eventuallyEq hev)
  have hI : L Complex.I = -Complex.I := by
    have hc : HasDerivAt (fun t : ℝ => (7 / 4 : ℂ) * Complex.exp (t * Complex.I))
        ((7 / 4 : ℂ) * Complex.I) 0 := by
      have h := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I).cexp
      have h2 := h.const_mul (7 / 4 : ℂ)
      simpa using h2
    have h0 : (7 / 4 : ℂ) * Complex.exp ((0 : ℝ) * Complex.I) = 7 / 4 := by simp
    have hA : HasDerivAt (fun t : ℝ => deck ((7 / 4 : ℂ) * Complex.exp (t * Complex.I)))
        (L ((7 / 4 : ℂ) * Complex.I)) 0 := by
      have h' : HasFDerivAt deck L ((7 / 4 : ℂ) * Complex.exp ((0 : ℝ) * Complex.I)) := by
        rw [h0]
        exact hd.hasFDerivAt
      exact HasFDerivAt.comp_hasDerivAt (l := deck)
        (f := fun t : ℝ => (7 / 4 : ℂ) * Complex.exp (t * Complex.I)) (0 : ℝ) h' hc
    have hB : HasDerivAt (fun t : ℝ => -((7 / 4 : ℂ) * Complex.exp (t * Complex.I)))
        (-((7 / 4 : ℂ) * Complex.I)) 0 := hc.neg
    have he := hA.unique (hB.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => deck_circle t))
    have hs : (7 / 4 : ℂ) * Complex.I = (7 / 4 : ℝ) • Complex.I := by
      rw [Complex.real_smul]
      push_cast
      ring
    rw [hs, map_smul] at he
    have he2 : (7 / 4 : ℝ) • L Complex.I = (7 / 4 : ℝ) • (-Complex.I) := by
      rw [he, smul_neg]
    exact smul_right_injective ℂ (show (7 / 4 : ℝ) ≠ 0 by norm_num) he2
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hv, map_add, map_smul, map_smul, h1, hI]
  apply Complex.ext <;> simp

def annDeckDiffeo : annulusSurface.{u}.Carrier ≃ₘ⟮SurfaceModel.model annulusSurface.{u}.kind,
    SurfaceModel.model annulusSurface.{u}.kind⟯ annulusSurface.{u}.Carrier where
  toFun := annDeck
  invFun := annDeck
  left_inv := annDeck_annDeck
  right_inv := annDeck_annDeck
  contMDiff_toFun := contMDiff_annDeck
  contMDiff_invFun := contMDiff_annDeck

theorem annDeckDiffeo_reverses :
    annDeckDiffeo.{u}.preservesOrientation annOrientation annOrientation.opposite := by
  set x₀ := annMk.{u} (7 / 4 : ℂ) seven_quarters_mem
  refine Diffeomorph.preservesOrientation_of_eq_at _ _ _ x₀ ?_
  set A := (annDeckDiffeo.{u}.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv
  have hx₀ : annEmb x₀ = 7 / 4 := rfl
  have hcomp : A.trans (annDiff (annDeckDiffeo x₀)) =
      (annDiff x₀).trans Complex.conjLIE.toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℂ) annEmb (annDeck x₀)
        (mfderiv (SurfaceModel.model annulusSurface.{u}.kind)
          (SurfaceModel.model annulusSurface.{u}.kind) annDeck x₀ v) =
      Complex.conjLIE.toLinearEquiv
        (mfderiv (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℂ) annEmb x₀ v)
    have hE1 : MDifferentiableAt (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℂ) annEmb
        (annDeck x₀) := (isSmoothEmbedding_annEmb.isImmersion.contMDiff.mdifferentiable
          (by simp)) _
    have hE2 : MDifferentiableAt (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℂ) annEmb
        x₀ := (isSmoothEmbedding_annEmb.isImmersion.contMDiff.mdifferentiable (by simp)) _
    have hD : MDifferentiableAt (SurfaceModel.model annulusSurface.{u}.kind)
        (SurfaceModel.model annulusSurface.{u}.kind) annDeck x₀ :=
      (contMDiff_annDeck.mdifferentiable (by simp)) _
    have hdk : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) deck (annEmb x₀) :=
      ((contDiffAt_deck (ne_zero_of_mem_annulus (annEmb_mem x₀))).differentiableAt
        (by simp)).mdifferentiableAt
    rw [← mfderiv_comp_apply x₀ hE1 hD]
    have he : annEmb.{u} ∘ annDeck.{u} = deck ∘ annEmb.{u} := rfl
    rw [he, mfderiv_comp_apply x₀ hdk hE2, mfderiv_eq_fderiv, hx₀,
      fderiv_deck_seven_quarters]
    rfl
  have hinj := (Orientation.map (Fin 2) (annDiff (annDeckDiffeo x₀))).injective
  apply hinj
  have e1 := orientation_map_trans_fin A (annDiff (annDeckDiffeo x₀))
    (annOrientation.orientation x₀)
  have e2 := orientation_map_trans_fin (annDiff x₀) Complex.conjLIE.toLinearEquiv
    (annOrientation.orientation x₀)
  have e3 := congrArg (fun L => Orientation.map (Fin 2) L (annOrientation.orientation x₀)) hcomp
  have e4 := congrArg (Orientation.map (Fin 2) Complex.conjLIE.toLinearEquiv)
    (orientation_map_annOrientation x₀)
  have e5 : Orientation.map (Fin 2) Complex.conjLIE.toLinearEquiv Complex.orientation =
      -Complex.orientation := by
    refine (Orientation.map_eq_neg_iff_det_neg _ _ (by simp)).mpr ?_
    rw [Complex.det_conjLIE]
    norm_num
  have e6 := orientation_map_annOrientation (annDeckDiffeo x₀)
  refine e1.symm.trans (e3.trans (e2.trans (e4.trans (e5.trans ?_))))
  rw [ManifoldOrientation.opposite_orientation]
  have e7 := Orientation.map_neg (ι := Fin 2) (annDiff (annDeckDiffeo x₀))
    (annOrientation.orientation (annDeckDiffeo x₀))
  exact (congrArg Neg.neg e6.symm).trans e7.symm

theorem productTangentBasis_orientation_neg_left {E E' H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ E H}
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N]
    [ChartedSpace H' N] {m n : ℕ} {x : M} {y : N}
    (b : Module.Basis (Fin m) ℝ (TangentSpace I x)) (c : Module.Basis (Fin n) ℝ (TangentSpace J y))
    (i : Fin m) :
    (productTangentBasis I J (b.unitsSMul (Function.update 1 i (-1))) c).orientation
      = -(productTangentBasis I J b c).orientation := by
  have hbp : (b.unitsSMul (Function.update 1 i (-1))).prod c
      = (b.prod c).unitsSMul (Function.update 1 (Sum.inl i) (-1)) := by
    ext j <;> cases j <;>
      simp only [Module.Basis.unitsSMul_apply, Module.Basis.prod_apply, Function.update_apply,
        Sum.elim_inl, Sum.elim_inr] <;>
      (split_ifs <;> simp_all [Module.Basis.unitsSMul_apply, Units.smul_def])
  rw [productTangentBasis_orientation_eq, productTangentBasis_orientation_eq, hbp,
    Module.Basis.orientation_reindex, Module.Basis.orientation_reindex,
    Module.Basis.orientation_neg_single, Orientation.reindex_neg]
  rfl

theorem productOrientation_opposite_left {E E' H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I ∞ M] [IsManifold J ∞ N] {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n) :
    (DifferentialGeometry.productOrientation I J hm hn oM oN).opposite
      = DifferentialGeometry.productOrientation I J hm hn oM.opposite oN := by
  refine productOrientation_unique I J hm hn oM.opposite oN
    (DifferentialGeometry.productOrientation I J hm hn oM oN).opposite ?_
  intro x y b c hb hc
  have hb1 : (b.unitsSMul (Function.update 1 (⟨0, hm⟩ : Fin m) (-1))).orientation
      = oM.orientation x := by
    rw [Module.Basis.orientation_neg_single, hb, ManifoldOrientation.opposite_orientation]
    exact neg_neg (oM.orientation x)
  have hchar := productOrientation_characterization I J hm hn oM oN x y
    (b.unitsSMul (Function.update 1 (⟨0, hm⟩ : Fin m) (-1))) c hb1 hc
  rw [ManifoldOrientation.opposite_orientation, ← hchar,
    productTangentBasis_orientation_neg_left b c ⟨0, hm⟩]
  exact (neg_neg ((productTangentBasis I J b c).orientation)).symm

theorem productOrientation_opposite_opposite {E E' H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [IsManifold I ∞ M] [IsManifold J ∞ N] {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n) :
    DifferentialGeometry.productOrientation I J hm hn oM.opposite oN.opposite
      = DifferentialGeometry.productOrientation I J hm hn oM oN := by
  rw [← productOrientation_opposite_right, ← productOrientation_opposite_left,
    ManifoldOrientation.opposite_opposite]

def sector : Set ℂ := {w | 0 < w.re + w.im ∧ 0 < w.im - w.re}

def sectorBox : Set (ℝ × ℝ) := Ioo (-1 : ℝ) 1 ×ˢ Icc (1 / 2 : ℝ) 3

theorem sqrt_sq_add_one_pos (a : ℝ) : 0 < Real.sqrt (a ^ 2 + 1) :=
  Real.sqrt_pos.mpr (by positivity)

theorem sq_sqrt_sq_add_one (a : ℝ) : Real.sqrt (a ^ 2 + 1) ^ 2 = a ^ 2 + 1 :=
  Real.sq_sqrt (by positivity)

theorem norm_sq_eq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

def sectorHomeomorph : ↥(sector ∩ annulus) ≃ₜ ↥sectorBox where
  toFun w := ⟨(w.1.re / w.1.im, ‖w.1‖), by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := w.2
    have him : 0 < w.1.im := by linarith
    refine ⟨⟨?_, ?_⟩, h3, h4⟩
    · rw [lt_div_iff₀ him]
      linarith
    · rw [div_lt_iff₀ him]
      linarith⟩
  invFun p := ⟨⟨p.1.2 * p.1.1 / Real.sqrt (p.1.1 ^ 2 + 1), p.1.2 / Real.sqrt (p.1.1 ^ 2 + 1)⟩, by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := p.2
    have hs := sqrt_sq_add_one_pos p.1.1
    have hr : 0 < p.1.2 := by linarith
    have hn : ‖(⟨p.1.2 * p.1.1 / Real.sqrt (p.1.1 ^ 2 + 1),
        p.1.2 / Real.sqrt (p.1.1 ^ 2 + 1)⟩ : ℂ)‖ = p.1.2 := by
      have h := norm_sq_eq (⟨p.1.2 * p.1.1 / Real.sqrt (p.1.1 ^ 2 + 1),
        p.1.2 / Real.sqrt (p.1.1 ^ 2 + 1)⟩ : ℂ)
      simp only at h
      have e : (p.1.2 * p.1.1 / Real.sqrt (p.1.1 ^ 2 + 1)) ^ 2 +
          (p.1.2 / Real.sqrt (p.1.1 ^ 2 + 1)) ^ 2 = p.1.2 ^ 2 := by
        rw [div_pow, div_pow, sq_sqrt_sq_add_one]
        field_simp
      rw [e] at h
      exact (pow_left_inj₀ (norm_nonneg _) hr.le two_ne_zero).mp h
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · change 0 < p.1.2 * p.1.1 / Real.sqrt (p.1.1 ^ 2 + 1) + p.1.2 / Real.sqrt (p.1.1 ^ 2 + 1)
      rw [← add_div]
      apply div_pos _ hs
      nlinarith
    · change 0 < p.1.2 / Real.sqrt (p.1.1 ^ 2 + 1) - p.1.2 * p.1.1 / Real.sqrt (p.1.1 ^ 2 + 1)
      rw [← sub_div]
      apply div_pos _ hs
      nlinarith
    · rw [hn]
      exact h3
    · rw [hn]
      exact h4⟩
  left_inv w := by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := w.2
    have him : 0 < w.1.im := by linarith
    have hs : Real.sqrt ((w.1.re / w.1.im) ^ 2 + 1) = ‖w.1‖ / w.1.im := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (div_nonneg (norm_nonneg _) him.le)]
      field_simp
      rw [norm_sq_eq]
    have hn : 0 < ‖w.1‖ := by linarith [h3]
    apply Subtype.ext
    apply Complex.ext
    · change ‖w.1‖ * (w.1.re / w.1.im) / Real.sqrt ((w.1.re / w.1.im) ^ 2 + 1) = w.1.re
      rw [hs]
      field_simp
    · change ‖w.1‖ / Real.sqrt ((w.1.re / w.1.im) ^ 2 + 1) = w.1.im
      rw [hs]
      field_simp
  right_inv p := by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := p.2
    have hs := sqrt_sq_add_one_pos p.1.1
    have hr : 0 < p.1.2 := by linarith
    have hn : ‖(⟨p.1.2 * p.1.1 / Real.sqrt (p.1.1 ^ 2 + 1),
        p.1.2 / Real.sqrt (p.1.1 ^ 2 + 1)⟩ : ℂ)‖ = p.1.2 := by
      have h := norm_sq_eq (⟨p.1.2 * p.1.1 / Real.sqrt (p.1.1 ^ 2 + 1),
        p.1.2 / Real.sqrt (p.1.1 ^ 2 + 1)⟩ : ℂ)
      simp only at h
      have e : (p.1.2 * p.1.1 / Real.sqrt (p.1.1 ^ 2 + 1)) ^ 2 +
          (p.1.2 / Real.sqrt (p.1.1 ^ 2 + 1)) ^ 2 = p.1.2 ^ 2 := by
        rw [div_pow, div_pow, sq_sqrt_sq_add_one]
        field_simp
      rw [e] at h
      exact (pow_left_inj₀ (norm_nonneg _) hr.le two_ne_zero).mp h
    apply Subtype.ext
    apply Prod.ext
    · change p.1.2 * p.1.1 / Real.sqrt (p.1.1 ^ 2 + 1) / (p.1.2 / Real.sqrt (p.1.1 ^ 2 + 1)) =
        p.1.1
      field_simp
    · exact hn
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ (continuous_norm.comp continuous_subtype_val)
    refine Continuous.div (Complex.continuous_re.comp continuous_subtype_val)
      (Complex.continuous_im.comp continuous_subtype_val) fun w => ?_
    obtain ⟨⟨h1, h2⟩, -, -⟩ := w.2
    linarith
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    have hu : Continuous fun p : ↥sectorBox => p.1.1 := continuous_fst.comp continuous_subtype_val
    have hr : Continuous fun p : ↥sectorBox => p.1.2 := continuous_snd.comp continuous_subtype_val
    have hsq : Continuous fun p : ↥sectorBox => Real.sqrt (p.1.1 ^ 2 + 1) :=
      ((hu.pow 2).add continuous_const).sqrt
    have hne : ∀ p : ↥sectorBox, Real.sqrt (p.1.1 ^ 2 + 1) ≠ 0 := fun p =>
      (sqrt_sq_add_one_pos _).ne'
    have hc : Continuous fun p : ↥sectorBox =>
        ((p.1.2 * p.1.1 / Real.sqrt (p.1.1 ^ 2 + 1) : ℝ) : ℂ) +
          ((p.1.2 / Real.sqrt (p.1.1 ^ 2 + 1) : ℝ) : ℂ) * Complex.I :=
      (Complex.continuous_ofReal.comp ((hr.mul hu).div hsq hne)).add
        ((Complex.continuous_ofReal.comp (hr.div hsq hne)).mul continuous_const)
    refine hc.congr fun p => ?_
    apply Complex.ext <;> simp

theorem contractibleSpace_sector : ContractibleSpace ↥(sector ∩ annulus) := by
  have : ContractibleSpace ↥sectorBox :=
    (convex_Ioo (-1 : ℝ) 1 |>.prod (convex_Icc (1 / 2 : ℝ) 3)).contractibleSpace
      ⟨(0, 1), ⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  exact sectorHomeomorph.contractibleSpace

theorem range_annEmb : range annEmb.{u} = annulus := by
  rw [← planarModel_two_eq, ← annulusPlanarBase.{u}.range_embedding]
  rfl

theorem isSimplyConnected_sector :
    IsSimplyConnected (annEmb.{u} ⁻¹' sector) := by
  refine isSimplyConnected_preimage_of_contractible isSmoothEmbedding_annEmb.isEmbedding
    range_annEmb (fun _ => contractibleSpace_sector) ?_
  have h2 : (2 * Complex.I : ℂ) ∈ annulus := by
    rw [annulus, mem_ofPred_eq, norm_mul, Complex.norm_I, mul_one,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs]
    constructor <;> norm_num
  refine ⟨annMk.{u} _ h2, ?_⟩
  change 0 < (2 * Complex.I).re + (2 * Complex.I).im ∧ 0 < (2 * Complex.I).im - (2 * Complex.I).re
  norm_num

theorem continuous_annEmb : Continuous annEmb.{u} := isSmoothEmbedding_annEmb.isEmbedding.continuous

def rightOpen : TopologicalSpace.Opens annulusSurface.{u}.Carrier :=
  ⟨{x | 0 < (annEmb x).re + (annEmb x).im}, isOpen_lt continuous_const
    ((Complex.continuous_re.comp continuous_annEmb).add
      (Complex.continuous_im.comp continuous_annEmb))⟩

def leftOpen : TopologicalSpace.Opens annulusSurface.{u}.Carrier :=
  ⟨{x | 0 < (annEmb x).im - (annEmb x).re}, isOpen_lt continuous_const
    ((Complex.continuous_im.comp continuous_annEmb).sub
      (Complex.continuous_re.comp continuous_annEmb))⟩

def cosAnn (x : annulusSurface.{u}.Carrier) : ℝ := (annEmb x).re / ‖annEmb x‖

theorem continuous_cosAnn : Continuous cosAnn.{u} :=
  (Complex.continuous_re.comp continuous_annEmb).div (continuous_norm.comp continuous_annEmb)
    fun x => (norm_pos_of_mem_annulus (annEmb_mem x)).ne'

def seamCutoff (x : annulusSurface.{u}.Carrier) : ℝ :=
  Real.smoothTransition (-cosAnn x + 1 / 2)

theorem contMDiff_seamCutoff :
    ContMDiff (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℝ) ∞ seamCutoff.{u} := by
  intro x
  have hw := ne_zero_of_mem_annulus (annEmb_mem x)
  have hg : ContDiffAt ℝ ∞ (fun w : ℂ => -(w.re / ‖w‖) + 1 / 2) (annEmb x) :=
    ((Complex.reCLM.contDiff.contDiffAt.div (contDiffAt_norm ℝ hw)
      (norm_ne_zero_iff.mpr hw)).neg).add contDiffAt_const
  exact Real.smoothTransition.contDiff.contDiffAt.comp_contMDiffAt
    (hg.comp_contMDiffAt (isSmoothEmbedding_annEmb.isImmersion.contMDiff x))

theorem half_lt_cosAnn {x : annulusSurface.{u}.Carrier} (h1 : |(annEmb x).im| ≤ (annEmb x).re)
    (h2 : 0 < (annEmb x).re) : 1 / 2 < cosAnn x := by
  have hn := norm_pos_of_mem_annulus (annEmb_mem x)
  rw [cosAnn, lt_div_iff₀ hn]
  have hsq := norm_sq_eq (annEmb x)
  have h3 : (annEmb x).im ^ 2 ≤ (annEmb x).re ^ 2 := by
    nlinarith [abs_nonneg (annEmb x).im, sq_abs (annEmb x).im]
  nlinarith

theorem cosAnn_lt_neg_half {x : annulusSurface.{u}.Carrier}
    (h1 : |(annEmb x).im| ≤ -(annEmb x).re) (h2 : (annEmb x).re < 0) : cosAnn x < -(1 / 2) := by
  have hn := norm_pos_of_mem_annulus (annEmb_mem x)
  rw [cosAnn, div_lt_iff₀ hn]
  have hsq := norm_sq_eq (annEmb x)
  have h3 : (annEmb x).im ^ 2 ≤ (annEmb x).re ^ 2 := by
    nlinarith [abs_nonneg (annEmb x).im, sq_abs (annEmb x).im]
  nlinarith

theorem seamCutoff_eq_zero {x : annulusSurface.{u}.Carrier} (h : 1 / 2 ≤ cosAnn x) :
    seamCutoff x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem seamCutoff_eq_one {x : annulusSurface.{u}.Carrier} (h : cosAnn x ≤ -(1 / 2)) :
    seamCutoff x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem seamCutoff_mem (x : annulusSurface.{u}.Carrier) :
    0 ≤ seamCutoff x ∧ seamCutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem seamCutoff_eventually_zero (b : annulusSurface.{u}.Carrier) (hb : b ∈ rightOpen.{u})
    (hb' : b ∉ leftOpen.{u}) : seamCutoff =ᶠ[𝓝 b] 0 := by
  have h1 : 0 < (annEmb b).re + (annEmb b).im := hb
  have h2 : ¬ 0 < (annEmb b).im - (annEmb b).re := hb'
  have hc : 1 / 2 < cosAnn b := half_lt_cosAnn (abs_le.mpr ⟨by linarith, by linarith⟩)
    (by linarith)
  filter_upwards [(isOpen_lt continuous_const continuous_cosAnn).mem_nhds hc] with y hy
  exact seamCutoff_eq_zero (le_of_lt hy)

theorem seamCutoff_eventually_one (b : annulusSurface.{u}.Carrier) (hb : b ∈ leftOpen.{u})
    (hb' : b ∉ rightOpen.{u}) : seamCutoff =ᶠ[𝓝 b] 1 := by
  have h1 : 0 < (annEmb b).im - (annEmb b).re := hb
  have h2 : ¬ 0 < (annEmb b).re + (annEmb b).im := hb'
  have hc : cosAnn b < -(1 / 2) := cosAnn_lt_neg_half (abs_le.mpr ⟨by linarith, by linarith⟩)
    (by linarith)
  filter_upwards [(isOpen_lt continuous_cosAnn continuous_const).mem_nhds hc] with y hy
  exact seamCutoff_eq_one (le_of_lt hy)

theorem exists_seamCover : ∃ O : Finset (TopologicalSpace.Opens annulusSurface.{u}.Carrier),
    rightOpen.{u} ⊓ leftOpen.{u} = ⨆ O' ∈ O, O' ∧
      (O : Set (TopologicalSpace.Opens annulusSurface.{u}.Carrier)).PairwiseDisjoint id ∧
      ∀ O' ∈ O, IsSimplyConnected (O' : Set annulusSurface.{u}.Carrier) := by
  refine ⟨{rightOpen ⊓ leftOpen}, by rw [Finset.iSup_singleton], by simp, fun O' hO' => ?_⟩
  rw [Finset.mem_singleton] at hO'
  subst hO'
  exact isSimplyConnected_sector

theorem deck_factor_pos (x : annulusSurface.{u}.Carrier) :
    0 < (7 / 2 - ‖annEmb x‖) / ‖annEmb x‖ :=
  div_pos (by linarith [(annEmb_mem x).2]) (norm_pos_of_mem_annulus (annEmb_mem x))

theorem re_annEmb_annDeck (x : annulusSurface.{u}.Carrier) :
    (annEmb (annDeck x)).re = -((7 / 2 - ‖annEmb x‖) / ‖annEmb x‖ * (annEmb x).re) := by
  rw [annEmb_annDeck, deck, Complex.neg_re, Complex.smul_re, smul_eq_mul]

theorem im_annEmb_annDeck (x : annulusSurface.{u}.Carrier) :
    (annEmb (annDeck x)).im = -((7 / 2 - ‖annEmb x‖) / ‖annEmb x‖ * (annEmb x).im) := by
  rw [annEmb_annDeck, deck, Complex.neg_im, Complex.smul_im, smul_eq_mul]

theorem re_ne_zero_of_im_eq_zero {x : annulusSurface.{u}.Carrier} (h : (annEmb x).im = 0) :
    (annEmb x).re ≠ 0 := by
  intro h'
  have := ne_zero_of_mem_annulus (annEmb_mem x)
  exact this (Complex.ext h' h)

theorem mem_sup_of_im_nonneg {x : annulusSurface.{u}.Carrier} (h : 0 ≤ (annEmb x).im) :
    x ∈ rightOpen.{u} ⊔ leftOpen.{u} := by
  rw [TopologicalSpace.Opens.mem_sup]
  rcases h.lt_or_eq with h | h
  · by_cases h2 : 0 < (annEmb x).re + (annEmb x).im
    · exact Or.inl h2
    · right
      change 0 < (annEmb x).im - (annEmb x).re
      linarith
  · rcases (re_ne_zero_of_im_eq_zero h.symm).lt_or_gt with h3 | h3
    · right
      change 0 < (annEmb x).im - (annEmb x).re
      linarith
    · left
      change 0 < (annEmb x).re + (annEmb x).im
      linarith

def seamZone : Set annulusSurface.{u}.Carrier := {x | |(annEmb x).im| < |(annEmb x).re|}

theorem isOpen_seamZone : IsOpen seamZone.{u} :=
  isOpen_lt ((Complex.continuous_im.comp continuous_annEmb).abs)
    ((Complex.continuous_re.comp continuous_annEmb).abs)

theorem mem_seamZone_of_im_eq_zero {x : annulusSurface.{u}.Carrier} (h : (annEmb x).im = 0) :
    x ∈ seamZone.{u} := by
  change |(annEmb x).im| < |(annEmb x).re|
  rw [h, abs_zero]
  exact abs_pos.mpr (re_ne_zero_of_im_eq_zero h)

theorem seamZone_right {x : annulusSurface.{u}.Carrier} (hx : x ∈ seamZone.{u})
    (hr : 0 < (annEmb x).re) :
    seamCutoff x = 0 ∧ x ∈ rightOpen.{u} ∧ seamCutoff (annDeck x) = 1 ∧
      annDeck x ∈ leftOpen.{u} := by
  have hx' : |(annEmb x).im| < (annEmb x).re := by
    have := hx
    change |(annEmb x).im| < |(annEmb x).re| at this
    rwa [abs_of_pos hr] at this
  have hk := deck_factor_pos x
  set k := (7 / 2 - ‖annEmb x‖) / ‖annEmb x‖
  have hre := re_annEmb_annDeck x
  have him := im_annEmb_annDeck x
  have hi := abs_lt.mp hx'
  refine ⟨seamCutoff_eq_zero (half_lt_cosAnn hx'.le hr).le, ?_, seamCutoff_eq_one ?_, ?_⟩
  · change 0 < (annEmb x).re + (annEmb x).im
    linarith
  · refine (cosAnn_lt_neg_half ?_ ?_).le
    · rw [hre, him, abs_le]
      constructor <;> nlinarith
    · rw [hre]
      nlinarith
  · change 0 < (annEmb (annDeck x)).im - (annEmb (annDeck x)).re
    rw [hre, him]
    nlinarith

theorem seamZone_left {x : annulusSurface.{u}.Carrier} (hx : x ∈ seamZone.{u})
    (hr : (annEmb x).re < 0) :
    seamCutoff x = 1 ∧ x ∈ leftOpen.{u} ∧ seamCutoff (annDeck x) = 0 ∧
      annDeck x ∈ rightOpen.{u} := by
  have hx' : |(annEmb x).im| < -(annEmb x).re := by
    have := hx
    change |(annEmb x).im| < |(annEmb x).re| at this
    rwa [abs_of_neg hr] at this
  have hk := deck_factor_pos x
  set k := (7 / 2 - ‖annEmb x‖) / ‖annEmb x‖
  have hre := re_annEmb_annDeck x
  have him := im_annEmb_annDeck x
  have hi := abs_lt.mp hx'
  refine ⟨seamCutoff_eq_one (cosAnn_lt_neg_half hx'.le hr).le, ?_, seamCutoff_eq_zero ?_, ?_⟩
  · change 0 < (annEmb x).im - (annEmb x).re
    linarith
  · refine (half_lt_cosAnn ?_ ?_).le
    · rw [hre, him, abs_le]
      constructor <;> nlinarith
    · rw [hre]
      nlinarith
  · change 0 < (annEmb (annDeck x)).re + (annEmb (annDeck x)).im
    rw [hre, him]
    nlinarith

theorem im_annDeck_neg_iff (x : annulusSurface.{u}.Carrier) :
    (annEmb (annDeck x)).im < 0 ↔ 0 < (annEmb x).im := by
  rw [im_annEmb_annDeck, neg_lt_zero]
  exact ⟨fun h => pos_of_mul_pos_right h (deck_factor_pos x).le,
    fun h => mul_pos (deck_factor_pos x) h⟩

theorem im_annDeck_eq_zero_iff (x : annulusSurface.{u}.Carrier) :
    (annEmb (annDeck x)).im = 0 ↔ (annEmb x).im = 0 := by
  rw [im_annEmb_annDeck, neg_eq_zero, mul_eq_zero]
  exact ⟨fun h => h.resolve_left (deck_factor_pos x).ne', Or.inr⟩

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {E : F.base.Carrier → EuclideanSpace ℝ (Fin 3)}
  (hE : Manifold.IsSmoothEmbedding (SurfaceModel.model F.base.kind)
    𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ E) (hrange : range E = mobiusModel)

theorem exists_pullProduct :
    ∃ Φ : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) ≃ₘ⟮
        (pullCarrier F hE hrange).model, (SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)⟯
        annulusSurface.{u}.Carrier × Circle,
      ∀ x, (Φ x).1 = (pullFibration F hE hrange).projection x :=
  circleBundlesOverPlanarBases_planar (pullCarrier F hE hrange) ⊤ (pullFibration F hE hrange) 2
    (by simp) annulusPlanarBase.{u} (Diffeomorph.refl _ _ ∞)


def deckP (q : (pullCarrier F hE hrange).Carrier) : (pullCarrier F hE hrange).Carrier :=
  ⟨(annDeck q.val.1, q.val.2), (cover_annDeck hE hrange q.val.1).trans q.2⟩

theorem pullProj_deckP (q : (pullCarrier F hE hrange).Carrier) :
    pullProj F hrange (deckP F hE hrange q) = pullProj F hrange q := rfl

theorem deckP_deckP (q : (pullCarrier F hE hrange).Carrier) :
    deckP F hE hrange (deckP F hE hrange q) = q :=
  Subtype.ext (Prod.ext (annDeck_annDeck _) rfl)

theorem contMDiff_deckP :
    ContMDiff (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model ∞
      (deckP F hE hrange) := by
  intro q
  refine contMDiffAt_pull_of F hE hrange ?_ ((contMDiff_pullProj F hE hrange) q)
  refine Continuous.continuousAt ?_
  refine Continuous.subtype_mk ?_ _
  exact ((continuous_annMk continuous_deck_annEmb _).comp
    (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val)

theorem bijective_mfderiv_pullProj (q : (pullCarrier F hE hrange).Carrier) :
    Function.Bijective (mfderiv (pullCarrier F hE hrange).model C.model
      (fun q : (pullCarrier F hE hrange).Carrier => pullProj F hrange q) q) := by
  have h := bijective_mfderiv_of_isLocalHomeomorph (I := C.model)
    (isLocalHomeomorph_pullProj F hE hrange) q
  exact h

def pullDiff (q : (pullCarrier F hE hrange).Carrier) :
    EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (Manifold.differentialEquivOfBijective (pullCarrier F hE hrange).model C.model
    (fun q : (pullCarrier F hE hrange).Carrier => pullProj F hrange q)
    (bijective_mfderiv_pullProj F hE hrange) q).toLinearEquiv

theorem orientation_map_pullDiff (q : (pullCarrier F hE hrange).Carrier) :
    Orientation.map (Fin 3) (pullDiff F hE hrange q)
      ((pullCarrier F hE hrange).orientation.orientation q) =
        C.orientation.orientation (pullProj F hrange q) := by
  let := Manifold.coveringChartedSpace (H := C.kind.Space) (isLocalHomeomorph_pullProj F hE hrange)
  let := Manifold.covering_isManifold (isLocalHomeomorph_pullProj F hE hrange) C.model
  have h := Manifold.orientation_map_manifoldOrientationPullback C.model C.model
    (finrank_euclideanSpace_fin) (pullProj F hrange)
    (Manifold.covering_projection_contMDiff (isLocalHomeomorph_pullProj F hE hrange) C.model)
    (bijective_mfderiv_of_isLocalHomeomorph (isLocalHomeomorph_pullProj F hE hrange))
    C.orientation q
  exact h

theorem mfderiv_deckP_apply (q : (pullCarrier F hE hrange).Carrier) (v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model
      (deckP F hE hrange) q v =
      (pullDiff F hE hrange (deckP F hE hrange q)).symm (pullDiff F hE hrange q v) := by
  apply (pullDiff F hE hrange (deckP F hE hrange q)).injective
  rw [LinearEquiv.apply_symm_apply]
  have h1 : MDifferentiableAt (pullCarrier F hE hrange).model C.model
      (fun q : (pullCarrier F hE hrange).Carrier => pullProj F hrange q) (deckP F hE hrange q) :=
    ((contMDiff_pullProj F hE hrange).mdifferentiable (by simp)) _
  have h2 : MDifferentiableAt (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model
      (deckP F hE hrange) q :=
    ((contMDiff_deckP F hE hrange).mdifferentiable (by simp)) _
  have hc := mfderiv_comp_apply q h1 h2 v
  exact hc.symm

theorem orientation_map_deckP (q : (pullCarrier F hE hrange).Carrier) :
    Orientation.map (Fin 3) ((pullDiff F hE hrange q).trans
      (pullDiff F hE hrange (deckP F hE hrange q)).symm)
      ((pullCarrier F hE hrange).orientation.orientation q) =
        (pullCarrier F hE hrange).orientation.orientation (deckP F hE hrange q) := by
  have e1 := orientation_map_trans_fin (pullDiff F hE hrange q)
    (pullDiff F hE hrange (deckP F hE hrange q)).symm
    ((pullCarrier F hE hrange).orientation.orientation q)
  have e2 := congrArg (Orientation.map (Fin 3) (pullDiff F hE hrange (deckP F hE hrange q)).symm)
    (orientation_map_pullDiff F hE hrange q)
  have e3 := orientation_map_pullDiff F hE hrange (deckP F hE hrange q)
  have e4 := congrArg (Orientation.map (Fin 3) (pullDiff F hE hrange (deckP F hE hrange q)).symm)
    e3
  have e5 := orientation_map_trans_fin (pullDiff F hE hrange (deckP F hE hrange q))
    (pullDiff F hE hrange (deckP F hE hrange q)).symm
    ((pullCarrier F hE hrange).orientation.orientation (deckP F hE hrange q))
  rw [LinearEquiv.self_trans_symm, Orientation.map_refl] at e5
  refine e1.trans (e2.trans ((e4.symm.trans e5.symm).trans ?_))
  rfl

def deckT (x : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier)) :
    (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) :=
  ⟨deckP F hE hrange x.val, trivial⟩

theorem deckT_deckT (x : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier)) :
    deckT F hE hrange (deckT F hE hrange x) = x :=
  Subtype.ext (deckP_deckP F hE hrange x.val)

theorem projection_deckT (x : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier)) :
    (pullFibration F hE hrange).projection (deckT F hE hrange x) =
      annDeck ((pullFibration F hE hrange).projection x) := rfl

theorem contMDiff_deckT :
    ContMDiff (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model ∞
      (deckT F hE hrange) :=
  (ContMDiff.subtypeVal_comp_iff _ _).mp ((contMDiff_deckP F hE hrange).comp contMDiff_subtype_val)

theorem mfderiv_deckT_apply (x : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier))
    (v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model
      (deckT F hE hrange) x v =
      mfderiv (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model
        (deckP F hE hrange) x.val v := by
  have hv1 : MDifferentiableAt (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model
      (Subtype.val : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) →
        (pullCarrier F hE hrange).Carrier) (deckT F hE hrange x) :=
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp)) _
  have hv2 : MDifferentiableAt (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model
      (Subtype.val : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) →
        (pullCarrier F hE hrange).Carrier) x :=
    ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp)) _
  have hd1 : MDifferentiableAt (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model
      (deckT F hE hrange) x := ((contMDiff_deckT F hE hrange).mdifferentiable (by simp)) _
  have hd2 : MDifferentiableAt (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model
      (deckP F hE hrange) x.val := ((contMDiff_deckP F hE hrange).mdifferentiable (by simp)) _
  have h1 := mfderiv_comp_apply x hv1 hd1 v
  have h2 := mfderiv_comp_apply x hd2 hv2 v
  have h3 := mfderiv_subtype_val_apply (I := (pullCarrier F hE hrange).model) ⊤
    (deckT F hE hrange x) (mfderiv (pullCarrier F hE hrange).model
      (pullCarrier F hE hrange).model (deckT F hE hrange) x v)
  have h4 := mfderiv_subtype_val_apply (I := (pullCarrier F hE hrange).model) ⊤ x v
  exact ((h3.symm.trans h1.symm).trans h2).trans
    (congrArg (mfderiv (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model
      (deckP F hE hrange) x.val) h4)

variable {F hE hrange} in
def twistCoord (τ : FibreCoordinate (pullFibration F hE hrange) ⊤) :
    FibreCoordinate (pullFibration F hE hrange) ⊤ :=
  FibreCoordinate.ofAngle ⊤ (fun x => (τ.angle (deckT F hE hrange x))⁻¹)
    (fun q => deckT F hE hrange (τ.symmFn (annDeck q.1.val) q.2⁻¹))
    (by
      intro x _
      refine (((contMDiff_inv (𝓡 1) ∞).contMDiffAt).comp x ?_).contMDiffWithinAt
      refine ContMDiffAt.comp (g := τ.angle) x ?_ ((contMDiff_deckT F hE hrange) x)
      exact (τ.contMDiffOn_angle _ trivial).contMDiffAt (by simp))
    (by
      intro q
      refine ((contMDiff_deckT F hE hrange) _).comp q ?_
      have hp : ContMDiff ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
          ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)) ∞
          (fun q : (⊤ : TopologicalSpace.Opens annulusSurface.{u}.Carrier) × Circle =>
            (annDeck q.1.val, q.2⁻¹)) :=
        (contMDiff_annDeck.comp (contMDiff_subtype_val.comp contMDiff_fst)).prodMk
          ((contMDiff_inv (𝓡 1) ∞).comp contMDiff_snd)
      exact ((τ.contMDiffOn_symmFn _ ⟨trivial, trivial⟩).contMDiffAt (by simp)).comp q (hp q))
    (fun q => by
      change annDeck ((pullFibration F hE hrange).projection
        (τ.symmFn (annDeck q.1.val) q.2⁻¹)) = q.1.val
      exact (congrArg annDeck (τ.projection_symmFn (annDeck q.1.val) q.2⁻¹)).trans
        (annDeck_annDeck _))
    (fun q => by
      rw [deckT_deckT, τ.angle_symmFn trivial, inv_inv])
    (fun x _ => by
      change deckT F hE hrange (τ.symmFn (annDeck ((pullFibration F hE hrange).projection x))
        (τ.angle (deckT F hE hrange x))⁻¹⁻¹) = x
      rw [inv_inv, ← projection_deckT, τ.symmFn_angle _ trivial, deckT_deckT])

theorem twistCoord_angle (τ : FibreCoordinate (pullFibration F hE hrange) ⊤)
    (x : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier)) :
    (twistCoord τ).angle x = (τ.angle (deckT F hE hrange x))⁻¹ :=
  FibreCoordinate.angle_ofAngle _ _ _ _ _ _ _ _ x trivial

theorem twistCoord_symmFn (τ : FibreCoordinate (pullFibration F hE hrange) ⊤)
    (w : annulusSurface.{u}.Carrier) (v : Circle) :
    (twistCoord τ).symmFn w v = deckT F hE hrange (τ.symmFn (annDeck w) v⁻¹) := by
  rw [FibreCoordinate.symmFn_of_mem _ (TopologicalSpace.Opens.mem_top w)]
  rfl

def deckProd : (annulusSurface.{u}.Carrier × Circle) ≃ₘ⟮
    (SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1),
    (SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)⟯
    (annulusSurface.{u}.Carrier × Circle) :=
  annDeckDiffeo.prodCongr circleInvDiffeo

theorem deckProd_preservesOrientation :
    deckProd.{u}.preservesOrientation
      (DifferentialGeometry.productOrientation (SurfaceModel.model annulusSurface.{u}.kind)
        (𝓡 1) (by norm_num) le_rfl annOrientation circleOrientation)
      (DifferentialGeometry.productOrientation (SurfaceModel.model annulusSurface.{u}.kind)
        (𝓡 1) (by norm_num) le_rfl annOrientation circleOrientation) := by
  have h := Diffeomorph.prodCongr_preservesOrientation (by norm_num) le_rfl annDeckDiffeo.{u}
    circleInvDiffeo annDeckDiffeo_reverses circleInvDiffeo_preservesOrientation
  rw [productOrientation_opposite_opposite] at h
  exact h

theorem twistCoord_isPositive (τ : FibreCoordinate (pullFibration F hE hrange) ⊤)
    (hτ : τ.IsPositive (annOrientation.restrictOpen ⊤)) :
    (twistCoord τ).IsPositive (annOrientation.restrictOpen ⊤) := by
  refine FibreCoordinate.isPositive_of_ambient annOrientation (twistCoord τ) fun x _ L hL => ?_
  let y := deckT F hE hrange x
  let A₁ := (pullDiff F hE hrange x.val).trans
    (pullDiff F hE hrange (deckP F hE hrange x.val)).symm
  let y' : TopologicalSpace.Opens.comap (pullFibration F hE hrange).projection ⊤ := ⟨y, trivial⟩
  let L₁ := (τ.toDiffeo.mfderivToContinuousLinearEquiv (by simp) y').toLinearEquiv
  have hL₁ : ∀ v, L₁ v = mfderiv (pullCarrier F hE hrange).model
      ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
      (fun z => ((pullFibration F hE hrange).projection z, τ.angle z)) y v :=
    fun v => τ.mfderiv_toDiffeo_apply y' v
  let p := ((pullFibration F hE hrange).projection y, τ.angle y)
  let A₃ := (deckProd.{u}.mfderivToContinuousLinearEquiv (by simp) p).toLinearEquiv
  have hg₁ : MDifferentiableAt (pullCarrier F hE hrange).model
      ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
      (fun z => ((pullFibration F hE hrange).projection z, τ.angle z)) y :=
    ((pullFibration F hE hrange).smooth.mdifferentiableAt (by simp)).prodMk
      (((τ.contMDiffOn_angle _ trivial).contMDiffAt (by simp)).mdifferentiableAt (by simp))
  have hK : MDifferentiableAt ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
      ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)) deckProd.{u} p :=
    (deckProd.{u}.contMDiff.mdifferentiable (by simp)) p
  have hdT : MDifferentiableAt (pullCarrier F hE hrange).model (pullCarrier F hE hrange).model
      (deckT F hE hrange) x := ((contMDiff_deckT F hE hrange).mdifferentiable (by simp)) x
  have hcomp := hK.hasMFDerivAt.comp x (hg₁.hasMFDerivAt.comp x hdT.hasMFDerivAt)
  have hev : (fun z => ((pullFibration F hE hrange).projection z, (twistCoord τ).angle z)) =ᶠ[𝓝 x]
      (deckProd.{u} ∘ ((fun z => ((pullFibration F hE hrange).projection z, τ.angle z)) ∘
        deckT F hE hrange)) :=
    Filter.Eventually.of_forall fun z => by
      change ((pullFibration F hE hrange).projection z, (twistCoord τ).angle z) =
        (annDeck (annDeck ((pullFibration F hE hrange).projection z)),
          (τ.angle (deckT F hE hrange z))⁻¹)
      rw [twistCoord_angle, annDeck_annDeck]
  have hm := (hcomp.congr_of_eventuallyEq hev).mfderiv
  have hLeq : L = A₁.trans (L₁.trans A₃) := by
    apply LinearEquiv.ext
    intro v
    rw [hL, hm]
    change A₃ (mfderiv _ _ _ y (mfderiv _ _ (deckT F hE hrange) x v)) = A₃ (L₁ (A₁ v))
    refine congrArg A₃ ?_
    have h1 := (mfderiv_deckT_apply F hE hrange x v).trans
      (mfderiv_deckP_apply F hE hrange x.val v)
    exact (DFunLike.congr_arg (mfderiv (pullCarrier F hE hrange).model
      ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
      (fun z => ((pullFibration F hE hrange).projection z, τ.angle z)) y) h1).trans
        (hL₁ (A₁ v)).symm
  subst hLeq
  have e1 : Orientation.map (Fin 3) A₁
      (((pullCarrier F hE hrange).orientation.restrictOpen ⊤).orientation x) =
      ((pullCarrier F hE hrange).orientation.restrictOpen ⊤).orientation y :=
    orientation_map_deckP F hE hrange x.val
  have e2 := FibreCoordinate.orientation_map_ambient (o := annOrientation) τ hτ y trivial L₁ hL₁
  have hp : deckProd.{u} p =
      ((pullFibration F hE hrange).projection x, (twistCoord τ).angle x) := by
    rw [twistCoord_angle]
    exact Prod.ext (annDeck_annDeck _) rfl
  have e3 := deckProd_preservesOrientation.{u} p
  rw [hp] at e3
  refine (orientation_map_trans_fin A₁ (L₁.trans A₃) _).trans ?_
  refine (orientation_map_trans_fin L₁ A₃ _).trans ?_
  exact (congrArg (Orientation.map (Fin 3) A₃) ((congrArg (Orientation.map (Fin 3) L₁) e1).trans
    e2)).trans e3

instance connectedSpace_top_ann :
    ConnectedSpace (⊤ : TopologicalSpace.Opens annulusSurface.{u}.Carrier) :=
  isConnected_iff_connectedSpace.mp (by
    rw [TopologicalSpace.Opens.coe_top]
    exact isConnected_univ)

theorem exists_positive_pullCoord :
    ∃ τ : FibreCoordinate (pullFibration F hE hrange) ⊤,
      τ.IsPositive (annOrientation.restrictOpen ⊤) := by
  obtain ⟨Φ, hΦ⟩ := exists_pullProduct F hE hrange
  let τ₀ : FibreCoordinate (pullFibration F hE hrange) ⊤ :=
    FibreCoordinate.ofAngle ⊤ (fun x => (Φ x).2) (fun q => Φ.symm (q.1.val, q.2))
      (contMDiff_snd.comp Φ.contMDiff).contMDiffOn
      (Φ.symm.contMDiff.comp ((contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd))
      (fun q => by
        have h := hΦ (Φ.symm (q.1.val, q.2))
        rw [Diffeomorph.apply_symm_apply] at h
        exact h.symm)
      (fun q => by
        rw [Diffeomorph.apply_symm_apply])
      (fun x _ => by
        change Φ.symm ((pullFibration F hE hrange).projection x, (Φ x).2) = x
        rw [← hΦ x, Prod.mk.eta, Diffeomorph.symm_apply_apply])
  obtain ⟨τ, hτ, -⟩ := τ₀.exists_isPositive (annOrientation.restrictOpen ⊤)
  exact ⟨τ, hτ⟩

theorem exists_upperCoord (τ : FibreCoordinate (pullFibration F hE hrange) ⊤)
    (hτ : τ.IsPositive (annOrientation.restrictOpen ⊤)) :
    ∃ τu : FibreCoordinate (pullFibration F hE hrange) (rightOpen ⊔ leftOpen),
      (∀ w v, seamCutoff w = 0 → w ∈ rightOpen → τu.symmFn w v = τ.symmFn w v) ∧
      (∀ w v, seamCutoff w = 1 → w ∈ leftOpen → τu.symmFn w v = (twistCoord τ).symmFn w v) := by
  obtain ⟨τu, -, -, -, h0, h1⟩ := FibreCoordinate.glue (τ.restrict le_top)
    ((twistCoord τ).restrict le_top) annOrientation (hτ.restrict le_top)
    ((twistCoord_isPositive F hE hrange τ hτ).restrict le_top) seamCutoff contMDiff_seamCutoff
    seamCutoff_mem seamCutoff_eventually_zero seamCutoff_eventually_one exists_seamCover
  refine ⟨τu, fun w v hw hr => ?_, fun w v hw hl => ?_⟩
  · have hm : w ∈ rightOpen ⊔ leftOpen := TopologicalSpace.Opens.mem_sup.mpr (Or.inl hr)
    rw [FibreCoordinate.symmFn_of_mem _ hm, h0 (⟨w, hm⟩, v) hw hr,
      FibreCoordinate.symmFn_of_mem _ hr, FibreCoordinate.symm_restrict,
      FibreCoordinate.symmFn_of_mem _ (TopologicalSpace.Opens.mem_top w)]
  · have hm : w ∈ rightOpen ⊔ leftOpen := TopologicalSpace.Opens.mem_sup.mpr (Or.inr hl)
    rw [FibreCoordinate.symmFn_of_mem _ hm, h1 (⟨w, hm⟩, v) hw hl,
      FibreCoordinate.symmFn_of_mem _ hl, FibreCoordinate.symm_restrict,
      FibreCoordinate.symmFn_of_mem _ (TopologicalSpace.Opens.mem_top w)]

end MobiusCover

end GC.Seifert
