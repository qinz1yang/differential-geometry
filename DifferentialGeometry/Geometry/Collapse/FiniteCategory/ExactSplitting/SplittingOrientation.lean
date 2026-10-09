import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingRow
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.ProductDistance
import DifferentialGeometry.Topology.Manifold.AmbientSplitOrientation
import DifferentialGeometry.Topology.Manifold.LinearModelChange
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.OriginalManifold
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteOrder

/-!
# LFR11, orientation clause, in general rank

Chapter 13, row LFR11 (`thm:collapse-exact-splitting-regularity`), last two sentences: "An
orientation of `N`, together with the ordered Euclidean factor, orients `Z`. Compatible smooth
structures may be chosen as in LFR01." The factor `Z = t⁻¹(0)` of an exact splitting
`e : M ≃ᵢ ℓ²(F × Y)` only has the `C^{K+1}` atlas of X96, so its orientation lives on a compatible
smooth structure (a smooth carrier `φ : S → Z`):

* `splittingCarrierOrientation`: for EVERY smooth manifold `S` and `C¹` immersion `φ : S → Z`
  with `dim S = dim Z` (encoded by the index equivalence `σ`), an orientation `oM` of `M` and an
  ordered basis `bF` of `F` orient `S`; `splittingCarrierOrientation_eq_iff`: a basis `b` of
  `T_s S` is positive iff the ordered frame `(X_{bF a})_a, (dι dφ (b i))_i` is positive for `oM`,
  where `X = splittingFrame` is the parallel frame with `dt (X_u) = u`;
* `splittingCarrierFrame_eq_mfderiv_product`: that frame is `DΨ_{(0, φ s)} ∘ (id × dφ_s)` for the
  actual product map `Ψ`, i.e. the orientation is the one making `Ψ` orientation-compatible with
  the product orientation of `F × S` on the zero slice;
* `exists_oriented_smoothCarrier_splittingFactor`: a smooth carrier exists, modelled on any `V`
  with a linear identification `P ≃L V`, `C^{K+1}`-diffeomorphic to `Z`, and oriented as above.

General rank `j = dim F`, general dimension; the rank-one 3-dimensional case was
`surfaceFactor_smoothCarrier_oriented`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold Function Module
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Manifold

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

universe u

variable {E H : Type*} {M : Type u} {F Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y] [NeZero (Module.finrank ℝ E)] {r : ℕ∞}

local notation "P" => Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
local notation "IZ" => 𝓘(ℝ, P)
local notation "IP" => ModelWithCorners.prod (𝓘(ℝ, F)) IZ

variable {V HS S : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace HS] {IS : ModelWithCorners ℝ V HS} [TopologicalSpace S] [ChartedSpace HS S]
  [IsManifold IS ∞ S] {ιF : Type*}

omit [FiniteDimensional ℝ V] [IsManifold IS ∞ S] in
/-- The composite `S → Z → M` of a carrier map is `C¹`. -/
theorem contMDiff_val_comp_carrier
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (φ : S → {x : M // (e x).fst = 0})
    (hφ : letI := splittingFactorChartedSpace g hr hnorm e; ContMDiff IS IZ 1 φ) :
    ContMDiff IS I 1 (Subtype.val ∘ φ) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  have h1 : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) + 2 := le_add_left (by norm_num)
  exact ((contMDiff_splittingFactor_val g hr hnorm e).of_le h1).comp hφ

omit [FiniteDimensional ℝ V] [IsManifold IS ∞ S] in
/-- The columns of the splitting frame along a carrier map are continuous. -/
theorem continuous_splittingFrame_carrier
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (φ : S → {x : M // (e x).fst = 0})
    (hφ : letI := splittingFactorChartedSpace g hr hnorm e; ContMDiff IS IZ 1 φ) (a : F) :
    Continuous (fun s => (⟨(Subtype.val ∘ φ) s, splittingFrame g e (φ s).val a⟩ :
      TangentBundle I M)) :=
  (contMDiff_splittingFrame_apply g hr hnorm e).continuous.comp
    (continuous_const.prodMk (contMDiff_val_comp_carrier g hr hnorm e φ hφ).continuous)

omit [FiniteDimensional ℝ V] [IsManifold IS ∞ S] in
/-- The derivative of `S → Z → M` is `dι ∘ dφ`. -/
theorem mfderiv_val_comp_carrier
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (φ : S → {x : M // (e x).fst = 0})
    (hφ : letI := splittingFactorChartedSpace g hr hnorm e; ContMDiff IS IZ 1 φ) (s : S)
    (v : TangentSpace IS s) :
    letI := splittingFactorChartedSpace g hr hnorm e
    mfderiv IS I (Subtype.val ∘ φ) s v =
      mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) (φ s) (mfderiv IS IZ φ s v) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  have hval := contMDiff_splittingFactor_val g hr hnorm e
  have h := mfderiv_comp s (hval.mdifferentiableAt (by simp) (x := φ s))
    (hφ.mdifferentiableAt one_ne_zero (x := s))
  exact congrArg (fun A => A v) h

omit [IsManifold IS ∞ S] in
/-- **The frame `(u, v) ↦ X_u + dι dφ v` is bijective** for a carrier immersion of the right
dimension. -/
theorem bijective_splittingFrame_carrier
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (bF : Basis ιF ℝ F)
    (σ : ιF ⊕ Fin (finrank ℝ V) ≃ Fin (finrank ℝ E)) (φ : S → {x : M // (e x).fst = 0})
    (hφ : letI := splittingFactorChartedSpace g hr hnorm e; ContMDiff IS IZ 1 φ)
    (hinj : letI := splittingFactorChartedSpace g hr hnorm e;
      ∀ s, Injective (mfderiv IS IZ φ s)) (s : S) :
    Bijective (ambientSplitFrame I IS (Subtype.val ∘ φ) (fun s => splittingFrame g e (φ s).val) s) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  obtain ⟨-, -, -, hinjι, hrange, -⟩ := exactSplitting_regularity g hr hnorm e
  have hfin : Module.finrank ℝ (F × V) = Module.finrank ℝ E := by
    classical
    let _ : Fintype ιF := by
      let _ : Fintype (ιF ⊕ Fin (finrank ℝ V)) := Fintype.ofEquiv _ σ.symm
      exact Fintype.ofInjective (Sum.inl : ιF → ιF ⊕ Fin (finrank ℝ V)) Sum.inl_injective
    rw [Module.finrank_prod, Module.finrank_eq_card_basis bF, ← Module.finrank_fin_fun ℝ
      (n := finrank ℝ V), ← Module.finrank_fin_fun ℝ (n := finrank ℝ E)]
    simp only [Module.finrank_fin_fun]
    have h := Fintype.card_congr σ
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    exact h
  have hinj' : Injective (ambientSplitFrame I IS (Subtype.val ∘ φ)
      (fun s => splittingFrame g e (φ s).val) s) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    rw [ambientSplitFrame_apply] at hw
    let dt : E →L[ℝ] F := mvfderiv I (fun y => (e y).fst) (φ s).val
    have hdtX : dt (splittingFrame g e (φ s).val w.1 : E) = w.1 :=
      mvfderiv_splittingFrame g hr hnorm e (φ s).val w.1
    have hD := mfderiv_val_comp_carrier g hr hnorm e φ hφ s w.2
    have hdtD : dt (mfderiv IS I (Subtype.val ∘ φ) s w.2 : E) = 0 := by
      have hmem : mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) (φ s)
          (mfderiv IS IZ φ s w.2) ∈ LinearMap.range
            (mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) (φ s)).toLinearMap :=
        ⟨_, rfl⟩
      rw [hrange (φ s)] at hmem
      exact (congrArg dt hD).trans hmem
    let X0 : E := splittingFrame g e (φ s).val w.1
    let D0 : E := mfderiv IS I (Subtype.val ∘ φ) s w.2
    change X0 + D0 = 0 at hw
    have h0 : dt (X0 + D0) = 0 := (congrArg dt hw).trans dt.map_zero
    rw [map_add, hdtX, hdtD, add_zero] at h0
    have ha : D0 = 0 := by
      have hX : X0 = 0 := by
        change (splittingFrame g e (φ s).val w.1 : E) = 0
        rw [h0, map_zero]
      rw [hX, zero_add] at hw
      exact hw
    have h3 : mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) (φ s)
        (mfderiv IS IZ φ s w.2) =
        mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) (φ s) 0 :=
      hD.symm.trans (ha.trans (map_zero _).symm)
    have h4 : mfderiv IS IZ φ s w.2 = 0 := hinjι (φ s) h3
    have h5 : w.2 = 0 := hinj s (h4.trans (map_zero _).symm)
    exact Prod.ext h0 h5
  exact ⟨hinj', (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj'⟩

/-- **LFR11, orientation clause (general rank), on a smooth carrier.** An orientation of `M` and
the ordered Euclidean factor `bF` orient every smooth carrier `φ : S → Z` of the zero factor. -/
def splittingCarrierOrientation
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (bF : Basis ιF ℝ F)
    (σ : ιF ⊕ Fin (finrank ℝ V) ≃ Fin (finrank ℝ E)) (φ : S → {x : M // (e x).fst = 0})
    (hφ : letI := splittingFactorChartedSpace g hr hnorm e; ContMDiff IS IZ 1 φ)
    (hinj : letI := splittingFactorChartedSpace g hr hnorm e;
      ∀ s, Injective (mfderiv IS IZ φ s))
    (oM : SmoothOrientation I M) : SmoothOrientation IS S :=
  ambientSplitSmoothOrientation I IS bF σ (Subtype.val ∘ φ)
    (contMDiff_val_comp_carrier g hr hnorm e φ hφ) (fun s => splittingFrame g e (φ s).val)
    (continuous_splittingFrame_carrier g hr hnorm e φ hφ)
    (bijective_splittingFrame_carrier g hr hnorm e bF σ φ hφ hinj) oM

/-- **Characterisation.** A basis `b` of `T_s S` is positive for `splittingCarrierOrientation`
iff the ordered frame `(X_{bF a})_a, (dι dφ (b i))_i` is positive for `oM`. -/
theorem splittingCarrierOrientation_eq_iff
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    {hr : 2 ≤ r}
    {hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))}
    {e : M ≃ᵢ WithLp 2 (F × Y)} {bF : Basis ιF ℝ F}
    {σ : ιF ⊕ Fin (finrank ℝ V) ≃ Fin (finrank ℝ E)} {φ : S → {x : M // (e x).fst = 0}}
    {hφ : letI := splittingFactorChartedSpace g hr hnorm e; ContMDiff IS IZ 1 φ}
    {hinj : letI := splittingFactorChartedSpace g hr hnorm e;
      ∀ s, Injective (mfderiv IS IZ φ s)}
    {oM : SmoothOrientation I M} {s : S} {b : Basis (Fin (finrank ℝ V)) ℝ V} :
    b.orientation = (splittingCarrierOrientation g hr hnorm e bF σ φ hφ hinj oM).val s ↔
      (splitFrameBasis bF b σ (ambientSplitFrameEquiv I IS (Subtype.val ∘ φ)
        (fun s => splittingFrame g e (φ s).val)
        (bijective_splittingFrame_carrier g hr hnorm e bF σ φ hφ hinj) s).toLinearEquiv).orientation =
        oM.val (φ s).val :=
  ambientSplitSmoothOrientation_eq_iff _ _

omit [IsManifold IS ∞ S] in
/-- The vectors of the ordered frame: first the parallel fields `X_{bF a}`, then `dι dφ (b i)`. -/
theorem splittingCarrierFrame_apply
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (bF : Basis ιF ℝ F)
    (σ : ιF ⊕ Fin (finrank ℝ V) ≃ Fin (finrank ℝ E)) (φ : S → {x : M // (e x).fst = 0})
    (hφ : letI := splittingFactorChartedSpace g hr hnorm e; ContMDiff IS IZ 1 φ)
    (hinj : letI := splittingFactorChartedSpace g hr hnorm e;
      ∀ s, Injective (mfderiv IS IZ φ s))
    (s : S) (b : Basis (Fin (finrank ℝ V)) ℝ V) :
    letI := splittingFactorChartedSpace g hr hnorm e
    (∀ a, splitFrameBasis bF b σ (ambientSplitFrameEquiv I IS (Subtype.val ∘ φ)
        (fun s => splittingFrame g e (φ s).val)
        (bijective_splittingFrame_carrier g hr hnorm e bF σ φ hφ hinj) s).toLinearEquiv
          (σ (Sum.inl a)) = splittingFrame g e (φ s).val (bF a)) ∧
    (∀ i, splitFrameBasis bF b σ (ambientSplitFrameEquiv I IS (Subtype.val ∘ φ)
        (fun s => splittingFrame g e (φ s).val)
        (bijective_splittingFrame_carrier g hr hnorm e bF σ φ hφ hinj) s).toLinearEquiv
          (σ (Sum.inr i)) =
        mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) (φ s)
          (mfderiv IS IZ φ s (b i))) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  refine ⟨fun a => ?_, fun i => ?_⟩
  · rw [splitFrameBasis_apply_inl]
    exact ambientSplitFrame_inl I IS (Subtype.val ∘ φ) (fun s => splittingFrame g e (φ s).val) s
      (bF a)
  · rw [splitFrameBasis_apply_inr]
    exact (ambientSplitFrame_inr I IS (Subtype.val ∘ φ) (fun s => splittingFrame g e (φ s).val) s
      (b i)).trans (mfderiv_val_comp_carrier g hr hnorm e φ hφ s (b i))

omit [FiniteDimensional ℝ V] [IsManifold IS ∞ S] in
/-- **Compatibility with the product orientation.** The ordered frame at `s` is the derivative of
the actual product map `Ψ` at `(0, φ s)` precomposed with `id × dφ_s`. -/
theorem splittingCarrierFrame_eq_mfderiv_product
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (φ : S → {x : M // (e x).fst = 0})
    (hφ : letI := splittingFactorChartedSpace g hr hnorm e; ContMDiff IS IZ 1 φ) (s : S) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ambientSplitFrame I IS (Subtype.val ∘ φ) (fun s => splittingFrame g e (φ s).val) s =
      (mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) ((0 : F), φ s) :
        (F × P) →L[ℝ] E).comp
        ((ContinuousLinearMap.id ℝ F).prodMap (mfderiv IS IZ φ s : V →L[ℝ] P)) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  refine ContinuousLinearMap.prod_ext_iff.mpr ⟨?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro u
    change ambientSplitFrame I IS (Subtype.val ∘ φ) (fun s => splittingFrame g e (φ s).val) s
        (u, 0) = mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) ((0 : F), φ s)
          ((u, mfderiv IS IZ φ s 0) : F × P)
    have e2 : ((u, mfderiv IS IZ φ s 0) : F × P) = ((u, 0) : F × P) :=
      Prod.ext rfl (map_zero (mfderiv IS IZ φ s))
    rw [ambientSplitFrame_inl, e2, mfderiv_splittingProductDiffeomorph_fst g hr hnorm e]
    exact congrArg (fun x => (splittingFrame g e x u : E))
      (splittingProductDiffeomorph_zero g hr hnorm e (φ s)).symm
  · apply ContinuousLinearMap.ext
    intro v
    change ambientSplitFrame I IS (Subtype.val ∘ φ) (fun s => splittingFrame g e (φ s).val) s
        (0, v) = mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) ((0 : F), φ s)
          (((0 : F), mfderiv IS IZ φ s v) : F × P)
    exact (ambientSplitFrame_inr I IS (Subtype.val ∘ φ) (fun s => splittingFrame g e (φ s).val) s
      v).trans ((mfderiv_val_comp_carrier g hr hnorm e φ hφ s v).trans
        (mfderiv_splittingProductDiffeomorph_zero g hr hnorm e (φ s)
          (mfderiv IS IZ φ s v)).symm)

private theorem natCast_add_two_eq (k : ℕ) : (((k : ℕ∞) : ℕ∞ω) + 2) = ((k + 2 : ℕ) : ℕ∞ω) := by
  push_cast
  rfl

private theorem natCast_add_one_eq (k : ℕ) : (((k : ℕ∞) : ℕ∞ω) + 1) = ((k + 1 : ℕ) : ℕ∞ω) := by
  push_cast
  rfl

/-- **LFR11, orientation clause (general rank): existence of an oriented compatible smooth
structure.** The zero factor `Z` has a smooth carrier `S`, modelled on any `V` linearly identified
with `P`, `C^{K+1}`-diffeomorphic to `Z` (`K = k + 1` the order of `g`), oriented by `oM` and the
ordered Euclidean factor `bF` as in `splittingCarrierOrientation_eq_iff`. -/
theorem exists_oriented_smoothCarrier_splittingFactor [SecondCountableTopology M] {k : ℕ}
    (g : ContMDiffRiemannianMetric I (((k : ℕ∞) : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (L : P ≃L[ℝ] V) (bF : Basis ιF ℝ F)
    (σ : ιF ⊕ Fin (finrank ℝ V) ≃ Fin (finrank ℝ E)) (oM : SmoothOrientation I M) :
    letI := splittingFactorChartedSpace g hk hnorm e
    letI := splittingFactor_isManifold_one g hk hnorm e
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace V S) (_ : IsManifold 𝓘(ℝ, V) ∞ S)
      (φ : S ≃ₜ {x : M // (e x).fst = 0}),
      ContMDiff 𝓘(ℝ, V) IZ ((k + 2 : ℕ) : ℕ∞ω) φ ∧
      ContMDiff IZ 𝓘(ℝ, V) ((k + 2 : ℕ) : ℕ∞ω) φ.symm ∧
      ∃ (hbij : ∀ s, Bijective (ambientSplitFrame I 𝓘(ℝ, V) (Subtype.val ∘ φ)
          (fun s => splittingFrame g e (φ s).val) s))
        (oS : SmoothOrientation 𝓘(ℝ, V) S),
        ∀ (s : S) (b : Basis (Fin (finrank ℝ V)) ℝ V), b.orientation = oS.val s ↔
          (splitFrameBasis bF b σ (ambientSplitFrameEquiv I 𝓘(ℝ, V) (Subtype.val ∘ φ)
            (fun s => splittingFrame g e (φ s).val) hbij s).toLinearEquiv).orientation =
            oM.val (φ s).val := by
  let _ := splittingFactorChartedSpace g hk hnorm e
  let _ := splittingFactor_isManifold_one g hk hnorm e
  let Z := {x : M // (e x).fst = 0}
  have hk2 : 2 ≤ k := by exact_mod_cast hk
  let _ : IsManifold IZ ((k + 2 : ℕ) : ℕ∞ω) Z :=
    natCast_add_two_eq k ▸ splittingFactor_isManifold g hk hnorm e
  let ZV := LinearModelChange Z L
  let _ : IsManifold 𝓘(ℝ, V) ((k + 2 : ℕ) : ℕ∞ω) ZV := LinearModelChange.isManifold L
  let φ₀ : Diffeomorph 𝓘(ℝ, V) IZ ZV Z ((k + 2 : ℕ) : ℕ∞ω) := LinearModelChange.diffeomorph L
  let h' : ContMDiffRiemannianMetric IZ ((k + 1 : ℕ) : ℕ∞ω) P (TangentSpace IZ : Z → Type _) :=
    { inducedMetric g hk hnorm e with
      contMDiff := natCast_add_one_eq k ▸ (inducedMetric g hk hnorm e).contMDiff }
  obtain ⟨hV, -⟩ := exists_finite_order_pullback_metric_of_diffeomorph (k + 1) (k + 2)
    (k + 1) le_rfl le_rfl h' φ₀
  let _ : LocallyCompactSpace ZV := ChartedSpace.locallyCompactSpace V ZV
  let _ : TopologicalSpace.MetrizableSpace ZV :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable ZV
  let _ : MetricSpace ZV := TopologicalSpace.metrizableSpaceMetric ZV
  obtain ⟨s, A, -, -, ⟨f, -, -⟩, -⟩ :=
    exists_smoothCarrier_metric_of_secondCountable (E := V) (X := ZV) (K := k + 1)
      (by omega) hV
  let Φ : Diffeomorph 𝓘(ℝ, V) IZ (SmoothCarrier A) Z ((k + 2 : ℕ) : ℕ∞ω) := f.trans φ₀
  have h1 : (1 : ℕ∞ω) ≤ ((k + 2 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 1 ≤ k + 2 by omega)
  have hφ : ContMDiff 𝓘(ℝ, V) IZ 1 Φ.toHomeomorph := Φ.contMDiff.of_le h1
  have hs0 : ((k + 2 : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
  have hinj : ∀ x, Injective (mfderiv 𝓘(ℝ, V) IZ Φ.toHomeomorph x) := fun x =>
    (Φ.mfderivToContinuousLinearEquiv hs0 x).injective
  exact ⟨SmoothCarrier A, inferInstance, inferInstance, inferInstance, Φ.toHomeomorph,
    Φ.contMDiff, Φ.symm.contMDiff,
    bijective_splittingFrame_carrier g hk hnorm e bF σ Φ.toHomeomorph hφ hinj,
    splittingCarrierOrientation g hk hnorm e bF σ Φ.toHomeomorph hφ hinj oM,
    fun _ _ => splittingCarrierOrientation_eq_iff⟩

end DifferentialGeometry.Geometry.ExactSplitting
