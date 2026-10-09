import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelSlice
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CrossSpaceTransition
import DifferentialGeometry.Geometry.Metric.Pullback.TransportedCarrier
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chart

/-!
# Curvature transfer across different model spaces (lane CMS3-CARRIER, group G4a)

LFR47 adaptation (review §13, disposition D9): the tree's `TransportedCarrier.metric` already allows
the carrier `X` to have a model `EX` different from the model `E` of `N`, but its curvature theorem
(`TransportedCarrier.metric_sectionalCurvature`) is stated for the same model only. For the soul
carrier `X = TotalSpace F V` the model is `EB × F`. Here, as a SEPARATE lemma:

* `sectionalCurvature_eq_of_diffeomorph_cross`: for a `C³` diffeomorphism `f : X → N` between
  manifolds with possibly different (finite-dimensional, boundaryless) models and metrics with
  `h = f^* g`, `sec_h (p; v, w) = sec_g (f p; df v, df w)`. Proof: read both sectional curvatures in
  extended charts (`sectionalCurvature_eq_coefficientSectional`) and apply F7-LFR11b's
  `coefficientSectional_transition_cross` to the chart transition `φ ∘ f ∘ φ_X⁻¹ : EX → E`;
* `TransportedCarrier.metric_sectionalCurvature_cross` and `..._nonneg_cross`: the carrier version,
  so `sec ≥ 0` survives the carrier change whatever the model of the carrier.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Topology (TransportedCarrier)

variable {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX} [IX.Boundaryless]
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X] [IsManifold IX ∞ X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- **Sectional curvature is natural under `C³` diffeomorphisms between different models.** -/
theorem sectionalCurvature_eq_of_diffeomorph_cross {mX n : ℕ∞ω}
    (h : ContMDiffRiemannianMetric IX mX EX (TangentSpace IX : X → Type _))
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _))
    (hm : (2 : ℕ∞ω) ≤ mX) (hn : (2 : ℕ∞ω) ≤ n) (f : X ≃ₘ^3⟮IX, I⟯ N)
    (hmetric : ∀ (q : X) (v w : TangentSpace IX q),
      h.inner q v w = g.inner (f q) (mfderiv IX I f q v) (mfderiv IX I f q w))
    (p : X) (v w : TangentSpace IX p) :
    h.sectionalCurvature p v w =
      g.sectionalCurvature (f p) (mfderiv IX I f p v) (mfderiv IX I f p w) := by
  have h30 : (3 : ℕ∞ω) ≠ 0 := by norm_num
  set φX := DifferentialGeometry.PartialDiffeomorph.extChartAt IX 3 p with hφX
  set φ := DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 (f p) with hφ
  have hp : p ∈ φX.source := mem_extChartAt_source p
  have hfp : f p ∈ φ.source := mem_extChartAt_source (f p)
  rw [h.sectionalCurvature_eq_coefficientSectional hm φX hp,
    g.sectionalCurvature_eq_coefficientSectional hn φ hfp]
  have hφXl : ∀ q ∈ φX.source, φX.symm (φX q) = q := fun q hq => φX.toPartialEquiv.left_inv hq
  set U : Set EX := φX.target ∩ φX.symm ⁻¹' (f ⁻¹' φ.source) with hUdef
  have hUo : IsOpen U :=
    φX.symm.contMDiffOn.continuousOn.isOpen_inter_preimage φX.open_target
      (φ.open_source.preimage f.continuous)
  have hpU : φX p ∈ U := ⟨φX.toPartialEquiv.map_source hp, by
    change f (φX.symm (φX p)) ∈ φ.source
    rw [hφXl p hp]; exact hfp⟩
  set Φ : EX → E := fun y => φ (f (φX.symm y)) with hΦdef
  have hΦs : ContMDiffOn 𝓘(ℝ, EX) 𝓘(ℝ, E) 3 Φ U := by
    have h1 : ContMDiffOn 𝓘(ℝ, EX) I 3 (fun y => f (φX.symm y)) U :=
      f.contMDiff.comp_contMDiffOn (φX.symm.contMDiffOn.mono inter_subset_left)
    exact φ.contMDiffOn.comp h1 (fun y hy => hy.2)
  have hΦd : ContDiffOn ℝ 3 Φ U := contMDiffOn_iff_contDiffOn.mp hΦs
  have hchainL : ∀ y ∈ U, (fderiv ℝ Φ y : EX →L[ℝ] E) =
      ((mfderiv I 𝓘(ℝ, E) φ (f (φX.symm y))).comp ((mfderiv IX I f (φX.symm y)).comp
        (mfderiv 𝓘(ℝ, EX) IX φX.symm y)) : EX →L[ℝ] E) := by
    intro y hy
    have hψd : MDifferentiableAt 𝓘(ℝ, EX) IX φX.symm y := φX.symm.mdifferentiableAt h30 hy.1
    have hfd : MDifferentiableAt IX I f (φX.symm y) := f.mdifferentiable h30 _
    have hcd : MDifferentiableAt I 𝓘(ℝ, E) φ (f (φX.symm y)) := φ.mdifferentiableAt h30 hy.2
    have h1 := mfderiv_comp y hfd hψd
    have h2 := mfderiv_comp y hcd (hfd.comp y hψd)
    have h4 : fderiv ℝ Φ y = mfderiv 𝓘(ℝ, EX) 𝓘(ℝ, E) (φ ∘ (f ∘ φX.symm)) y := by
      rw [mfderiv_eq_fderiv]
      rfl
    rw [h4, h2, h1]
    rfl
  have hpull : ∀ y ∈ U, ∀ a a' : EX,
      (h.inner (φX.symm y) : EX →L[ℝ] EX →L[ℝ] ℝ).bilinearComp
        (mfderiv 𝓘(ℝ, EX) IX φX.symm y : EX →L[ℝ] EX)
        (mfderiv 𝓘(ℝ, EX) IX φX.symm y : EX →L[ℝ] EX) a a' =
      sliceCoeffFinite g φ (Φ y) (fderiv ℝ Φ y a) (fderiv ℝ Φ y a') := by
    intro y hy a a'
    have e1 := hmetric (φX.symm y) (mfderiv 𝓘(ℝ, EX) IX φX.symm y a)
      (mfderiv 𝓘(ℝ, EX) IX φX.symm y a')
    have e2 := inner_eq_sliceCoeffFinite h30 g (c := φ) (x := f (φX.symm y)) hy.2
      (mfderiv IX I f (φX.symm y) (mfderiv 𝓘(ℝ, EX) IX φX.symm y a))
      (mfderiv IX I f (φX.symm y) (mfderiv 𝓘(ℝ, EX) IX φX.symm y a'))
    have ha := congrArg (fun L : EX →L[ℝ] E => L a) (hchainL y hy)
    have ha' := congrArg (fun L : EX →L[ℝ] E => L a') (hchainL y hy)
    exact e1.trans (e2.trans (congrArg₂ (fun u u' => sliceCoeffFinite g φ (Φ y) u u') ha.symm
      ha'.symm))
  have hinv : ∀ y ∈ U, (fderiv ℝ Φ y).IsInvertible := by
    intro y hy
    rw [hchainL y hy]
    exact ((φ.isLocalDiffeomorphAt I 𝓘(ℝ, E) 3 hy.2).isInvertible_mfderiv h30).comp
      (((f.isLocalDiffeomorph (φX.symm y)).isInvertible_mfderiv h30).comp
        ((φX.symm.isLocalDiffeomorphAt 𝓘(ℝ, EX) IX 3 hy.1).isInvertible_mfderiv h30))
  have hΦW : MapsTo Φ U φ.target := fun y hy => φ.toPartialEquiv.map_source hy.2
  have hcross := DifferentialGeometry.Analysis.coefficientSectional_transition_cross hUo
    φ.open_target (contDiffOn_sliceCoeffFinite g hn (by norm_num) φ)
    (fun z _ u u' => sliceCoeffFinite_symm g φ z u u')
    (fun z hz => isCoercive_sliceCoeffFinite h30 g hz) hΦd hΦW hinv hpull hpU
    (mfderiv IX 𝓘(ℝ, EX) φX p v) (mfderiv IX 𝓘(ℝ, EX) φX p w)
  refine hcross.trans ?_
  have hpt : Φ (φX p) = φ (f p) := by
    change φ (f (φX.symm (φX p))) = φ (f p)
    rw [hφXl p hp]
  have key : ∀ q, φX.symm (φX p) = q → ∀ a : TangentSpace IX p, q = p →
      fderiv ℝ Φ (φX p) (mfderiv IX 𝓘(ℝ, EX) φX p a) =
        mfderiv I 𝓘(ℝ, E) φ (f q) (mfderiv IX I f q a) := by
    rintro q rfl a -
    have hid : mfderiv 𝓘(ℝ, EX) IX φX.symm (φX p) (mfderiv IX 𝓘(ℝ, EX) φX p a) = a :=
      mfderiv_symm_apply_mfderiv_ofOrder h30 hp a
    refine (congrArg (fun L : EX →L[ℝ] E => L (mfderiv IX 𝓘(ℝ, EX) φX p a))
      (hchainL (φX p) hpU)).trans ?_
    exact congrArg (fun t => mfderiv I 𝓘(ℝ, E) φ (f (φX.symm (φX p)))
      (mfderiv IX I f (φX.symm (φX p)) t)) hid
  rw [hpt, key p (hφXl p hp) v rfl, key p (hφXl p hp) w rfl]
  rfl

variable {r : ℕ∞}

/-- **LFR47 curvature across models**: the sectional curvature of the transported metric is the
sectional curvature of `g` on the corresponding plane, whatever the model of the carrier
(`3 ≤ r`, both metrics of order at least two). -/
theorem TransportedCarrier.metric_sectionalCurvature_cross (F : X ≃ₘ^r⟮IX, I⟯ N)
    {m n : WithTop ℕ∞} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _))
    (hmn : m ≤ n) (hmr : m + 1 ≤ r) (hr : 3 ≤ r) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (y : TransportedCarrier F.toHomeomorph) (v w : TangentSpace IX y) :
    (TransportedCarrier.metric F g hmn hmr).sectionalCurvature y v w =
      g.sectionalCurvature y.point (mfderiv IX I (TransportedCarrier.identity F) y v)
        (mfderiv IX I (TransportedCarrier.identity F) y w) := by
  let f3 : TransportedCarrier F.toHomeomorph ≃ₘ^3⟮IX, I⟯ N :=
    { toEquiv := (TransportedCarrier.identity F).toEquiv
      contMDiff_toFun :=
        (TransportedCarrier.identity F).contMDiff.of_le (WithTop.coe_le_coe.mpr hr)
      contMDiff_invFun :=
        (TransportedCarrier.identity F).symm.contMDiff.of_le (WithTop.coe_le_coe.mpr hr) }
  exact sectionalCurvature_eq_of_diffeomorph_cross (TransportedCarrier.metric F g hmn hmr) g hm hn
    f3 (fun _ _ _ => rfl) y v w

/-- **`sec ≥ 0` survives the carrier change across models.** -/
theorem TransportedCarrier.metric_sectionalCurvature_nonneg_cross (F : X ≃ₘ^r⟮IX, I⟯ N)
    {m n : WithTop ℕ∞} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _))
    (hmn : m ≤ n) (hmr : m + 1 ≤ r) (hr : 3 ≤ r) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hsec : ∀ (x : N) (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w)
    (y : TransportedCarrier F.toHomeomorph) (v w : TangentSpace IX y) :
    0 ≤ (TransportedCarrier.metric F g hmn hmr).sectionalCurvature y v w := by
  rw [TransportedCarrier.metric_sectionalCurvature_cross F g hmn hmr hr hm hn]
  exact hsec _ _ _

end DifferentialGeometry.Geometry.FiniteSoul
