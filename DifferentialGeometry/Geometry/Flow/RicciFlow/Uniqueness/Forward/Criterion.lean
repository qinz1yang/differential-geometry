import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.Vanishing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Curvature.TimeDerivative

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [T2Space M]
variable [CompactSpace M] [I.Boundaryless]

section ChartFrame

variable (I) in
def chartFrame (x₀ : M) : Fin (Module.finrank Real E) → (y : M) → TangentSpace I y :=
  (trivializationAt E (TangentSpace I) x₀).localFrame (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)

variable (I) in
omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem chartFrame_isFrame (x₀ : M) :
    IsLocalFrameOn I E 1 (chartFrame I x₀) (trivializationAt E (TangentSpace I) x₀).baseSet :=
  (trivializationAt E (TangentSpace I) x₀).isLocalFrameOn_localFrame_baseSet I 1
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)

variable (I) in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem chartFrame_mem (x₀ : M) :
    x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
  FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀

end ChartFrame

section Speeds

def connSpeed (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Avec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y) :
    Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  fun t x => connectionDifferenceDot (I := I) g₁ g₂ (Avec t) t x

def rmSpeed (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Svec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
        TangentSpace I y) :
    Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x :=
  fun t x => rmDiffDot (I := I) g₁ g₂ (Svec t) t x

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
theorem connSpeed_hasDerivAt (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Avec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    {t : Real} {x : M}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hgamma : ∀ i j k : Fin (Module.finrank Real E),
      HasDerivAt
        (fun r : Real =>
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₁ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k -
            DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
              (metricCov (I := I) (g₂ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k)
        ((chartFrame_isFrame I x).coeff k x
          ((Avec t x (chartFrame I x j x)) (chartFrame I x i x))) t)
    (v : Fin 3 → TangentSpace I x) :
    HasDerivAt (fun r : Real => connectionDifferenceLowAt (I := I) (g₁ r) (g₂ r) x v)
      (connSpeed (I := I) g₁ g₂ Avec t x v) t :=
  connectionDifferenceLow_hasDerivAt_frame (I := I) g₁ g₂ (chartFrame I x) (chartFrame_isFrame I x)
    (trivializationAt E (TangentSpace I) x).open_baseSet (chartFrame_mem I x) (Avec t)
    hPDE₁ hgamma v

omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
theorem rmSpeed_hasDerivAt (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Svec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
        TangentSpace I y)
    {t : Real} {x : M}
    (hPDE₁ : ∀ X Y : TangentSpace I x,
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t)
    (hrm : ∀ X Y Z : TangentSpace I x,
      HasDerivAt (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) x X) Y) Z)
        (((Svec t x X) Y) Z) t)
    (v : Fin 4 → TangentSpace I x) :
    HasDerivAt (fun r : Real => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
      (rmSpeed (I := I) g₁ g₂ Svec t x v) t :=
  rmDiffLow_hasDerivAt (I := I) g₁ g₂ (Svec t) hPDE₁ hrm v

end Speeds

section PDEUpgrade

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem pde_hasDerivAt (g : Real → SmoothRiemannianMetric I M) {a b : Real}
    (hpde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Geometry.Curvature.ricciTensor (I := I) (g t) x v w) (Ici a) t)
    {t : Real} (ht : t ∈ Ioo a b) (x : M) (X Y : TangentSpace I x) :
    HasDerivAt (fun r : Real => (g r).inner x X Y)
      ((-2 : Real) * metricRicciAt (I := I) (g t) x
        (fun i : Fin 2 => if i = 0 then X else Y)) t := by
  have hbridge : metricRicciAt (I := I) (g t) x (fun i : Fin 2 => if i = 0 then X else Y) =
      DifferentialGeometry.Geometry.Curvature.ricciTensor (I := I) (g t) x X Y :=
    metricRicciAt_apply_eq_ricciTensor (I := I) (g t) x X Y
  rw [hbridge]
  exact (hpde t ⟨ht.1.le, ht.2⟩ x X Y).hasDerivAt (Ici_mem_nhds ht.1)

end PDEUpgrade

section Inputs

structure ForwardUniqueSlab (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Adot : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Sfield : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (a c C_A C_R C_Ric C_V C_U C_rem : Real) : Prop where

  fluxLe : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 5 (Uflux t x) ≤
    C_U * forwardUniqueDensity (I := I) g₁ g₂ t x

  remLe : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 4 (rem t x) ≤
    C_rem * forwardUniqueDensity (I := I) g₁ g₂ t x

  reactLe : ∀ t ∈ Ioo a c, ∀ x,
    movingReact0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x)
        (metricDiffAt (I := I) (g₁ t) (g₂ t) x) +
      movingReact0S (I := I) (g₁ t) x 3 (metricRicciAt (I := I) (g₁ t) x)
        (connectionDifferenceLowAt (I := I) (g₁ t) (g₂ t) x) +
      movingReact0S (I := I) (g₁ t) x 4 (metricRicciAt (I := I) (g₁ t) x)
        (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x) ≤
    C_R * forwardUniqueDensity (I := I) g₁ g₂ t x

  ricciLe : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 2
      (metricRicciAt (I := I) (g₁ t) x - metricRicciAt (I := I) (g₂ t) x) ≤
    C_Ric * forwardUniqueDensity (I := I) g₁ g₂ t x

  adotLe : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 3 (Adot t x) ≤
    C_A * (forwardUniqueDensity (I := I) g₁ g₂ t x +
      normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) (Sfield t) x))

  volLe : ∀ t ∈ Ioo a c, ∀ x, (1 / 2 : Real) * traceTimeDerivMetric (I := I) g₁ t x ≤ C_V

structure ForwardUniquenessAssumptions (g₁ g₂ : Real → SmoothRiemannianMetric I M)
    (Avec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (Svec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
        TangentSpace I y)
    (Sfield : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (a b : Real) : Prop where

  gamma : ∀ t ∈ Ioo a b, ∀ x : M, ∀ i j k : Fin (Module.finrank Real E),
    HasDerivAt
      (fun r : Real =>
        DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (metricCov (I := I) (g₁ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k -
          DifferentialGeometry.Tensor.Coordinates.christoffelSymbolInFrame
            (metricCov (I := I) (g₂ r)) (chartFrame I x) (chartFrame_isFrame I x) x i j k)
      ((chartFrame_isFrame I x).coeff k x
        ((Avec t x (chartFrame I x j x)) (chartFrame I x i x))) t

  rm : ∀ t ∈ Ioo a b, ∀ (x : M) (X Y Z : TangentSpace I x),
    HasDerivAt (fun r : Real => ((rmDiffVec (I := I) (g₁ r) (g₂ r) x X) Y) Z)
      (((Svec t x X) Y) Z) t

  car : ∀ t ∈ Ioo a b, ∀ x, Sfield t x = rmDiffLowAt (I := I) (g₁ t) (g₂ t) x

  sdec : ∀ t ∈ Ioo a b, ∀ x, rmSpeed (I := I) g₁ g₂ Svec t x =
    roughLap0SField (I := I) (g₁ t) (Sfield t) x +
      covDiv0SField (I := I) (g₁ t) (Uflux t) x + rem t x

  bounds : ∀ c ∈ Ioo a b, ∃ C_A C_R C_Ric C_V C_U C_rem : Real,
    ForwardUniqueSlab (I := I) g₁ g₂ (connSpeed (I := I) g₁ g₂ Avec) Sfield Uflux rem
      a c C_A C_R C_Ric C_V C_U C_rem

  dens : ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
    (fun p : Real × M => forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
    (Ioo a b ×ˢ (univ : Set M))

  energyCont : ContinuousOn (forwardUniqueEnergy (I := I) (M := M) g₁ g₂) (Ico a b)

  densInt : ∀ t ∈ Ico a b, Integrable (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)

  densCont : ∀ t ∈ Ico a b, Continuous (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)

  restInt : ∀ t ∈ Ioo a b, Integrable
    (fun x => rateRest (I := I) g₁ g₂ (connSpeed (I := I) g₁ g₂ Avec) t x)
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)

  pairInt : ∀ t ∈ Ioo a b, Integrable
    (fun x => 2 * inner0S (I := I) (g₁ t) x 4 (rmSpeed (I := I) g₁ g₂ Svec t x)
      (rmDiffLowAt (I := I) (g₁ t) (g₂ t) x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)

  lapInt : ∀ t ∈ Ioo a b, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
      (roughLap0SField (I := I) (g₁ t) (Sfield t) x) (Sfield t x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)

  divInt : ∀ t ∈ Ioo a b, Integrable (fun x => inner0S (I := I) (g₁ t) x 4
      (covDiv0SField (I := I) (g₁ t) (Uflux t) x) (Sfield t x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)

  remInt : ∀ t ∈ Ioo a b, Integrable
    (fun x => inner0S (I := I) (g₁ t) x 4 (rem t x) (Sfield t x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)

  nabInt : ∀ t ∈ Ioo a b, Integrable (fun x => inner0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₁ t) (Sfield t) x) (Uflux t x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)

  disInt : ∀ t ∈ Ioo a b, Integrable (fun x => normSq0S (I := I) (g₁ t) x 5
      (metricNabla0S (I := I) (g₁ t) (Sfield t) x))
    (riemannianMeasureFamily (I := I) (M := M) g₁ t)

end Inputs

section


theorem forward_unique_of_assumptions
    (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b : Real}
    (Avec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y)
    (Svec : Real → (y : M) →
      TangentSpace I y →L[Real] TangentSpace I y →L[Real] TangentSpace I y →L[Real]
        TangentSpace I y)
    (Sfield : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 4)
    (Uflux : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 5)
    (rem : Real → (x : M) → Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x)
    (h1smooth : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (h1pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₁ s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Geometry.Curvature.ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (h2pde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (g₂ s).inner x v w)
        ((-2 : Real) * DifferentialGeometry.Geometry.Curvature.ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    (h0 : g₁ a = g₂ a)
    (hin : ForwardUniquenessAssumptions (I := I) g₁ g₂ Avec Svec Sfield Uflux rem a b) :
    ∀ t ∈ Ico a b, g₁ t = g₂ t := by
  refine metrics_eq_ico (I := I) g₁ g₂ ?_
  intro c hc t ht
  have hsub : Ioo a c ⊆ Ioo a b := fun s hs => ⟨hs.1, lt_trans hs.2 hc.2⟩
  have hsubIcc : Icc a c ⊆ Ico a b := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hc.2⟩
  obtain ⟨C_A, C_R, C_Ric, C_V, C_U, C_rem, hb⟩ := hin.bounds c hc
  have hCA : (0 : Real) ≤ max C_A 0 := le_max_right _ _
  have hyoung : (1 / (2 * (max C_A 0 + 1))) * max C_A 0 + (1 / 2 : Real) ≤ 1 := by
    have he : (1 / (2 * (max C_A 0 + 1))) * max C_A 0
        = max C_A 0 / (2 * (max C_A 0 + 1)) := by ring
    have hdiv : max C_A 0 / (2 * (max C_A 0 + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    rw [he]; linarith
  have hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo a c ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := fun x₀ i j =>
    (h1smooth x₀ i j).mono
      (Set.prod_mono (fun s hs => ⟨hs.1.le, lt_trans hs.2 hc.2⟩) (subset_refl _))
  have hPDE₁ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : Real => (g₁ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₁ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t :=
    fun s hs x X Y => pde_hasDerivAt (I := I) g₁ h1pde (hsub hs) x X Y
  have hPDE₂ : ∀ t ∈ Ioo a c, ∀ (x : M) (X Y : TangentSpace I x),
      HasDerivAt (fun r : Real => (g₂ r).inner x X Y)
        ((-2 : Real) * metricRicciAt (I := I) (g₂ t) x
          (fun i : Fin 2 => if i = 0 then X else Y)) t :=
    fun s hs x X Y => pde_hasDerivAt (I := I) g₂ h2pde (hsub hs) x X Y
  have hA : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 3 → TangentSpace I x),
      HasDerivAt (fun r : Real => connectionDifferenceLowAt (I := I) (g₁ r) (g₂ r) x v)
        (connSpeed (I := I) g₁ g₂ Avec t x v) t := fun s hs x v =>
    connSpeed_hasDerivAt (I := I) g₁ g₂ Avec (fun X Y => hPDE₁ s hs x X Y)
      (fun i j k => hin.gamma s (hsub hs) x i j k) v
  have hS : ∀ t ∈ Ioo a c, ∀ (x : M) (v : Fin 4 → TangentSpace I x),
      HasDerivAt (fun r : Real => rmDiffLowAt (I := I) (g₁ r) (g₂ r) x v)
        (rmSpeed (I := I) g₁ g₂ Svec t x v) t := fun s hs x v =>
    rmSpeed_hasDerivAt (I := I) g₁ g₂ Svec (fun X Y => hPDE₁ s hs x X Y)
      (fun X Y Z => hin.rm s (hsub hs) x X Y Z) v
  have hAdot : ∀ t ∈ Ioo a c, ∀ x, normSq0S (I := I) (g₁ t) x 3
      (connSpeed (I := I) g₁ g₂ Avec t x) ≤
      max C_A 0 * (forwardUniqueDensity (I := I) g₁ g₂ t x +
        normSq0S (I := I) (g₁ t) x 5 (metricNabla0S (I := I) (g₁ t) (Sfield t) x)) := by
    intro s hs x
    refine (hb.adotLe s hs x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact add_nonneg (density_nonneg (I := I) g₁ g₂ s x)
      (normSq0S_nonneg (I := I) (g₁ s) x 5 _)
  exact metrics_eq_on (I := I) (ε := 1 / 2) (δ := 1 / (2 * (max C_A 0 + 1)))
    (C_A := max C_A 0) g₁ g₂ (connSpeed (I := I) g₁ g₂ Avec)
    (rmSpeed (I := I) g₁ g₂ Svec) Sfield Uflux rem hc.1 hgram
    (hin.dens.mono (Set.prod_mono hsub (subset_refl _))) hPDE₁ hPDE₂ hA hS
    (by norm_num) (by positivity) hyoung
    (fun s hs => hin.car s (hsub hs)) (fun s hs => hin.sdec s (hsub hs))
    (hb.fluxLe) (hb.remLe) (hb.reactLe) (hb.ricciLe) hAdot (hb.volLe)
    (fun s hs => hin.restInt s (hsub hs)) (fun s hs => hin.pairInt s (hsub hs))
    (fun s hs => hin.lapInt s (hsub hs)) (fun s hs => hin.divInt s (hsub hs))
    (fun s hs => hin.remInt s (hsub hs)) (fun s hs => hin.nabInt s (hsub hs))
    (fun s hs => hin.disInt s (hsub hs)) (fun s hs => hin.densInt s (hsubIcc hs))
    (fun s hs => hin.densCont s (hsubIcc hs)) h0
    (hin.energyCont.mono hsubIcc) t ht

end

end DifferentialGeometry.PDE.RicciFlow

end
