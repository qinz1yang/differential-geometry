import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormalizedTimeJets
import DifferentialGeometry.Geometry.Metric.Pullback.CovariantDerivative
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.CrossTensorPullback


set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u


theorem derivWithin_add_of_eq {f₁ f₂ : ℝ → ℝ} {T : Set ℝ} {s d₁ d₂ : ℝ}
    (h₁ : derivWithin f₁ T s = d₁) (h₂ : derivWithin f₂ T s = d₂)
    (hdiff : UniqueDiffWithinAt ℝ T s →
      DifferentiableWithinAt ℝ f₁ T s ∧ DifferentiableWithinAt ℝ f₂ T s) :
    derivWithin (fun a => f₁ a + f₂ a) T s = d₁ + d₂ := by
  by_cases hu : UniqueDiffWithinAt ℝ T s
  · obtain ⟨hf₁, hf₂⟩ := hdiff hu
    rw [derivWithin_fun_add hf₁ hf₂, h₁, h₂]
  · have e0 : ∀ f : ℝ → ℝ, derivWithin f T s = 0 := fun f =>
      derivWithin_zero_of_not_uniqueDiffWithinAt (f := f) hu
    rw [e0, ← h₁, ← h₂, e0, e0, add_zero]


section TensorAlgebra

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]


theorem tensor02CovDeriv_add
    (A B : Tensor0SField (I := J) (M := N) (n := ∞) 2)
    (gRef : SmoothRiemannianMetric J N) (a : ℕ) :
    tensor02CovDeriv (I := J) (A + B) gRef a =
      tensor02CovDeriv (I := J) A gRef a + tensor02CovDeriv (I := J) B gRef a := by
  rw [tensor02_cov_deriv_eq_cov_deriv_of_field, tensor02_cov_deriv_eq_cov_deriv_of_field, tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_add]


theorem tensor02CovDerivNormWith_add_le (a : ℕ)
    (A B : Tensor0SField (I := J) (M := N) (n := ∞) 2)
    (cov nrm : SmoothRiemannianMetric J N) (y : N) :
    tensor02CovDerivNormWith (I := J) a (A + B) cov nrm y ≤
      tensor02CovDerivNormWith (I := J) a A cov nrm y +
        tensor02CovDerivNormWith (I := J) a B cov nrm y := by
  unfold tensor02CovDerivNormWith
  rw [tensor02CovDeriv_add]
  exact _root_.Tensor0SBundle.sqrt_normSq0S_add_le (I := J) nrm y (a + 2)
    (tensor02CovDeriv (I := J) A cov a y) (tensor02CovDeriv (I := J) B cov a y)

end TensorAlgebra


section Restriction

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]


def MetricComparisonOn.mono {h : ℝ → SmoothRiemannianMetric J N}
    {g : ℝ → SmoothRiemannianMetric I3 M} {F : N → M} {U U' : Set N} {times : Set ℝ}
    {order order' : ℕ} {eps eps' : ℝ}
    (C : MetricComparisonOn h g F U times order eps)
    (hU : U' ⊆ U) (horder : order' ≤ order) (heps : eps ≤ eps') :
    MetricComparisonOn h g F U' times order' eps' where
  pullback := C.pullback
  pullback_eq s y hy := C.pullback_eq s y (hU hy)
  jet := C.jet
  jet_zero := C.jet_zero
  jet_succ b s hs y hy := C.jet_succ b s hs y (hU hy)
  equivalence := by
    intro s hs y hy v
    have hnn : 0 ≤ (h s).inner y v v := inner_self_nonneg (h s) y v
    obtain ⟨hlo, hhi⟩ := C.equivalence s hs y (hU hy) v
    refine ⟨le_trans ?_ hlo, le_trans hhi ?_⟩
    · exact mul_le_mul_of_nonneg_right (by linarith) hnn
    · exact mul_le_mul_of_nonneg_right (by linarith) hnn
  close a b hab s hs y hy :=
    le_trans (C.close a b (hab.trans horder) s hs y (hU hy)) heps

end Restriction


section Composition

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance comparisonCompositionC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance comparisonCompositionMidC1 : IsManifold I3 1 P :=
  IsManifold.of_le (n := ∞) (by decide)


structure TransportedErrorTower {k : ℝ → SmoothRiemannianMetric I3 P}
    {g : ℝ → SmoothRiemannianMetric I3 M} {F : P → M} {V : Set P} {times' : Set ℝ}
    {order' : ℕ} {eps : ℝ} (c : MetricComparisonOn k g F V times' order' eps)
    (h : ℝ → SmoothRiemannianMetric J N) (G : N → P)
    (U : Set N) (times : Set ℝ) (order : ℕ) (K : ℝ) where
  tower : ℕ → ℝ → Tensor0SField (I := J) (M := N) (n := ∞) 2
  zero_eq : ∀ s, ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace J y,
    tower 0 s y v = c.jet 0 s (G y) (fun q => mfderiv J I3 G y (v q))
  succ_eq : ∀ b s, s ∈ times → ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace J y,
    tower (b + 1) s y v = derivWithin (fun a => tower b a y v) times s
  differentiableWithinAt : ∀ b s, s ∈ times → UniqueDiffWithinAt ℝ times s →
    ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace J y,
      DifferentiableWithinAt ℝ (fun a => tower b a y v) times s
  close : ∀ a b, a + 2 * b ≤ order → ∀ s ∈ times, ∀ y ∈ U,
    tensor02CovDerivNormWith (I := J) a (tower b s) (h s) (h s) y ≤ K * eps


def TransportedErrorTower.ofPullbackCross {k : ℝ → SmoothRiemannianMetric I3 P}
    {g : ℝ → SmoothRiemannianMetric I3 M} {F : P → M} {V : Set P} {times : Set ℝ}
    {order' : ℕ} {eps : ℝ} (c : MetricComparisonOn k g F V times order' eps)
    (h : ℝ → SmoothRiemannianMetric J N) (Phi : N ≃ₘ⟮J, I3⟯ P)
    {U : Set N} {order : ℕ} {K : ℝ}
    (hV : ∀ y ∈ U, Phi y ∈ V) (hK : 0 ≤ K) (horder : order ≤ order')
    (hdiff : ∀ b s, s ∈ times → UniqueDiffWithinAt ℝ times s → ∀ y ∈ U,
      ∀ v : Fin 2 → TangentSpace J y,
        DifferentiableWithinAt ℝ
          (fun a => c.jet b a (Phi y) (fun q => mfderiv J I3 Phi y (v q))) times s)
    (hback : ∀ a b, a + 2 * b ≤ order → ∀ s ∈ times, ∀ y ∈ U,
      tensor02CovDerivNormWith a (pullbackTensor02FieldCross Phi (c.jet b s))
          (h s) (h s) y ≤
        K * tensor02CovDerivNormWith a (pullbackTensor02FieldCross Phi (c.jet b s))
          (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi)
          (DifferentialGeometry.Diffeomorph.pullbackMetricCross (k s) Phi) y) :
    TransportedErrorTower c h Phi U times order K where
  tower b s := pullbackTensor02FieldCross Phi (c.jet b s)
  zero_eq s y _ v := pullbackTensor02FieldCross_apply Phi (c.jet 0 s) y v
  succ_eq := by
    intro b s hs y hy v
    have hfun : (fun a => pullbackTensor02FieldCross Phi (c.jet b a) y v)
        = fun a => c.jet b a (Phi y) (fun q => mfderiv J I3 Phi y (v q)) := by
      funext a
      exact pullbackTensor02FieldCross_apply Phi (c.jet b a) y v
    rw [pullbackTensor02FieldCross_apply Phi (c.jet (b + 1) s) y v, hfun]
    exact c.jet_succ b s hs (Phi y) (hV y hy) _
  differentiableWithinAt := by
    intro b s hs hu y hy v
    have hfun : (fun a => pullbackTensor02FieldCross Phi (c.jet b a) y v)
        = fun a => c.jet b a (Phi y) (fun q => mfderiv J I3 Phi y (v q)) := by
      funext a
      exact pullbackTensor02FieldCross_apply Phi (c.jet b a) y v
    rw [hfun]
    exact hdiff b s hs hu y hy v
  close := by
    intro a b hab s hs y hy
    refine le_trans (hback a b hab s hs y hy) ?_
    rw [tensor02CovDerivNormWith_pullbackTensor02FieldCross (k s) (k s) Phi (c.jet b s) a y]
    exact mul_le_mul_of_nonneg_left
      (c.close a b (hab.trans horder) s hs (Phi y) (hV y hy)) hK


def MetricComparisonOn.trans {h : ℝ → SmoothRiemannianMetric J N}
    {k : ℝ → SmoothRiemannianMetric I3 P} {g : ℝ → SmoothRiemannianMetric I3 M}
    {G : N → P} {F : P → M} {U : Set N} {V : Set P} {times times' : Set ℝ}
    {order order' : ℕ} {alpha eps K : ℝ}
    (c₁ : MetricComparisonOn h k G U times order alpha)
    (c₂ : MetricComparisonOn k g F V times' order' eps)
    (T : TransportedErrorTower c₂ h G U times order K)
    (hGV : ∀ y ∈ U, G y ∈ V)
    (hG : ∀ y ∈ U, MDifferentiableAt J I3 G y)
    (hF : ∀ y ∈ U, MDifferentiableAt I3 I3 F (G y))
    (hc₁ : ∀ b s, s ∈ times → UniqueDiffWithinAt ℝ times s → ∀ y ∈ U,
      ∀ v : Fin 2 → TangentSpace J y,
        DifferentiableWithinAt ℝ (fun a => c₁.jet b a y v) times s) :
    MetricComparisonOn h g (fun y => F (G y)) U times order (alpha + K * eps) where
  pullback s := c₁.pullback s + T.tower 0 s
  pullback_eq := by
    intro s y hy v
    have h1 : c₁.pullback s y v =
        (k s).inner (G y) (mfderiv J I3 G y (v 0)) (mfderiv J I3 G y (v 1)) :=
      c₁.pullback_eq s y hy v
    have h2 : T.tower 0 s y v = c₂.jet 0 s (G y) (fun q => mfderiv J I3 G y (v q)) :=
      T.zero_eq s y hy v
    have h3 : c₂.jet 0 s (G y) (fun q => mfderiv J I3 G y (v q)) =
        c₂.pullback s (G y) (fun q => mfderiv J I3 G y (v q)) -
          (k s).inner (G y) (mfderiv J I3 G y (v 0)) (mfderiv J I3 G y (v 1)) :=
      c₂.jet_zero s (G y) (fun q => mfderiv J I3 G y (v q))
    have h4 : c₂.pullback s (G y) (fun q => mfderiv J I3 G y (v q)) =
        (g s).inner (F (G y))
          (mfderiv I3 I3 F (G y) (mfderiv J I3 G y (v 0)))
          (mfderiv I3 I3 F (G y) (mfderiv J I3 G y (v 1))) :=
      c₂.pullback_eq s (G y) (hGV y hy) (fun q => mfderiv J I3 G y (v q))
    have hchain : ∀ z : TangentSpace J y,
        mfderiv J I3 (fun r => F (G r)) y z =
          mfderiv I3 I3 F (G y) (mfderiv J I3 G y z) := by
      intro z
      simpa only [Function.comp_def] using
        mfderiv_comp_apply (I := J) (I' := I3) (I'' := I3) y (hF y hy) (hG y hy) z
    change c₁.pullback s y v + T.tower 0 s y v =
      (g s).inner (F (G y)) (mfderiv J I3 (fun r => F (G r)) y (v 0))
        (mfderiv J I3 (fun r => F (G r)) y (v 1))
    rw [h1, h2, h3, h4, hchain (v 0), hchain (v 1)]
    ring
  jet b s := c₁.jet b s + T.tower b s
  jet_zero := by
    intro s y v
    change c₁.jet 0 s y v + T.tower 0 s y v =
      c₁.pullback s y v + T.tower 0 s y v - (h s).inner y (v 0) (v 1)
    rw [c₁.jet_zero s y v]
    ring
  jet_succ := by
    intro b s hs y hy v
    change c₁.jet (b + 1) s y v + T.tower (b + 1) s y v =
      derivWithin (fun a => c₁.jet b a y v + T.tower b a y v) times s
    exact (derivWithin_add_of_eq (c₁.jet_succ b s hs y hy v).symm
      (T.succ_eq b s hs y hy v).symm
      (fun hu => ⟨hc₁ b s hs hu y hy v, T.differentiableWithinAt b s hs hu y hy v⟩)).symm
  equivalence := by
    intro s hs y hy v
    refine quadratic_comparison_of_error_norm (I := J) (h s)
      (c₁.pullback s + T.tower 0 s) (c₁.jet 0 s + T.tower 0 s) y
      (eps := alpha + K * eps) ?_ ?_ v
    · intro w
      change c₁.jet 0 s y w + T.tower 0 s y w =
        c₁.pullback s y w + T.tower 0 s y w - (h s).inner y (w 0) (w 1)
      rw [c₁.jet_zero s y w]
      ring
    · refine le_trans (tensor02CovDerivNormWith_add_le (J := J) 0 (c₁.jet 0 s)
        (T.tower 0 s) (h s) (h s) y) ?_
      exact add_le_add (c₁.close 0 0 (by simp) s hs y hy) (T.close 0 0 (by simp) s hs y hy)
  close := by
    intro a b hab s hs y hy
    refine le_trans (tensor02CovDerivNormWith_add_le (J := J) a (c₁.jet b s)
      (T.tower b s) (h s) (h s) y) ?_
    exact add_le_add (c₁.close a b hab s hs y hy) (T.close a b hab s hs y hy)

end Composition


section PartialTrans

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  {H₃ : Type*} [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
  {A : Type*} [TopologicalSpace A] [ChartedSpace H₁ A]
  {B : Type*} [TopologicalSpace B] [ChartedSpace H₂ B]
  {C : Type*} [TopologicalSpace C] [ChartedSpace H₃ C]


def partialDiffeomorphTransMixed
    (Φ : PartialDiffeomorph I₁ I₂ A B ∞) (Ψ : PartialDiffeomorph I₂ I₃ B C ∞) :
    PartialDiffeomorph I₁ I₃ A C ∞ where
  toPartialEquiv := Φ.toPartialEquiv.trans Ψ.toPartialEquiv
  open_source := by
    have hsrc : (Φ.toPartialEquiv.trans Ψ.toPartialEquiv).source
        = Φ.source ∩ (Φ : A → B) ⁻¹' Ψ.source := rfl
    rw [hsrc]
    exact Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source Ψ.open_source
  open_target := by
    have htgt : (Φ.toPartialEquiv.trans Ψ.toPartialEquiv).target
        = Ψ.target ∩ (Ψ.symm : C → B) ⁻¹' Φ.target := by
      rw [PartialEquiv.trans_target]
      rfl
    rw [htgt]
    exact Ψ.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Ψ.open_target
      Φ.open_target
  contMDiffOn_toFun := by
    have hsrc : (Φ.toPartialEquiv.trans Ψ.toPartialEquiv).source
        = Φ.source ∩ (Φ : A → B) ⁻¹' Ψ.source := rfl
    rw [hsrc]
    exact Ψ.contMDiffOn_toFun.comp (Φ.contMDiffOn_toFun.mono Set.inter_subset_left)
      (fun y hy => hy.2)
  contMDiffOn_invFun := by
    have htgt : (Φ.toPartialEquiv.trans Ψ.toPartialEquiv).target
        = Ψ.target ∩ (Ψ.symm : C → B) ⁻¹' Φ.target := by
      rw [PartialEquiv.trans_target]
      rfl
    rw [htgt]
    exact Φ.symm.contMDiffOn_toFun.comp (Ψ.symm.contMDiffOn_toFun.mono Set.inter_subset_left)
      (fun y hy => hy.2)

@[simp]
theorem coe_partialDiffeomorphTransMixed
    (Φ : PartialDiffeomorph I₁ I₂ A B ∞) (Ψ : PartialDiffeomorph I₂ I₃ B C ∞) :
    (partialDiffeomorphTransMixed Φ Ψ : A → C) = fun y => Ψ (Φ y) := rfl

theorem source_partialDiffeomorphTransMixed
    (Φ : PartialDiffeomorph I₁ I₂ A B ∞) (Ψ : PartialDiffeomorph I₂ I₃ B C ∞) :
    (partialDiffeomorphTransMixed Φ Ψ).source = Φ.source ∩ (Φ : A → B) ⁻¹' Ψ.source := rfl

end PartialTrans


section NeckTransport

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]

omit [SigmaCompactSpace M] [SigmaCompactSpace P] in
theorem neck_window_subset {alpha : ℝ} (halpha : 0 < alpha) :
    (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹ : Set Cylinder) ⊆
      Set.univ ×ˢ Set.Ioo (-alpha⁻¹) alpha⁻¹ := by
  have hinv : (2 * alpha)⁻¹ ≤ alpha⁻¹ := inv_anti₀ halpha (by linarith)
  exact Set.prod_mono (subset_refl _) (Set.Ioo_subset_Ioo (by linarith) hinv)


def StrongNeck.transport {Dm : RealTimeInterval} {Sm : SolutionOn (I := I3) (M := P) Dm}
    {p : P} {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D} {x : M} {t : ℝ}
    {alpha eps K : ℝ} {V : Set P} {times' : Set ℝ} {order' : ℕ}
    (nk : StrongNeck Sm alpha p 0) (hQ : 0 < S.scalar t x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (rescaledMetric Sm 0 (Sm.scalar 0 p) nk.Q_pos)
      (rescaledMetric S t (S.scalar t x) hQ) Fmap V times' order' eps)
    (T : TransportedErrorTower cmp nk.cylinder.metric nk.map
      (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) (Set.Icc (-1) 0)
      ⌈(2 * alpha)⁻¹⌉₊ K)
    (hsmall : 2 * alpha < 1 / 11) (hKeps : K * eps ≤ alpha)
    (hbase : Fmap p = x)
    (hcore : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source)
    (htime : Set.Icc (t - (S.scalar t x)⁻¹) t ⊆ D.carrier)
    (hjet : ∀ b s, s ∈ Set.Icc (-1 : ℝ) 0 → UniqueDiffWithinAt ℝ (Set.Icc (-1 : ℝ) 0) s →
      ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        ∀ v : Fin 2 → TangentSpace IC y,
          DifferentiableWithinAt ℝ (fun a => nk.comparison.jet b a y v)
            (Set.Icc (-1 : ℝ) 0) s) :
    StrongNeck S (2 * alpha) x t where
  eps_pos := by have := nk.eps_pos; linarith
  eps_small := hsmall
  Q_pos := hQ
  cylinder := nk.cylinder
  map := partialDiffeomorphTransMixed nk.map Fmap
  center := nk.center
  center_eq := by
    change Fmap (nk.map (nk.center, 0)) = x
    rw [nk.center_eq, hbase]
  domain := by
    intro y hy
    refine Set.mem_inter (nk.domain (neck_window_subset nk.eps_pos hy)) ?_
    exact hVsource (hcore y hy)
  time_domain := htime
  comparison := by
    have ha : (0 : ℝ) < alpha := nk.eps_pos
    have hsub := neck_window_subset (alpha := alpha) ha
    have horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ ⌈alpha⁻¹⌉₊ :=
      Nat.ceil_mono (inv_anti₀ ha (by linarith))
    have hmapdiff : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        MDifferentiableAt IC I3 (nk.map : Cylinder → P) y := fun y hy =>
      nk.map.mdifferentiableAt (by simp) (nk.domain (hsub hy))
    exact ((nk.comparison.mono hsub horder le_rfl).trans cmp T hcore hmapdiff
      (fun y hy => Fmap.mdifferentiableAt (by simp) (hVsource (hcore y hy))) hjet).mono
      (subset_refl _) le_rfl (by linarith)


def SpatialNeck.transport {gm : SmoothRiemannianMetric I3 P} {p : P}
    {g : SmoothRiemannianMetric I3 M} {x : M} {alpha eps K : ℝ} {V : Set P}
    {times' : Set ℝ} {order' : ℕ}
    (nk : SpatialNeck gm alpha p) (hQ : 0 < metricScalarAt g x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (fun _ => scaleMetric (metricScalarAt gm p) nk.Q_pos gm)
      (fun _ => scaleMetric (metricScalarAt g x) hQ g) Fmap V times' order' eps)
    (T : TransportedErrorTower cmp (fun _ => nk.cylinder.metric 0) nk.map
      (Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹) {0} ⌈(2 * alpha)⁻¹⌉₊ K)
    (hsmall : 2 * alpha < 1 / 11) (hKeps : K * eps ≤ alpha)
    (hbase : Fmap p = x)
    (hcore : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source) :
    SpatialNeck g (2 * alpha) x where
  eps_pos := by have := nk.eps_pos; linarith
  eps_small := hsmall
  Q_pos := hQ
  cylinder := nk.cylinder
  map := partialDiffeomorphTransMixed nk.map Fmap
  center := nk.center
  center_eq := by
    change Fmap (nk.map (nk.center, 0)) = x
    rw [nk.center_eq, hbase]
  domain := by
    intro y hy
    refine Set.mem_inter (nk.domain (neck_window_subset nk.eps_pos hy)) ?_
    exact hVsource (hcore y hy)
  comparison := by
    have ha : (0 : ℝ) < alpha := nk.eps_pos
    have hsub := neck_window_subset (alpha := alpha) ha
    have horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ ⌈alpha⁻¹⌉₊ :=
      Nat.ceil_mono (inv_anti₀ ha (by linarith))
    have hmapdiff : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        MDifferentiableAt IC I3 (nk.map : Cylinder → P) y := fun y hy =>
      nk.map.mdifferentiableAt (by simp) (nk.domain (hsub hy))
    exact ((nk.comparison.mono hsub horder le_rfl).trans cmp T hcore hmapdiff
      (fun y hy => Fmap.mdifferentiableAt (by simp) (hVsource (hcore y hy)))
      (fun _ _ _ _ _ _ _ => DifferentiableWithinAt.singleton)).mono
      (subset_refl _) le_rfl (by linarith)

end NeckTransport

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
