import DifferentialGeometry.Topology.Manifold.EmbeddedBallStraightening
import DifferentialGeometry.Topology.Manifold.PartialChartSupportedExtension
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.TransportDiffeomorphism

noncomputable section
open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private def diffeomorphOfContDiff (f g : E → E) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  { toEquiv := { toFun := f, invFun := g, left_inv := hl, right_inv := hr }
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := hg.contMDiff }

omit [FiniteDimensional ℝ E] in
private theorem diffeomorphOfContDiff_apply (f g : E → E) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hl : Function.LeftInverse g f) (hr : Function.RightInverse g f)
    (y : E) : diffeomorphOfContDiff f g hf hg hl hr y = f y := rfl

private def modelTranslateDiffeomorph (t : E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  diffeomorphOfContDiff (fun y => y + t) (fun y => y - t)
    (contDiff_id.add contDiff_const) (contDiff_id.sub contDiff_const)
    (fun y => by simp) (fun y => by simp)

omit [FiniteDimensional ℝ E] in
private theorem modelTranslateDiffeomorph_apply (t y : E) :
    modelTranslateDiffeomorph t y = y + t := rfl

private def modelScaleDiffeomorph (c : ℝ) (hc : c ≠ 0) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  diffeomorphOfContDiff (fun y => c • y) (fun y => c⁻¹ • y)
    (contDiff_const_smul c) (contDiff_const_smul c⁻¹)
    (fun y => by simp only [smul_smul, inv_mul_cancel₀ hc, one_smul])
    (fun y => by simp only [smul_smul, mul_inv_cancel₀ hc, one_smul])

omit [FiniteDimensional ℝ E] in
private theorem modelScaleDiffeomorph_apply (c : ℝ) (hc : c ≠ 0) (y : E) :
    modelScaleDiffeomorph c hc y = c • y := rfl

private def modelLinearDiffeomorph (A : E ≃L[ℝ] E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  diffeomorphOfContDiff (fun y => A y) (fun y => A.symm y) A.contDiff A.symm.contDiff
    (fun y => A.symm_apply_apply y) (fun y => A.apply_symm_apply y)

omit [FiniteDimensional ℝ E] in
private theorem modelLinearDiffeomorph_apply (A : E ≃L[ℝ] E) (y : E) :
    modelLinearDiffeomorph A y = A y := rfl

private def modelAffineDiffeomorph (A₀ A₁ : E ≃L[ℝ] E) (ε₀ ε₁ : ℝ) (hε₀ : ε₀ ≠ 0)
    (hε₁ : ε₁ ≠ 0) (p₀ p₁ : E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
  (modelTranslateDiffeomorph (-p₀)).trans
    ((modelLinearDiffeomorph A₀.symm).trans
      ((modelScaleDiffeomorph ε₀⁻¹ (inv_ne_zero hε₀)).trans
        ((modelLinearDiffeomorph A₁).trans
          ((modelScaleDiffeomorph ε₁ hε₁).trans (modelTranslateDiffeomorph p₁)))))

omit [FiniteDimensional ℝ E] in
private theorem modelAffineDiffeomorph_apply (A₀ A₁ : E ≃L[ℝ] E) (ε₀ ε₁ : ℝ)
    (hε₀ : ε₀ ≠ 0) (hε₁ : ε₁ ≠ 0) (p₀ p₁ : E) (y : E) :
    modelAffineDiffeomorph A₀ A₁ ε₀ ε₁ hε₀ hε₁ p₀ p₁ y =
      ε₁ • A₁ (ε₀⁻¹ • A₀.symm (y - p₀)) + p₁ := by
  simp only [modelAffineDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    modelTranslateDiffeomorph_apply, modelScaleDiffeomorph_apply, modelLinearDiffeomorph_apply,
    sub_eq_add_neg]

theorem exists_diffeomorph_eqOn_closedBall_of_partialDiffeomorphs
    (φ₀ φ₁ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (h₀ : closedBall (0 : E) 2 ⊆ φ₀.source) (h₁ : closedBall (0 : E) 2 ⊆ φ₁.source) :
    ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ∀ x ∈ closedBall (0 : E) 2, F (φ₀ x) = φ₁ x := by
  obtain ⟨A₀, ε₀, F₀, -, hε₀, -, hF₀, -⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall φ₀ (by norm_num) h₀
      isOpen_univ (subset_univ _)
  obtain ⟨A₁, ε₁, F₁, -, hε₁, -, hF₁, -⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall φ₁ (by norm_num) h₁
      isOpen_univ (subset_univ _)
  have hε₀' : ε₀ ≠ 0 := ne_of_gt hε₀
  have hε₁' : ε₁ ≠ 0 := ne_of_gt hε₁
  refine ⟨(F₀.trans (modelAffineDiffeomorph A₀ A₁ ε₀ ε₁ hε₀' hε₁' (φ₀ 0) (φ₁ 0))).trans
    F₁.symm, ?_⟩
  intro x hx
  have key : modelAffineDiffeomorph A₀ A₁ ε₀ ε₁ hε₀' hε₁' (φ₀ 0) (φ₁ 0) (F₀ (φ₀ x)) =
      F₁ (φ₁ x) := by
    rw [modelAffineDiffeomorph_apply, hF₀ x hx, hF₁ x hx]
    have h1 : (ε₀ • A₀ x + φ₀ 0) - φ₀ 0 = ε₀ • A₀ x := by abel
    rw [h1]
    simp only [ContinuousLinearEquiv.map_smul, A₀.symm_apply_apply, smul_smul,
      inv_mul_cancel₀ hε₀', one_smul]
  simp only [Diffeomorph.coe_trans, Function.comp_apply]
  rw [key, F₁.symm_apply_apply]

abbrev ballChartModel : Type := EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ballChartModel M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace ballChartModel M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace ballChartModel M'']

def BallChartTransport (c : BallChart 3 (𝓡 3) M) (c' : BallChart 3 (𝓡 3) M') : Prop :=
  ∃ Φ : Diffeomorph (𝓡 3) (𝓡 3) M M' ∞,
    ∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, Φ (c.chart x) = c'.chart x

theorem BallChartTransport.refl (c : BallChart 3 (𝓡 3) M) : BallChartTransport c c :=
  ⟨Diffeomorph.refl (𝓡 3) M ∞, fun _ _ => rfl⟩

theorem BallChartTransport.symm {c : BallChart 3 (𝓡 3) M} {c' : BallChart 3 (𝓡 3) M'}
    (h : BallChartTransport c c') : BallChartTransport c' c := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨Φ.symm, fun x hx => by rw [← hΦ x hx, Diffeomorph.symm_apply_apply]⟩

theorem BallChartTransport.trans {c : BallChart 3 (𝓡 3) M} {c' : BallChart 3 (𝓡 3) M'}
    {c'' : BallChart 3 (𝓡 3) M''} (h : BallChartTransport c c') (h' : BallChartTransport c' c'') :
    BallChartTransport c c'' := by
  obtain ⟨Φ, hΦ⟩ := h
  obtain ⟨Ψ, hΨ⟩ := h'
  exact ⟨Φ.trans Ψ, fun x hx => by
    simp only [Diffeomorph.coe_trans, Function.comp_apply, hΦ x hx, hΨ x hx]⟩

def BallChartIsotopic (c c' : BallChart 3 (𝓡 3) M) : Prop :=
  ∃ J : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M M ∞,
    ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M => J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M => (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl (𝓡 3) M ∞ ∧
      ∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, J 1 (c.chart x) = c'.chart x

theorem BallChartIsotopic.toTransport {c c' : BallChart 3 (𝓡 3) M}
    (h : BallChartIsotopic c c') : BallChartTransport c c' := by
  obtain ⟨J, -, -, -, hJ⟩ := h
  exact ⟨J 1, hJ⟩

theorem BallChartIsotopic.refl (c : BallChart 3 (𝓡 3) M) : BallChartIsotopic c c := by
  exact ⟨fun _ => Diffeomorph.refl (𝓡 3) M ∞, contMDiff_snd, contMDiff_snd, rfl,
    fun _ _ => rfl⟩

theorem BallChartIsotopic.trans {c c' c'' : BallChart 3 (𝓡 3) M} (h : BallChartIsotopic c c')
    (h' : BallChartIsotopic c' c'') : BallChartIsotopic c c'' := by
  obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := h
  obtain ⟨K, hK, hKi, hK0, hK1⟩ := h'
  refine ⟨fun t => (J t).trans (K t), ?_, ?_, ?_, ?_⟩
  · exact hK.comp (contMDiff_fst.prodMk hJ)
  · exact hJi.comp (contMDiff_fst.prodMk hKi)
  · change (J 0).trans (K 0) = Diffeomorph.refl (𝓡 3) M ∞
    rw [hJ0, hK0, Diffeomorph.refl_trans]
  · intro x hx
    simp only [Diffeomorph.coe_trans, Function.comp_apply, hJ1 x hx, hK1 x hx]

theorem BallChartIsotopic.symm {c c' : BallChart 3 (𝓡 3) M} (h : BallChartIsotopic c c') :
    BallChartIsotopic c' c := by
  obtain ⟨J, hJ, hJi, hJ0, hJ1⟩ := h
  refine ⟨fun t => (J t).symm, hJi, ?_, ?_, ?_⟩
  · exact hJ
  · change (J 0).symm = Diffeomorph.refl (𝓡 3) M ∞
    rw [hJ0, Diffeomorph.symm_refl]
  · intro x hx
    rw [← hJ1 x hx]
    exact (J 1).symm_apply_apply (c.chart x)


omit [FiniteDimensional ℝ E] in
private theorem extendChartById_chartSymm
    (φ : PartialDiffeomorph 𝓘(ℝ, ballChartModel) (𝓡 3) ballChartModel M ∞)
    (f : ballChartModel → ballChartModel) {y : M} (hy : y ∈ φ.target) :
    extendChartById φ.symm.toOpenPartialHomeomorph f y = φ (f (φ.symm y)) := by
  rw [extendChartById]
  have hsrc : y ∈ φ.symm.toOpenPartialHomeomorph.source := hy
  rw [if_pos hsrc]
  rfl

variable [T2Space M]

theorem ballChartTransport_of_modelDiffeomorph (c c' : BallChart 3 (𝓡 3) M)
    (D : Diffeomorph 𝓘(ℝ, ballChartModel) 𝓘(ℝ, ballChartModel) ballChartModel
      ballChartModel ∞)
    {K : Set ballChartModel} (hK : IsCompact K) (hKt : K ⊆ c'.chart.source)
    (hfix : ∀ z, z ∉ K → D z = z ∧ D.symm z = z)
    (hover : ∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, c.chart x ∈ c'.chart.target)
    (hact : ∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, D (c'.chart.symm (c.chart x)) = x) :
    BallChartTransport c c' := by
  obtain ⟨J, -, -, hJe, -, -, -⟩ :=
    exists_diffeomorph_extension_of_partial_chart_family
      (P := Unit) c'.chart.symm.toOpenPartialHomeomorph
      c'.chart.contMDiffOn_invFun c'.chart.contMDiffOn_toFun
      (fun _ : Unit => D)
      (D.contDiff.comp contDiff_snd) ((D.symm).contDiff.comp contDiff_snd)
      hK hKt (fun _ z hz => hfix z hz)
  refine ⟨J (), fun x hx => ?_⟩
  rw [(hJe () (c.chart x)).1, extendChartById_chartSymm c'.chart D (hover x hx), hact x hx]

def LocalizedModelTransportInput (c c' : BallChart 3 (𝓡 3) M) : Prop :=
  (∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, c.chart x ∈ c'.chart.target) ∧
    ∃ (D : Diffeomorph 𝓘(ℝ, ballChartModel) 𝓘(ℝ, ballChartModel) ballChartModel
        ballChartModel ∞) (K : Set ballChartModel),
      IsCompact K ∧ K ⊆ c'.chart.source ∧
        (∀ z, z ∉ K → D z = z ∧ D.symm z = z) ∧
        ∀ x ∈ Metric.closedBall (0 : ballChartModel) 2, D (c'.chart.symm (c.chart x)) = x

theorem ballChartTransport_of_localizedModelTransportInput {c c' : BallChart 3 (𝓡 3) M}
    (h : LocalizedModelTransportInput c c') : BallChartTransport c c' := by
  obtain ⟨hover, D, K, hK, hKt, hfix, hact⟩ := h
  exact ballChartTransport_of_modelDiffeomorph c c' D hK hKt hfix hover hact

end DifferentialGeometry.Topology.Manifold
namespace DifferentialGeometry.Topology

universe u v u' v'

theorem nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport
    {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{u'} 3}
    {N : ConnectedClosedOrientedManifold.{v} 3} {N' : ConnectedClosedOrientedManifold.{v'} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (c' : OrientedBallChart M'.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold)
    (d' : OrientedBallChart N'.toClosedOrientedManifold)
    (a : BoundaryAttachment)
    (hΦ : Manifold.BallChartTransport c.toBallChart c'.toBallChart)
    (hΨ : Manifold.BallChartTransport d.toBallChart d'.toBallChart) :
    letI := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    letI := ConnectedSumQuotient.csChartedSpace c'.toBallChart d'.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c'.toBallChart d'.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    Nonempty (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) := by
  obtain ⟨Φd, hΦd⟩ := hΦ
  obtain ⟨Ψd, hΨd⟩ := hΨ
  exact csTransportDiffeomorph c c' d d' a Φd Ψd
    (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hΦd x hx)
    (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hΨd x hx)

end DifferentialGeometry.Topology


namespace DifferentialGeometry.Topology

universe u v w

def OrientedBallChartTransport {M : ConnectedClosedOrientedManifold.{u} 3}
    {M' : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (c' : OrientedBallChart M'.toClosedOrientedManifold) : Prop :=
  ∃ Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier,
    Φ.preservesOrientation M.orientation M'.orientation ∧
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        Φ (c.toBallChart.chart x) = c'.toBallChart.chart x

theorem OrientedBallChartTransport.refl
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold) :
    OrientedBallChartTransport c c :=
  ⟨Diffeomorph.refl (𝓡 3) M.Carrier ∞, Diffeomorph.preservesOrientation_refl M.orientation,
    fun _ _ => rfl⟩

theorem OrientedBallChartTransport.symm
    {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{v} 3}
    {c : OrientedBallChart M.toClosedOrientedManifold}
    {c' : OrientedBallChart M'.toClosedOrientedManifold}
    (h : OrientedBallChartTransport c c') : OrientedBallChartTransport c' c := by
  obtain ⟨Φ, hΦo, hΦ⟩ := h
  exact ⟨Φ.symm, Diffeomorph.preservesOrientation_symm hΦo, fun x hx => by
    rw [← hΦ x hx, Diffeomorph.symm_apply_apply]⟩

theorem OrientedBallChartTransport.trans
    {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{v} 3}
    {M'' : ConnectedClosedOrientedManifold.{w} 3}
    {c : OrientedBallChart M.toClosedOrientedManifold}
    {c' : OrientedBallChart M'.toClosedOrientedManifold}
    {c'' : OrientedBallChart M''.toClosedOrientedManifold}
    (h : OrientedBallChartTransport c c') (h' : OrientedBallChartTransport c' c'') :
    OrientedBallChartTransport c c'' := by
  obtain ⟨Φ, hΦo, hΦ⟩ := h
  obtain ⟨Ψ, hΨo, hΨ⟩ := h'
  exact ⟨Φ.trans Ψ, Diffeomorph.preservesOrientation_trans hΦo hΨo, fun x hx => by
    simp only [Diffeomorph.coe_trans, Function.comp_apply, hΦ x hx, hΨ x hx]⟩

theorem OrientedBallChartTransport.toBallChartTransport
    {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{v} 3}
    {c : OrientedBallChart M.toClosedOrientedManifold}
    {c' : OrientedBallChart M'.toClosedOrientedManifold}
    (h : OrientedBallChartTransport c c') :
    Manifold.BallChartTransport c.toBallChart c'.toBallChart := by
  obtain ⟨Φ, -, hΦ⟩ := h
  exact ⟨Φ, hΦ⟩

theorem nonempty_connectedSumQuotient_diffeomorph_of_orientedBallChartTransport
    {M : ConnectedClosedOrientedManifold.{u} 3} {M' : ConnectedClosedOrientedManifold.{v} 3}
    {N : ConnectedClosedOrientedManifold.{u} 3} {N' : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (c' : OrientedBallChart M'.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold)
    (d' : OrientedBallChart N'.toClosedOrientedManifold)
    (a : BoundaryAttachment)
    (hΦ : OrientedBallChartTransport c c') (hΨ : OrientedBallChartTransport d d') :
    letI := ConnectedSumQuotient.csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    letI := ConnectedSumQuotient.csChartedSpace c'.toBallChart d'.toBallChart a.1.toHomeomorph
    letI := ConnectedSumQuotient.csIsManifold c'.toBallChart d'.toBallChart a.1.toHomeomorph
      (ConnectedSumQuotient.contDiffOn_reflectMap a.1)
      (ConnectedSumQuotient.contDiffOn_reflectMapInv a.1)
    Nonempty (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph ≃ₘ⟮𝓡 3, 𝓡 3⟯
      ConnectedSumQuotient c'.toBallChart d'.toBallChart a.1.toHomeomorph) :=
  nonempty_connectedSumQuotient_diffeomorph_of_ballChartTransport c c' d d' a
    hΦ.toBallChartTransport hΨ.toBallChartTransport

end DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology

universe u v

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M']

def BallChart.pullback (c' : BallChart 3 (𝓡 3) M')
    (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M' ∞) : BallChart 3 (𝓡 3) M where
  chart := c'.chart.trans (Diffeomorph.toPartialDiffeomorph Φ.symm)
  closedBall_subset_source := by
    intro x hx
    change x ∈ (c'.chart.toOpenPartialHomeomorph.trans
      (Diffeomorph.toPartialDiffeomorph Φ.symm).toOpenPartialHomeomorph).source
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨c'.closedBall_subset_source hx, Set.mem_univ _⟩

theorem BallChart.pullback_apply (c' : BallChart 3 (𝓡 3) M')
    (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M' ∞) (x : EuclideanSpace ℝ (Fin 3)) :
    (BallChart.pullback c' Φ).chart x = Φ.symm (c'.chart x) := by
  change (c'.chart.toOpenPartialHomeomorph.trans
    (Diffeomorph.toPartialDiffeomorph Φ.symm).toOpenPartialHomeomorph) x = _
  rw [OpenPartialHomeomorph.trans_apply]
  rfl

theorem BallChart.map_pullback (c' : BallChart 3 (𝓡 3) M')
    (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M' ∞) (x : EuclideanSpace ℝ (Fin 3)) :
    Φ ((BallChart.pullback c' Φ).chart x) = c'.chart x := by
  rw [BallChart.pullback_apply, Diffeomorph.apply_symm_apply]

theorem exists_ballChart_pullback (c' : BallChart 3 (𝓡 3) M')
    (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M' ∞) :
    ∃ c : BallChart 3 (𝓡 3) M,
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        Φ (c.chart x) = c'.chart x :=
  ⟨BallChart.pullback c' Φ, fun x _ => BallChart.map_pullback c' Φ x⟩

theorem exists_orientedBallChart_pullback {M : ConnectedClosedOrientedManifold.{u} 3}
    {M' : ConnectedClosedOrientedManifold.{v} 3}
    (c' : OrientedBallChart M'.toClosedOrientedManifold)
    (Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier) :
    ∃ c : BallChart 3 (𝓡 3) M.Carrier,
      ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        Φ (c.chart x) = c'.toBallChart.chart x :=
  exists_ballChart_pullback c'.toBallChart Φ

end DifferentialGeometry.Topology
