import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PartialErrorTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckTransportDecoupled
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.exists_transport_of_local_comparisons
    {Dm : RealTimeInterval} {Sm : SolutionOn (I := I3) (M := P) Dm}
    {p : P} {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {x : M} {t alpha eps : ℝ} {V : Set P} {order' : ℕ}
    (nk : StrongNeck Sm (neckModelTolerance alpha) p 0) (hQ : 0 < S.scalar t x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (rescaledMetric Sm 0 (Sm.scalar 0 p) nk.Q_pos)
      (rescaledMetric S t (S.scalar t x) hQ) Fmap V (Set.Icc (-1) 0) order' eps)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : 0 ≤ eps) (heps' : eps ≤ neckSourceTolerance alpha)
    (horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ order')
    (hbase : Fmap p = x)
    (houter : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-alpha⁻¹) alpha⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source)
    (htime : Set.Icc (t - (S.scalar t x)⁻¹) t ⊆ D.carrier)
    (hdiff : ∀ b s, s ∈ Set.Icc (-1 : ℝ) 0 →
      ∀ z ∈ nk.map '' (Set.univ ×ˢ Set.Ioo (-alpha⁻¹) alpha⁻¹),
      ∀ v : Fin 2 → TangentSpace I3 z,
        DifferentiableWithinAt ℝ (fun a => cmp.jet b a z v) (Set.Icc (-1 : ℝ) 0) s)
    (hjet : ∀ b s, s ∈ Set.Icc (-1 : ℝ) 0 → UniqueDiffWithinAt ℝ (Set.Icc (-1 : ℝ) 0) s →
      ∀ y ∈ Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹,
        ∀ v : Fin 2 → TangentSpace IC y,
          DifferentiableWithinAt ℝ (fun a => nk.comparison.jet b a y v)
            (Set.Icc (-1 : ℝ) 0) s) :
    ∃ nk' : StrongNeck S (2 * alpha) x t,
      nk'.map = partialDiffeomorphTransMixed nk.map Fmap := by
  let U : TopologicalSpace.Opens Cylinder :=
    ⟨Set.univ ×ˢ Set.Ioo (-alpha⁻¹) alpha⁻¹, isOpen_univ.prod isOpen_Ioo⟩
  let W : TopologicalSpace.Opens Cylinder :=
    ⟨Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, isOpen_univ.prod isOpen_Ioo⟩
  let K : Set Cylinder := Set.univ ×ˢ Set.Icc (-(2 * alpha)⁻¹) (2 * alpha)⁻¹
  have hrad : (2 * alpha)⁻¹ < alpha⁻¹ := inv_strictAnti₀ ha (by linarith)
  have hKU : K ⊆ U := by
    intro y hy
    exact ⟨hy.1, lt_of_lt_of_le (neg_lt_neg hrad) hy.2.1,
      lt_of_le_of_lt hy.2.2 hrad⟩
  have hWK : (W : Set Cylinder) ⊆ K :=
    Set.prod_mono (subset_refl _) Set.Ioo_subset_Icc_self
  have hWU : (W : Set Cylinder) ⊆ U := hWK.trans hKU
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  obtain ⟨chi, hchi, _hcompact, hone, hsupp, _hrange⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump (I := IC) hK U.isOpen hKU
  have hchiW : EqOn chi (fun _ => 1) W := by
    intro y hy
    exact subset_of_mem_nhdsSet hone (hWK hy)
  have hU : (U : Set Cylinder) ⊆ nk.map.source := by
    apply Set.Subset.trans ?_ nk.domain
    have hr := inv_anti₀ (neckModelTolerance_pos ha) (neckModelTolerance_le alpha)
    exact Set.prod_mono (subset_refl _) (Set.Ioo_subset_Ioo (neg_le_neg hr) hr)
  have hsub : (W : Set Cylinder) ⊆
      Set.univ ×ˢ Set.Ioo (-(neckModelTolerance alpha)⁻¹) (neckModelTolerance alpha)⁻¹ :=
    neck_window_subset_of_le (neckModelTolerance_pos ha) (neckModelTolerance_le alpha)
  have hord : ⌈(2 * alpha)⁻¹⌉₊ ≤ ⌈(neckModelTolerance alpha)⁻¹⌉₊ :=
    Nat.ceil_mono (inv_anti₀ (neckModelTolerance_pos ha)
      ((neckModelTolerance_le alpha).trans (by linarith)))
  obtain ⟨T⟩ := TransportedErrorTower.nonempty_of_partial_pullback cmp nk.cylinder.metric nk.map
    U W hU hWU houter chi hchi hsupp hchiW (nk.comparison.mono hsub hord le_rfl)
    horder heps (neckModelTolerance_pos ha) (neckModelTolerance_le_smallness alpha) hdiff
  exact ⟨StrongNeck.transport' nk hQ Fmap cmp T hsmall (neckModelTolerance_le alpha)
    (backgroundJetConstant_mul_le_of_le_neckSourceTolerance ha heps') hbase
    (fun y hy => houter y (hWU hy)) hVsource htime hjet, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
