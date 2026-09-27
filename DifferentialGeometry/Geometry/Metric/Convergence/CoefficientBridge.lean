import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.EuclideanComponents
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Metric
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Tower
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz
import DifferentialGeometry.Geometry.Metric.Construction.OpenExtension
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Metric.Convergence.Locality
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients

import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity

section

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem metricDerivNorm_restrictOpen_le_of_coefficient_components
    (V : TopologicalSpace.Opens E)
    (Gv : SmoothRiemannianMetric 𝓘(ℝ, E) V)
    (gTot : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (Q B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hQcd : ContDiffOn ℝ ∞ Q V) (hBcd : ContDiffOn ℝ ∞ B V)
    (hQ : ∀ (z : V) (v w : E), Gv.inner z v w = Q z v w)
    (hB : ∀ (z : V) (v w : E), gTot.inner (z : E) v w = B z v w)
    (hco : ∀ z : E, z ∈ V → IsCoercive (B z))
    (a : ℕ) (z : V) {C bnd : ℝ} (hC : 1 ≤ C) (hbnd : 0 ≤ bnd)
    (hequiv : ∀ v : E,
      C⁻¹ * ‖v‖ ^ 2 ≤ B z v v ∧ B z v v ≤ C * ‖v‖ ^ 2)
    (hcomp : ∀ slots : Fin (2 + a) → Fin (Module.finrank ℝ E),
      |iterCovComp (I := 𝓘(ℝ, E))
        (fun i _ => (stdOrthonormalBasis ℝ E).toBasis i)
        (fun w i j m => (stdOrthonormalBasis ℝ E).toBasis.coord m
          (MetricKoszul.raisedKoszulOp (B w) (fderiv ℝ B w)
            ((stdOrthonormalBasis ℝ E).toBasis i) ((stdOrthonormalBasis ℝ E).toBasis j)))
        (fun w s => (Q w - B w)
          ((stdOrthonormalBasis ℝ E).toBasis (s 0))
          ((stdOrthonormalBasis ℝ E).toBasis (s 1))) a z slots| ≤ bnd) :
    metricDerivNorm a Gv (gTot.restrictOpen V) (gTot.restrictOpen V) z ≤
      Real.sqrt (C ^ (2 + a)) *
        (Real.sqrt (Fintype.card (Fin (2 + a) → Fin (Module.finrank ℝ E)) : ℝ) * bnd) := by
  classical
  let e := (stdOrthonormalBasis ℝ E).toBasis
  let frame : Fin (Module.finrank ℝ E) → (w : V) → TangentSpace 𝓘(ℝ, E) w :=
    fun i _ => e i
  let hframe := constantBasis_isLocalFrameOn V e
  let gv := gTot.restrictOpen V
  let Gamma := fun w i j m => e.coord m
    (MetricKoszul.raisedKoszulOp (B w) (fderiv ℝ B w) (e i) (e j))
  let base := fun w (s : Fin 2 → Fin (Module.finrank ℝ E)) =>
    (Q w - B w) (e (s 0)) (e (s 1))
  have hequivV : ∀ v : E,
      C⁻¹ * ‖v‖ ^ 2 ≤ gv.inner z v v ∧ gv.inner z v v ≤ C * ‖v‖ ^ 2 := by
    intro v
    change C⁻¹ * ‖v‖ ^ 2 ≤ gTot.inner (z : E) v v ∧
      gTot.inner (z : E) v v ≤ C * ‖v‖ ^ 2
    rw [hB z v v]
    exact hequiv v
  apply metricDerivNorm_le_of_iterCovComp_le_of_equiv V Gv gv a z hC hbnd hequivV
  intro slots
  have hchrEq :
      (fun w ↦ Tensor.Coordinates.christoffelSymbolInFrame
        (Geometry.Connection.leviCivitaConnectionOfMetric
          (I := 𝓘(Real, E)) gv) frame hframe w) =
        fun (w : V) ↦ Gamma (w : E) := by
    funext w i j m
    have hfield : DifferentialGeometry.Geometry.Curvature.restrictOpenTangentField
        (I := 𝓘(Real, E)) V
        (fun y : E ↦ (constantModelVectorFieldSection (E := E) (e j)) y) =
          fun y : V ↦ (show TangentSpace 𝓘(Real, E) y from e j) := by
      funext y
      rw [DifferentialGeometry.Geometry.Curvature.restrictOpenTangentField_apply]
      with_unfolding_all
        rfl
    have hres := DifferentialGeometry.Geometry.Curvature.metricCov_restrictOpen_globalSection
      (I := 𝓘(Real, E)) gTot V
      (constantModelVectorFieldSection (E := E) (e j)) w (e i)
    rw [hfield] at hres
    have hres' :
        ((Geometry.Connection.leviCivitaConnectionOfMetric
            (I := 𝓘(Real, E)) gv (frame j) w) (e i)) =
          ((Geometry.Connection.leviCivitaConnectionOfMetric
            (I := 𝓘(Real, E)) gTot (fun _ : E ↦ e j) (w : E)) (e i)) := by
      exact hres
    have hEq :
        (fun y : E ↦ gTot.inner y) =ᶠ[nhds (w : E)] B := by
      filter_upwards [V.2.mem_nhds w.2] with y hy
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      exact hB ⟨y, hy⟩ u v
    have hBdiff : DifferentiableAt Real B (w : E) :=
      ((hBcd.contDiffAt (V.2.mem_nhds w.2)).differentiableAt (by simp))
    have hcov :
        ((Geometry.Connection.leviCivitaConnectionOfMetric
            (I := 𝓘(Real, E)) gv (frame j) w) (frame i w)) =
          MetricKoszul.koszulVec (hco (w : E) w.2)
            (fderiv Real B (w : E)) (e i) (e j) := by
      rw [hres']
      exact Geometry.Connection.const_cov_eq_nhds
        gTot B hEq hBdiff (hco (w : E) w.2) (e i) (e j)
    have hbasis : hframe.toBasisAt (Set.mem_univ w) = e := by
      ext q
      rw [hframe.toBasisAt_coe]
      with_unfolding_all
        rfl
    change hframe.coeff m w _ = _
    rw [hcov]
    simp only [IsLocalFrameOn.coeff, Set.mem_univ, dite_true, hbasis]
    exact congrArg (e.coord m)
      (MetricKoszul.raisedKoszulOp_eq (hco (w : E) w.2)
        (fderiv Real B (w : E)) (e i) (e j)).symm
  have hbaseEq :
      frameComp0S (I := 𝓘(Real, E))
          (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) Gv -
            Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) gv) frame =
        fun (w : V) ↦ base (w : E) := by
    funext w s
    change Gv.inner w (e (s 0)) (e (s 1)) -
        gv.inner w (e (s 0)) (e (s 1)) =
      (Q (w : E) - B (w : E)) (e (s 0)) (e (s 1))
    change Gv.inner w (e (s 0)) (e (s 1)) -
      gTot.inner (w : E) (e (s 0)) (e (s 1)) = _
    rw [hQ w (e (s 0)) (e (s 1)), hB w (e (s 0)) (e (s 1))]
    rfl
  have hdiff := metric_iterCovComp_mdifferentiableAt V e B Q hBcd hQcd hco
  have hres := DifferentialGeometry.PDE.RicciFlow.iterCovComp_restrict
    V (fun i ↦ e i) Gamma base hdiff a z slots
  calc
    |iterCovComp (I := 𝓘(Real, E)) (M := V)
        (fun i _ ↦ (stdOrthonormalBasis Real E).toBasis i)
        (fun w ↦ Tensor.Coordinates.christoffelSymbolInFrame
          (Geometry.Connection.leviCivitaConnectionOfMetric
            (I := 𝓘(Real, E)) gv)
          (fun i (_ : V) ↦ (stdOrthonormalBasis Real E).toBasis i)
          (constantBasis_isLocalFrameOn V
            (stdOrthonormalBasis Real E).toBasis) w)
        (frameComp0S (I := 𝓘(Real, E))
          (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) Gv -
            Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) gv)
          (fun i (_ : V) ↦ (stdOrthonormalBasis Real E).toBasis i))
        a z slots| =
      |iterCovComp (I := 𝓘(Real, E)) (M := V)
        (fun i _ ↦ e i) (fun w ↦ Gamma (w : E))
        (fun w ↦ base (w : E)) a z slots| := by
          simp only [e, frame, hchrEq, hbaseEq]
    _ = |iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i)
        Gamma base a (z : E) slots| := congrArg abs hres
    _ ≤ bnd := by simpa only [e, Gamma, base] using hcomp slots

end DifferentialGeometry.CheegerGromovCompactness

end

end


section

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem metricCInfConvergenceOnCompacts_restrictOpen_of_coefficient_convergence
    (V : TopologicalSpace.Opens E)
    (G : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) V)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (Q : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hconv : MapCInfConvergenceOnCompacts (V : Set E) Q B)
    (hQcd : ∀ k, ContDiffOn ℝ ∞ (Q k) V) (hBcd : ContDiffOn ℝ ∞ B V)
    (hQ : ∀ (k : ℕ) (z : V) (v w : E), (G k).inner z v w = Q k z v w)
    (hB : ∀ (z : V) (v w : E), g.inner (z : E) v w = B z v w)
    {C : ℝ} (hC : 1 ≤ C)
    (hbound : ∀ (z : V) (v : E),
      C⁻¹ * ‖v‖ ^ 2 ≤ B z v v ∧ B z v v ≤ C * ‖v‖ ^ 2) :
    MetricCInfConvergenceOnCompacts G (g.restrictOpen V) (g.restrictOpen V) := by
  classical
  have hco : ∀ z : E, z ∈ V → IsCoercive (B z) := by
    intro z hz
    refine ⟨C⁻¹, inv_pos.mpr (lt_of_lt_of_le zero_lt_one hC), ?_⟩
    intro v
    simpa only [pow_two, mul_assoc] using (hbound ⟨z, hz⟩ v).1
  let e := (stdOrthonormalBasis ℝ E).toBasis
  let Gamma := fun w i j m => e.coord m
    (MetricKoszul.raisedKoszulOp (B w) (fderiv ℝ B w) (e i) (e j))
  let base := fun k w (s : Fin 2 → Fin (Module.finrank ℝ E)) =>
    (Q k w - B w) (e (s 0)) (e (s 1))
  have htower : ∀ a : ℕ, MapCInfConvergenceOnCompacts (V : Set E)
      (fun k => iterCovComp (I := 𝓘(ℝ, E)) (fun i _ => e i) Gamma (base k) a)
      (fun _ _ => (0 : ℝ)) := by
    intro a
    exact metric_tower_convergence V.isOpen e (fun _ => B) Q B
      (mapCInfConvergence_const B) hconv (fun _ => hBcd) hQcd hBcd (fun _ => hco) hco a
  intro K hK p ε hε
  have hLK : IsCompact (Subtype.val '' K : Set E) := hK.image continuous_subtype_val
  have hLV : (Subtype.val '' K : Set E) ⊆ V := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hper : ∀ a : Fin (p + 1), ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ z ∈ K,
      metricDerivNorm (a : ℕ) (G k) (g.restrictOpen V) (g.restrictOpen V) z ≤ ε / 2 := by
    intro a
    let D := Real.sqrt (C ^ (2 + (a : ℕ))) *
      Real.sqrt (Fintype.card (Fin (2 + (a : ℕ)) → Fin (Module.finrank ℝ E)) : ℝ)
    have hD : 0 ≤ D := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    let δ := (ε / 2) / (D + 1)
    have hδ : 0 < δ := div_pos (by positivity) (by positivity)
    obtain ⟨N, hN⟩ := htower a (Subtype.val '' K) hLK hLV 0 δ hδ
    refine ⟨N, fun k hk z hz => ?_⟩
    have hnorm : ‖iterCovComp (I := 𝓘(ℝ, E))
        (fun i _ => e i) Gamma (base k) a (z : E)‖ ≤ δ := by
      have hraw := hN k hk 0 le_rfl (z : E) ⟨z, hz, rfl⟩
      simp only [mapDerivNorm, norm_iteratedFDeriv_zero] at hraw
      change ‖iterCovComp (I := 𝓘(ℝ, E)) (fun i _ => e i) Gamma (base k) a (z : E) - 0‖ ≤ δ at hraw
      simpa only [sub_zero] using hraw
    have hc := metricDerivNorm_restrictOpen_le_of_coefficient_components V (G k) g (Q k) B
      (hQcd k) hBcd (hQ k) hB hco a z hC hδ.le (hbound z) (fun slots => by
        have hh := (norm_le_pi_norm _ slots).trans hnorm
        exact hh)
    calc
      metricDerivNorm (a : ℕ) (G k) (g.restrictOpen V) (g.restrictOpen V) z ≤
          Real.sqrt (C ^ (2 + (a : ℕ))) *
            (Real.sqrt (Fintype.card (Fin (2 + (a : ℕ)) → Fin (Module.finrank ℝ E)) : ℝ) * δ) := hc
      _ = D * δ := by dsimp only [D]; ring
      _ ≤ ε / 2 := by
        dsimp only [δ]
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < D + 1)]
        nlinarith
  choose N hN using hper
  refine ⟨Finset.univ.sup N, fun k hk => ?_⟩
  apply lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall K p (G k) (g.restrictOpen V) (g.restrictOpen V)
      (ε / 2) (by positivity) ?_) (by linarith)
  intro a ha z hz
  let a' : Fin (p + 1) := ⟨a, by omega⟩
  exact hN a' k ((Finset.le_sup (Finset.mem_univ a')).trans hk) z hz

end DifferentialGeometry.CheegerGromovCompactness

end

end


section

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem metricCInfConvergenceOnCompacts_of_coefficient_convergence
    (V : TopologicalSpace.Opens E)
    (G : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) V)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) V)
    (Q : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hconv : MapCInfConvergenceOnCompacts (V : Set E) Q B)
    (hQcd : ∀ k, ContDiffOn ℝ ∞ (Q k) V) (hBcd : ContDiffOn ℝ ∞ B V)
    (hQ : ∀ (k : ℕ) (z : V) (v w : E), (G k).inner z v w = Q k z v w)
    (hB : ∀ (z : V) (v w : E), g.inner z v w = B z v w) :
    MetricCInfConvergenceOnCompacts G g g := by
  intro K hK p ε hε
  have hLK : IsCompact (Subtype.val '' K : Set E) := hK.image continuous_subtype_val
  have hLV : (Subtype.val '' K : Set E) ⊆ V := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  obtain ⟨C, hC, U, hU, hKU, hUV, _, hbounds⟩ :=
    hBcd.continuousOn.exists_uniform_bilin_quadratic_bounds_nhds V.isOpen hLK hLV
      (fun z hz v hv => by
        rw [← hB ⟨z, hz⟩ v v]
        exact g.pos ⟨z, hz⟩ v hv)
  let Uo : TopologicalSpace.Opens E := ⟨U, hU⟩
  have hUoV : (Uo : Set E) ⊆ V := subset_closure.trans hUV
  obtain ⟨gTot, W, hLW, hWU, hTot, _⟩ :=
    exists_smooth_metric_agrees_on_neighborhood_of_is_compact
      (euclideanMetric (E := E)) Uo (g.restrictOpenOfSubset hUoV) hLK hKU
  have hWV : (W : Set E) ⊆ V := hWU.trans hUoV
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen 𝓘(ℝ, E) V.isOpen)
  let GW : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) W :=
    fun k => (G k).restrictOpenOfSubset hWV
  have hgW : g.restrictOpenOfSubset hWV = gTot.restrictOpen W := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    exact (hTot z z.property v w).symm
  have hconvW : MetricCInfConvergenceOnCompacts GW
      (gTot.restrictOpen W) (gTot.restrictOpen W) := by
    apply metricCInfConvergenceOnCompacts_restrictOpen_of_coefficient_convergence
      W GW gTot Q B (hC := hC)
    · intro L hL hLW p
      exact hconv L hL (hLW.trans hWV) p
    · exact fun k => (hQcd k).mono hWV
    · exact hBcd.mono hWV
    · intro k z v w
      exact hQ k (TopologicalSpace.Opens.inclusion hWV z) v w
    · intro z v w
      exact (hTot z z.property v w).trans (hB ⟨z, hWV z.property⟩ v w)
    · intro z v
      exact hbounds z (subset_closure (hWU z.property)) v
  let L : Set W := (Subtype.val : W → E) ⁻¹' (Subtype.val '' K)
  have hL : IsCompact L :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hLK
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hLW)
  obtain ⟨N, hN⟩ := hconvW L hL p (ε / 2) (by positivity)
  have hN' : ∀ k, N ≤ k → metricDerivNormSupOn L p (GW k) (g.restrictOpenOfSubset hWV) (g.restrictOpenOfSubset hWV) < ε / 2 := by
    intro k hk
    rw [hgW]
    exact hN k hk
  refine ⟨N, fun k hk => ?_⟩
  apply lt_of_le_of_lt
    (metricDerivNormSupOn_le_of_forall K p (G k) g g (ε / 2) (by positivity) ?_)
    (by linarith)
  intro a ha z hz
  let w : W := ⟨z, hLW ⟨z, hz, rfl⟩⟩
  have hw : w ∈ L := ⟨z, hz, rfl⟩
  have hn := derivNorm_le_sup hL ha (GW k) (gTot.restrictOpen W) (gTot.restrictOpen W)
    (x := w) hw
  rw [← hgW] at hn
  have heq := metricDerivNorm_flat hWV (G k) g g a w
  change metricDerivNorm a (GW k) (g.restrictOpenOfSubset hWV)
    (g.restrictOpenOfSubset hWV) w = metricDerivNorm a (G k) g g z at heq
  rw [heq] at hn
  exact hn.trans (hN' k hk).le

end DifferentialGeometry.CheegerGromovCompactness

end

end


section

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem metricCInfConvergenceOnCompacts_of_pullback_coefficients
    {ι : Type*} (U : ι → TopologicalSpace.Opens E)
    (j : ∀ i, U i → M) (hj : ∀ i, IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (j i))
    (hinj : ∀ i, Function.Injective (j i)) (hcover : ∀ x : M, ∃ i z, j i z = x)
    (jbar : ι → E → M) (hjbar : ∀ i (z : U i), jbar i (z : E) = j i z)
    (gSeq : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (gInf : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hconv : ∀ i, MapCInfConvergenceOnCompacts (U i : Set E)
      (fun k => Geometry.pullbackMetricCoefficients (gSeq k) (jbar i))
      (Geometry.pullbackMetricCoefficients gInf (jbar i))) :
    MetricCInfConvergenceOnCompacts gSeq gInf gInf := by
  let _ : ∀ i, SigmaCompactSpace (U i) := fun i =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen 𝓘(ℝ, E) (U i).isOpen)
  apply metricCInfConvergenceOnCompacts_of_injective_localDiffeomorph_cover
    j hj hinj hcover gSeq gInf gInf
  intro i
  have hjbar' : (fun z : U i => jbar i z) = j i := funext (hjbar i)
  have hjsm : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (jbar i) (U i) := by
    intro z hz
    have h := (hj i).contMDiff.contMDiffAt (x := (⟨z, hz⟩ : U i))
    rw [← hjbar'] at h
    exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt
  have hcoeff : ∀ (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (z : U i) (v w : E),
      (localPullMetric g (j i) (hj i)).inner z v w =
        Geometry.pullbackMetricCoefficients g (jbar i) z v w := by
    intro g z v w
    have hp := localPullMetric_inner g (j i) (hj i) z v w
    rw [hp, Geometry.pullbackMetricCoefficients_apply]
    have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (j i) z =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (jbar i) (z : E) := by
      rw [← hjbar']
      exact DifferentialGeometry.mfderiv_restrict_open (jbar i) (U i) z
    rw [hd]
    rw [hjbar i z]
    rfl
  apply metricCInfConvergenceOnCompacts_of_coefficient_convergence (U i)
    (fun k => localPullMetric (gSeq k) (j i) (hj i))
    (localPullMetric gInf (j i) (hj i))
    (fun k => Geometry.pullbackMetricCoefficients (gSeq k) (jbar i))
    (Geometry.pullbackMetricCoefficients gInf (jbar i)) (hconv i)
    (fun k => Geometry.contDiffOn_pullback_metric_coefficients (gSeq k) (U i).isOpen hjsm)
    (Geometry.contDiffOn_pullback_metric_coefficients gInf (U i).isOpen hjsm)
    (fun k => hcoeff (gSeq k)) (hcoeff gInf)

end DifferentialGeometry.CheegerGromovCompactness

end

end
