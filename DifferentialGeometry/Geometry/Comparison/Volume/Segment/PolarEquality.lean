import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar
import DifferentialGeometry.Geometry.Comparison.Volume.JacobiRiccati.Basic

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem transDens_eq_rigid
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {v : TangentSpace I x}
    (hv : v ∈ SegDom (I := I) g hEnorm x) (hvne : v ≠ 0)
    (w : Fin (Module.finrank ℝ E - 1) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (w i) (w j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner x v (w i) = 0)
    (q : ℝ) (hq : 0 ≤ q) (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (heq : curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
        (fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)) 1 =
      hypDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) 1) :
    let γ := intrinsicGeodesic (I := I) g hEnorm x v
    let V := fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)
    let d := Module.finrank ℝ E - 1
    let ℓ := Real.sqrt (g.inner x v v)
    (∀ t ∈ Set.Ioo (0 : ℝ) 1,
      curveDensity (I := I) g γ V t / hypDensity (q * ℓ) d t = 1) ∧
    ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ricciTensor (I := I) g (γ t) (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t) = -((d : ℝ) * (q * ℓ) ^ 2) ∧
        curveShape (I := I) g γ V t =
          (curveMean (I := I) g γ V t / (d : ℝ)) •
            (1 : Matrix (Fin d) (Fin d) ℝ) := by
  classical
  let γ := intrinsicGeodesic (I := I) g hEnorm x v
  let V := fun i => intrinsicJacobi (I := I) g hEnorm x v (w i)
  let d := Module.finrank ℝ E - 1
  let ℓ := Real.sqrt (g.inner x v v)
  let R := fun t => curveDensity (I := I) g γ V t / hypDensity (q * ℓ) d t
  change (∀ t ∈ Set.Ioo (0 : ℝ) 1, R t = 1) ∧ ∀ t ∈ Set.Ioo (0 : ℝ) 1, _
  have hℓ : 0 < ℓ := Real.sqrt_pos.2 (g.pos x v hvne)
  have hqℓ : 0 ≤ q * ℓ := mul_nonneg hq hℓ.le
  have hno : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ¬ IsConjVec (I := I) g hEnorm x ((t • v : TangentSpace I x) : E) :=
    fun t ht => segDom_not_conj (I := I) g hEnorm x hv ht
  have hanti : AntitoneOn R (Set.Ioo (0 : ℝ) 1) := by
    simpa only [R, γ, V, d, ℓ] using intrRatioOfFrame (I := I) g hEnorm x v q 1
      hq hd (g.pos x v hvne) w hON hperp hno hRic
  have hlim₀ : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [R, γ, V, d, ℓ] using poleLimit (I := I) g hEnorm x v q hq w hON
  have hden₁ : 0 < hypDensity (q * ℓ) d 1 := hypDensity_pos hqℓ (by norm_num)
  have hR₁ : R 1 = 1 := by
    simp only [R, γ, V, d, ℓ]
    rw [heq, div_self hden₁.ne']
  have hlim₁ : Tendsto R (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt R 1 :=
      (curveDensity_jacobiFrame_continuousAt (I := I) g hEnorm x v w 1).div
        (hypDen_continuous (q * ℓ) d).continuousAt hden₁.ne'
    simpa only [hR₁] using hc.continuousWithinAt.tendsto
  have hratio : ∀ t ∈ Set.Ioo (0 : ℝ) 1, R t = 1 := by
    intro t ht
    apply le_antisymm
    · apply ge_of_tendsto hlim₀
      filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
      exact hanti ⟨hs.1, hs.2.trans ht.2⟩ ht hs.2.le
    · apply le_of_tendsto hlim₁
      filter_upwards [Ioo_mem_nhdsLT ht.2] with s hs
      exact hanti ht ⟨ht.1.trans hs.1, hs.2⟩ hs.1.le
  refine ⟨hratio, ?_⟩
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := isGeodesic_contMDiff (I := I) g
    (intrinsicGeodesic_isGeodesic (I := I) g hEnorm x v)
    (intrinsicGeodesic_continuous (I := I) g hEnorm x v)
  have hspeed (t : ℝ) : g.inner (γ t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t) = ℓ ^ 2 := by
    calc
      _ = g.inner x v v := by
        with_unfolding_all exact
          intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x v t
      _ = ℓ ^ 2 := (Real.sq_sqrt (g.pos x v hvne).le).symm
  have hVdiff (t : ℝ) (i : Fin d) :=
    (intrJacobi_diff (I := I) g hEnorm x v (w i) t).1
  have hDVdiff (t : ℝ) (i : Fin d) :=
    (intrJacobi_diff (I := I) g hEnorm x v (w i) t).2
  have hVperp (t : ℝ) (ht : t ≠ 0) (i : Fin d) :
      g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
    simpa only [γ, V] using intrJacobi_perp_ne (I := I) g hEnorm x v (w i) ht (hperp i)
  have hDVperp (t : ℝ) (ht : t ≠ 0) (i : Fin d) :
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (covDerivAlong (I := I) g γ (V i) t) = 0 := by
    simpa only [γ, V] using intrJacobi_dperp (I := I) g hEnorm x v (w i) ht (hperp i)
  have hJ (t : ℝ) (i : Fin d) : IsJacobiAt (I := I) g γ (V i) t := by
    with_unfolding_all exact
      (intrinsic_jacobi (I := I) g hEnorm x (v : E) (w i : E) t)
  have hW : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ i j,
      jacobiWronskian (I := I) g γ (V i) (V j) t = 0 := by
    intro t ht i j
    exact wronskian_eq_zero (I := I) (by norm_num) g γ (V i) (V j) hγ
      (fun s _ => hVdiff s i) (fun s _ => hVdiff s j)
      (fun s _ => hDVdiff s i) (fun s _ => hDVdiff s j)
      (fun s _ => hJ s i) (fun s _ => hJ s j) (by simp [V]) (by simp [V])
      t ⟨ht.1.le, ht.2.le⟩
  have hwLI : LinearIndependent ℝ w := linIndep_of_ortho (E := E) (I := I) (M := M) g x w hON
  have hLI : ∀ t ∈ Set.Ioo (0 : ℝ) 1, LinearIndependent ℝ fun i => V i t := by
    intro t ht
    let L : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I
      (fun z : E => expMapIntrinsic (I := I) g hEnorm x (show TangentSpace I x from z))
      (t • (v : E))
    have hLinj : Function.Injective L := by
      unfold IsConjVec at hno
      exact Classical.not_not.mp (hno t ht)
    have hscaled : LinearIndependent ℝ fun i => t • w i := by
      have hscaled' := hwLI.units_smul (fun _ => Units.mk0 t ht.1.ne')
      change LinearIndependent ℝ (fun i => t • w i) at hscaled'
      exact hscaled'
    have hmapped := hscaled.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr hLinj)
    have he : (fun i => V i t) = fun i => L (t • (w i : E)) := by
      funext i
      with_unfolding_all exact
        (intrinsic_jacobi_at (I := I) g hEnorm x (v : E) (w i : E) t)
    rwa [he]
  have hmean : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      curveMean (I := I) g γ V t = hypMeanCurv (q * ℓ) d t := by
    intro t ht
    have hder := hasDerivAt_denRatio (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g γ V (q * ℓ) t d hqℓ ht.1 (hγ.contMDiffAt.of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
      (hVdiff t) (curveGram_det_pos (I := I) g γ V t (hLI t ht)) (hW t ht)
    have hlocal : R =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hratio s hs
    have hz := hder.unique ((hasDerivAt_const (x := t) (c := (1 : ℝ))).congr_of_eventuallyEq hlocal)
    change R t * (curveMean (I := I) g γ V t - hypMeanCurv (q * ℓ) d t) = 0 at hz
    rw [hratio t ht, one_mul] at hz
    exact sub_eq_zero.mp hz
  intro t ht
  obtain ⟨e, heON, heperp⟩ := exists_perp_pos (I := I) g (γ t)
    (curveVelocity (I := I) γ t) (by rw [hspeed t]; positivity)
  have hm := DifferentialGeometry.Geometry.Riemannian.Volume.mean_riccati_le
    (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g γ V t q ℓ (curveVelocity (I := I) γ t) rfl (Fintype.card_fin d) hd hℓ
    (hspeed t) (hVperp t ht.1.ne') (hDVperp t ht.1.ne')
    (hγ.contMDiffAt.of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
    (hVdiff t) (hDVdiff t) (hLI t ht)
    (hW t ht) (hJ t) e heON heperp hRic
  have hlocal : (curveMean (I := I) g γ V) =ᶠ[𝓝 t] hypMeanCurv (q * ℓ) d := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hmean s hs
  have heqDer := hm.1.unique
    ((hasDerivAt_hypMean hqℓ ht.1 hd).congr_of_eventuallyEq hlocal)
  rw [← hmean t ht] at heqDer
  exact (DifferentialGeometry.Geometry.Riemannian.Volume.mean_riccati_eq_iff
    (I := I) g γ V t q ℓ
    (curveVelocity (I := I) γ t) rfl (Fintype.card_fin d) hd hℓ (hspeed t)
    (hVperp t ht.1.ne') (hDVperp t ht.1.ne') (hLI t ht) (hW t ht)
    e heON heperp hRic).mp heqDer

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
