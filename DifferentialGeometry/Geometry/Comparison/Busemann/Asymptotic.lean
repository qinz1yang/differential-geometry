import DifferentialGeometry.Geometry.Comparison.Busemann.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.NoConjugatePoints.MinimizingSegment

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Topology
open scoped ENNReal Manifold

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open Exponential Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_asymptotic_ray
    [ConnectedSpace M]
    [RiemannianBundle (fun z : M => TangentSpace I z)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun z : M => TangentSpace I z)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {p : M} {gamma : Real → M}
    (hgamma : IsMinimizingRay (I := I) g p gamma) (x : M) :
    ∃ u : TangentSpace I x, g.inner x u u = 1 ∧
      let sigma : Real → M := fun t ↦
        expMapIntrinsic (I := I) g hEnorm x (t • u)
      IsMinimizingRay (I := I) g x sigma ∧
        ∀ (t : Real), 0 ≤ t → ∀ y : M,
          busemann (I := I) gamma y ≤
            (riemannianEDist I (sigma t) y).toReal - t +
              busemann (I := I) gamma x := by
  classical
  let D : Real := (riemannianEDist I (gamma 0) x).toReal
  obtain ⟨N, hN⟩ := exists_nat_gt D
  let pole : Nat → Nat := fun n ↦ N + n
  have hpole_mono : StrictMono pole := by
    intro a b hab
    exact Nat.add_lt_add_left hab N
  let L : Nat → Real := fun n ↦
    (riemannianEDist I x (gamma (pole n : Real))).toReal
  have hfin (n : Nat) :
      riemannianEDist I x (gamma (pole n : Real)) ≠ (⊤ : ENNReal) :=
    riemannianEDist_ne_top (I := I) x (gamma (pole n : Real))
  choose v hv_exp hv_len using fun n : Nat ↦
    minExp_of_ne_top (I := I) g hEnorm x (gamma (pole n : Real)) (hfin n)
  have hL_pos (n : Nat) : 0 < L n := by
    have hsym :
        (riemannianEDist I (gamma (pole n : Real)) x).toReal = L n := by
      exact congrArg ENNReal.toReal
        (Manifold.riemannianEDist_comm (I := I)
          (x := gamma (pole n : Real)) (y := x))
    have hlower : -D ≤ L n - (pole n : Real) := by
      simpa only [D, busemannApprox, hsym] using
        busemannApprox_lower_bound (I := I) hgamma x (pole n)
    have hNp : N ≤ pole n := by simp only [pole, Nat.le_add_right]
    have hNp_real : (N : Real) ≤ (pole n : Real) := by exact_mod_cast hNp
    have hDp : D < (pole n : Real) := hN.trans_le hNp_real
    linarith
  let u : Nat → TangentSpace I x := fun n ↦ (L n)⁻¹ • v n
  have hv_sq (n : Nat) : g.inner x (v n) (v n) = (L n) ^ 2 := by
    rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g x (v n)), hv_len n]
  have hu (n : Nat) : g.inner x (u n) (u n) = 1 := by
    change g.inner x ((L n)⁻¹ • v n) ((L n)⁻¹ • v n) = 1
    rw [gInner_smul_self (I := I) g x (L n)⁻¹ (v n), hv_sq n]
    rw [← mul_pow, inv_mul_cancel₀ (hL_pos n).ne', one_pow]
  have hscale (n : Nat) : L n • u n = v n := by
    change L n • ((L n)⁻¹ • v n) = v n
    rw [smul_smul, mul_inv_cancel₀ (hL_pos n).ne', one_smul]
  obtain ⟨uInf, huInf, phi, hphi, hu_tendsto⟩ :=
    (gUnitSphere_isCompact (I := I) g x).tendsto_subseq
      (x := u) (fun n ↦ hu n)
  change g.inner x uInf uInf = 1 at huInf
  let sigma : Real → M := fun t ↦
    expMapIntrinsic (I := I) g hEnorm x (t • uInf)
  have hsigma_tendsto (t : Real) :
      Tendsto
        (fun n : Nat ↦
          expMapIntrinsic (I := I) g hEnorm x (t • u (phi n)))
        atTop (nhds (sigma t)) := by
    have hsmul : Tendsto (fun n : Nat ↦ t • u (phi n)) atTop
        (nhds (t • uInf)) :=
      ((continuous_const_smul t).tendsto uInf).comp hu_tendsto
    change Tendsto
      (fun n : Nat ↦
        expMapIntrinsic (I := I) g hEnorm x (t • u (phi n)))
      atTop (nhds (expMapIntrinsic (I := I) g hEnorm x (t • uInf)))
    convert ((expMapIntrinsic_continuous (I := I) g hEnorm x).tendsto
      (t • uInf)).comp hsmul using 1
    · funext n
      rfl
  have hreal_triangle (a b c : M) :
      (riemannianEDist I a c).toReal ≤
        (riemannianEDist I a b).toReal +
          (riemannianEDist I b c).toReal := by
    have htri : riemannianEDist I a c ≤
        riemannianEDist I a b + riemannianEDist I b c :=
      Manifold.riemannianEDist_triangle
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr
        ⟨riemannianEDist_ne_top (I := I) a b,
          riemannianEDist_ne_top (I := I) b c⟩) htri
    rw [ENNReal.toReal_add
      (riemannianEDist_ne_top (I := I) a b)
      (riemannianEDist_ne_top (I := I) b c)] at hreal
    exact hreal
  have hsupport : ∀ (t : Real), 0 ≤ t → ∀ y : M,
      busemann (I := I) gamma y ≤
        (riemannianEDist I (sigma t) y).toReal - t +
          busemann (I := I) gamma x := by
    intro t ht y
    obtain ⟨m, hm⟩ := exists_nat_ge (t + D)
    have hL_eventually : ∀ᶠ n in atTop, t ≤ L (phi n) := by
      filter_upwards [eventually_ge_atTop m] with n hn
      have hmphi : m ≤ phi n := hn.trans (hphi.id_le n)
      have hmPole : m ≤ pole (phi n) := hmphi.trans (by simp only [pole, Nat.le_add_left])
      have hmPole_real : (m : Real) ≤ (pole (phi n) : Real) := by
        exact_mod_cast hmPole
      have htDPole : t + D ≤ (pole (phi n) : Real) := hm.trans hmPole_real
      have hsym :
          (riemannianEDist I (gamma (pole (phi n) : Real)) x).toReal =
            L (phi n) := by
        exact congrArg ENNReal.toReal
          (Manifold.riemannianEDist_comm (I := I)
            (x := gamma (pole (phi n) : Real)) (y := x))
      have hlower : -D ≤ L (phi n) - (pole (phi n) : Real) := by
        simpa only [D, busemannApprox, hsym] using
          busemannApprox_lower_bound (I := I) hgamma x (pole (phi n))
      linarith
    have hfinite : ∀ᶠ n in atTop,
        busemannApprox (I := I) gamma (pole (phi n)) y ≤
          (riemannianEDist I
              (expMapIntrinsic (I := I) g hEnorm x (t • u (phi n))) y).toReal - t +
            busemannApprox (I := I) gamma (pole (phi n)) x := by
      filter_upwards [hL_eventually] with n htL
      have hLne : L (phi n) ≠ 0 := (hL_pos (phi n)).ne'
      have hs : t / L (phi n) ∈ Icc (0 : Real) 1 := by
        constructor
        · exact div_nonneg ht (hL_pos (phi n)).le
        · exact (div_le_one (hL_pos (phi n))).2 htL
      have hpoint :
          intrinsicGeodesic (I := I) g hEnorm x (v (phi n))
              (t / L (phi n)) =
            expMapIntrinsic (I := I) g hEnorm x (t • u (phi n)) := by
        have hsmul :
            (t / L (phi n)) • (L (phi n) • u (phi n)) =
              t • u (phi n) := by
          rw [smul_smul]
          congr 1
          field_simp [hLne]
        rw [← hscale (phi n)]
        calc
          intrinsicGeodesic (I := I) g hEnorm x
                (L (phi n) • u (phi n)) (t / L (phi n)) =
              intrinsicGeodesic (I := I) g hEnorm x
                ((t / L (phi n)) • (L (phi n) • u (phi n))) 1 :=
            (intrinsicGeodesic_smul (I := I) g hEnorm x
              (L (phi n) • u (phi n)) (t / L (phi n))).symm
          _ = expMapIntrinsic (I := I) g hEnorm x
                (t • u (phi n)) := by rw [hsmul, expMapIntrinsic_def]
      have htail :=
        Variation.minSegment_tail_edist (I := I) g hEnorm (v (phi n))
          (hv_exp (phi n)) (hv_len (phi n)) rfl (hfin (phi n)) hs
      rw [hpoint] at htail
      have htail_arg :
          (1 - t / L (phi n)) * L (phi n) = L (phi n) - t := by
        field_simp [hLne]
      rw [htail_arg] at htail
      have htri := hreal_triangle (gamma (pole (phi n) : Real))
        (expMapIntrinsic (I := I) g hEnorm x (t • u (phi n))) y
      have htail' :
          riemannianEDist I (gamma (pole (phi n) : Real))
              (expMapIntrinsic (I := I) g hEnorm x (t • u (phi n))) =
            ENNReal.ofReal (L (phi n) - t) := by
        simpa only [riemannianEDist_comm] using htail
      rw [htail', ENNReal.toReal_ofReal (sub_nonneg.mpr htL)] at htri
      have hsym :
          (riemannianEDist I (gamma (pole (phi n) : Real)) x).toReal =
            L (phi n) := by
        exact congrArg ENNReal.toReal
          (Manifold.riemannianEDist_comm (I := I)
            (x := gamma (pole (phi n) : Real)) (y := x))
      dsimp only [busemannApprox]
      rw [hsym]
      linarith
    have hpole_tendsto : Tendsto (fun n : Nat ↦ pole (phi n)) atTop atTop :=
      hpole_mono.tendsto_atTop.comp hphi.tendsto_atTop
    have hleft : Tendsto
        (fun n : Nat ↦ busemannApprox (I := I) gamma (pole (phi n)) y)
        atTop (nhds (busemann (I := I) gamma y)) :=
      (tendsto_busemannApprox (I := I) hgamma y).comp hpole_tendsto
    have hed_tendsto : Tendsto
        (fun n : Nat ↦ riemannianEDist I
          (expMapIntrinsic (I := I) g hEnorm x (t • u (phi n))) y)
        atTop (nhds (riemannianEDist I (sigma t) y)) :=
      ((continuous_riemannianEDist_to (I := I) y).tendsto (sigma t)).comp
        (hsigma_tendsto t)
    have hdist_tendsto : Tendsto
        (fun n : Nat ↦
          (riemannianEDist I
            (expMapIntrinsic (I := I) g hEnorm x (t • u (phi n))) y).toReal)
        atTop (nhds ((riemannianEDist I (sigma t) y).toReal)) :=
      (ENNReal.continuousAt_toReal
        (riemannianEDist_ne_top (I := I) (sigma t) y)).tendsto.comp hed_tendsto
    have hxlim : Tendsto
        (fun n : Nat ↦ busemannApprox (I := I) gamma (pole (phi n)) x)
        atTop (nhds (busemann (I := I) gamma x)) :=
      (tendsto_busemannApprox (I := I) hgamma x).comp hpole_tendsto
    have htlim : Tendsto (fun _ : Nat ↦ t) atTop (nhds t) :=
      tendsto_const_nhds
    have hright := (hdist_tendsto.sub htlim).add hxlim
    exact le_of_tendsto_of_tendsto hleft hright hfinite
  have hradial : ∀ ⦃t : Real⦄, 0 ≤ t →
      riemannianEDist I x (sigma t) = ENNReal.ofReal t := by
    intro t ht
    have hupper : riemannianEDist I x (sigma t) ≤ ENNReal.ofReal t := by
      have h := intrinsicGeodesic_riemannianEDist_le
        (I := I) g hEnorm x uInf (s := 0) (t := t) ht
      rw [intrinsicGeodesic_zero (I := I) g hEnorm x uInf,
        huInf, Real.sqrt_one, one_mul, sub_zero] at h
      simpa only [sigma, expMapIntrinsic_def,
        intrinsicGeodesic_smul] using h
    have hsupp := hsupport t ht x
    have hlower_real : t ≤ (riemannianEDist I x (sigma t)).toReal := by
      have hcomm :
          (riemannianEDist I (sigma t) x).toReal =
            (riemannianEDist I x (sigma t)).toReal :=
        congrArg ENNReal.toReal
          (Manifold.riemannianEDist_comm (I := I)
            (x := sigma t) (y := x))
      rw [hcomm] at hsupp
      linarith
    have hlower : ENNReal.ofReal t ≤ riemannianEDist I x (sigma t) :=
      (ENNReal.ofReal_le_iff_le_toReal
        (riemannianEDist_ne_top (I := I) x (sigma t))).2 hlower_real
    exact le_antisymm hupper hlower
  have hbuse_sigma : ∀ ⦃t : Real⦄, 0 ≤ t →
      busemann (I := I) gamma (sigma t) =
        busemann (I := I) gamma x - t := by
    intro t ht
    have hsupp := hsupport t ht (sigma t)
    have hsub := busemann_sub_le (I := I) hgamma x (sigma t)
    have hdist : (riemannianEDist I x (sigma t)).toReal = t := by
      rw [hradial ht, ENNReal.toReal_ofReal ht]
    simp only [riemannianEDist_self, ENNReal.toReal_zero, zero_sub] at hsupp
    rw [hdist] at hsub
    linarith
  have hsigma_start : sigma 0 = x := by
    simp only [sigma, zero_smul]
    exact expMapIntrinsic_zero (I := I) g hEnorm x
  have hsigma_geo : IsGeodesicOn (I := I) g sigma (Ici 0) := by
    have hsigma : sigma = intrinsicGeodesic (I := I) g hEnorm x uInf := by
      funext t
      simpa only [sigma, expMapIntrinsic_def] using
        intrinsicGeodesic_smul (I := I) g hEnorm x uInf t
    rw [hsigma]
    exact (intrinsicGeodesic_isGeodesic (I := I) g hEnorm x uInf).isGeodesicOn
      (Ici 0)
  have hsigma_pair : ∀ ⦃s t : Real⦄, 0 ≤ s → s ≤ t →
      riemannianEDist I (sigma s) (sigma t) = ENNReal.ofReal (t - s) := by
    intro s t hs hst
    have hupper : riemannianEDist I (sigma s) (sigma t) ≤
        ENNReal.ofReal (t - s) := by
      have h := intrinsicGeodesic_riemannianEDist_le
        (I := I) g hEnorm x uInf (s := s) (t := t) hst
      rw [huInf, Real.sqrt_one, one_mul] at h
      simpa only [sigma, expMapIntrinsic_def,
        intrinsicGeodesic_smul] using h
    have hsub := busemann_sub_le (I := I) hgamma (sigma s) (sigma t)
    rw [hbuse_sigma hs, hbuse_sigma (hs.trans hst)] at hsub
    have hlower_real : t - s ≤
        (riemannianEDist I (sigma s) (sigma t)).toReal := by
      linarith
    have hlower : ENNReal.ofReal (t - s) ≤
        riemannianEDist I (sigma s) (sigma t) :=
      (ENNReal.ofReal_le_iff_le_toReal
        (riemannianEDist_ne_top (I := I) (sigma s) (sigma t))).2 hlower_real
    exact le_antisymm hupper hlower
  refine ⟨uInf, huInf, ?_⟩
  exact ⟨⟨hsigma_start, hsigma_geo, hsigma_pair⟩, hsupport⟩

end Riemannian
end Geometry
end DifferentialGeometry
