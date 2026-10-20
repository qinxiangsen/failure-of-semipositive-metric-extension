import FailureOfSemipositiveMetricExtension.GenericConicCoverage
import Mathlib.Analysis.Analytic.Uniqueness

/-! The actual generic locus is dense in each nearby surface. In each of the
eight genuine charts it is the nonzero set of an explicitly nonzero polynomial.
The only analytic input is mathlib's identity theorem on connected complex space. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set Topology
open scoped Manifold ContDiff

theorem entire_nonzero_dense (f : FixedFiber.Coord → ℂ) (hf : ContDiff ℂ ω f)
    (q : FixedFiber.Coord) (hq : f q ≠ 0) : Dense {p | f p ≠ 0} := by
  apply dense_iff_inter_open.mpr
  intro U hU ⟨p,hp⟩
  by_contra h
  have he : f =ᶠ[𝓝 p] 0 := by
    filter_upwards [hU.mem_nhds hp] with w hw
    by_contra hn
    exact h ⟨w,hw,hn⟩
  exact hq ((hf.analyticOnNhd (s := Set.univ)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ p) he (mem_univ q))

def chartVector (t : ℂ) (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) : Fin 3 → ℂ :=
  GlobalIncidence.baseVector r t (Blowup.projection (localParam e q))

def goodPolynomial (t : ℂ) (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) : ℂ :=
  let w := chartVector t r e q
  Coordinates.F₁ t (w 0) (w 1) (w 2) * Coordinates.F₂ t (w 0) (w 1) (w 2) *
    (Coordinates.F₂ t (w 0) (w 1) (w 2)-Coordinates.F₁ t (w 0) (w 1) (w 2))

theorem goodPolynomial_contDiff (t : ℂ) (r : Fin 4) (e : Fin 2) :
    ContDiff ℂ ω (goodPolynomial t r e) := by
  have hv : ContDiff ℂ ω (chartVector t r e) :=
    (GlobalIncidence.baseVector_contDiff r ω).comp
      (contDiff_const.prodMk (localParam_projection_contDiff e ω))
  have h0 := (contDiff_apply ℂ ℂ 0).comp hv
  have h1 := (contDiff_apply ℂ ℂ 1).comp hv
  have h2 := (contDiff_apply ℂ ℂ 2).comp hv
  unfold goodPolynomial Coordinates.F₁ Coordinates.F₂
  exact ((h0.mul (h2.sub (contDiff_const.mul h1))).mul
    (h1.mul (h2.sub (contDiff_const.mul h0)))).mul
      ((h1.mul (h2.sub (contDiff_const.mul h0))).sub (h0.mul (h2.sub (contDiff_const.mul h1))))

def polynomialWitness (t : ℂ) (r : Fin 4) (e : Fin 2) : FixedFiber.Coord :=
  match r,e with
  | 0,0 => (2,3*t/2)
  | 0,1 => (3*t,2/(3*t))
  | 1,0 => (1/2,3*t)
  | 1,1 => (3*t/2,1/(3*t))
  | 2,0 => (1,2*t)
  | 2,1 => (2*t,1/(2*t))
  | 3,0 => (1/(3*t),2)
  | 3,1 => (2/(3*t),1/2)

theorem goodPolynomial_witness (t : ℂ) (ht : t ≠ 0) (r : Fin 4) (e : Fin 2) :
    goodPolynomial t r e (polynomialWitness t r e) ≠ 0 := by
  fin_cases r <;> fin_cases e <;>
    simp only [goodPolynomial,chartVector,polynomialWitness,GlobalIncidence.baseVector,
      localParam,Blowup.projection_X,Blowup.projection_Y,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one,Coordinates.F₁,Coordinates.F₂]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp [ht,pow_ne_zero,div_ne_zero]
  all_goals ring_nf
  all_goals simp [ht,pow_ne_zero]

theorem goodPolynomial_nonzero_dense (t : ℂ) (ht : t ≠ 0) (r : Fin 4) (e : Fin 2) :
    Dense {q | goodPolynomial t r e q ≠ 0} :=
  entire_nonzero_dense _ (goodPolynomial_contDiff t r e) _ (goodPolynomial_witness t ht r e)

theorem goodPolynomial_goodVector (t : ℂ) (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord)
    (hq : goodPolynomial t r e q ≠ 0) : GoodVector t (chartVector t r e q) := by
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hq).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hq).1).2,(mul_ne_zero_iff.mp hq).2⟩

theorem goodPolynomial_param_mem (t : ℂ) (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord)
    (hq : goodPolynomial t r e q ≠ 0) : FixedFiber.param t r e q ∈ genericLocus t :=
  ⟨chartVector t r e q,goodPolynomial_goodVector t r e q hq,rfl⟩

/-- Density in the existing subspace topology of the actual fixed incidence fibre. -/
theorem genericLocus_dense (t : ℂ) (ht : t ≠ 0) : Dense (genericLocus t) := by
  apply dense_iff_inter_open.mpr
  intro U hU ⟨p,hp⟩
  obtain ⟨⟨r,e⟩,hc⟩ := FixedFiber.charts_cover t p
  let q := FixedFiber.coordinates t r e p
  have hq : q ∈ FixedFiber.domain t r e := (FixedFiber.chart t r e).map_source hc
  have heq : FixedFiber.param t r e q = p := FixedFiber.param_coordinates t r e p hc
  have ho : IsOpen (FixedFiber.domain t r e ∩ FixedFiber.param t r e ⁻¹' U) :=
    (FixedFiber.param_continuousOn t r e).isOpen_inter_preimage (FixedFiber.domain_isOpen t r e) hU
  obtain ⟨q',hq',hn⟩ := (goodPolynomial_nonzero_dense t ht r e).inter_open_nonempty _ ho
    ⟨q,hq,by change FixedFiber.param t r e q ∈ U; rwa [heq]⟩
  exact ⟨FixedFiber.param t r e q',hq'.2,goodPolynomial_param_mem t r e q' hn⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
