import FailureOfSemipositiveMetricExtension.CentralTransverseLineCoverage
import FailureOfSemipositiveMetricExtension.GenericConicDensity

/-! The actual transverse-line family covers a dense subset of the central
surface, including density near all four exceptional curves. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
noncomputable section
open Set Topology
open scoped Manifold ContDiff

def chartVector (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) : Fin 3 → ℂ :=
  GlobalIncidence.baseVector r 0 (Blowup.projection (localParam e q))

def goodPolynomial (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) : ℂ :=
  let w := chartVector r e q
  w 0 * w 1 * (w 1-w 0)

theorem goodPolynomial_contDiff (r : Fin 4) (e : Fin 2) : ContDiff ℂ ω (goodPolynomial r e) := by
  have hv : ContDiff ℂ ω (chartVector r e) :=
    (GlobalIncidence.baseVector_contDiff r ω).comp
      (contDiff_const.prodMk (localParam_projection_contDiff e ω))
  have h0 := (contDiff_apply ℂ ℂ 0).comp hv
  have h1 := (contDiff_apply ℂ ℂ 1).comp hv
  exact (h0.mul h1).mul (h1.sub h0)

theorem goodPolynomial_witness (r : Fin 4) (e : Fin 2) : goodPolynomial r e (2,3) ≠ 0 := by
  fin_cases r <;> fin_cases e <;>
    norm_num [goodPolynomial,chartVector,GlobalIncidence.baseVector,localParam,
      Blowup.projection_X,Blowup.projection_Y]

theorem goodPolynomial_nonzero_dense (r : Fin 4) (e : Fin 2) :
    Dense {q | goodPolynomial r e q ≠ 0} :=
  NearbyPencil.Conic.entire_nonzero_dense _ (goodPolynomial_contDiff r e) _ (goodPolynomial_witness r e)

theorem goodPolynomial_goodVector (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord)
    (hq : goodPolynomial r e q ≠ 0) : GoodVector (chartVector r e q) :=
  ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hq).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hq).1).2,(mul_ne_zero_iff.mp hq).2⟩

theorem goodPolynomial_param_mem (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord)
    (hq : goodPolynomial r e q ≠ 0) : FixedFiber.param 0 r e q ∈ genericLocus :=
  ⟨chartVector r e q,goodPolynomial_goodVector r e q hq,rfl⟩

theorem genericLocus_dense : Dense genericLocus := by
  apply dense_iff_inter_open.mpr
  intro U hU ⟨p,hp⟩
  obtain ⟨⟨r,e⟩,hc⟩ := FixedFiber.charts_cover 0 p
  let q := FixedFiber.coordinates 0 r e p
  have hq : q ∈ FixedFiber.domain 0 r e := (FixedFiber.chart 0 r e).map_source hc
  have heq : FixedFiber.param 0 r e q = p := FixedFiber.param_coordinates 0 r e p hc
  have ho : IsOpen (FixedFiber.domain 0 r e ∩ FixedFiber.param 0 r e ⁻¹' U) :=
    (FixedFiber.param_continuousOn 0 r e).isOpen_inter_preimage (FixedFiber.domain_isOpen 0 r e) hU
  obtain ⟨q',hq',hn⟩ := (goodPolynomial_nonzero_dense r e).inter_open_nonempty _ ho
    ⟨q,hq,by change FixedFiber.param 0 r e q ∈ U; rwa [heq]⟩
  exact ⟨FixedFiber.param 0 r e q',hq'.2,goodPolynomial_param_mem r e q' hn⟩

/-- The union of the ranges of the genuine closed holomorphic line embeddings
is dense in the actual central surface. -/
theorem line_family_dense : Dense {p : Fiber 0 | ∃ c : Data, ∃ d : Direction, param c d = p} :=
  genericLocus_dense.mono (fun p hp => genericLocus_mem_line p hp)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
