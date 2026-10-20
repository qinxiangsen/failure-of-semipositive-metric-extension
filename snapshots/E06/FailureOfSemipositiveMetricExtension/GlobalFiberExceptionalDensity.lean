import FailureOfSemipositiveMetricExtension.GlobalFiberManifold
import FailureOfSemipositiveMetricExtension.GlobalExceptionalDensity

/-! The nonexceptional locus is genuinely dense in each actual fixed fibre. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
noncomputable section
open Set

def awayCentres (t : ℂ) : Set (Fiber t) := inclusion t ⁻¹' GlobalIncidence.awayCentres

theorem param_mem_awayCentres_iff (t : ℂ) (r : Fin 4) (e : Fin 2) (q : Coord)
    (hq : q ∈ domain t r e) : param t r e q ∈ awayCentres t ↔ q.1 ≠ 0 :=
  GlobalIncidence.chartParam_mem_awayCentres_iff r e (q,t) hq

theorem awayCentres_isOpen (t : ℂ) : IsOpen (awayCentres t) :=
  GlobalIncidence.awayCentres_isOpen.preimage (inclusion_continuous t)

theorem awayCentres_dense (t : ℂ) : Dense (awayCentres t) := by
  have hd : Dense {q : Coord | q.1 ≠ 0} :=
    (dense_compl_singleton (0 : ℂ)).preimage isOpenMap_fst
  apply dense_iff_inter_open.mpr
  intro U hU ⟨p,hp⟩
  obtain ⟨⟨r,e⟩,hc⟩ := charts_cover t p
  let q := coordinates t r e p
  have hq : q ∈ domain t r e := (chart t r e).map_source hc
  have heq : param t r e q = p := param_coordinates t r e p hc
  have ho : IsOpen (domain t r e ∩ param t r e ⁻¹' U) :=
    (param_continuousOn t r e).isOpen_inter_preimage (domain_isOpen t r e) hU
  obtain ⟨q',hq',hneq⟩ := hd.inter_open_nonempty _ ho ⟨q,hq,by change param t r e q ∈ U; rwa [heq]⟩
  exact ⟨param t r e q',hq'.2,(param_mem_awayCentres_iff t r e q' hq'.1).mpr hneq⟩
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
