import FailureOfSemipositiveMetricExtension.GlobalExceptionalOrder

/-! Density of the nonexceptional locus in the actual global family. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set

def awayCentres : Set Total := {p | ∀ r, blowdown p ≠ centre r (projection p)}

theorem chartParam_eq_centre_iff (r : Fin 4) (e : Fin 2) (q : ChartCoord) :
    blowdown (chartParam r e q) = centre r q.2 ↔ q.1.1 = 0 := by
  change affineBase r q.2 (FailureOfSemipositiveMetricExtension.Blowup.projection (localParam e q.1)) = _ ↔ _
  rw [← affineBase_zero r q.2,(affineBase_injective r q.2).eq_iff]
  fin_cases e
  · exact FailureOfSemipositiveMetricExtension.Blowup.projection_X_eq_zero_iff q.1.1 q.1.2
  · exact FailureOfSemipositiveMetricExtension.Blowup.projection_Y_eq_zero_iff q.1.1 q.1.2

theorem chartParam_mem_awayCentres_iff (r : Fin 4) (e : Fin 2) (q : ChartCoord)
    (hq : q ∈ chartDomain r e) :
    chartParam r e q ∈ awayCentres ↔ q.1.1 ≠ 0 := by
  constructor
  · intro h hz
    exact h r ((chartParam_eq_centre_iff r e q).mpr hz)
  · intro h j
    by_cases hj : j = r
    · subst j
      exact fun heq => h ((chartParam_eq_centre_iff r e q).mp heq)
    · exact hq j hj

theorem awayCentres_isOpen : IsOpen awayCentres := by
  rw [awayCentres,setOf_forall]
  apply isOpen_iInter_of_finite
  intro r
  exact (isClosed_eq blowdown_continuous ((centre_continuous r).comp projection_continuous)).isOpen_compl

theorem awayCentres_dense : Dense awayCentres := by
  have hd : Dense {q : ChartCoord | q.1.1 ≠ 0} :=
    (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_fst.comp isOpenMap_fst)
  apply dense_iff_inter_open.mpr
  intro U hU ⟨p,hp⟩
  obtain ⟨r,e,q,hq,hpchart⟩ := global_charts_cover p
  have ho : IsOpen (chartDomain r e ∩ chartParam r e ⁻¹' U) :=
    (chartParam_continuousOn r e).isOpen_inter_preimage (chartDomain_isOpen r e) hU
  obtain ⟨q',hq',hneq⟩ := hd.inter_open_nonempty _ ho ⟨q,hq,by change chartParam r e q ∈ U; rwa [← hpchart]⟩
  exact ⟨chartParam r e q',hq'.2,(chartParam_mem_awayCentres_iff r e q' hq'.1).mpr hneq⟩
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
