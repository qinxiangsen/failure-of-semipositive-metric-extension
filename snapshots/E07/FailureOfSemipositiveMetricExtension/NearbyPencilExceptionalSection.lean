import FailureOfSemipositiveMetricExtension.NearbyPencilBundleIsomorphism
import FailureOfSemipositiveMetricExtension.GlobalExceptional

/-! The fourth exceptional line is an actual analytic section of the nearby pencil
map. In particular the pencil map is surjective and proper, with compact fibres. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil
noncomputable section
open Set Bundle IsManifold Topology
open FixedFiberBundle
open scoped Manifold ContDiff
attribute [local instance] Classical.propDecidable

private theorem chartParam_refinement (r : Fin 4) (e : Fin 2) (q : ChartCoord)
    (hq : q ∈ chartDomain r e) :
    ∃ b : Fin 4 → Fin 2, chartParam r e q ∈ GlobalLineBundle.divisionPatch (r,e,b) := by
  let p := chartParam r e q
  let b := ((GlobalLineBundle.core 0 (fun _ => 0)).indexAt p).2
  refine ⟨b,⟨q,hq,rfl⟩,?_,?_⟩
  · exact affineBase_mem_chartSet r q.2 _
  · intro j
    by_cases hj : j = r
    · subst j
      change directions p r ∈ ProjectiveLine.chartSet (Function.update b r e r)
      rw [Function.update_self]
      change directions (chartParam r e q) r ∈ _
      rw [chartParam,localLift_direction,localParam_direction]
      exact ⟨q.1.2,rfl⟩
    · have hm := ((GlobalLineBundle.core 0 (fun _ => 0)).mem_baseSet_at p).2 j
      simpa [GlobalLineBundle.divisionFrame,Function.update_of_ne hj,b] using hm

/-- The actual global map in each actual blow-up chart is projectivization of
exactly the divided polynomial pair already constructed in the paper's pencil. -/
theorem pencilMap_param (t : ℂ) (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord)
    (hq : q ∈ FixedFiber.domain t r e) :
    pencilMap t (FixedFiber.param t r e q) =
      ProjectiveLine.vectorPoint (fun k => GlobalLineBundle.pencilLocalCoefficient r e k (q,t)) := by
  obtain ⟨b,hb⟩ := chartParam_refinement r e (q,t) hq
  let d : GlobalLineBundle.DivisionIndex := (r,e,b)
  let p := FixedFiber.param t r e q
  have hi : p ∈ baseSet t (GlobalLineBundle.divisionFrame d) := hb.2
  have hn := GlobalLineBundle.pencilOtherDenominator_ne_zero d (chartParam r e (q,t)) hb
  rw [pencilMap_local t (GlobalLineBundle.divisionFrame d) p hi]
  have hv : localVector t (GlobalLineBundle.divisionFrame d) p =
      (GlobalLineBundle.pencilOtherDenominator d (chartParam r e (q,t)))⁻¹ •
        (fun k => GlobalLineBundle.pencilLocalCoefficient r e k (q,t)) := by
    ext k
    change (GlobalLineBundle.liftedPencil k).coefficient (GlobalLineBundle.divisionFrame d)
      (chartParam r e (q,t)) = _
    rw [GlobalLineBundle.liftedPencil_coefficient k d _ hb]
    change GlobalLineBundle.pencilLocalCoefficient r e k (chartCoordinates r e (chartParam r e (q,t))) /
      GlobalLineBundle.pencilOtherDenominator d (chartParam r e (q,t)) = _
    rw [chartCoordinates_param]
    simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
    ring
  rw [hv,ProjectiveLine.vectorPoint_smul _ (inv_ne_zero hn)]

/-- The true fourth exceptional point, considered as a point of the fixed fibre. -/
def exceptionalParam (t : ℂ) (d : Direction) : Fiber t :=
  ⟨((pointOverCentre 3 t d).val.1,(pointOverCentre 3 t d).val.2.1),(pointOverCentre 3 t d).property⟩

@[simp] theorem inclusion_exceptionalParam (t : ℂ) (d : Direction) :
    FixedFiber.inclusion t (exceptionalParam t d) = pointOverCentre 3 t d := rfl

@[simp] theorem exceptionalParam_param (t : ℂ) (e : Fin 2) (s : ℂ) :
    exceptionalParam t (ProjectiveLine.param e s) = FixedFiber.param t 3 e (0,s) := by
  apply FixedFiber.inclusion_injective t
  rw [inclusion_exceptionalParam,FixedFiber.inclusion_param,chartParam_exceptional]

theorem exceptionalParam_contMDiff (t : ℂ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) ω (exceptionalParam t) := by
  intro d
  obtain ⟨e,s,hs⟩ := ProjectiveLine.charts_cover d
  have hd : d ∈ ProjectiveLine.chartSet e := ⟨s,hs.symm⟩
  have hc := (ProjectiveLineBundle.coordinates_contMDiffOn e ω).contMDiffAt
    ((ProjectiveLine.chartSet_isOpen e).mem_nhds hd)
  have hv : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) ω
      (fun w : Direction => ((0 : ℂ),ProjectiveLine.coordinates e w)) d :=
    contMDiffAt_const.prodMk_space hc
  have ha := (FixedFiber.param_contMDiffOn t 3 e ω).contMDiffAt
    ((FixedFiber.domain_isOpen t 3 e).mem_nhds
      (exceptional_mem_chartDomain 3 e (ProjectiveLine.coordinates e d) t))
  apply (ha.comp d hv).congr_of_eventuallyEq
  filter_upwards [(ProjectiveLine.chartSet_isOpen e).mem_nhds hd] with w hw
  change exceptionalParam t w = FixedFiber.param t 3 e (0,ProjectiveLine.coordinates e w)
  rw [← exceptionalParam_param,ProjectiveLine.param_coordinates e w hw]

/-- The fourth exceptional projective line maps identically to the pencil base. -/
@[simp] theorem pencilMap_exceptionalParam (t : ℂ) (d : Direction) :
    pencilMap t (exceptionalParam t d) = d := by
  obtain ⟨e,s,rfl⟩ := ProjectiveLine.charts_cover d
  rw [exceptionalParam_param,pencilMap_param t 3 e (0,s) (exceptional_mem_chartDomain 3 e s t)]
  fin_cases e
  · change ProjectiveLine.vectorPoint (fun k => GlobalLineBundle.pencilLocalCoefficient 3 0 k ((0,s),t)) = ProjectiveLine.param 0 s
    have hv : (fun k => GlobalLineBundle.pencilLocalCoefficient 3 0 k ((0,s),t)) = Blowup.vectorX s := by
      ext k
      fin_cases k <;> simp [GlobalLineBundle.pencilLocalCoefficient,PencilSections.x₄,Blowup.vectorX]
    rw [hv,ProjectiveLine.vectorPoint_eq_mk _ (Blowup.vectorX_ne_zero s)]
    rfl
  · change ProjectiveLine.vectorPoint (fun k => GlobalLineBundle.pencilLocalCoefficient 3 1 k ((0,s),t)) = ProjectiveLine.param 1 s
    have hv : (fun k => GlobalLineBundle.pencilLocalCoefficient 3 1 k ((0,s),t)) = Blowup.vectorY s := by
      ext k
      fin_cases k <;> simp [GlobalLineBundle.pencilLocalCoefficient,PencilSections.y₄,Blowup.vectorY]
    rw [hv,ProjectiveLine.vectorPoint_eq_mk _ (Blowup.vectorY_ne_zero s)]
    rfl

theorem exceptionalParam_injective (t : ℂ) : Function.Injective (exceptionalParam t) := by
  intro d e h
  simpa only [pencilMap_exceptionalParam] using congrArg (pencilMap t) h

theorem exceptionalParam_isClosedEmbedding (t : ℂ) : Topology.IsClosedEmbedding (exceptionalParam t) :=
  (exceptionalParam_contMDiff t).continuous.isClosedEmbedding (exceptionalParam_injective t)

theorem pencilMap_surjective (t : ℂ) : Function.Surjective (pencilMap t) :=
  fun d => ⟨exceptionalParam t d,pencilMap_exceptionalParam t d⟩

theorem pencilMap_isProperMap (t : ℂ) (ht : t ≠ 0) : IsProperMap (pencilMap t) :=
  (pencilMap_continuous t ht).isProperMap

theorem pencilMap_fiber_isCompact (t : ℂ) (ht : t ≠ 0) (d : Direction) :
    IsCompact {p : Fiber t | pencilMap t p = d} :=
  (isClosed_eq (pencilMap_continuous t ht) continuous_const).isCompact

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil
