import FailureOfSemipositiveMetricExtension.HisamotoExceptionalDivisor

/-! The exceptional defining functions glue to an actual global analytic
section of the incidence line bundle (1,-1). Its zero divisor is reduced and
is exactly the actual exceptional fibre. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto
noncomputable section
open Set Bundle Topology
open scoped Manifold ContDiff

theorem exceptionalCoefficient_contMDiffOn (f : Frame) :
    ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ) ω (exceptionalCoefficient f) (LineBundle.baseSet f) := by
  rcases f with ⟨i,j⟩
  fin_cases j
  · have h := (contDiff_fst : ContDiff ℂ ω (Prod.fst : Coord → ℂ)).contMDiff.comp_contMDiffOn
      (affineCoordinates_contMDiffOn i 0 ω)
    apply h.congr
    intro q hq
    have he := (affineChart i 0).left_inv hq
    change affineParam i 0 ((affineChart i 0) q) = q at he
    change exceptionalCoefficient (i,0) q = ((affineChart i 0) q).1
    calc
      _ = exceptionalCoefficient (i,0) (affineParam i 0 ((affineChart i 0) q)) := congrArg _ he.symm
      _ = _ := exceptionalCoefficient_affine_zero i _
  · apply (contMDiffOn_const : ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ) ω (fun _ : Point => (1 : ℂ)) _).congr
    intro q hq
    have he := (affineChart i 1).left_inv hq
    change affineParam i 1 ((affineChart i 1) q) = q at he
    change exceptionalCoefficient (i,1) q = 1
    calc
      _ = exceptionalCoefficient (i,1) (affineParam i 1 ((affineChart i 1) q)) := congrArg _ he.symm
      _ = _ := exceptionalCoefficient_affine_one i _

/-- A section of the actual vector bundle, expressed in its selected frame. -/
def exceptionalSection (q : Point) : (LineBundle.core 1 (-1)).Fiber q :=
  exceptionalCoefficient ((LineBundle.core 1 (-1)).indexAt q) q

def exceptionalSectionMap (q : Point) : (LineBundle.core 1 (-1)).TotalSpace := ⟨q,exceptionalSection q⟩

theorem exceptionalSection_frame (f : Frame) (q : Point) (hq : q ∈ LineBundle.baseSet f) :
    (LineBundle.core 1 (-1)).localTriv f (exceptionalSectionMap q) = (q,exceptionalCoefficient f q) := by
  refine Prod.ext ?_ ?_
  · rfl
  · exact (exceptionalCoefficient_compatible ((LineBundle.core 1 (-1)).indexAt q) f q
    ⟨(LineBundle.core 1 (-1)).mem_baseSet_at q,hq⟩).symm

theorem exceptionalSection_analytic :
    ContMDiff 𝓘(ℂ,Coord) (𝓘(ℂ,Coord).prod 𝓘(ℂ)) ω exceptionalSectionMap := by
  intro q
  let f := (LineBundle.core 1 (-1)).indexAt q
  have hq : q ∈ LineBundle.baseSet f := (LineBundle.core 1 (-1)).mem_baseSet_at q
  let e := (LineBundle.core 1 (-1)).localTriv f
  letI : MemTrivializationAtlas e := ⟨⟨f,rfl⟩⟩
  apply (e.contMDiffAt_iff (show exceptionalSectionMap q ∈ e.source from hq)).mpr
  constructor
  · exact contMDiffAt_id
  · have h := (exceptionalCoefficient_contMDiffOn f).contMDiffAt
      ((LineBundle.core 1 (-1)).isOpen_baseSet f |>.mem_nhds hq)
    apply h.congr_of_eventuallyEq
    filter_upwards [(LineBundle.core 1 (-1)).isOpen_baseSet f |>.mem_nhds hq] with p hp
    exact congrArg Prod.snd (exceptionalSection_frame f p hp)

theorem exceptionalSection_zero_iff (q : Point) : exceptionalSection q = 0 ↔ q ∈ exceptionalSet :=
  exceptionalCoefficient_zero_iff ((LineBundle.core 1 (-1)).indexAt q) q
    ((LineBundle.core 1 (-1)).mem_baseSet_at q)

/-- In charts meeting the zero locus its frame expression is one coordinate,
so no higher vanishing multiplicity is hidden in the bundle identification. -/
theorem exceptionalSection_reduced_local (i : Fin 2) (q : Coord) :
    (LineBundle.core 1 (-1)).localTriv (i,0) (exceptionalSectionMap (affineParam i 0 q)) =
      (affineParam i 0 q,q.1) := by
  have hq : affineParam i 0 q ∈ LineBundle.baseSet (i,0) :=
    (affineChart i 0).map_target (by rw [affineChart_target]; exact mem_univ q)
  have h := exceptionalSection_frame (i,0) (affineParam i 0 q) hq
  rw [exceptionalCoefficient_affine_zero] at h
  exact h

end
end FailureOfSemipositiveMetricExtension.Hisamoto
